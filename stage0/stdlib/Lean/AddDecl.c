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
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind(lean_object* v_env_1784_, lean_object* v_declName_1785_, uint8_t v_kind_1786_){
_start:
{
lean_object* v___x_1787_; uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1787_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_1788_ = 0;
v___x_1789_ = lean_box(v_kind_1786_);
v___x_1790_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1787_, v_env_1784_, v_declName_1785_, v___x_1789_, v___x_1788_);
return v___x_1790_;
}
}
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind___boxed(lean_object* v_env_1791_, lean_object* v_declName_1792_, lean_object* v_kind_1793_){
_start:
{
uint8_t v_kind_boxed_1794_; lean_object* v_res_1795_; 
v_kind_boxed_1794_ = lean_unbox(v_kind_1793_);
v_res_1795_ = l_Lean_recordOriginalConstKind(v_env_1791_, v_declName_1792_, v_kind_boxed_1794_);
return v_res_1795_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1796_, lean_object* v___y_1797_){
_start:
{
lean_object* v___x_1799_; lean_object* v_nextMacroScope_1800_; lean_object* v_ngen_1801_; lean_object* v_auxDeclNGen_1802_; lean_object* v_traceState_1803_; lean_object* v_recordedDeps_1804_; lean_object* v_messages_1805_; lean_object* v_infoState_1806_; lean_object* v_snapshotTasks_1807_; lean_object* v___x_1809_; uint8_t v_isShared_1810_; uint8_t v_isSharedCheck_1818_; 
v___x_1799_ = lean_st_ref_take(v___y_1797_);
v_nextMacroScope_1800_ = lean_ctor_get(v___x_1799_, 1);
v_ngen_1801_ = lean_ctor_get(v___x_1799_, 2);
v_auxDeclNGen_1802_ = lean_ctor_get(v___x_1799_, 3);
v_traceState_1803_ = lean_ctor_get(v___x_1799_, 4);
v_recordedDeps_1804_ = lean_ctor_get(v___x_1799_, 6);
v_messages_1805_ = lean_ctor_get(v___x_1799_, 7);
v_infoState_1806_ = lean_ctor_get(v___x_1799_, 8);
v_snapshotTasks_1807_ = lean_ctor_get(v___x_1799_, 9);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1799_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; lean_object* v_unused_1820_; 
v_unused_1819_ = lean_ctor_get(v___x_1799_, 5);
lean_dec(v_unused_1819_);
v_unused_1820_ = lean_ctor_get(v___x_1799_, 0);
lean_dec(v_unused_1820_);
v___x_1809_ = v___x_1799_;
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
else
{
lean_inc(v_snapshotTasks_1807_);
lean_inc(v_infoState_1806_);
lean_inc(v_messages_1805_);
lean_inc(v_recordedDeps_1804_);
lean_inc(v_traceState_1803_);
lean_inc(v_auxDeclNGen_1802_);
lean_inc(v_ngen_1801_);
lean_inc(v_nextMacroScope_1800_);
lean_dec(v___x_1799_);
v___x_1809_ = lean_box(0);
v_isShared_1810_ = v_isSharedCheck_1818_;
goto v_resetjp_1808_;
}
v_resetjp_1808_:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1811_ = lean_box(0);
v___x_1812_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1810_ == 0)
{
lean_ctor_set(v___x_1809_, 5, v___x_1812_);
lean_ctor_set(v___x_1809_, 0, v_env_1796_);
v___x_1814_ = v___x_1809_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_env_1796_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_nextMacroScope_1800_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_ngen_1801_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_auxDeclNGen_1802_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_traceState_1803_);
lean_ctor_set(v_reuseFailAlloc_1817_, 5, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1817_, 6, v_recordedDeps_1804_);
lean_ctor_set(v_reuseFailAlloc_1817_, 7, v_messages_1805_);
lean_ctor_set(v_reuseFailAlloc_1817_, 8, v_infoState_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 9, v_snapshotTasks_1807_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_put(v___y_1797_, v___x_1814_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v___x_1811_);
return v___x_1816_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1821_, v___y_1822_);
lean_dec(v___y_1822_);
return v_res_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_){
_start:
{
lean_object* v___x_1829_; 
v___x_1829_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1825_, v___y_1827_);
return v___x_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
return v_res_1834_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_box(0);
v___x_1836_ = l_Lean_interruptExceptionId;
v___x_1837_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
lean_ctor_set(v___x_1837_, 1, v___x_1835_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1840_, 0, v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_ref_1847_; lean_object* v___x_1848_; lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1857_; 
v_ref_1847_ = lean_ctor_get(v___y_1844_, 2);
v___x_1848_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1843_, v___y_1844_, v___y_1845_);
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1857_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1851_ = v___x_1848_;
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1857_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_inc(v_ref_1847_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v_ref_1847_);
lean_ctor_set(v___x_1853_, 1, v_a_1849_);
if (v_isShared_1852_ == 0)
{
lean_ctor_set_tag(v___x_1851_, 1);
lean_ctor_set(v___x_1851_, 0, v___x_1853_);
v___x_1855_ = v___x_1851_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
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
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_){
_start:
{
lean_object* v_res_1862_; 
v_res_1862_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1858_, v___y_1859_, v___y_1860_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1862_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v___y_1868_; lean_object* v___y_1869_; 
if (lean_obj_tag(v_ex_1863_) == 16)
{
lean_object* v___x_1873_; lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v___x_1873_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1874_ = lean_ctor_get(v___x_1873_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1873_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1873_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1873_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
else
{
v___y_1868_ = v___y_1864_;
v___y_1869_ = v___y_1865_;
goto v___jp_1867_;
}
v___jp_1867_:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1868_);
v___x_1871_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1863_, v___x_1870_);
v___x_1872_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1871_, v___y_1868_, v___y_1869_);
return v___x_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1887_, lean_object* v___y_1888_, lean_object* v___y_1889_){
_start:
{
if (lean_obj_tag(v_x_1887_) == 0)
{
lean_object* v_a_1891_; lean_object* v___x_1892_; 
v_a_1891_ = lean_ctor_get(v_x_1887_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v_x_1887_, 1);
v___x_1892_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1891_, v___y_1888_, v___y_1889_);
return v___x_1892_;
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v_x_1887_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v_x_1887_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v_x_1887_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v_x_1887_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
lean_ctor_set_tag(v___x_1895_, 0);
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_){
_start:
{
lean_object* v_res_1905_; 
v_res_1905_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1901_, v___y_1902_, v___y_1903_);
lean_dec(v___y_1903_);
lean_dec_ref(v___y_1902_);
return v_res_1905_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(1u);
v___x_1913_ = l_Lean_Level_ofNat(v___x_1912_);
return v___x_1913_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = lean_box(0);
v___x_1915_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1916_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1915_);
lean_ctor_set(v___x_1916_, 1, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1918_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1919_ = l_Lean_mkConst(v___x_1918_, v___x_1917_);
return v___x_1919_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_unsigned_to_nat(0u);
v___x_1921_ = l_Lean_Level_ofNat(v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1923_ = l_Lean_mkSort(v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_box(0);
v___x_1930_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1931_ = l_Lean_mkConst(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1932_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1933_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1934_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1935_ = l_Lean_mkAppB(v___x_1934_, v___x_1933_, v___x_1932_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
if (lean_obj_tag(v_as_x27_1941_) == 0)
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1946_, 0, v_b_1942_);
return v___x_1946_;
}
else
{
lean_object* v_head_1947_; lean_object* v_tail_1948_; lean_object* v___x_1949_; lean_object* v___y_1951_; uint8_t v___y_1952_; lean_object* v_a_1956_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; uint8_t v___x_1962_; lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v_toCold_1966_; lean_object* v_env_1967_; lean_object* v_cancelTk_x3f_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec_ref(v_b_1942_);
v_head_1947_ = lean_ctor_get(v_as_x27_1941_, 0);
v_tail_1948_ = lean_ctor_get(v_as_x27_1941_, 1);
v___x_1949_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1959_ = lean_box(0);
v___x_1960_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1947_);
v___x_1961_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1961_, 0, v_head_1947_);
lean_ctor_set(v___x_1961_, 1, v___x_1959_);
lean_ctor_set(v___x_1961_, 2, v___x_1960_);
v___x_1962_ = 0;
v___x_1963_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1963_, 0, v___x_1961_);
lean_ctor_set_uint8(v___x_1963_, sizeof(void*)*1, v___x_1962_);
v___x_1964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
v___x_1965_ = lean_st_ref_get(v___y_1944_);
v_toCold_1966_ = lean_ctor_get(v___y_1943_, 0);
v_env_1967_ = lean_ctor_get(v___x_1965_, 0);
lean_inc_ref(v_env_1967_);
lean_dec(v___x_1965_);
v_cancelTk_x3f_1968_ = lean_ctor_get(v_toCold_1966_, 10);
v___x_1969_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1943_);
v___x_1970_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1967_, v___x_1969_, v___x_1964_, v_cancelTk_x3f_1968_);
lean_dec_ref_known(v___x_1964_, 1);
lean_dec_ref(v___x_1969_);
v___x_1971_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1970_, v___y_1943_, v___y_1944_);
if (lean_obj_tag(v___x_1971_) == 0)
{
lean_object* v_a_1972_; lean_object* v___x_1973_; lean_object* v___x_1975_; uint8_t v_isShared_1976_; uint8_t v_isSharedCheck_1981_; 
v_a_1972_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1972_);
lean_dec_ref_known(v___x_1971_, 1);
v___x_1973_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1972_, v___y_1944_);
v_isSharedCheck_1981_ = !lean_is_exclusive(v___x_1973_);
if (v_isSharedCheck_1981_ == 0)
{
lean_object* v_unused_1982_; 
v_unused_1982_ = lean_ctor_get(v___x_1973_, 0);
lean_dec(v_unused_1982_);
v___x_1975_ = v___x_1973_;
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
else
{
lean_dec(v___x_1973_);
v___x_1975_ = lean_box(0);
v_isShared_1976_ = v_isSharedCheck_1981_;
goto v_resetjp_1974_;
}
v_resetjp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1979_; 
v___x_1977_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1976_ == 0)
{
lean_ctor_set(v___x_1975_, 0, v___x_1977_);
v___x_1979_ = v___x_1975_;
goto v_reusejp_1978_;
}
else
{
lean_object* v_reuseFailAlloc_1980_; 
v_reuseFailAlloc_1980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1980_, 0, v___x_1977_);
v___x_1979_ = v_reuseFailAlloc_1980_;
goto v_reusejp_1978_;
}
v_reusejp_1978_:
{
return v___x_1979_;
}
}
}
else
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1971_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1971_, 1);
v_a_1956_ = v_a_1983_;
goto v___jp_1955_;
}
v___jp_1950_:
{
if (v___y_1952_ == 0)
{
lean_dec_ref(v___y_1951_);
v_as_x27_1941_ = v_tail_1948_;
v_b_1942_ = v___x_1949_;
goto _start;
}
else
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1954_, 0, v___y_1951_);
return v___x_1954_;
}
}
v___jp_1955_:
{
uint8_t v___x_1957_; 
v___x_1957_ = l_Lean_Exception_isInterrupt(v_a_1956_);
if (v___x_1957_ == 0)
{
uint8_t v___x_1958_; 
lean_inc_ref(v_a_1956_);
v___x_1958_ = l_Lean_Exception_isRuntime(v_a_1956_);
v___y_1951_ = v_a_1956_;
v___y_1952_ = v___x_1958_;
goto v___jp_1950_;
}
else
{
v___y_1951_ = v_a_1956_;
v___y_1952_ = v___x_1957_;
goto v___jp_1950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1984_, lean_object* v_b_1985_, lean_object* v___y_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1984_, v_b_1985_, v___y_1986_, v___y_1987_);
lean_dec(v___y_1987_);
lean_dec_ref(v___y_1986_);
lean_dec(v_as_x27_1984_);
return v_res_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1990_, lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_2023_; uint8_t v___y_2024_; lean_object* v_a_2027_; lean_object* v___y_2031_; uint8_t v___y_2032_; lean_object* v_a_2035_; 
switch(lean_obj_tag(v_decl_1990_))
{
case 1:
{
lean_object* v_val_2038_; lean_object* v_toConstantVal_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; lean_object* v_fallbackDecl_2042_; lean_object* v___x_2043_; lean_object* v_toCold_2044_; lean_object* v_env_2045_; lean_object* v_cancelTk_x3f_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; 
v_val_2038_ = lean_ctor_get(v_decl_1990_, 0);
v_toConstantVal_2039_ = lean_ctor_get(v_val_2038_, 0);
v___x_2040_ = 0;
lean_inc_ref(v_toConstantVal_2039_);
v___x_2041_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2041_, 0, v_toConstantVal_2039_);
lean_ctor_set_uint8(v___x_2041_, sizeof(void*)*1, v___x_2040_);
v_fallbackDecl_2042_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2042_, 0, v___x_2041_);
v___x_2043_ = lean_st_ref_get(v_a_1992_);
v_toCold_2044_ = lean_ctor_get(v_a_1991_, 0);
v_env_2045_ = lean_ctor_get(v___x_2043_, 0);
lean_inc_ref(v_env_2045_);
lean_dec(v___x_2043_);
v_cancelTk_x3f_2046_ = lean_ctor_get(v_toCold_2044_, 10);
v___x_2047_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1991_);
v___x_2048_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2045_, v___x_2047_, v_fallbackDecl_2042_, v_cancelTk_x3f_2046_);
lean_dec_ref_known(v_fallbackDecl_2042_, 1);
lean_dec_ref(v___x_2047_);
v___x_2049_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2048_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2059_; 
lean_dec_ref_known(v_decl_1990_, 1);
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref_known(v___x_2049_, 1);
v___x_2051_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2050_, v_a_1992_);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2051_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2051_, 0);
lean_dec(v_unused_2060_);
v___x_2053_ = v___x_2051_;
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
else
{
lean_dec(v___x_2051_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2059_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2055_; lean_object* v___x_2057_; 
v___x_2055_ = lean_box(0);
if (v_isShared_2054_ == 0)
{
lean_ctor_set(v___x_2053_, 0, v___x_2055_);
v___x_2057_ = v___x_2053_;
goto v_reusejp_2056_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v___x_2055_);
v___x_2057_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2056_;
}
v_reusejp_2056_:
{
return v___x_2057_;
}
}
}
else
{
lean_object* v_a_2061_; 
v_a_2061_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2049_, 1);
v_a_2027_ = v_a_2061_;
goto v___jp_2026_;
}
}
case 2:
{
lean_object* v_val_2062_; lean_object* v_toConstantVal_2063_; uint8_t v___x_2064_; lean_object* v___x_2065_; lean_object* v_fallbackDecl_2066_; lean_object* v___x_2067_; lean_object* v_toCold_2068_; lean_object* v_env_2069_; lean_object* v_cancelTk_x3f_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v_val_2062_ = lean_ctor_get(v_decl_1990_, 0);
v_toConstantVal_2063_ = lean_ctor_get(v_val_2062_, 0);
v___x_2064_ = 0;
lean_inc_ref(v_toConstantVal_2063_);
v___x_2065_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2065_, 0, v_toConstantVal_2063_);
lean_ctor_set_uint8(v___x_2065_, sizeof(void*)*1, v___x_2064_);
v_fallbackDecl_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2066_, 0, v___x_2065_);
v___x_2067_ = lean_st_ref_get(v_a_1992_);
v_toCold_2068_ = lean_ctor_get(v_a_1991_, 0);
v_env_2069_ = lean_ctor_get(v___x_2067_, 0);
lean_inc_ref(v_env_2069_);
lean_dec(v___x_2067_);
v_cancelTk_x3f_2070_ = lean_ctor_get(v_toCold_2068_, 10);
v___x_2071_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1991_);
v___x_2072_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2069_, v___x_2071_, v_fallbackDecl_2066_, v_cancelTk_x3f_2070_);
lean_dec_ref_known(v_fallbackDecl_2066_, 1);
lean_dec_ref(v___x_2071_);
v___x_2073_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2072_, v_a_1991_, v_a_1992_);
if (lean_obj_tag(v___x_2073_) == 0)
{
lean_object* v_a_2074_; lean_object* v___x_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2083_; 
lean_dec_ref_known(v_decl_1990_, 1);
v_a_2074_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2073_, 1);
v___x_2075_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2074_, v_a_1992_);
v_isSharedCheck_2083_ = !lean_is_exclusive(v___x_2075_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v___x_2075_, 0);
lean_dec(v_unused_2084_);
v___x_2077_ = v___x_2075_;
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
else
{
lean_dec(v___x_2075_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2083_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2079_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(0);
if (v_isShared_2078_ == 0)
{
lean_ctor_set(v___x_2077_, 0, v___x_2079_);
v___x_2081_ = v___x_2077_;
goto v_reusejp_2080_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v___x_2079_);
v___x_2081_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2080_;
}
v_reusejp_2080_:
{
return v___x_2081_;
}
}
}
else
{
lean_object* v_a_2085_; 
v_a_2085_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_a_2085_);
lean_dec_ref_known(v___x_2073_, 1);
v_a_2035_ = v_a_2085_;
goto v___jp_2034_;
}
}
default: 
{
v___y_1995_ = v_a_1991_;
v___y_1996_ = v_a_1992_;
goto v___jp_1994_;
}
}
v___jp_1994_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = l_Lean_Declaration_getNames(v_decl_1990_);
v___x_1998_ = lean_box(0);
v___x_1999_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_2000_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1997_, v___x_1999_, v___y_1995_, v___y_1996_);
lean_dec(v___x_1997_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2013_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2003_ = v___x_2000_;
v_isShared_2004_ = v_isSharedCheck_2013_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_a_2001_);
lean_dec(v___x_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2013_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
lean_object* v_fst_2005_; 
v_fst_2005_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_fst_2005_);
lean_dec(v_a_2001_);
if (lean_obj_tag(v_fst_2005_) == 0)
{
lean_object* v___x_2007_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_1998_);
v___x_2007_ = v___x_2003_;
goto v_reusejp_2006_;
}
else
{
lean_object* v_reuseFailAlloc_2008_; 
v_reuseFailAlloc_2008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2008_, 0, v___x_1998_);
v___x_2007_ = v_reuseFailAlloc_2008_;
goto v_reusejp_2006_;
}
v_reusejp_2006_:
{
return v___x_2007_;
}
}
else
{
lean_object* v_val_2009_; lean_object* v___x_2011_; 
v_val_2009_ = lean_ctor_get(v_fst_2005_, 0);
lean_inc(v_val_2009_);
lean_dec_ref_known(v_fst_2005_, 1);
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v_val_2009_);
v___x_2011_ = v___x_2003_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_val_2009_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
v_a_2014_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2000_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2000_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
v___jp_2022_:
{
if (v___y_2024_ == 0)
{
lean_dec_ref(v___y_2023_);
v___y_1995_ = v_a_1991_;
v___y_1996_ = v_a_1992_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_decl_1990_);
v___x_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2025_, 0, v___y_2023_);
return v___x_2025_;
}
}
v___jp_2026_:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Exception_isInterrupt(v_a_2027_);
if (v___x_2028_ == 0)
{
uint8_t v___x_2029_; 
lean_inc_ref(v_a_2027_);
v___x_2029_ = l_Lean_Exception_isRuntime(v_a_2027_);
v___y_2023_ = v_a_2027_;
v___y_2024_ = v___x_2029_;
goto v___jp_2022_;
}
else
{
v___y_2023_ = v_a_2027_;
v___y_2024_ = v___x_2028_;
goto v___jp_2022_;
}
}
v___jp_2030_:
{
if (v___y_2032_ == 0)
{
lean_dec_ref(v___y_2031_);
v___y_1995_ = v_a_1991_;
v___y_1996_ = v_a_1992_;
goto v___jp_1994_;
}
else
{
lean_object* v___x_2033_; 
lean_dec(v_decl_1990_);
v___x_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2033_, 0, v___y_2031_);
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
v___y_2031_ = v_a_2035_;
v___y_2032_ = v___x_2037_;
goto v___jp_2030_;
}
else
{
v___y_2031_ = v_a_2035_;
v___y_2032_ = v___x_2036_;
goto v___jp_2030_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2086_, lean_object* v_a_2087_, lean_object* v_a_2088_, lean_object* v_a_2089_){
_start:
{
lean_object* v_res_2090_; 
v_res_2090_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2086_, v_a_2087_, v_a_2088_);
lean_dec(v_a_2088_);
lean_dec_ref(v_a_2087_);
return v_res_2090_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2091_, lean_object* v_x_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_){
_start:
{
lean_object* v___x_2096_; 
v___x_2096_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2092_, v___y_2093_, v___y_2094_);
return v___x_2096_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2097_, lean_object* v_x_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2097_, v_x_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2103_, lean_object* v_as_x27_2104_, lean_object* v_b_2105_, lean_object* v_a_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2104_, v_b_2105_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2111_, lean_object* v_as_x27_2112_, lean_object* v_b_2113_, lean_object* v_a_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2111_, v_as_x27_2112_, v_b_2113_, v_a_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v_as_x27_2112_);
lean_dec(v_as_2111_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2124_, v___y_2125_, v___y_2126_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
return v_res_2128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2129_, lean_object* v_ex_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v___x_2134_; 
v___x_2134_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2130_, v___y_2131_, v___y_2132_);
return v___x_2134_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2135_, lean_object* v_ex_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v_res_2140_; 
v_res_2140_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2135_, v_ex_2136_, v___y_2137_, v___y_2138_);
lean_dec(v___y_2138_);
lean_dec_ref(v___y_2137_);
return v_res_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2141_, lean_object* v_msg_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_){
_start:
{
lean_object* v___x_2146_; 
v___x_2146_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2142_, v___y_2143_, v___y_2144_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2147_, lean_object* v_msg_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2147_, v_msg_2148_, v___y_2149_, v___y_2150_);
lean_dec(v___y_2150_);
lean_dec_ref(v___y_2149_);
return v_res_2152_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = lean_unsigned_to_nat(32u);
v___x_2154_ = lean_mk_empty_array_with_capacity(v___x_2153_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
return v___x_2155_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2156_ = ((size_t)5ULL);
v___x_2157_ = lean_unsigned_to_nat(0u);
v___x_2158_ = lean_unsigned_to_nat(32u);
v___x_2159_ = lean_mk_empty_array_with_capacity(v___x_2158_);
v___x_2160_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2161_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
lean_ctor_set(v___x_2161_, 1, v___x_2159_);
lean_ctor_set(v___x_2161_, 2, v___x_2157_);
lean_ctor_set(v___x_2161_, 3, v___x_2157_);
lean_ctor_set_usize(v___x_2161_, 4, v___x_2156_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2162_){
_start:
{
lean_object* v___x_2164_; lean_object* v_traceState_2165_; lean_object* v_traces_2166_; lean_object* v___x_2167_; lean_object* v_traceState_2168_; lean_object* v_env_2169_; lean_object* v_nextMacroScope_2170_; lean_object* v_ngen_2171_; lean_object* v_auxDeclNGen_2172_; lean_object* v_cache_2173_; lean_object* v_recordedDeps_2174_; lean_object* v_messages_2175_; lean_object* v_infoState_2176_; lean_object* v_snapshotTasks_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2196_; 
v___x_2164_ = lean_st_ref_get(v___y_2162_);
v_traceState_2165_ = lean_ctor_get(v___x_2164_, 4);
lean_inc_ref(v_traceState_2165_);
lean_dec(v___x_2164_);
v_traces_2166_ = lean_ctor_get(v_traceState_2165_, 0);
lean_inc_ref(v_traces_2166_);
lean_dec_ref(v_traceState_2165_);
v___x_2167_ = lean_st_ref_take(v___y_2162_);
v_traceState_2168_ = lean_ctor_get(v___x_2167_, 4);
v_env_2169_ = lean_ctor_get(v___x_2167_, 0);
v_nextMacroScope_2170_ = lean_ctor_get(v___x_2167_, 1);
v_ngen_2171_ = lean_ctor_get(v___x_2167_, 2);
v_auxDeclNGen_2172_ = lean_ctor_get(v___x_2167_, 3);
v_cache_2173_ = lean_ctor_get(v___x_2167_, 5);
v_recordedDeps_2174_ = lean_ctor_get(v___x_2167_, 6);
v_messages_2175_ = lean_ctor_get(v___x_2167_, 7);
v_infoState_2176_ = lean_ctor_get(v___x_2167_, 8);
v_snapshotTasks_2177_ = lean_ctor_get(v___x_2167_, 9);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2167_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2179_ = v___x_2167_;
v_isShared_2180_ = v_isSharedCheck_2196_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snapshotTasks_2177_);
lean_inc(v_infoState_2176_);
lean_inc(v_messages_2175_);
lean_inc(v_recordedDeps_2174_);
lean_inc(v_cache_2173_);
lean_inc(v_traceState_2168_);
lean_inc(v_auxDeclNGen_2172_);
lean_inc(v_ngen_2171_);
lean_inc(v_nextMacroScope_2170_);
lean_inc(v_env_2169_);
lean_dec(v___x_2167_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2196_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
uint64_t v_tid_2181_; lean_object* v___x_2183_; uint8_t v_isShared_2184_; uint8_t v_isSharedCheck_2194_; 
v_tid_2181_ = lean_ctor_get_uint64(v_traceState_2168_, sizeof(void*)*1);
v_isSharedCheck_2194_ = !lean_is_exclusive(v_traceState_2168_);
if (v_isSharedCheck_2194_ == 0)
{
lean_object* v_unused_2195_; 
v_unused_2195_ = lean_ctor_get(v_traceState_2168_, 0);
lean_dec(v_unused_2195_);
v___x_2183_ = v_traceState_2168_;
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
else
{
lean_dec(v_traceState_2168_);
v___x_2183_ = lean_box(0);
v_isShared_2184_ = v_isSharedCheck_2194_;
goto v_resetjp_2182_;
}
v_resetjp_2182_:
{
lean_object* v___x_2185_; lean_object* v___x_2187_; 
v___x_2185_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2184_ == 0)
{
lean_ctor_set(v___x_2183_, 0, v___x_2185_);
v___x_2187_ = v___x_2183_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v___x_2185_);
lean_ctor_set_uint64(v_reuseFailAlloc_2193_, sizeof(void*)*1, v_tid_2181_);
v___x_2187_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 4, v___x_2187_);
v___x_2189_ = v___x_2179_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_env_2169_);
lean_ctor_set(v_reuseFailAlloc_2192_, 1, v_nextMacroScope_2170_);
lean_ctor_set(v_reuseFailAlloc_2192_, 2, v_ngen_2171_);
lean_ctor_set(v_reuseFailAlloc_2192_, 3, v_auxDeclNGen_2172_);
lean_ctor_set(v_reuseFailAlloc_2192_, 4, v___x_2187_);
lean_ctor_set(v_reuseFailAlloc_2192_, 5, v_cache_2173_);
lean_ctor_set(v_reuseFailAlloc_2192_, 6, v_recordedDeps_2174_);
lean_ctor_set(v_reuseFailAlloc_2192_, 7, v_messages_2175_);
lean_ctor_set(v_reuseFailAlloc_2192_, 8, v_infoState_2176_);
lean_ctor_set(v_reuseFailAlloc_2192_, 9, v_snapshotTasks_2177_);
v___x_2189_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_st_ref_put(v___y_2162_, v___x_2189_);
v___x_2191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2191_, 0, v_traces_2166_);
return v___x_2191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2197_);
lean_dec(v___y_2197_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v___x_2203_; 
v___x_2203_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2201_);
return v___x_2203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2208_, lean_object* v_opts_2209_, lean_object* v_act_2210_, lean_object* v_decl_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; 
lean_inc(v___y_2213_);
lean_inc_ref(v___y_2212_);
v___x_2215_ = lean_apply_2(v_act_2210_, v___y_2212_, v___y_2213_);
v___x_2216_ = l_Lean_profileitIOUnsafe___redArg(v_category_2208_, v_opts_2209_, v___x_2215_, v_decl_2211_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2217_, lean_object* v_opts_2218_, lean_object* v_act_2219_, lean_object* v_decl_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2217_, v_opts_2218_, v_act_2219_, v_decl_2220_, v___y_2221_, v___y_2222_);
lean_dec(v___y_2222_);
lean_dec_ref(v___y_2221_);
lean_dec_ref(v_opts_2218_);
lean_dec_ref(v_category_2217_);
return v_res_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2225_, lean_object* v_category_2226_, lean_object* v_opts_2227_, lean_object* v_act_2228_, lean_object* v_decl_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2226_, v_opts_2227_, v_act_2228_, v_decl_2229_, v___y_2230_, v___y_2231_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2234_, lean_object* v_category_2235_, lean_object* v_opts_2236_, lean_object* v_act_2237_, lean_object* v_decl_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2234_, v_category_2235_, v_opts_2236_, v_act_2237_, v_decl_2238_, v___y_2239_, v___y_2240_);
lean_dec(v___y_2240_);
lean_dec_ref(v___y_2239_);
lean_dec_ref(v_opts_2236_);
lean_dec_ref(v_category_2235_);
return v_res_2242_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2243_, lean_object* v_a_2244_){
_start:
{
if (lean_obj_tag(v_a_2243_) == 0)
{
lean_object* v___x_2245_; 
v___x_2245_ = l_List_reverse___redArg(v_a_2244_);
return v___x_2245_;
}
else
{
lean_object* v_head_2246_; lean_object* v_tail_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2256_; 
v_head_2246_ = lean_ctor_get(v_a_2243_, 0);
v_tail_2247_ = lean_ctor_get(v_a_2243_, 1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_a_2243_);
if (v_isSharedCheck_2256_ == 0)
{
v___x_2249_ = v_a_2243_;
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_tail_2247_);
lean_inc(v_head_2246_);
lean_dec(v_a_2243_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2256_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v___x_2253_; 
v___x_2251_ = l_Lean_MessageData_ofName(v_head_2246_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 1, v_a_2244_);
lean_ctor_set(v___x_2249_, 0, v___x_2251_);
v___x_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2251_);
lean_ctor_set(v_reuseFailAlloc_2255_, 1, v_a_2244_);
v___x_2253_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
v_a_2243_ = v_tail_2247_;
v_a_2244_ = v___x_2253_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2260_, lean_object* v_x_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2265_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2266_ = l_Lean_Declaration_getTopLevelNames(v_decl_2260_);
v___x_2267_ = lean_box(0);
v___x_2268_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2266_, v___x_2267_);
v___x_2269_ = l_Lean_MessageData_ofList(v___x_2268_);
v___x_2270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2270_, 0, v___x_2265_);
lean_ctor_set(v___x_2270_, 1, v___x_2269_);
v___x_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2271_, 0, v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2272_, lean_object* v_x_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_){
_start:
{
lean_object* v_res_2277_; 
v_res_2277_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2272_, v_x_2273_, v___y_2274_, v___y_2275_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_x_2273_);
return v_res_2277_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2278_, size_t v_i_2279_, lean_object* v_bs_2280_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2290_, lean_object* v_i_2291_, lean_object* v_bs_2292_){
_start:
{
size_t v_sz_boxed_2293_; size_t v_i_boxed_2294_; lean_object* v_res_2295_; 
v_sz_boxed_2293_ = lean_unbox_usize(v_sz_2290_);
lean_dec(v_sz_2290_);
v_i_boxed_2294_ = lean_unbox_usize(v_i_2291_);
lean_dec(v_i_2291_);
v_res_2295_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2293_, v_i_boxed_2294_, v_bs_2292_);
return v_res_2295_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2296_, lean_object* v_data_2297_, lean_object* v_ref_2298_, lean_object* v_msg_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
lean_object* v_toCold_2303_; lean_object* v_currRecDepth_2304_; lean_object* v_ref_2305_; uint16_t v_optionFlags_2306_; uint8_t v_suppressElabErrors_2307_; uint8_t v_isRecordingDeps_2308_; lean_object* v_ref_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v_traceState_2312_; lean_object* v_traces_2313_; lean_object* v___x_2314_; size_t v_sz_2315_; size_t v___x_2316_; lean_object* v___x_2317_; lean_object* v_msg_2318_; lean_object* v___x_2319_; lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2358_; 
v_toCold_2303_ = lean_ctor_get(v___y_2300_, 0);
v_currRecDepth_2304_ = lean_ctor_get(v___y_2300_, 1);
v_ref_2305_ = lean_ctor_get(v___y_2300_, 2);
v_optionFlags_2306_ = lean_ctor_get_uint16(v___y_2300_, sizeof(void*)*3);
v_suppressElabErrors_2307_ = lean_ctor_get_uint8(v___y_2300_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2308_ = lean_ctor_get_uint8(v___y_2300_, sizeof(void*)*3 + 3);
v_ref_2309_ = l_Lean_replaceRef(v_ref_2298_, v_ref_2305_);
lean_inc(v_currRecDepth_2304_);
lean_inc_ref(v_toCold_2303_);
v___x_2310_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2310_, 0, v_toCold_2303_);
lean_ctor_set(v___x_2310_, 1, v_currRecDepth_2304_);
lean_ctor_set(v___x_2310_, 2, v_ref_2309_);
lean_ctor_set_uint16(v___x_2310_, sizeof(void*)*3, v_optionFlags_2306_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3 + 2, v_suppressElabErrors_2307_);
lean_ctor_set_uint8(v___x_2310_, sizeof(void*)*3 + 3, v_isRecordingDeps_2308_);
v___x_2311_ = lean_st_ref_get(v___y_2301_);
v_traceState_2312_ = lean_ctor_get(v___x_2311_, 4);
lean_inc_ref(v_traceState_2312_);
lean_dec(v___x_2311_);
v_traces_2313_ = lean_ctor_get(v_traceState_2312_, 0);
lean_inc_ref(v_traces_2313_);
lean_dec_ref(v_traceState_2312_);
v___x_2314_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2313_);
lean_dec_ref(v_traces_2313_);
v_sz_2315_ = lean_array_size(v___x_2314_);
v___x_2316_ = ((size_t)0ULL);
v___x_2317_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2315_, v___x_2316_, v___x_2314_);
v_msg_2318_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2318_, 0, v_data_2297_);
lean_ctor_set(v_msg_2318_, 1, v_msg_2299_);
lean_ctor_set(v_msg_2318_, 2, v___x_2317_);
v___x_2319_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2318_, v___x_2310_, v___y_2301_);
lean_dec_ref_known(v___x_2310_, 3);
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2322_ = v___x_2319_;
v_isShared_2323_ = v_isSharedCheck_2358_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2319_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2358_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2324_; lean_object* v_traceState_2325_; lean_object* v_env_2326_; lean_object* v_nextMacroScope_2327_; lean_object* v_ngen_2328_; lean_object* v_auxDeclNGen_2329_; lean_object* v_cache_2330_; lean_object* v_recordedDeps_2331_; lean_object* v_messages_2332_; lean_object* v_infoState_2333_; lean_object* v_snapshotTasks_2334_; lean_object* v___x_2336_; uint8_t v_isShared_2337_; uint8_t v_isSharedCheck_2357_; 
v___x_2324_ = lean_st_ref_take(v___y_2301_);
v_traceState_2325_ = lean_ctor_get(v___x_2324_, 4);
v_env_2326_ = lean_ctor_get(v___x_2324_, 0);
v_nextMacroScope_2327_ = lean_ctor_get(v___x_2324_, 1);
v_ngen_2328_ = lean_ctor_get(v___x_2324_, 2);
v_auxDeclNGen_2329_ = lean_ctor_get(v___x_2324_, 3);
v_cache_2330_ = lean_ctor_get(v___x_2324_, 5);
v_recordedDeps_2331_ = lean_ctor_get(v___x_2324_, 6);
v_messages_2332_ = lean_ctor_get(v___x_2324_, 7);
v_infoState_2333_ = lean_ctor_get(v___x_2324_, 8);
v_snapshotTasks_2334_ = lean_ctor_get(v___x_2324_, 9);
v_isSharedCheck_2357_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2357_ == 0)
{
v___x_2336_ = v___x_2324_;
v_isShared_2337_ = v_isSharedCheck_2357_;
goto v_resetjp_2335_;
}
else
{
lean_inc(v_snapshotTasks_2334_);
lean_inc(v_infoState_2333_);
lean_inc(v_messages_2332_);
lean_inc(v_recordedDeps_2331_);
lean_inc(v_cache_2330_);
lean_inc(v_traceState_2325_);
lean_inc(v_auxDeclNGen_2329_);
lean_inc(v_ngen_2328_);
lean_inc(v_nextMacroScope_2327_);
lean_inc(v_env_2326_);
lean_dec(v___x_2324_);
v___x_2336_ = lean_box(0);
v_isShared_2337_ = v_isSharedCheck_2357_;
goto v_resetjp_2335_;
}
v_resetjp_2335_:
{
uint64_t v_tid_2338_; lean_object* v___x_2340_; uint8_t v_isShared_2341_; uint8_t v_isSharedCheck_2355_; 
v_tid_2338_ = lean_ctor_get_uint64(v_traceState_2325_, sizeof(void*)*1);
v_isSharedCheck_2355_ = !lean_is_exclusive(v_traceState_2325_);
if (v_isSharedCheck_2355_ == 0)
{
lean_object* v_unused_2356_; 
v_unused_2356_ = lean_ctor_get(v_traceState_2325_, 0);
lean_dec(v_unused_2356_);
v___x_2340_ = v_traceState_2325_;
v_isShared_2341_ = v_isSharedCheck_2355_;
goto v_resetjp_2339_;
}
else
{
lean_dec(v_traceState_2325_);
v___x_2340_ = lean_box(0);
v_isShared_2341_ = v_isSharedCheck_2355_;
goto v_resetjp_2339_;
}
v_resetjp_2339_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2342_ = lean_box(0);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v_ref_2298_);
lean_ctor_set(v___x_2343_, 1, v_a_2320_);
v___x_2344_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2296_, v___x_2343_);
if (v_isShared_2341_ == 0)
{
lean_ctor_set(v___x_2340_, 0, v___x_2344_);
v___x_2346_ = v___x_2340_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v___x_2344_);
lean_ctor_set_uint64(v_reuseFailAlloc_2354_, sizeof(void*)*1, v_tid_2338_);
v___x_2346_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2348_; 
if (v_isShared_2337_ == 0)
{
lean_ctor_set(v___x_2336_, 4, v___x_2346_);
v___x_2348_ = v___x_2336_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_env_2326_);
lean_ctor_set(v_reuseFailAlloc_2353_, 1, v_nextMacroScope_2327_);
lean_ctor_set(v_reuseFailAlloc_2353_, 2, v_ngen_2328_);
lean_ctor_set(v_reuseFailAlloc_2353_, 3, v_auxDeclNGen_2329_);
lean_ctor_set(v_reuseFailAlloc_2353_, 4, v___x_2346_);
lean_ctor_set(v_reuseFailAlloc_2353_, 5, v_cache_2330_);
lean_ctor_set(v_reuseFailAlloc_2353_, 6, v_recordedDeps_2331_);
lean_ctor_set(v_reuseFailAlloc_2353_, 7, v_messages_2332_);
lean_ctor_set(v_reuseFailAlloc_2353_, 8, v_infoState_2333_);
lean_ctor_set(v_reuseFailAlloc_2353_, 9, v_snapshotTasks_2334_);
v___x_2348_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2349_; lean_object* v___x_2351_; 
v___x_2349_ = lean_st_ref_put(v___y_2301_, v___x_2348_);
if (v_isShared_2323_ == 0)
{
lean_ctor_set(v___x_2322_, 0, v___x_2342_);
v___x_2351_ = v___x_2322_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2342_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2359_, lean_object* v_data_2360_, lean_object* v_ref_2361_, lean_object* v_msg_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2359_, v_data_2360_, v_ref_2361_, v_msg_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2367_){
_start:
{
if (lean_obj_tag(v_x_2367_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v_x_2367_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_x_2367_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v_x_2367_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v_x_2367_);
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
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
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
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
v_a_2377_ = lean_ctor_get(v_x_2367_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v_x_2367_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v_x_2367_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v_x_2367_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
lean_ctor_set_tag(v___x_2379_, 0);
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2385_);
return v_res_2387_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2388_){
_start:
{
if (lean_obj_tag(v_e_2388_) == 0)
{
uint8_t v___x_2389_; 
v___x_2389_ = 2;
return v___x_2389_;
}
else
{
uint8_t v___x_2390_; 
v___x_2390_ = 0;
return v___x_2390_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2391_){
_start:
{
uint8_t v_res_2392_; lean_object* v_r_2393_; 
v_res_2392_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2391_);
lean_dec_ref(v_e_2391_);
v_r_2393_ = lean_box(v_res_2392_);
return v_r_2393_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2394_; double v___x_2395_; 
v___x_2394_ = lean_unsigned_to_nat(0u);
v___x_2395_ = lean_float_of_nat(v___x_2394_);
return v___x_2395_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; 
v___x_2397_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2398_ = l_Lean_stringToMessageData(v___x_2397_);
return v___x_2398_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2399_; double v___x_2400_; 
v___x_2399_ = lean_unsigned_to_nat(1000u);
v___x_2400_ = lean_float_of_nat(v___x_2399_);
return v___x_2400_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2401_, uint8_t v_collapsed_2402_, lean_object* v_tag_2403_, lean_object* v_opts_2404_, uint8_t v_clsEnabled_2405_, lean_object* v_oldTraces_2406_, lean_object* v_msg_2407_, lean_object* v_resStartStop_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v_data_2417_; lean_object* v_fst_2420_; lean_object* v_snd_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___y_2425_; lean_object* v_a_2426_; uint8_t v___y_2441_; double v___y_2473_; 
v_fst_2412_ = lean_ctor_get(v_resStartStop_2408_, 0);
lean_inc(v_fst_2412_);
v_snd_2413_ = lean_ctor_get(v_resStartStop_2408_, 1);
lean_inc(v_snd_2413_);
lean_dec_ref(v_resStartStop_2408_);
v_fst_2420_ = lean_ctor_get(v_snd_2413_, 0);
lean_inc(v_fst_2420_);
v_snd_2421_ = lean_ctor_get(v_snd_2413_, 1);
lean_inc(v_snd_2421_);
lean_dec(v_snd_2413_);
v___x_2422_ = l_Lean_trace_profiler;
v___x_2423_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2404_, v___x_2422_);
if (v___x_2423_ == 0)
{
v___y_2441_ = v___x_2423_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2478_; uint8_t v___x_2479_; 
v___x_2478_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2479_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2404_, v___x_2478_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; lean_object* v___x_2481_; double v___x_2482_; double v___x_2483_; double v___x_2484_; 
v___x_2480_ = l_Lean_trace_profiler_threshold;
v___x_2481_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2404_, v___x_2480_);
v___x_2482_ = lean_float_of_nat(v___x_2481_);
v___x_2483_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2484_ = lean_float_div(v___x_2482_, v___x_2483_);
v___y_2473_ = v___x_2484_;
goto v___jp_2472_;
}
else
{
lean_object* v___x_2485_; lean_object* v___x_2486_; double v___x_2487_; 
v___x_2485_ = l_Lean_trace_profiler_threshold;
v___x_2486_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2404_, v___x_2485_);
v___x_2487_ = lean_float_of_nat(v___x_2486_);
v___y_2473_ = v___x_2487_;
goto v___jp_2472_;
}
}
v___jp_2414_:
{
lean_object* v___x_2418_; 
lean_inc(v___y_2416_);
v___x_2418_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2406_, v_data_2417_, v___y_2416_, v___y_2415_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v___x_2419_; 
lean_dec_ref_known(v___x_2418_, 1);
v___x_2419_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2412_);
return v___x_2419_;
}
else
{
lean_dec(v_fst_2412_);
return v___x_2418_;
}
}
v___jp_2424_:
{
uint8_t v_result_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; double v___x_2430_; lean_object* v_data_2431_; 
v_result_2427_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2412_);
v___x_2428_ = lean_box(v_result_2427_);
v___x_2429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2429_, 0, v___x_2428_);
v___x_2430_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2403_);
lean_inc_ref(v___x_2429_);
lean_inc(v_cls_2401_);
v_data_2431_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2431_, 0, v_cls_2401_);
lean_ctor_set(v_data_2431_, 1, v___x_2429_);
lean_ctor_set(v_data_2431_, 2, v_tag_2403_);
lean_ctor_set_float(v_data_2431_, sizeof(void*)*3, v___x_2430_);
lean_ctor_set_float(v_data_2431_, sizeof(void*)*3 + 8, v___x_2430_);
lean_ctor_set_uint8(v_data_2431_, sizeof(void*)*3 + 16, v_collapsed_2402_);
if (v___x_2423_ == 0)
{
lean_dec_ref_known(v___x_2429_, 1);
lean_dec(v_snd_2421_);
lean_dec(v_fst_2420_);
lean_dec_ref(v_tag_2403_);
lean_dec(v_cls_2401_);
v___y_2415_ = v_a_2426_;
v___y_2416_ = v___y_2425_;
v_data_2417_ = v_data_2431_;
goto v___jp_2414_;
}
else
{
lean_object* v_data_2432_; double v___x_2433_; double v___x_2434_; 
lean_dec_ref_known(v_data_2431_, 3);
v_data_2432_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2432_, 0, v_cls_2401_);
lean_ctor_set(v_data_2432_, 1, v___x_2429_);
lean_ctor_set(v_data_2432_, 2, v_tag_2403_);
v___x_2433_ = lean_unbox_float(v_fst_2420_);
lean_dec(v_fst_2420_);
lean_ctor_set_float(v_data_2432_, sizeof(void*)*3, v___x_2433_);
v___x_2434_ = lean_unbox_float(v_snd_2421_);
lean_dec(v_snd_2421_);
lean_ctor_set_float(v_data_2432_, sizeof(void*)*3 + 8, v___x_2434_);
lean_ctor_set_uint8(v_data_2432_, sizeof(void*)*3 + 16, v_collapsed_2402_);
v___y_2415_ = v_a_2426_;
v___y_2416_ = v___y_2425_;
v_data_2417_ = v_data_2432_;
goto v___jp_2414_;
}
}
v___jp_2435_:
{
lean_object* v_ref_2436_; lean_object* v___x_2437_; 
v_ref_2436_ = lean_ctor_get(v___y_2409_, 2);
lean_inc(v___y_2410_);
lean_inc_ref(v___y_2409_);
lean_inc(v_fst_2412_);
v___x_2437_ = lean_apply_4(v_msg_2407_, v_fst_2412_, v___y_2409_, v___y_2410_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
v___y_2425_ = v_ref_2436_;
v_a_2426_ = v_a_2438_;
goto v___jp_2424_;
}
else
{
lean_object* v___x_2439_; 
lean_dec_ref_known(v___x_2437_, 1);
v___x_2439_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2425_ = v_ref_2436_;
v_a_2426_ = v___x_2439_;
goto v___jp_2424_;
}
}
v___jp_2440_:
{
if (v_clsEnabled_2405_ == 0)
{
if (v___y_2441_ == 0)
{
lean_object* v___x_2442_; lean_object* v_traceState_2443_; lean_object* v_env_2444_; lean_object* v_nextMacroScope_2445_; lean_object* v_ngen_2446_; lean_object* v_auxDeclNGen_2447_; lean_object* v_cache_2448_; lean_object* v_recordedDeps_2449_; lean_object* v_messages_2450_; lean_object* v_infoState_2451_; lean_object* v_snapshotTasks_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2471_; 
lean_dec(v_snd_2421_);
lean_dec(v_fst_2420_);
lean_dec_ref(v_msg_2407_);
lean_dec_ref(v_tag_2403_);
lean_dec(v_cls_2401_);
v___x_2442_ = lean_st_ref_take(v___y_2410_);
v_traceState_2443_ = lean_ctor_get(v___x_2442_, 4);
v_env_2444_ = lean_ctor_get(v___x_2442_, 0);
v_nextMacroScope_2445_ = lean_ctor_get(v___x_2442_, 1);
v_ngen_2446_ = lean_ctor_get(v___x_2442_, 2);
v_auxDeclNGen_2447_ = lean_ctor_get(v___x_2442_, 3);
v_cache_2448_ = lean_ctor_get(v___x_2442_, 5);
v_recordedDeps_2449_ = lean_ctor_get(v___x_2442_, 6);
v_messages_2450_ = lean_ctor_get(v___x_2442_, 7);
v_infoState_2451_ = lean_ctor_get(v___x_2442_, 8);
v_snapshotTasks_2452_ = lean_ctor_get(v___x_2442_, 9);
v_isSharedCheck_2471_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2471_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2471_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_snapshotTasks_2452_);
lean_inc(v_infoState_2451_);
lean_inc(v_messages_2450_);
lean_inc(v_recordedDeps_2449_);
lean_inc(v_cache_2448_);
lean_inc(v_traceState_2443_);
lean_inc(v_auxDeclNGen_2447_);
lean_inc(v_ngen_2446_);
lean_inc(v_nextMacroScope_2445_);
lean_inc(v_env_2444_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2471_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
uint64_t v_tid_2456_; lean_object* v_traces_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2470_; 
v_tid_2456_ = lean_ctor_get_uint64(v_traceState_2443_, sizeof(void*)*1);
v_traces_2457_ = lean_ctor_get(v_traceState_2443_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v_traceState_2443_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2459_ = v_traceState_2443_;
v_isShared_2460_ = v_isSharedCheck_2470_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_traces_2457_);
lean_dec(v_traceState_2443_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2470_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2461_; lean_object* v___x_2463_; 
v___x_2461_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2406_, v_traces_2457_);
lean_dec_ref(v_traces_2457_);
if (v_isShared_2460_ == 0)
{
lean_ctor_set(v___x_2459_, 0, v___x_2461_);
v___x_2463_ = v___x_2459_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2461_);
lean_ctor_set_uint64(v_reuseFailAlloc_2469_, sizeof(void*)*1, v_tid_2456_);
v___x_2463_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
lean_object* v___x_2465_; 
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 4, v___x_2463_);
v___x_2465_ = v___x_2454_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v_env_2444_);
lean_ctor_set(v_reuseFailAlloc_2468_, 1, v_nextMacroScope_2445_);
lean_ctor_set(v_reuseFailAlloc_2468_, 2, v_ngen_2446_);
lean_ctor_set(v_reuseFailAlloc_2468_, 3, v_auxDeclNGen_2447_);
lean_ctor_set(v_reuseFailAlloc_2468_, 4, v___x_2463_);
lean_ctor_set(v_reuseFailAlloc_2468_, 5, v_cache_2448_);
lean_ctor_set(v_reuseFailAlloc_2468_, 6, v_recordedDeps_2449_);
lean_ctor_set(v_reuseFailAlloc_2468_, 7, v_messages_2450_);
lean_ctor_set(v_reuseFailAlloc_2468_, 8, v_infoState_2451_);
lean_ctor_set(v_reuseFailAlloc_2468_, 9, v_snapshotTasks_2452_);
v___x_2465_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2466_ = lean_st_ref_put(v___y_2410_, v___x_2465_);
v___x_2467_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2412_);
return v___x_2467_;
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
v___jp_2472_:
{
double v___x_2474_; double v___x_2475_; double v___x_2476_; uint8_t v___x_2477_; 
v___x_2474_ = lean_unbox_float(v_snd_2421_);
v___x_2475_ = lean_unbox_float(v_fst_2420_);
v___x_2476_ = lean_float_sub(v___x_2474_, v___x_2475_);
v___x_2477_ = lean_float_decLt(v___y_2473_, v___x_2476_);
v___y_2441_ = v___x_2477_;
goto v___jp_2440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2488_, lean_object* v_collapsed_2489_, lean_object* v_tag_2490_, lean_object* v_opts_2491_, lean_object* v_clsEnabled_2492_, lean_object* v_oldTraces_2493_, lean_object* v_msg_2494_, lean_object* v_resStartStop_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_){
_start:
{
uint8_t v_collapsed_boxed_2499_; uint8_t v_clsEnabled_boxed_2500_; lean_object* v_res_2501_; 
v_collapsed_boxed_2499_ = lean_unbox(v_collapsed_2489_);
v_clsEnabled_boxed_2500_ = lean_unbox(v_clsEnabled_2492_);
v_res_2501_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2488_, v_collapsed_boxed_2499_, v_tag_2490_, v_opts_2491_, v_clsEnabled_boxed_2500_, v_oldTraces_2493_, v_msg_2494_, v_resStartStop_2495_, v___y_2496_, v___y_2497_);
lean_dec(v___y_2497_);
lean_dec_ref(v___y_2496_);
lean_dec_ref(v_opts_2491_);
return v_res_2501_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2504_; double v___x_2505_; 
v___x_2504_ = lean_unsigned_to_nat(1000000000u);
v___x_2505_ = lean_float_of_nat(v___x_2504_);
return v___x_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2506_, lean_object* v___x_2507_, uint8_t v___x_2508_, lean_object* v___x_2509_, lean_object* v___f_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___y_2515_; lean_object* v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2528_; lean_object* v_a_2529_; lean_object* v___y_2533_; lean_object* v___y_2534_; uint8_t v___y_2535_; lean_object* v___y_2546_; lean_object* v_a_2547_; lean_object* v_toCold_2550_; lean_object* v_options_2551_; uint8_t v_hasTrace_2552_; 
v_toCold_2550_ = lean_ctor_get(v___y_2511_, 0);
v_options_2551_ = lean_ctor_get(v_toCold_2550_, 2);
v_hasTrace_2552_ = lean_ctor_get_uint8(v_options_2551_, sizeof(void*)*1);
if (v_hasTrace_2552_ == 0)
{
lean_object* v_cancelTk_x3f_2553_; lean_object* v___x_2554_; 
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec(v___x_2507_);
v_cancelTk_x3f_2553_ = lean_ctor_get(v_toCold_2550_, 10);
lean_inc(v_decl_2506_);
v___x_2554_ = l_Lean_warnIfUsesSorry(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v___x_2555_; lean_object* v_env_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec_ref_known(v___x_2554_, 1);
v___x_2555_ = lean_st_ref_get(v___y_2512_);
v_env_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc_ref(v_env_2556_);
lean_dec(v___x_2555_);
v___x_2557_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2511_);
v___x_2558_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2556_, v___x_2557_, v_decl_2506_, v_cancelTk_x3f_2553_);
lean_dec_ref(v___x_2557_);
v___x_2559_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2558_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
lean_dec(v_decl_2506_);
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2560_, v___y_2512_);
return v___x_2561_;
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
v_a_2562_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2559_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2559_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
lean_inc(v_a_2562_);
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
v___y_2546_ = v___x_2567_;
v_a_2547_ = v_a_2562_;
goto v___jp_2545_;
}
}
}
}
else
{
lean_dec(v_decl_2506_);
return v___x_2554_;
}
}
else
{
lean_object* v_cancelTk_x3f_2570_; lean_object* v_inheritedTraceOptions_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; uint8_t v___x_2574_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v_a_2578_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v_a_2593_; lean_object* v___y_2596_; lean_object* v___y_2597_; lean_object* v_a_2598_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; uint8_t v___y_2610_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v_a_2615_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v_a_2621_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v_a_2633_; lean_object* v___y_2636_; lean_object* v___y_2637_; lean_object* v_a_2638_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2647_; lean_object* v___y_2648_; lean_object* v___y_2649_; uint8_t v___y_2650_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v_a_2655_; 
v_cancelTk_x3f_2570_ = lean_ctor_get(v_toCold_2550_, 10);
v_inheritedTraceOptions_2571_ = lean_ctor_get(v_toCold_2550_, 11);
v___x_2572_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2507_);
v___x_2573_ = l_Lean_Name_append(v___x_2572_, v___x_2507_);
v___x_2574_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2571_, v_options_2551_, v___x_2573_);
lean_dec(v___x_2573_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2685_ = l_Lean_trace_profiler;
v___x_2686_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2551_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; 
lean_dec_ref(v___f_2510_);
lean_dec_ref(v___x_2509_);
lean_dec(v___x_2507_);
lean_inc(v_decl_2506_);
v___x_2687_ = l_Lean_warnIfUsesSorry(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2687_) == 0)
{
lean_object* v___x_2688_; lean_object* v_env_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
lean_dec_ref_known(v___x_2687_, 1);
v___x_2688_ = lean_st_ref_get(v___y_2512_);
v_env_2689_ = lean_ctor_get(v___x_2688_, 0);
lean_inc_ref(v_env_2689_);
lean_dec(v___x_2688_);
v___x_2690_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2511_);
v___x_2691_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2689_, v___x_2690_, v_decl_2506_, v_cancelTk_x3f_2570_);
lean_dec_ref(v___x_2690_);
v___x_2692_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2691_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; 
lean_dec(v_decl_2506_);
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
v___x_2694_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2693_, v___y_2512_);
return v___x_2694_;
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
v_a_2695_ = lean_ctor_get(v___x_2692_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2692_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2692_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
lean_inc(v_a_2695_);
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
v___y_2528_ = v___x_2700_;
v_a_2529_ = v_a_2695_;
goto v___jp_2527_;
}
}
}
}
else
{
lean_dec(v_decl_2506_);
return v___x_2687_;
}
}
else
{
goto v___jp_2658_;
}
}
else
{
goto v___jp_2658_;
}
v___jp_2575_:
{
lean_object* v___x_2579_; double v___x_2580_; double v___x_2581_; double v___x_2582_; double v___x_2583_; double v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2579_ = lean_io_mono_nanos_now();
v___x_2580_ = lean_float_of_nat(v___y_2577_);
v___x_2581_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2582_ = lean_float_div(v___x_2580_, v___x_2581_);
v___x_2583_ = lean_float_of_nat(v___x_2579_);
v___x_2584_ = lean_float_div(v___x_2583_, v___x_2581_);
v___x_2585_ = lean_box_float(v___x_2582_);
v___x_2586_ = lean_box_float(v___x_2584_);
v___x_2587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2585_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2588_, 0, v_a_2578_);
lean_ctor_set(v___x_2588_, 1, v___x_2587_);
v___x_2589_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2507_, v___x_2508_, v___x_2509_, v_options_2551_, v___x_2574_, v___y_2576_, v___f_2510_, v___x_2588_, v___y_2511_, v___y_2512_);
return v___x_2589_;
}
v___jp_2590_:
{
lean_object* v___x_2594_; 
v___x_2594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2594_, 0, v_a_2593_);
v___y_2576_ = v___y_2591_;
v___y_2577_ = v___y_2592_;
v_a_2578_ = v___x_2594_;
goto v___jp_2575_;
}
v___jp_2595_:
{
lean_object* v___x_2599_; 
v___x_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2599_, 0, v_a_2598_);
v___y_2576_ = v___y_2596_;
v___y_2577_ = v___y_2597_;
v_a_2578_ = v___x_2599_;
goto v___jp_2575_;
}
v___jp_2600_:
{
if (lean_obj_tag(v___y_2603_) == 0)
{
lean_object* v_a_2604_; 
v_a_2604_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_a_2604_);
lean_dec_ref_known(v___y_2603_, 1);
v___y_2596_ = v___y_2601_;
v___y_2597_ = v___y_2602_;
v_a_2598_ = v_a_2604_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2605_; 
v_a_2605_ = lean_ctor_get(v___y_2603_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___y_2603_, 1);
v___y_2591_ = v___y_2601_;
v___y_2592_ = v___y_2602_;
v_a_2593_ = v_a_2605_;
goto v___jp_2590_;
}
}
v___jp_2606_:
{
if (v___y_2610_ == 0)
{
lean_object* v___x_2611_; 
v___x_2611_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_dec_ref_known(v___x_2611_, 1);
v___y_2591_ = v___y_2607_;
v___y_2592_ = v___y_2609_;
v_a_2593_ = v___y_2608_;
goto v___jp_2590_;
}
else
{
lean_dec_ref(v___y_2608_);
v___y_2601_ = v___y_2607_;
v___y_2602_ = v___y_2609_;
v___y_2603_ = v___x_2611_;
goto v___jp_2600_;
}
}
else
{
lean_dec(v_decl_2506_);
v___y_2591_ = v___y_2607_;
v___y_2592_ = v___y_2609_;
v_a_2593_ = v___y_2608_;
goto v___jp_2590_;
}
}
v___jp_2612_:
{
uint8_t v___x_2616_; 
v___x_2616_ = l_Lean_Exception_isInterrupt(v_a_2615_);
if (v___x_2616_ == 0)
{
uint8_t v___x_2617_; 
lean_inc_ref(v_a_2615_);
v___x_2617_ = l_Lean_Exception_isRuntime(v_a_2615_);
v___y_2607_ = v___y_2613_;
v___y_2608_ = v_a_2615_;
v___y_2609_ = v___y_2614_;
v___y_2610_ = v___x_2617_;
goto v___jp_2606_;
}
else
{
v___y_2607_ = v___y_2613_;
v___y_2608_ = v_a_2615_;
v___y_2609_ = v___y_2614_;
v___y_2610_ = v___x_2616_;
goto v___jp_2606_;
}
}
v___jp_2618_:
{
lean_object* v___x_2622_; double v___x_2623_; double v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; 
v___x_2622_ = lean_io_get_num_heartbeats();
v___x_2623_ = lean_float_of_nat(v___y_2620_);
v___x_2624_ = lean_float_of_nat(v___x_2622_);
v___x_2625_ = lean_box_float(v___x_2623_);
v___x_2626_ = lean_box_float(v___x_2624_);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2625_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v_a_2621_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2507_, v___x_2508_, v___x_2509_, v_options_2551_, v___x_2574_, v___y_2619_, v___f_2510_, v___x_2628_, v___y_2511_, v___y_2512_);
return v___x_2629_;
}
v___jp_2630_:
{
lean_object* v___x_2634_; 
v___x_2634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2634_, 0, v_a_2633_);
v___y_2619_ = v___y_2631_;
v___y_2620_ = v___y_2632_;
v_a_2621_ = v___x_2634_;
goto v___jp_2618_;
}
v___jp_2635_:
{
lean_object* v___x_2639_; 
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v_a_2638_);
v___y_2619_ = v___y_2636_;
v___y_2620_ = v___y_2637_;
v_a_2621_ = v___x_2639_;
goto v___jp_2618_;
}
v___jp_2640_:
{
if (lean_obj_tag(v___y_2643_) == 0)
{
lean_object* v_a_2644_; 
v_a_2644_ = lean_ctor_get(v___y_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___y_2643_, 1);
v___y_2636_ = v___y_2641_;
v___y_2637_ = v___y_2642_;
v_a_2638_ = v_a_2644_;
goto v___jp_2635_;
}
else
{
lean_object* v_a_2645_; 
v_a_2645_ = lean_ctor_get(v___y_2643_, 0);
lean_inc(v_a_2645_);
lean_dec_ref_known(v___y_2643_, 1);
v___y_2631_ = v___y_2641_;
v___y_2632_ = v___y_2642_;
v_a_2633_ = v_a_2645_;
goto v___jp_2630_;
}
}
v___jp_2646_:
{
if (v___y_2650_ == 0)
{
lean_object* v___x_2651_; 
v___x_2651_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_dec_ref_known(v___x_2651_, 1);
v___y_2631_ = v___y_2648_;
v___y_2632_ = v___y_2649_;
v_a_2633_ = v___y_2647_;
goto v___jp_2630_;
}
else
{
lean_dec_ref(v___y_2647_);
v___y_2641_ = v___y_2648_;
v___y_2642_ = v___y_2649_;
v___y_2643_ = v___x_2651_;
goto v___jp_2640_;
}
}
else
{
lean_dec(v_decl_2506_);
v___y_2631_ = v___y_2648_;
v___y_2632_ = v___y_2649_;
v_a_2633_ = v___y_2647_;
goto v___jp_2630_;
}
}
v___jp_2652_:
{
uint8_t v___x_2656_; 
v___x_2656_ = l_Lean_Exception_isInterrupt(v_a_2655_);
if (v___x_2656_ == 0)
{
uint8_t v___x_2657_; 
lean_inc_ref(v_a_2655_);
v___x_2657_ = l_Lean_Exception_isRuntime(v_a_2655_);
v___y_2647_ = v_a_2655_;
v___y_2648_ = v___y_2653_;
v___y_2649_ = v___y_2654_;
v___y_2650_ = v___x_2657_;
goto v___jp_2646_;
}
else
{
v___y_2647_ = v_a_2655_;
v___y_2648_ = v___y_2653_;
v___y_2649_ = v___y_2654_;
v___y_2650_ = v___x_2656_;
goto v___jp_2646_;
}
}
v___jp_2658_:
{
lean_object* v___x_2659_; lean_object* v_a_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2659_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2512_);
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc(v_a_2660_);
lean_dec_ref(v___x_2659_);
v___x_2661_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2662_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2551_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; lean_object* v___x_2664_; 
v___x_2663_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2506_);
v___x_2664_ = l_Lean_warnIfUsesSorry(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v___x_2665_; lean_object* v_env_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec_ref_known(v___x_2664_, 1);
v___x_2665_ = lean_st_ref_get(v___y_2512_);
v_env_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc_ref(v_env_2666_);
lean_dec(v___x_2665_);
v___x_2667_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2511_);
v___x_2668_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2666_, v___x_2667_, v_decl_2506_, v_cancelTk_x3f_2570_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2668_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; lean_object* v_a_2672_; 
lean_dec(v_decl_2506_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2670_, v___y_2512_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref(v___x_2671_);
v___y_2596_ = v_a_2660_;
v___y_2597_ = v___x_2663_;
v_a_2598_ = v_a_2672_;
goto v___jp_2595_;
}
else
{
lean_object* v_a_2673_; 
v_a_2673_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2669_, 1);
v___y_2613_ = v_a_2660_;
v___y_2614_ = v___x_2663_;
v_a_2615_ = v_a_2673_;
goto v___jp_2612_;
}
}
else
{
lean_dec(v_decl_2506_);
v___y_2601_ = v_a_2660_;
v___y_2602_ = v___x_2663_;
v___y_2603_ = v___x_2664_;
goto v___jp_2600_;
}
}
else
{
lean_object* v___x_2674_; lean_object* v___x_2675_; 
v___x_2674_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2506_);
v___x_2675_ = l_Lean_warnIfUsesSorry(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v___x_2676_; lean_object* v_env_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
lean_dec_ref_known(v___x_2675_, 1);
v___x_2676_ = lean_st_ref_get(v___y_2512_);
v_env_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc_ref(v_env_2677_);
lean_dec(v___x_2676_);
v___x_2678_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2511_);
v___x_2679_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2677_, v___x_2678_, v_decl_2506_, v_cancelTk_x3f_2570_);
lean_dec_ref(v___x_2678_);
v___x_2680_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2679_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; lean_object* v_a_2683_; 
lean_dec(v_decl_2506_);
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
v___x_2682_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2681_, v___y_2512_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref(v___x_2682_);
v___y_2636_ = v_a_2660_;
v___y_2637_ = v___x_2674_;
v_a_2638_ = v_a_2683_;
goto v___jp_2635_;
}
else
{
lean_object* v_a_2684_; 
v_a_2684_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2684_);
lean_dec_ref_known(v___x_2680_, 1);
v___y_2653_ = v_a_2660_;
v___y_2654_ = v___x_2674_;
v_a_2655_ = v_a_2684_;
goto v___jp_2652_;
}
}
else
{
lean_dec(v_decl_2506_);
v___y_2641_ = v_a_2660_;
v___y_2642_ = v___x_2674_;
v___y_2643_ = v___x_2675_;
goto v___jp_2640_;
}
}
}
}
v___jp_2514_:
{
if (v___y_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v___y_2515_);
v___x_2518_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2506_, v___y_2511_, v___y_2512_);
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
lean_ctor_set(v___x_2520_, 0, v___y_2516_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___y_2516_);
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
lean_dec_ref(v___y_2516_);
return v___x_2518_;
}
}
else
{
lean_dec_ref(v___y_2516_);
lean_dec(v_decl_2506_);
return v___y_2515_;
}
}
v___jp_2527_:
{
uint8_t v___x_2530_; 
v___x_2530_ = l_Lean_Exception_isInterrupt(v_a_2529_);
if (v___x_2530_ == 0)
{
uint8_t v___x_2531_; 
lean_inc_ref(v_a_2529_);
v___x_2531_ = l_Lean_Exception_isRuntime(v_a_2529_);
v___y_2515_ = v___y_2528_;
v___y_2516_ = v_a_2529_;
v___y_2517_ = v___x_2531_;
goto v___jp_2514_;
}
else
{
v___y_2515_ = v___y_2528_;
v___y_2516_ = v_a_2529_;
v___y_2517_ = v___x_2530_;
goto v___jp_2514_;
}
}
v___jp_2532_:
{
if (v___y_2535_ == 0)
{
lean_object* v___x_2536_; 
lean_dec_ref(v___y_2534_);
v___x_2536_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2506_, v___y_2511_, v___y_2512_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2543_ == 0)
{
lean_object* v_unused_2544_; 
v_unused_2544_ = lean_ctor_get(v___x_2536_, 0);
lean_dec(v_unused_2544_);
v___x_2538_ = v___x_2536_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_dec(v___x_2536_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
lean_ctor_set_tag(v___x_2538_, 1);
lean_ctor_set(v___x_2538_, 0, v___y_2533_);
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___y_2533_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
else
{
lean_dec_ref(v___y_2533_);
return v___x_2536_;
}
}
else
{
lean_dec_ref(v___y_2533_);
lean_dec(v_decl_2506_);
return v___y_2534_;
}
}
v___jp_2545_:
{
uint8_t v___x_2548_; 
v___x_2548_ = l_Lean_Exception_isInterrupt(v_a_2547_);
if (v___x_2548_ == 0)
{
uint8_t v___x_2549_; 
lean_inc_ref(v_a_2547_);
v___x_2549_ = l_Lean_Exception_isRuntime(v_a_2547_);
v___y_2533_ = v_a_2547_;
v___y_2534_ = v___y_2546_;
v___y_2535_ = v___x_2549_;
goto v___jp_2532_;
}
else
{
v___y_2533_ = v_a_2547_;
v___y_2534_ = v___y_2546_;
v___y_2535_ = v___x_2548_;
goto v___jp_2532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2703_, lean_object* v___x_2704_, lean_object* v___x_2705_, lean_object* v___x_2706_, lean_object* v___f_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
uint8_t v___x_7949__boxed_2711_; lean_object* v_res_2712_; 
v___x_7949__boxed_2711_ = lean_unbox(v___x_2705_);
v_res_2712_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2703_, v___x_2704_, v___x_7949__boxed_2711_, v___x_2706_, v___f_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v___f_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___f_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; 
lean_inc(v_decl_2717_);
v___f_2721_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2721_, 0, v_decl_2717_);
v___x_2722_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2718_);
v___x_2723_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2724_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2725_ = 1;
v___x_2726_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2727_ = lean_box(v___x_2725_);
v___f_2728_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2728_, 0, v_decl_2717_);
lean_closure_set(v___f_2728_, 1, v___x_2724_);
lean_closure_set(v___f_2728_, 2, v___x_2727_);
lean_closure_set(v___f_2728_, 3, v___x_2726_);
lean_closure_set(v___f_2728_, 4, v___f_2721_);
v___x_2729_ = lean_box(0);
v___x_2730_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2723_, v___x_2722_, v___f_2728_, v___x_2729_, v_a_2718_, v_a_2719_);
lean_dec_ref(v___x_2722_);
return v___x_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2731_, v_a_2732_, v_a_2733_);
lean_dec(v_a_2733_);
lean_dec_ref(v_a_2732_);
return v_res_2735_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2736_, lean_object* v_x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_){
_start:
{
lean_object* v___x_2741_; 
v___x_2741_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2737_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2742_, lean_object* v_x_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2742_, v_x_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2748_, lean_object* v_a_2749_, lean_object* v_ref_2750_, lean_object* v_a_x3f_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v_env_2754_; lean_object* v___x_2755_; 
v___x_2753_ = lean_st_ref_get(v___y_2748_);
v_env_2754_ = lean_ctor_get(v___x_2753_, 0);
lean_inc_ref(v_env_2754_);
lean_dec(v___x_2753_);
v___x_2755_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2749_, v_env_2754_);
if (lean_obj_tag(v___x_2755_) == 0)
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec(v_ref_2750_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
v_a_2764_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2766_ = v___x_2755_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2755_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2773_; 
v___x_2768_ = lean_io_error_to_string(v_a_2764_);
v___x_2769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = l_Lean_MessageData_ofFormat(v___x_2769_);
v___x_2771_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2771_, 0, v_ref_2750_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 0, v___x_2771_);
v___x_2773_ = v___x_2766_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2771_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2776_, lean_object* v_a_2777_, lean_object* v_ref_2778_, lean_object* v_a_x3f_2779_, lean_object* v___y_2780_){
_start:
{
lean_object* v_res_2781_; 
v_res_2781_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2776_, v_a_2777_, v_ref_2778_, v_a_x3f_2779_);
lean_dec(v_a_x3f_2779_);
lean_dec(v___y_2776_);
return v_res_2781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v_a_2784_, lean_object* v_a_x3f_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v_env_2788_; lean_object* v_ref_2789_; lean_object* v___x_2790_; 
v___x_2787_ = lean_st_ref_get(v___y_2782_);
v_env_2788_ = lean_ctor_get(v___x_2787_, 0);
lean_inc_ref(v_env_2788_);
lean_dec(v___x_2787_);
v_ref_2789_ = lean_ctor_get(v___y_2783_, 2);
v___x_2790_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2784_, v_env_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; lean_object* v___x_2793_; uint8_t v_isShared_2794_; uint8_t v_isSharedCheck_2798_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2793_ = v___x_2790_;
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
else
{
lean_inc(v_a_2791_);
lean_dec(v___x_2790_);
v___x_2793_ = lean_box(0);
v_isShared_2794_ = v_isSharedCheck_2798_;
goto v_resetjp_2792_;
}
v_resetjp_2792_:
{
lean_object* v___x_2796_; 
if (v_isShared_2794_ == 0)
{
v___x_2796_ = v___x_2793_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v_a_2791_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
else
{
lean_object* v_a_2799_; lean_object* v___x_2801_; uint8_t v_isShared_2802_; uint8_t v_isSharedCheck_2810_; 
v_a_2799_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_2810_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_2810_ == 0)
{
v___x_2801_ = v___x_2790_;
v_isShared_2802_ = v_isSharedCheck_2810_;
goto v_resetjp_2800_;
}
else
{
lean_inc(v_a_2799_);
lean_dec(v___x_2790_);
v___x_2801_ = lean_box(0);
v_isShared_2802_ = v_isSharedCheck_2810_;
goto v_resetjp_2800_;
}
v_resetjp_2800_:
{
lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2808_; 
v___x_2803_ = lean_io_error_to_string(v_a_2799_);
v___x_2804_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2803_);
v___x_2805_ = l_Lean_MessageData_ofFormat(v___x_2804_);
lean_inc(v_ref_2789_);
v___x_2806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2806_, 0, v_ref_2789_);
lean_ctor_set(v___x_2806_, 1, v___x_2805_);
if (v_isShared_2802_ == 0)
{
lean_ctor_set(v___x_2801_, 0, v___x_2806_);
v___x_2808_ = v___x_2801_;
goto v_reusejp_2807_;
}
else
{
lean_object* v_reuseFailAlloc_2809_; 
v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2809_, 0, v___x_2806_);
v___x_2808_ = v_reuseFailAlloc_2809_;
goto v_reusejp_2807_;
}
v_reusejp_2807_:
{
return v___x_2808_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2811_, lean_object* v___y_2812_, lean_object* v_a_2813_, lean_object* v_a_x3f_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v_res_2816_; 
v_res_2816_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2811_, v___y_2812_, v_a_2813_, v_a_x3f_2814_);
lean_dec(v_a_x3f_2814_);
lean_dec_ref(v___y_2812_);
lean_dec(v___y_2811_);
return v_res_2816_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2817_, lean_object* v_asyncEnv_2818_, lean_object* v_decl_2819_, lean_object* v_x_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v___x_2824_; lean_object* v_r_2825_; 
v___x_2824_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2818_, v___y_2822_);
lean_dec_ref(v___x_2824_);
v_r_2825_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2819_, v___y_2821_, v___y_2822_);
if (lean_obj_tag(v_r_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2842_; 
v_a_2826_ = lean_ctor_get(v_r_2825_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v_r_2825_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2828_ = v_r_2825_;
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v_r_2825_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2842_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
lean_inc(v_a_2826_);
if (v_isShared_2829_ == 0)
{
lean_ctor_set_tag(v___x_2828_, 1);
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
lean_object* v___x_2832_; 
v___x_2832_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2822_, v___y_2821_, v_a_2817_, v___x_2831_);
lean_dec_ref(v___x_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2839_ == 0)
{
lean_object* v_unused_2840_; 
v_unused_2840_ = lean_ctor_get(v___x_2832_, 0);
lean_dec(v_unused_2840_);
v___x_2834_ = v___x_2832_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_dec(v___x_2832_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
lean_ctor_set(v___x_2834_, 0, v_a_2826_);
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2826_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
else
{
lean_dec(v_a_2826_);
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; 
v_a_2843_ = lean_ctor_get(v_r_2825_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v_r_2825_, 1);
v___x_2844_ = lean_box(0);
v___x_2845_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2822_, v___y_2821_, v_a_2817_, v___x_2844_);
if (lean_obj_tag(v___x_2845_) == 0)
{
lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2852_; 
v_isSharedCheck_2852_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; 
v_unused_2853_ = lean_ctor_get(v___x_2845_, 0);
lean_dec(v_unused_2853_);
v___x_2847_ = v___x_2845_;
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
else
{
lean_dec(v___x_2845_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2852_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2850_; 
if (v_isShared_2848_ == 0)
{
lean_ctor_set_tag(v___x_2847_, 1);
lean_ctor_set(v___x_2847_, 0, v_a_2843_);
v___x_2850_ = v___x_2847_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2843_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
}
else
{
lean_dec(v_a_2843_);
return v___x_2845_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2854_, lean_object* v_asyncEnv_2855_, lean_object* v_decl_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2854_, v_asyncEnv_2855_, v_decl_2856_, v_x_2857_, v___y_2858_, v___y_2859_);
lean_dec(v___y_2859_);
lean_dec_ref(v___y_2858_);
lean_dec_ref(v_x_2857_);
return v_res_2861_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; 
v___x_2863_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2864_ = l_Lean_stringToMessageData(v___x_2863_);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2865_, lean_object* v_x_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v___x_2870_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2871_ = l_Lean_Declaration_getNames(v_decl_2865_);
v___x_2872_ = lean_box(0);
v___x_2873_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2871_, v___x_2872_);
v___x_2874_ = l_Lean_MessageData_ofList(v___x_2873_);
v___x_2875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2875_, 0, v___x_2870_);
lean_ctor_set(v___x_2875_, 1, v___x_2874_);
v___x_2876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2876_, 0, v___x_2875_);
return v___x_2876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2877_, lean_object* v_x_2878_, lean_object* v___y_2879_, lean_object* v___y_2880_, lean_object* v___y_2881_){
_start:
{
lean_object* v_res_2882_; 
v_res_2882_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2877_, v_x_2878_, v___y_2879_, v___y_2880_);
lean_dec(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_x_2878_);
return v_res_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2885_, lean_object* v_msg_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_ref_2890_; lean_object* v___x_2891_; lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2937_; 
v_ref_2890_ = lean_ctor_get(v___y_2887_, 2);
v___x_2891_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2886_, v___y_2887_, v___y_2888_);
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2894_ = v___x_2891_;
v_isShared_2895_ = v_isSharedCheck_2937_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2891_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2937_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2896_; lean_object* v_traceState_2897_; lean_object* v_env_2898_; lean_object* v_nextMacroScope_2899_; lean_object* v_ngen_2900_; lean_object* v_auxDeclNGen_2901_; lean_object* v_cache_2902_; lean_object* v_recordedDeps_2903_; lean_object* v_messages_2904_; lean_object* v_infoState_2905_; lean_object* v_snapshotTasks_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2936_; 
v___x_2896_ = lean_st_ref_take(v___y_2888_);
v_traceState_2897_ = lean_ctor_get(v___x_2896_, 4);
v_env_2898_ = lean_ctor_get(v___x_2896_, 0);
v_nextMacroScope_2899_ = lean_ctor_get(v___x_2896_, 1);
v_ngen_2900_ = lean_ctor_get(v___x_2896_, 2);
v_auxDeclNGen_2901_ = lean_ctor_get(v___x_2896_, 3);
v_cache_2902_ = lean_ctor_get(v___x_2896_, 5);
v_recordedDeps_2903_ = lean_ctor_get(v___x_2896_, 6);
v_messages_2904_ = lean_ctor_get(v___x_2896_, 7);
v_infoState_2905_ = lean_ctor_get(v___x_2896_, 8);
v_snapshotTasks_2906_ = lean_ctor_get(v___x_2896_, 9);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2908_ = v___x_2896_;
v_isShared_2909_ = v_isSharedCheck_2936_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snapshotTasks_2906_);
lean_inc(v_infoState_2905_);
lean_inc(v_messages_2904_);
lean_inc(v_recordedDeps_2903_);
lean_inc(v_cache_2902_);
lean_inc(v_traceState_2897_);
lean_inc(v_auxDeclNGen_2901_);
lean_inc(v_ngen_2900_);
lean_inc(v_nextMacroScope_2899_);
lean_inc(v_env_2898_);
lean_dec(v___x_2896_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2936_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
uint64_t v_tid_2910_; lean_object* v_traces_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2935_; 
v_tid_2910_ = lean_ctor_get_uint64(v_traceState_2897_, sizeof(void*)*1);
v_traces_2911_ = lean_ctor_get(v_traceState_2897_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v_traceState_2897_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2913_ = v_traceState_2897_;
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_traces_2911_);
lean_dec(v_traceState_2897_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2935_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; lean_object* v___x_2916_; double v___x_2917_; uint8_t v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2926_; 
v___x_2915_ = lean_box(0);
v___x_2916_ = lean_box(0);
v___x_2917_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2918_ = 0;
v___x_2919_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2920_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2920_, 0, v_cls_2885_);
lean_ctor_set(v___x_2920_, 1, v___x_2916_);
lean_ctor_set(v___x_2920_, 2, v___x_2919_);
lean_ctor_set_float(v___x_2920_, sizeof(void*)*3, v___x_2917_);
lean_ctor_set_float(v___x_2920_, sizeof(void*)*3 + 8, v___x_2917_);
lean_ctor_set_uint8(v___x_2920_, sizeof(void*)*3 + 16, v___x_2918_);
v___x_2921_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2922_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v_a_2892_);
lean_ctor_set(v___x_2922_, 2, v___x_2921_);
lean_inc(v_ref_2890_);
v___x_2923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2923_, 0, v_ref_2890_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_PersistentArray_push___redArg(v_traces_2911_, v___x_2923_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v___x_2924_);
v___x_2926_ = v___x_2913_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v___x_2924_);
lean_ctor_set_uint64(v_reuseFailAlloc_2934_, sizeof(void*)*1, v_tid_2910_);
v___x_2926_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
lean_object* v___x_2928_; 
if (v_isShared_2909_ == 0)
{
lean_ctor_set(v___x_2908_, 4, v___x_2926_);
v___x_2928_ = v___x_2908_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_env_2898_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_nextMacroScope_2899_);
lean_ctor_set(v_reuseFailAlloc_2933_, 2, v_ngen_2900_);
lean_ctor_set(v_reuseFailAlloc_2933_, 3, v_auxDeclNGen_2901_);
lean_ctor_set(v_reuseFailAlloc_2933_, 4, v___x_2926_);
lean_ctor_set(v_reuseFailAlloc_2933_, 5, v_cache_2902_);
lean_ctor_set(v_reuseFailAlloc_2933_, 6, v_recordedDeps_2903_);
lean_ctor_set(v_reuseFailAlloc_2933_, 7, v_messages_2904_);
lean_ctor_set(v_reuseFailAlloc_2933_, 8, v_infoState_2905_);
lean_ctor_set(v_reuseFailAlloc_2933_, 9, v_snapshotTasks_2906_);
v___x_2928_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
lean_object* v___x_2929_; lean_object* v___x_2931_; 
v___x_2929_ = lean_st_ref_put(v___y_2888_, v___x_2928_);
if (v_isShared_2895_ == 0)
{
lean_ctor_set(v___x_2894_, 0, v___x_2915_);
v___x_2931_ = v___x_2894_;
goto v_reusejp_2930_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2915_);
v___x_2931_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2930_;
}
v_reusejp_2930_:
{
return v___x_2931_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2938_, lean_object* v_msg_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_, lean_object* v___y_2942_){
_start:
{
lean_object* v_res_2943_; 
v_res_2943_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2938_, v_msg_2939_, v___y_2940_, v___y_2941_);
lean_dec(v___y_2941_);
lean_dec_ref(v___y_2940_);
return v_res_2943_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2945_; lean_object* v___x_2946_; 
v___x_2945_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2946_ = l_Lean_stringToMessageData(v___x_2945_);
return v___x_2946_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2947_, lean_object* v_cls_2948_, lean_object* v_x_2949_, lean_object* v___y_2950_, lean_object* v___y_2951_){
_start:
{
lean_object* v_toCold_2953_; lean_object* v_options_2954_; uint8_t v_hasTrace_2955_; 
v_toCold_2953_ = lean_ctor_get(v___y_2950_, 0);
v_options_2954_ = lean_ctor_get(v_toCold_2953_, 2);
v_hasTrace_2955_ = lean_ctor_get_uint8(v_options_2954_, sizeof(void*)*1);
if (v_hasTrace_2955_ == 0)
{
lean_object* v___x_2956_; 
lean_dec(v_cls_2948_);
v___x_2956_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2947_, v___y_2950_, v___y_2951_);
return v___x_2956_;
}
else
{
lean_object* v_inheritedTraceOptions_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_inheritedTraceOptions_2957_ = lean_ctor_get(v_toCold_2953_, 11);
v___x_2958_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2948_);
v___x_2959_ = l_Lean_Name_append(v___x_2958_, v_cls_2948_);
v___x_2960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2957_, v_options_2954_, v___x_2959_);
lean_dec(v___x_2959_);
if (v___x_2960_ == 0)
{
lean_object* v___x_2961_; 
lean_dec(v_cls_2948_);
v___x_2961_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2947_, v___y_2950_, v___y_2951_);
return v___x_2961_;
}
else
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2963_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2948_, v___x_2962_, v___y_2950_, v___y_2951_);
if (lean_obj_tag(v___x_2963_) == 0)
{
lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2963_, 1);
v___x_2964_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2947_, v___y_2950_, v___y_2951_);
return v___x_2964_;
}
else
{
lean_dec(v_decl_2947_);
return v___x_2963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2965_, lean_object* v_cls_2966_, lean_object* v_x_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
lean_object* v_res_2971_; 
v_res_2971_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2965_, v_cls_2966_, v_x_2967_, v___y_2968_, v___y_2969_);
lean_dec(v___y_2969_);
lean_dec_ref(v___y_2968_);
lean_dec(v_x_2967_);
return v_res_2971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2972_, lean_object* v___y_2973_){
_start:
{
lean_object* v___x_2975_; uint8_t v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2975_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2973_);
v___x_2976_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2975_, v_opt_2972_);
lean_dec_ref(v___x_2975_);
v___x_2977_ = lean_box(v___x_2976_);
v___x_2978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2978_, 0, v___x_2977_);
return v___x_2978_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2979_, lean_object* v___y_2980_, lean_object* v___y_2981_){
_start:
{
lean_object* v_res_2982_; 
v_res_2982_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2979_, v___y_2980_);
lean_dec_ref(v___y_2980_);
lean_dec_ref(v_opt_2979_);
return v_res_2982_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2983_){
_start:
{
if (lean_obj_tag(v_x_2983_) == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = 1;
return v___x_2984_;
}
else
{
lean_object* v_head_2985_; lean_object* v_tail_2986_; uint8_t v___x_2987_; 
v_head_2985_ = lean_ctor_get(v_x_2983_, 0);
v_tail_2986_ = lean_ctor_get(v_x_2983_, 1);
v___x_2987_ = l_Lean_isPrivateName(v_head_2985_);
if (v___x_2987_ == 0)
{
return v___x_2987_;
}
else
{
v_x_2983_ = v_tail_2986_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2989_){
_start:
{
uint8_t v_res_2990_; lean_object* v_r_2991_; 
v_res_2990_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2989_);
lean_dec(v_x_2989_);
v_r_2991_ = lean_box(v_res_2990_);
return v_r_2991_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2997_; lean_object* v___x_2998_; 
v___x_2997_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2998_ = l_Lean_stringToMessageData(v___x_2997_);
return v___x_2998_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_3001_ = l_Lean_stringToMessageData(v___x_3000_);
return v___x_3001_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_3003_; lean_object* v___x_3004_; 
v___x_3003_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_3004_ = l_Lean_stringToMessageData(v___x_3003_);
return v___x_3004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_3005_, uint8_t v_hasTrace_3006_, uint8_t v___x_3007_, lean_object* v___x_3008_, uint8_t v___x_3009_, lean_object* v_cls_3010_, lean_object* v___x_3011_, lean_object* v_____x_3012_, lean_object* v_exportedInfo_x3f_3013_, lean_object* v___y_3014_, lean_object* v___y_3015_){
_start:
{
lean_object* v___y_3018_; lean_object* v___y_3019_; lean_object* v_a_3020_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v_a_3033_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v___y_3046_; lean_object* v___y_3047_; lean_object* v___y_3048_; lean_object* v___y_3049_; lean_object* v___y_3050_; lean_object* v___y_3051_; lean_object* v___y_3052_; lean_object* v___y_3053_; lean_object* v___y_3054_; lean_object* v_snd_3116_; lean_object* v_fst_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3258_; 
v_snd_3116_ = lean_ctor_get(v_____x_3012_, 1);
v_fst_3117_ = lean_ctor_get(v_____x_3012_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_____x_3012_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3119_ = v_____x_3012_;
v_isShared_3120_ = v_isSharedCheck_3258_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_snd_3116_);
lean_inc(v_fst_3117_);
lean_dec(v_____x_3012_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3258_;
goto v_resetjp_3118_;
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
lean_ctor_set_tag(v___x_3023_, 1);
lean_ctor_set(v___x_3023_, 0, v_a_3020_);
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
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
lean_object* v___x_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
v___x_3034_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3031_, v___y_3032_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_3034_, 0);
lean_dec(v_unused_3042_);
v___x_3036_ = v___x_3034_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_dec(v___x_3034_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
lean_ctor_set(v___x_3036_, 0, v_a_3033_);
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3033_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
v___jp_3043_:
{
lean_object* v___x_3055_; 
lean_inc_ref(v___y_3045_);
v___x_3055_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3053_, v___y_3045_, v___y_3049_, v___y_3054_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v___x_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref_known(v___x_3055_, 1);
lean_dec(v___y_3046_);
lean_inc_ref(v___y_3047_);
v___x_3056_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3047_, v___y_3051_);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3102_ == 0)
{
lean_object* v_unused_3103_; 
v_unused_3103_ = lean_ctor_get(v___x_3056_, 0);
lean_dec(v_unused_3103_);
v___x_3058_ = v___x_3056_;
v_isShared_3059_ = v_isSharedCheck_3102_;
goto v_resetjp_3057_;
}
else
{
lean_dec(v___x_3056_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3102_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3060_; lean_object* v___x_3061_; uint8_t v___x_3062_; 
v___x_3060_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3052_);
v___x_3061_ = l_Lean_Elab_async;
v___x_3062_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3060_, v___x_3061_);
lean_dec_ref(v___x_3060_);
if (v___x_3062_ == 0)
{
lean_object* v___x_3063_; lean_object* v_r_3064_; 
lean_del_object(v___x_3058_);
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3044_);
v___x_3063_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3045_, v___y_3051_);
lean_dec_ref(v___x_3063_);
v_r_3064_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3005_, v___y_3052_, v___y_3051_);
if (lean_obj_tag(v_r_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3067_; uint8_t v_isShared_3068_; uint8_t v_isSharedCheck_3074_; 
v_a_3065_ = lean_ctor_get(v_r_3064_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v_r_3064_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3067_ = v_r_3064_;
v_isShared_3068_ = v_isSharedCheck_3074_;
goto v_resetjp_3066_;
}
else
{
lean_inc(v_a_3065_);
lean_dec(v_r_3064_);
v___x_3067_ = lean_box(0);
v_isShared_3068_ = v_isSharedCheck_3074_;
goto v_resetjp_3066_;
}
v_resetjp_3066_:
{
lean_object* v___x_3070_; 
lean_inc(v_a_3065_);
if (v_isShared_3068_ == 0)
{
lean_ctor_set_tag(v___x_3067_, 1);
v___x_3070_ = v___x_3067_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3065_);
v___x_3070_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
lean_object* v___x_3071_; 
v___x_3071_ = lean_apply_2(v___y_3048_, v___x_3070_, lean_box(0));
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_dec_ref_known(v___x_3071_, 1);
v___y_3031_ = v___y_3047_;
v___y_3032_ = v___y_3051_;
v_a_3033_ = v_a_3065_;
goto v___jp_3030_;
}
else
{
lean_object* v_a_3072_; 
lean_dec(v_a_3065_);
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___y_3018_ = v___y_3047_;
v___y_3019_ = v___y_3051_;
v_a_3020_ = v_a_3072_;
goto v___jp_3017_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3076_; lean_object* v___x_3077_; 
v_a_3075_ = lean_ctor_get(v_r_3064_, 0);
lean_inc(v_a_3075_);
lean_dec_ref_known(v_r_3064_, 1);
v___x_3076_ = lean_box(0);
v___x_3077_ = lean_apply_2(v___y_3048_, v___x_3076_, lean_box(0));
if (lean_obj_tag(v___x_3077_) == 0)
{
lean_dec_ref_known(v___x_3077_, 1);
v___y_3018_ = v___y_3047_;
v___y_3019_ = v___y_3051_;
v_a_3020_ = v_a_3075_;
goto v___jp_3017_;
}
else
{
lean_object* v_a_3078_; 
lean_dec(v_a_3075_);
v_a_3078_ = lean_ctor_get(v___x_3077_, 0);
lean_inc(v_a_3078_);
lean_dec_ref_known(v___x_3077_, 1);
v___y_3018_ = v___y_3047_;
v___y_3019_ = v___y_3051_;
v_a_3020_ = v_a_3078_;
goto v___jp_3017_;
}
}
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v___y_3045_);
lean_dec(v_decl_3005_);
v___x_3079_ = l_IO_CancelToken_new();
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 1);
lean_ctor_set(v___x_3058_, 0, v___x_3079_);
v___x_3081_ = v___x_3058_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; 
v___x_3082_ = lean_unsigned_to_nat(0u);
v___x_3083_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3084_ = l_Lean_Name_toString(v___x_3083_, v_hasTrace_3006_);
lean_inc_ref(v___x_3081_);
v___x_3085_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3050_, v___x_3081_, v___x_3084_, v___y_3052_, v___y_3051_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v_checked_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; lean_object* v___x_3092_; 
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc(v_a_3086_);
lean_dec_ref_known(v___x_3085_, 1);
v_checked_3087_ = lean_ctor_get(v___y_3044_, 2);
lean_inc_ref(v_checked_3087_);
lean_dec_ref(v___y_3044_);
v___x_3088_ = lean_io_map_task(v_a_3086_, v_checked_3087_, v___x_3082_, v___x_3007_);
v___x_3089_ = lean_box(0);
v___x_3090_ = lean_box(2);
v___x_3091_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3089_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
lean_ctor_set(v___x_3091_, 2, v___x_3081_);
lean_ctor_set(v___x_3091_, 3, v___x_3088_);
v___x_3092_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3091_, v___y_3051_);
return v___x_3092_;
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_dec_ref(v___x_3081_);
lean_dec_ref(v___y_3044_);
v_a_3093_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3085_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3085_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
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
}
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3115_; 
lean_dec_ref(v___y_3050_);
lean_dec_ref(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec_ref(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v_decl_3005_);
v_a_3104_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3115_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3115_ == 0)
{
v___x_3106_ = v___x_3055_;
v_isShared_3107_ = v_isSharedCheck_3115_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3055_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3115_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3113_; 
v___x_3108_ = lean_io_error_to_string(v_a_3104_);
v___x_3109_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v___x_3110_ = l_Lean_MessageData_ofFormat(v___x_3109_);
v___x_3111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3111_, 0, v___y_3046_);
lean_ctor_set(v___x_3111_, 1, v___x_3110_);
if (v_isShared_3107_ == 0)
{
lean_ctor_set(v___x_3106_, 0, v___x_3111_);
v___x_3113_ = v___x_3106_;
goto v_reusejp_3112_;
}
else
{
lean_object* v_reuseFailAlloc_3114_; 
v_reuseFailAlloc_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3114_, 0, v___x_3111_);
v___x_3113_ = v_reuseFailAlloc_3114_;
goto v_reusejp_3112_;
}
v_reusejp_3112_:
{
return v___x_3113_;
}
}
}
}
v_resetjp_3118_:
{
lean_object* v_fst_3121_; lean_object* v_snd_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3257_; 
v_fst_3121_ = lean_ctor_get(v_snd_3116_, 0);
v_snd_3122_ = lean_ctor_get(v_snd_3116_, 1);
v_isSharedCheck_3257_ = !lean_is_exclusive(v_snd_3116_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3124_ = v_snd_3116_;
v_isShared_3125_ = v_isSharedCheck_3257_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_snd_3122_);
lean_inc(v_fst_3121_);
lean_dec(v_snd_3116_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3257_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v_exportedInfo_x3f_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3172_; lean_object* v___y_3173_; lean_object* v___y_3176_; uint8_t v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3201_; uint8_t v___y_3202_; lean_object* v___y_3203_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___x_3247_; lean_object* v_env_3248_; uint8_t v___x_3249_; 
v___x_3247_ = lean_st_ref_get(v___y_3015_);
v_env_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc_ref(v_env_3248_);
lean_dec(v___x_3247_);
v___x_3249_ = l_Lean_Environment_containsOnBranch(v_env_3248_, v_fst_3117_);
lean_dec_ref(v_env_3248_);
if (v___x_3249_ == 0)
{
lean_del_object(v___x_3119_);
v___y_3212_ = v___y_3014_;
v___y_3213_ = v___y_3015_;
goto v___jp_3211_;
}
else
{
lean_object* v___x_3250_; lean_object* v_env_3251_; lean_object* v___x_3252_; lean_object* v___x_3254_; 
lean_del_object(v___x_3124_);
lean_dec(v_snd_3122_);
lean_dec(v_fst_3121_);
lean_dec(v_exportedInfo_x3f_3013_);
lean_dec(v___x_3011_);
lean_dec(v_cls_3010_);
lean_dec_ref(v___x_3008_);
lean_dec(v_decl_3005_);
v___x_3250_ = lean_st_ref_get(v___y_3015_);
v_env_3251_ = lean_ctor_get(v___x_3250_, 0);
lean_inc_ref(v_env_3251_);
lean_dec(v___x_3250_);
v___x_3252_ = lean_elab_environment_to_kernel_env(v_env_3251_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set_tag(v___x_3119_, 1);
lean_ctor_set(v___x_3119_, 1, v_fst_3117_);
lean_ctor_set(v___x_3119_, 0, v___x_3252_);
v___x_3254_ = v___x_3119_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3252_);
lean_ctor_set(v_reuseFailAlloc_3256_, 1, v_fst_3117_);
v___x_3254_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
lean_object* v___x_3255_; 
v___x_3255_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3254_, v___y_3014_, v___y_3015_);
return v___x_3255_;
}
}
v___jp_3126_:
{
lean_object* v_ref_3132_; uint8_t v___x_3133_; lean_object* v___x_3134_; 
v_ref_3132_ = lean_ctor_get(v___y_3129_, 2);
v___x_3133_ = lean_unbox(v_snd_3122_);
lean_dec(v_snd_3122_);
lean_inc_ref(v___y_3130_);
v___x_3134_ = l_Lean_Environment_addConstAsync(v___y_3130_, v_fst_3117_, v___x_3133_, v___y_3131_, v___x_3007_, v_hasTrace_3006_);
if (lean_obj_tag(v___x_3134_) == 0)
{
lean_object* v_a_3135_; lean_object* v_mainEnv_3136_; lean_object* v_asyncEnv_3137_; lean_object* v___f_3138_; lean_object* v___f_3139_; lean_object* v___x_3140_; 
lean_del_object(v___x_3124_);
v_a_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc_n(v_a_3135_, 3);
lean_dec_ref_known(v___x_3134_, 1);
v_mainEnv_3136_ = lean_ctor_get(v_a_3135_, 0);
lean_inc_ref(v_mainEnv_3136_);
v_asyncEnv_3137_ = lean_ctor_get(v_a_3135_, 1);
lean_inc_ref_n(v_asyncEnv_3137_, 2);
lean_inc(v_ref_3132_);
lean_inc(v___y_3128_);
v___f_3138_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3138_, 0, v___y_3128_);
lean_closure_set(v___f_3138_, 1, v_a_3135_);
lean_closure_set(v___f_3138_, 2, v_ref_3132_);
lean_inc(v_decl_3005_);
v___f_3139_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3139_, 0, v_a_3135_);
lean_closure_set(v___f_3139_, 1, v_asyncEnv_3137_);
lean_closure_set(v___f_3139_, 2, v_decl_3005_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_fst_3121_);
if (lean_obj_tag(v___y_3127_) == 0)
{
lean_inc_ref(v___x_3140_);
lean_inc(v_ref_3132_);
v___y_3044_ = v___y_3130_;
v___y_3045_ = v_asyncEnv_3137_;
v___y_3046_ = v_ref_3132_;
v___y_3047_ = v_mainEnv_3136_;
v___y_3048_ = v___f_3138_;
v___y_3049_ = v___x_3140_;
v___y_3050_ = v___f_3139_;
v___y_3051_ = v___y_3128_;
v___y_3052_ = v___y_3129_;
v___y_3053_ = v_a_3135_;
v___y_3054_ = v___x_3140_;
goto v___jp_3043_;
}
else
{
lean_inc(v_ref_3132_);
v___y_3044_ = v___y_3130_;
v___y_3045_ = v_asyncEnv_3137_;
v___y_3046_ = v_ref_3132_;
v___y_3047_ = v_mainEnv_3136_;
v___y_3048_ = v___f_3138_;
v___y_3049_ = v___x_3140_;
v___y_3050_ = v___f_3139_;
v___y_3051_ = v___y_3128_;
v___y_3052_ = v___y_3129_;
v___y_3053_ = v_a_3135_;
v___y_3054_ = v___y_3127_;
goto v___jp_3043_;
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3154_; 
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3127_);
lean_dec(v_fst_3121_);
lean_dec(v_decl_3005_);
v_a_3141_ = lean_ctor_get(v___x_3134_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3134_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3143_ = v___x_3134_;
v_isShared_3144_ = v_isSharedCheck_3154_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3134_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3154_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3149_; 
v___x_3145_ = lean_io_error_to_string(v_a_3141_);
v___x_3146_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
v___x_3147_ = l_Lean_MessageData_ofFormat(v___x_3146_);
lean_inc(v_ref_3132_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 1, v___x_3147_);
lean_ctor_set(v___x_3124_, 0, v_ref_3132_);
v___x_3149_ = v___x_3124_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_ref_3132_);
lean_ctor_set(v_reuseFailAlloc_3153_, 1, v___x_3147_);
v___x_3149_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
lean_object* v___x_3151_; 
if (v_isShared_3144_ == 0)
{
lean_ctor_set(v___x_3143_, 0, v___x_3149_);
v___x_3151_ = v___x_3143_;
goto v_reusejp_3150_;
}
else
{
lean_object* v_reuseFailAlloc_3152_; 
v_reuseFailAlloc_3152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3152_, 0, v___x_3149_);
v___x_3151_ = v_reuseFailAlloc_3152_;
goto v_reusejp_3150_;
}
v_reusejp_3150_:
{
return v___x_3151_;
}
}
}
}
}
v___jp_3155_:
{
lean_object* v___x_3159_; 
v___x_3159_ = lean_st_ref_get(v___y_3158_);
if (lean_obj_tag(v_exportedInfo_x3f_3156_) == 0)
{
lean_object* v_env_3160_; lean_object* v___x_3161_; 
v_env_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc_ref(v_env_3160_);
lean_dec(v___x_3159_);
v___x_3161_ = lean_box(0);
v___y_3127_ = v_exportedInfo_x3f_3156_;
v___y_3128_ = v___y_3158_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v_env_3160_;
v___y_3131_ = v___x_3161_;
goto v___jp_3126_;
}
else
{
lean_object* v_env_3162_; lean_object* v_val_3163_; uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v_env_3162_ = lean_ctor_get(v___x_3159_, 0);
lean_inc_ref(v_env_3162_);
lean_dec(v___x_3159_);
v_val_3163_ = lean_ctor_get(v_exportedInfo_x3f_3156_, 0);
v___x_3164_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3163_);
v___x_3165_ = lean_box(v___x_3164_);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
v___y_3127_ = v_exportedInfo_x3f_3156_;
v___y_3128_ = v___y_3158_;
v___y_3129_ = v___y_3157_;
v___y_3130_ = v_env_3162_;
v___y_3131_ = v___x_3166_;
goto v___jp_3126_;
}
}
v___jp_3167_:
{
lean_object* v___x_3170_; 
lean_inc(v_fst_3121_);
v___x_3170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3170_, 0, v_fst_3121_);
v_exportedInfo_x3f_3156_ = v___x_3170_;
v___y_3157_ = v___y_3168_;
v___y_3158_ = v___y_3169_;
goto v___jp_3155_;
}
v___jp_3171_:
{
lean_object* v___x_3174_; 
lean_inc(v_fst_3121_);
v___x_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3174_, 0, v_fst_3121_);
v_exportedInfo_x3f_3156_ = v___x_3174_;
v___y_3157_ = v___y_3172_;
v___y_3158_ = v___y_3173_;
goto v___jp_3155_;
}
v___jp_3175_:
{
lean_object* v___x_3180_; lean_object* v_env_3181_; lean_object* v_nextMacroScope_3182_; lean_object* v_ngen_3183_; lean_object* v_auxDeclNGen_3184_; lean_object* v_traceState_3185_; lean_object* v_recordedDeps_3186_; lean_object* v_messages_3187_; lean_object* v_infoState_3188_; lean_object* v_snapshotTasks_3189_; lean_object* v___x_3191_; uint8_t v_isShared_3192_; uint8_t v_isSharedCheck_3198_; 
v___x_3180_ = lean_st_ref_take(v___y_3179_);
v_env_3181_ = lean_ctor_get(v___x_3180_, 0);
v_nextMacroScope_3182_ = lean_ctor_get(v___x_3180_, 1);
v_ngen_3183_ = lean_ctor_get(v___x_3180_, 2);
v_auxDeclNGen_3184_ = lean_ctor_get(v___x_3180_, 3);
v_traceState_3185_ = lean_ctor_get(v___x_3180_, 4);
v_recordedDeps_3186_ = lean_ctor_get(v___x_3180_, 6);
v_messages_3187_ = lean_ctor_get(v___x_3180_, 7);
v_infoState_3188_ = lean_ctor_get(v___x_3180_, 8);
v_snapshotTasks_3189_ = lean_ctor_get(v___x_3180_, 9);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v___x_3180_, 5);
lean_dec(v_unused_3199_);
v___x_3191_ = v___x_3180_;
v_isShared_3192_ = v_isSharedCheck_3198_;
goto v_resetjp_3190_;
}
else
{
lean_inc(v_snapshotTasks_3189_);
lean_inc(v_infoState_3188_);
lean_inc(v_messages_3187_);
lean_inc(v_recordedDeps_3186_);
lean_inc(v_traceState_3185_);
lean_inc(v_auxDeclNGen_3184_);
lean_inc(v_ngen_3183_);
lean_inc(v_nextMacroScope_3182_);
lean_inc(v_env_3181_);
lean_dec(v___x_3180_);
v___x_3191_ = lean_box(0);
v_isShared_3192_ = v_isSharedCheck_3198_;
goto v_resetjp_3190_;
}
v_resetjp_3190_:
{
lean_object* v___x_3193_; lean_object* v___x_3195_; 
lean_inc(v_snd_3122_);
lean_inc(v_fst_3117_);
lean_inc_ref(v___y_3178_);
v___x_3193_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_3178_, v_env_3181_, v_fst_3117_, v_snd_3122_, v___y_3177_);
if (v_isShared_3192_ == 0)
{
lean_ctor_set(v___x_3191_, 5, v___x_3008_);
lean_ctor_set(v___x_3191_, 0, v___x_3193_);
v___x_3195_ = v___x_3191_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3193_);
lean_ctor_set(v_reuseFailAlloc_3197_, 1, v_nextMacroScope_3182_);
lean_ctor_set(v_reuseFailAlloc_3197_, 2, v_ngen_3183_);
lean_ctor_set(v_reuseFailAlloc_3197_, 3, v_auxDeclNGen_3184_);
lean_ctor_set(v_reuseFailAlloc_3197_, 4, v_traceState_3185_);
lean_ctor_set(v_reuseFailAlloc_3197_, 5, v___x_3008_);
lean_ctor_set(v_reuseFailAlloc_3197_, 6, v_recordedDeps_3186_);
lean_ctor_set(v_reuseFailAlloc_3197_, 7, v_messages_3187_);
lean_ctor_set(v_reuseFailAlloc_3197_, 8, v_infoState_3188_);
lean_ctor_set(v_reuseFailAlloc_3197_, 9, v_snapshotTasks_3189_);
v___x_3195_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_st_ref_put(v___y_3179_, v___x_3195_);
v_exportedInfo_x3f_3156_ = v_exportedInfo_x3f_3013_;
v___y_3157_ = v___y_3176_;
v___y_3158_ = v___y_3179_;
goto v___jp_3155_;
}
}
}
v___jp_3200_:
{
lean_object* v___x_3204_; lean_object* v_env_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; uint8_t v___x_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3204_ = lean_st_ref_get(v___y_3203_);
v_env_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc_ref(v_env_3205_);
lean_dec(v___x_3204_);
v___x_3206_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3207_ = lean_box(1);
v___x_3208_ = 0;
v___x_3209_ = lean_box(v___x_3009_);
lean_inc(v_fst_3117_);
v___x_3210_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3209_, v___x_3206_, v_env_3205_, v_fst_3117_, v___x_3207_, v___x_3208_);
if (lean_obj_tag(v___x_3210_) == 0)
{
v___y_3176_ = v___y_3201_;
v___y_3177_ = v___y_3202_;
v___y_3178_ = v___x_3206_;
v___y_3179_ = v___y_3203_;
goto v___jp_3175_;
}
else
{
lean_dec_ref_known(v___x_3210_, 1);
if (v___y_3202_ == 0)
{
lean_dec_ref(v___x_3008_);
v_exportedInfo_x3f_3156_ = v_exportedInfo_x3f_3013_;
v___y_3157_ = v___y_3201_;
v___y_3158_ = v___y_3203_;
goto v___jp_3155_;
}
else
{
v___y_3176_ = v___y_3201_;
v___y_3177_ = v___y_3202_;
v___y_3178_ = v___x_3206_;
v___y_3179_ = v___y_3203_;
goto v___jp_3175_;
}
}
}
v___jp_3211_:
{
lean_object* v___x_3214_; uint8_t v___x_3215_; 
lean_inc(v_decl_3005_);
v___x_3214_ = l_Lean_Declaration_getTopLevelNames(v_decl_3005_);
v___x_3215_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3214_);
lean_dec(v___x_3214_);
if (v___x_3215_ == 0)
{
lean_dec(v___x_3011_);
if (lean_obj_tag(v_exportedInfo_x3f_3013_) == 0)
{
if (v___x_3215_ == 0)
{
lean_object* v_toCold_3216_; lean_object* v_options_3217_; uint8_t v_hasTrace_3218_; 
lean_dec_ref(v___x_3008_);
v_toCold_3216_ = lean_ctor_get(v___y_3212_, 0);
v_options_3217_ = lean_ctor_get(v_toCold_3216_, 2);
v_hasTrace_3218_ = lean_ctor_get_uint8(v_options_3217_, sizeof(void*)*1);
if (v_hasTrace_3218_ == 0)
{
lean_dec(v_cls_3010_);
v___y_3172_ = v___y_3212_;
v___y_3173_ = v___y_3213_;
goto v___jp_3171_;
}
else
{
lean_object* v_inheritedTraceOptions_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_inheritedTraceOptions_3219_ = lean_ctor_get(v_toCold_3216_, 11);
v___x_3220_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3010_);
v___x_3221_ = l_Lean_Name_append(v___x_3220_, v_cls_3010_);
v___x_3222_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3219_, v_options_3217_, v___x_3221_);
lean_dec(v___x_3221_);
if (v___x_3222_ == 0)
{
lean_dec(v_cls_3010_);
v___y_3172_ = v___y_3212_;
v___y_3173_ = v___y_3213_;
goto v___jp_3171_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3224_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3010_, v___x_3223_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_dec_ref_known(v___x_3224_, 1);
v___y_3172_ = v___y_3212_;
v___y_3173_ = v___y_3213_;
goto v___jp_3171_;
}
else
{
lean_del_object(v___x_3124_);
lean_dec(v_snd_3122_);
lean_dec(v_fst_3121_);
lean_dec(v_fst_3117_);
lean_dec(v_decl_3005_);
return v___x_3224_;
}
}
}
}
else
{
lean_dec(v_cls_3010_);
v___y_3201_ = v___y_3212_;
v___y_3202_ = v___x_3215_;
v___y_3203_ = v___y_3213_;
goto v___jp_3200_;
}
}
else
{
lean_dec(v_cls_3010_);
v___y_3201_ = v___y_3212_;
v___y_3202_ = v___x_3215_;
v___y_3203_ = v___y_3213_;
goto v___jp_3200_;
}
}
else
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v_a_3227_; uint8_t v___x_3228_; 
lean_dec(v_exportedInfo_x3f_3013_);
lean_dec_ref(v___x_3008_);
v___x_3225_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3226_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3225_, v___y_3212_);
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref(v___x_3226_);
v___x_3228_ = lean_unbox(v_a_3227_);
lean_dec(v_a_3227_);
if (v___x_3228_ == 0)
{
lean_object* v_toCold_3229_; lean_object* v_options_3230_; uint8_t v_hasTrace_3231_; 
v_toCold_3229_ = lean_ctor_get(v___y_3212_, 0);
v_options_3230_ = lean_ctor_get(v_toCold_3229_, 2);
v_hasTrace_3231_ = lean_ctor_get_uint8(v_options_3230_, sizeof(void*)*1);
if (v_hasTrace_3231_ == 0)
{
lean_dec(v_cls_3010_);
v_exportedInfo_x3f_3156_ = v___x_3011_;
v___y_3157_ = v___y_3212_;
v___y_3158_ = v___y_3213_;
goto v___jp_3155_;
}
else
{
lean_object* v_inheritedTraceOptions_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v_inheritedTraceOptions_3232_ = lean_ctor_get(v_toCold_3229_, 11);
v___x_3233_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3010_);
v___x_3234_ = l_Lean_Name_append(v___x_3233_, v_cls_3010_);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3232_, v_options_3230_, v___x_3234_);
lean_dec(v___x_3234_);
if (v___x_3235_ == 0)
{
lean_dec(v_cls_3010_);
v_exportedInfo_x3f_3156_ = v___x_3011_;
v___y_3157_ = v___y_3212_;
v___y_3158_ = v___y_3213_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; 
v___x_3236_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3237_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3010_, v___x_3236_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3237_) == 0)
{
lean_dec_ref_known(v___x_3237_, 1);
v_exportedInfo_x3f_3156_ = v___x_3011_;
v___y_3157_ = v___y_3212_;
v___y_3158_ = v___y_3213_;
goto v___jp_3155_;
}
else
{
lean_del_object(v___x_3124_);
lean_dec(v_snd_3122_);
lean_dec(v_fst_3121_);
lean_dec(v_fst_3117_);
lean_dec(v___x_3011_);
lean_dec(v_decl_3005_);
return v___x_3237_;
}
}
}
}
else
{
lean_object* v_toCold_3238_; lean_object* v_options_3239_; uint8_t v_hasTrace_3240_; 
lean_dec(v___x_3011_);
v_toCold_3238_ = lean_ctor_get(v___y_3212_, 0);
v_options_3239_ = lean_ctor_get(v_toCold_3238_, 2);
v_hasTrace_3240_ = lean_ctor_get_uint8(v_options_3239_, sizeof(void*)*1);
if (v_hasTrace_3240_ == 0)
{
lean_dec(v_cls_3010_);
v___y_3168_ = v___y_3212_;
v___y_3169_ = v___y_3213_;
goto v___jp_3167_;
}
else
{
lean_object* v_inheritedTraceOptions_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_inheritedTraceOptions_3241_ = lean_ctor_get(v_toCold_3238_, 11);
v___x_3242_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3010_);
v___x_3243_ = l_Lean_Name_append(v___x_3242_, v_cls_3010_);
v___x_3244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3241_, v_options_3239_, v___x_3243_);
lean_dec(v___x_3243_);
if (v___x_3244_ == 0)
{
lean_dec(v_cls_3010_);
v___y_3168_ = v___y_3212_;
v___y_3169_ = v___y_3213_;
goto v___jp_3167_;
}
else
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3246_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3010_, v___x_3245_, v___y_3212_, v___y_3213_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_dec_ref_known(v___x_3246_, 1);
v___y_3168_ = v___y_3212_;
v___y_3169_ = v___y_3213_;
goto v___jp_3167_;
}
else
{
lean_del_object(v___x_3124_);
lean_dec(v_snd_3122_);
lean_dec(v_fst_3121_);
lean_dec(v_fst_3117_);
lean_dec(v_decl_3005_);
return v___x_3246_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3259_, lean_object* v_hasTrace_3260_, lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v___x_3263_, lean_object* v_cls_3264_, lean_object* v___x_3265_, lean_object* v_____x_3266_, lean_object* v_exportedInfo_x3f_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
uint8_t v_hasTrace_boxed_3271_; uint8_t v___x_54147__boxed_3272_; uint8_t v___x_54149__boxed_3273_; lean_object* v_res_3274_; 
v_hasTrace_boxed_3271_ = lean_unbox(v_hasTrace_3260_);
v___x_54147__boxed_3272_ = lean_unbox(v___x_3261_);
v___x_54149__boxed_3273_ = lean_unbox(v___x_3263_);
v_res_3274_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3259_, v_hasTrace_boxed_3271_, v___x_54147__boxed_3272_, v___x_3262_, v___x_54149__boxed_3273_, v_cls_3264_, v___x_3265_, v_____x_3266_, v_exportedInfo_x3f_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
return v_res_3274_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3276_; lean_object* v___x_3277_; 
v___x_3276_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3277_ = l_Lean_stringToMessageData(v___x_3276_);
return v___x_3277_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3279_; lean_object* v___x_3280_; 
v___x_3279_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3280_ = l_Lean_stringToMessageData(v___x_3279_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3281_, uint8_t v___x_3282_, lean_object* v_cls_3283_, lean_object* v___x_3284_, uint8_t v_forceExpose_3285_, lean_object* v_defn_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
lean_object* v_exportedInfo_x3f_3291_; lean_object* v___y_3292_; lean_object* v___y_3293_; lean_object* v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; uint8_t v___y_3311_; lean_object* v___x_3316_; lean_object* v_env_3317_; lean_object* v___x_3318_; uint8_t v___y_3320_; lean_object* v_env_3336_; 
v___x_3316_ = lean_st_ref_get(v___y_3288_);
v_env_3317_ = lean_ctor_get(v___x_3316_, 0);
lean_inc_ref(v_env_3317_);
lean_dec(v___x_3316_);
v___x_3318_ = lean_st_ref_get(v___y_3288_);
v_env_3336_ = lean_ctor_get(v___x_3318_, 0);
lean_inc_ref(v_env_3336_);
lean_dec(v___x_3318_);
if (v_forceExpose_3285_ == 0)
{
goto v___jp_3337_;
}
else
{
if (v___x_3282_ == 0)
{
lean_dec_ref(v_env_3336_);
lean_dec_ref(v_env_3317_);
lean_dec(v_cls_3283_);
v_exportedInfo_x3f_3291_ = v___x_3284_;
v___y_3292_ = v___y_3287_;
v___y_3293_ = v___y_3288_;
goto v___jp_3290_;
}
else
{
goto v___jp_3337_;
}
}
v___jp_3290_:
{
lean_object* v_toConstantVal_3294_; lean_object* v_name_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_toConstantVal_3294_ = lean_ctor_get(v_defn_3286_, 0);
v_name_3295_ = lean_ctor_get(v_toConstantVal_3294_, 0);
lean_inc(v_name_3295_);
v___x_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_defn_3286_);
v___x_3297_ = 0;
v___x_3298_ = lean_box(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_name_3295_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
lean_inc(v___y_3293_);
lean_inc_ref(v___y_3292_);
v___x_3301_ = lean_apply_5(v___f_3281_, v___x_3300_, v_exportedInfo_x3f_3291_, v___y_3292_, v___y_3293_, lean_box(0));
return v___x_3301_;
}
v___jp_3302_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3307_, 0, v___y_3305_);
lean_ctor_set_uint8(v___x_3307_, sizeof(void*)*1, v___y_3306_);
v___x_3308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v_exportedInfo_x3f_3291_ = v___x_3309_;
v___y_3292_ = v___y_3303_;
v___y_3293_ = v___y_3304_;
goto v___jp_3290_;
}
v___jp_3310_:
{
lean_object* v_toConstantVal_3312_; uint8_t v_safety_3313_; uint8_t v___x_3314_; uint8_t v___x_3315_; 
v_toConstantVal_3312_ = lean_ctor_get(v_defn_3286_, 0);
v_safety_3313_ = lean_ctor_get_uint8(v_defn_3286_, sizeof(void*)*4);
v___x_3314_ = 1;
v___x_3315_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3313_, v___x_3314_);
if (v___x_3315_ == 0)
{
lean_inc_ref(v_toConstantVal_3312_);
v___y_3303_ = v___y_3287_;
v___y_3304_ = v___y_3288_;
v___y_3305_ = v_toConstantVal_3312_;
v___y_3306_ = v___y_3311_;
goto v___jp_3302_;
}
else
{
lean_inc_ref(v_toConstantVal_3312_);
v___y_3303_ = v___y_3287_;
v___y_3304_ = v___y_3288_;
v___y_3305_ = v_toConstantVal_3312_;
v___y_3306_ = v___x_3282_;
goto v___jp_3302_;
}
}
v___jp_3319_:
{
lean_object* v_toCold_3321_; lean_object* v_options_3322_; uint8_t v_hasTrace_3323_; 
v_toCold_3321_ = lean_ctor_get(v___y_3287_, 0);
v_options_3322_ = lean_ctor_get(v_toCold_3321_, 2);
v_hasTrace_3323_ = lean_ctor_get_uint8(v_options_3322_, sizeof(void*)*1);
if (v_hasTrace_3323_ == 0)
{
lean_dec(v_cls_3283_);
v___y_3311_ = v___y_3320_;
goto v___jp_3310_;
}
else
{
lean_object* v_inheritedTraceOptions_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_inheritedTraceOptions_3324_ = lean_ctor_get(v_toCold_3321_, 11);
v___x_3325_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3283_);
v___x_3326_ = l_Lean_Name_append(v___x_3325_, v_cls_3283_);
v___x_3327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3324_, v_options_3322_, v___x_3326_);
lean_dec(v___x_3326_);
if (v___x_3327_ == 0)
{
lean_dec(v_cls_3283_);
v___y_3311_ = v___y_3320_;
goto v___jp_3310_;
}
else
{
lean_object* v_toConstantVal_3328_; lean_object* v_name_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_toConstantVal_3328_ = lean_ctor_get(v_defn_3286_, 0);
v_name_3329_ = lean_ctor_get(v_toConstantVal_3328_, 0);
v___x_3330_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3329_);
v___x_3331_ = l_Lean_MessageData_ofName(v_name_3329_);
v___x_3332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3332_, 0, v___x_3330_);
lean_ctor_set(v___x_3332_, 1, v___x_3331_);
v___x_3333_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3332_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3283_, v___x_3334_, v___y_3287_, v___y_3288_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_dec_ref_known(v___x_3335_, 1);
v___y_3311_ = v___y_3320_;
goto v___jp_3310_;
}
else
{
lean_dec_ref(v_defn_3286_);
lean_dec_ref(v___f_3281_);
return v___x_3335_;
}
}
}
}
v___jp_3337_:
{
lean_object* v___x_3338_; uint8_t v_isModule_3339_; 
v___x_3338_ = l_Lean_Environment_header(v_env_3317_);
lean_dec_ref(v_env_3317_);
v_isModule_3339_ = lean_ctor_get_uint8(v___x_3338_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3338_);
if (v_isModule_3339_ == 0)
{
lean_dec_ref(v_env_3336_);
lean_dec(v_cls_3283_);
v_exportedInfo_x3f_3291_ = v___x_3284_;
v___y_3292_ = v___y_3287_;
v___y_3293_ = v___y_3288_;
goto v___jp_3290_;
}
else
{
uint8_t v_isExporting_3340_; 
v_isExporting_3340_ = lean_ctor_get_uint8(v_env_3336_, sizeof(void*)*13);
lean_dec_ref(v_env_3336_);
if (v_isExporting_3340_ == 0)
{
lean_dec(v___x_3284_);
v___y_3320_ = v_isModule_3339_;
goto v___jp_3319_;
}
else
{
if (v___x_3282_ == 0)
{
lean_dec(v_cls_3283_);
v_exportedInfo_x3f_3291_ = v___x_3284_;
v___y_3292_ = v___y_3287_;
v___y_3293_ = v___y_3288_;
goto v___jp_3290_;
}
else
{
lean_dec(v___x_3284_);
v___y_3320_ = v___x_3282_;
goto v___jp_3319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3341_, lean_object* v___x_3342_, lean_object* v_cls_3343_, lean_object* v___x_3344_, lean_object* v_forceExpose_3345_, lean_object* v_defn_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
uint8_t v___x_54645__boxed_3350_; uint8_t v_forceExpose_boxed_3351_; lean_object* v_res_3352_; 
v___x_54645__boxed_3350_ = lean_unbox(v___x_3342_);
v_forceExpose_boxed_3351_ = lean_unbox(v_forceExpose_3345_);
v_res_3352_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3341_, v___x_54645__boxed_3350_, v_cls_3343_, v___x_3344_, v_forceExpose_boxed_3351_, v_defn_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3353_, lean_object* v___f_3354_, lean_object* v_____r_3355_, lean_object* v_exportedInfo_x3f_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_toConstantVal_3360_; lean_object* v_name_3361_; lean_object* v___x_3362_; uint8_t v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_toConstantVal_3360_ = lean_ctor_get(v_val_3353_, 0);
v_name_3361_ = lean_ctor_get(v_toConstantVal_3360_, 0);
lean_inc(v_name_3361_);
v___x_3362_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3362_, 0, v_val_3353_);
v___x_3363_ = 1;
v___x_3364_ = lean_box(v___x_3363_);
v___x_3365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3362_);
lean_ctor_set(v___x_3365_, 1, v___x_3364_);
v___x_3366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3366_, 0, v_name_3361_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
v___x_3367_ = lean_apply_5(v___f_3354_, v___x_3366_, v_exportedInfo_x3f_3356_, v___y_3357_, v___y_3358_, lean_box(0));
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3368_, lean_object* v___f_3369_, lean_object* v_____r_3370_, lean_object* v_exportedInfo_x3f_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
lean_object* v_res_3375_; 
v_res_3375_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3368_, v___f_3369_, v_____r_3370_, v_exportedInfo_x3f_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
return v_res_3375_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3376_, uint8_t v___x_3377_, lean_object* v___f_3378_, lean_object* v_____r_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v_toConstantVal_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; 
v_toConstantVal_3383_ = lean_ctor_get(v_val_3376_, 0);
lean_inc_ref(v_toConstantVal_3383_);
v___x_3384_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3384_, 0, v_toConstantVal_3383_);
lean_ctor_set_uint8(v___x_3384_, sizeof(void*)*1, v___x_3377_);
v___x_3385_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3385_, 0, v___x_3384_);
v___x_3386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3386_, 0, v___x_3385_);
v___x_3387_ = lean_box(0);
lean_inc(v___y_3381_);
lean_inc_ref(v___y_3380_);
v___x_3388_ = lean_apply_5(v___f_3378_, v___x_3387_, v___x_3386_, v___y_3380_, v___y_3381_, lean_box(0));
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3389_, lean_object* v___x_3390_, lean_object* v___f_3391_, lean_object* v_____r_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_){
_start:
{
uint8_t v___x_54776__boxed_3396_; lean_object* v_res_3397_; 
v___x_54776__boxed_3396_ = lean_unbox(v___x_3390_);
v_res_3397_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3389_, v___x_54776__boxed_3396_, v___f_3391_, v_____r_3392_, v___y_3393_, v___y_3394_);
lean_dec(v___y_3394_);
lean_dec_ref(v___y_3393_);
lean_dec_ref(v_val_3389_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3398_, lean_object* v___f_3399_, lean_object* v_____r_3400_, lean_object* v_exportedInfo_x3f_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v_toConstantVal_3405_; lean_object* v_name_3406_; lean_object* v___x_3407_; uint8_t v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v_toConstantVal_3405_ = lean_ctor_get(v_val_3398_, 0);
v_name_3406_ = lean_ctor_get(v_toConstantVal_3405_, 0);
lean_inc(v_name_3406_);
v___x_3407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3407_, 0, v_val_3398_);
v___x_3408_ = 3;
v___x_3409_ = lean_box(v___x_3408_);
v___x_3410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3410_, 0, v___x_3407_);
lean_ctor_set(v___x_3410_, 1, v___x_3409_);
v___x_3411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3411_, 0, v_name_3406_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
lean_inc(v___y_3403_);
lean_inc_ref(v___y_3402_);
v___x_3412_ = lean_apply_5(v___f_3399_, v___x_3411_, v_exportedInfo_x3f_3401_, v___y_3402_, v___y_3403_, lean_box(0));
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3413_, lean_object* v___f_3414_, lean_object* v_____r_3415_, lean_object* v_exportedInfo_x3f_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3413_, v___f_3414_, v_____r_3415_, v_exportedInfo_x3f_3416_, v___y_3417_, v___y_3418_);
lean_dec(v___y_3418_);
lean_dec_ref(v___y_3417_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3421_, lean_object* v___f_3422_, lean_object* v_____r_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
lean_object* v_toConstantVal_3427_; uint8_t v_isUnsafe_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; 
v_toConstantVal_3427_ = lean_ctor_get(v_val_3421_, 0);
v_isUnsafe_3428_ = lean_ctor_get_uint8(v_val_3421_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3427_);
v___x_3429_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3429_, 0, v_toConstantVal_3427_);
lean_ctor_set_uint8(v___x_3429_, sizeof(void*)*1, v_isUnsafe_3428_);
v___x_3430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
v___x_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
v___x_3432_ = lean_box(0);
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3424_);
v___x_3433_ = lean_apply_5(v___f_3422_, v___x_3432_, v___x_3431_, v___y_3424_, v___y_3425_, lean_box(0));
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3434_, lean_object* v___f_3435_, lean_object* v_____r_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3434_, v___f_3435_, v_____r_3436_, v___y_3437_, v___y_3438_);
lean_dec(v___y_3438_);
lean_dec_ref(v___y_3437_);
lean_dec_ref(v_val_3434_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3441_, uint8_t v___x_3442_, lean_object* v___x_3443_, lean_object* v_cls_3444_, uint8_t v___x_3445_, lean_object* v___x_3446_, lean_object* v_____x_3447_, lean_object* v_exportedInfo_x3f_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v_a_3455_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_a_3468_; lean_object* v___y_3479_; lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; uint8_t v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v_snd_3552_; lean_object* v_fst_3553_; lean_object* v___x_3555_; uint8_t v_isShared_3556_; uint8_t v_isSharedCheck_3696_; 
v_snd_3552_ = lean_ctor_get(v_____x_3447_, 1);
v_fst_3553_ = lean_ctor_get(v_____x_3447_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v_____x_3447_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3555_ = v_____x_3447_;
v_isShared_3556_ = v_isSharedCheck_3696_;
goto v_resetjp_3554_;
}
else
{
lean_inc(v_snd_3552_);
lean_inc(v_fst_3553_);
lean_dec(v_____x_3447_);
v___x_3555_ = lean_box(0);
v_isShared_3556_ = v_isSharedCheck_3696_;
goto v_resetjp_3554_;
}
v___jp_3452_:
{
lean_object* v___x_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3463_; 
v___x_3456_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3453_, v___y_3454_);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3463_ == 0)
{
lean_object* v_unused_3464_; 
v_unused_3464_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3464_);
v___x_3458_ = v___x_3456_;
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v___x_3456_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3463_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3461_; 
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 1);
lean_ctor_set(v___x_3458_, 0, v_a_3455_);
v___x_3461_ = v___x_3458_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v_a_3455_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
}
v___jp_3465_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
v___x_3469_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3466_, v___y_3467_);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3477_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
lean_ctor_set(v___x_3471_, 0, v_a_3468_);
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3468_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
v___jp_3478_:
{
lean_object* v___x_3491_; 
lean_inc_ref(v___y_3485_);
v___x_3491_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3480_, v___y_3485_, v___y_3484_, v___y_3490_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v___x_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3538_; 
lean_dec_ref_known(v___x_3491_, 1);
lean_dec(v___y_3488_);
lean_inc_ref(v___y_3481_);
v___x_3492_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3481_, v___y_3483_);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3538_ == 0)
{
lean_object* v_unused_3539_; 
v_unused_3539_ = lean_ctor_get(v___x_3492_, 0);
lean_dec(v_unused_3539_);
v___x_3494_ = v___x_3492_;
v_isShared_3495_ = v_isSharedCheck_3538_;
goto v_resetjp_3493_;
}
else
{
lean_dec(v___x_3492_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3538_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; uint8_t v___x_3498_; 
v___x_3496_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3489_);
v___x_3497_ = l_Lean_Elab_async;
v___x_3498_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3496_, v___x_3497_);
lean_dec_ref(v___x_3496_);
if (v___x_3498_ == 0)
{
lean_object* v___x_3499_; lean_object* v_r_3500_; 
lean_del_object(v___x_3494_);
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3482_);
v___x_3499_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3485_, v___y_3483_);
lean_dec_ref(v___x_3499_);
v_r_3500_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3441_, v___y_3489_, v___y_3483_);
if (lean_obj_tag(v_r_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3510_; 
v_a_3501_ = lean_ctor_get(v_r_3500_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v_r_3500_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3503_ = v_r_3500_;
v_isShared_3504_ = v_isSharedCheck_3510_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_a_3501_);
lean_dec(v_r_3500_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3510_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3506_; 
lean_inc(v_a_3501_);
if (v_isShared_3504_ == 0)
{
lean_ctor_set_tag(v___x_3503_, 1);
v___x_3506_ = v___x_3503_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3501_);
v___x_3506_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; 
v___x_3507_ = lean_apply_2(v___y_3479_, v___x_3506_, lean_box(0));
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_dec_ref_known(v___x_3507_, 1);
v___y_3466_ = v___y_3481_;
v___y_3467_ = v___y_3483_;
v_a_3468_ = v_a_3501_;
goto v___jp_3465_;
}
else
{
lean_object* v_a_3508_; 
lean_dec(v_a_3501_);
v_a_3508_ = lean_ctor_get(v___x_3507_, 0);
lean_inc(v_a_3508_);
lean_dec_ref_known(v___x_3507_, 1);
v___y_3453_ = v___y_3481_;
v___y_3454_ = v___y_3483_;
v_a_3455_ = v_a_3508_;
goto v___jp_3452_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3511_ = lean_ctor_get(v_r_3500_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v_r_3500_, 1);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_apply_2(v___y_3479_, v___x_3512_, lean_box(0));
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_dec_ref_known(v___x_3513_, 1);
v___y_3453_ = v___y_3481_;
v___y_3454_ = v___y_3483_;
v_a_3455_ = v_a_3511_;
goto v___jp_3452_;
}
else
{
lean_object* v_a_3514_; 
lean_dec(v_a_3511_);
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___y_3453_ = v___y_3481_;
v___y_3454_ = v___y_3483_;
v_a_3455_ = v_a_3514_;
goto v___jp_3452_;
}
}
}
else
{
lean_object* v___x_3515_; lean_object* v___x_3517_; 
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v___y_3479_);
lean_dec(v_decl_3441_);
v___x_3515_ = l_IO_CancelToken_new();
if (v_isShared_3495_ == 0)
{
lean_ctor_set_tag(v___x_3494_, 1);
lean_ctor_set(v___x_3494_, 0, v___x_3515_);
v___x_3517_ = v___x_3494_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v___x_3515_);
v___x_3517_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v___x_3518_ = lean_unsigned_to_nat(0u);
v___x_3519_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3520_ = l_Lean_Name_toString(v___x_3519_, v___x_3442_);
lean_inc_ref(v___x_3517_);
v___x_3521_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3487_, v___x_3517_, v___x_3520_, v___y_3489_, v___y_3483_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; lean_object* v_checked_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
v_checked_3523_ = lean_ctor_get(v___y_3482_, 2);
lean_inc_ref(v_checked_3523_);
lean_dec_ref(v___y_3482_);
v___x_3524_ = lean_io_map_task(v_a_3522_, v_checked_3523_, v___x_3518_, v___y_3486_);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_box(2);
v___x_3527_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3525_);
lean_ctor_set(v___x_3527_, 1, v___x_3526_);
lean_ctor_set(v___x_3527_, 2, v___x_3517_);
lean_ctor_set(v___x_3527_, 3, v___x_3524_);
v___x_3528_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3527_, v___y_3483_);
return v___x_3528_;
}
else
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3536_; 
lean_dec_ref(v___x_3517_);
lean_dec_ref(v___y_3482_);
v_a_3529_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3536_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3536_ == 0)
{
v___x_3531_ = v___x_3521_;
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3521_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3536_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_a_3529_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v___y_3487_);
lean_dec_ref(v___y_3485_);
lean_dec_ref(v___y_3482_);
lean_dec_ref(v___y_3481_);
lean_dec_ref(v___y_3479_);
lean_dec(v_decl_3441_);
v_a_3540_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3542_ = v___x_3491_;
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3491_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3551_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3544_; lean_object* v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3549_; 
v___x_3544_ = lean_io_error_to_string(v_a_3540_);
v___x_3545_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
v___x_3546_ = l_Lean_MessageData_ofFormat(v___x_3545_);
v___x_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3547_, 0, v___y_3488_);
lean_ctor_set(v___x_3547_, 1, v___x_3546_);
if (v_isShared_3543_ == 0)
{
lean_ctor_set(v___x_3542_, 0, v___x_3547_);
v___x_3549_ = v___x_3542_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v___x_3547_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
v_resetjp_3554_:
{
lean_object* v_fst_3557_; lean_object* v_snd_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3695_; 
v_fst_3557_ = lean_ctor_get(v_snd_3552_, 0);
v_snd_3558_ = lean_ctor_get(v_snd_3552_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_snd_3552_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3560_ = v_snd_3552_;
v_isShared_3561_ = v_isSharedCheck_3695_;
goto v_resetjp_3559_;
}
else
{
lean_inc(v_snd_3558_);
lean_inc(v_fst_3557_);
lean_dec(v_snd_3552_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3695_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___y_3563_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___y_3566_; lean_object* v___y_3567_; lean_object* v_exportedInfo_x3f_3593_; lean_object* v___y_3594_; lean_object* v___y_3595_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3609_; lean_object* v___y_3610_; uint8_t v___y_3613_; lean_object* v___y_3614_; lean_object* v___y_3615_; lean_object* v___y_3616_; uint8_t v___y_3638_; lean_object* v___y_3639_; lean_object* v___y_3640_; uint8_t v___y_3641_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___x_3685_; lean_object* v_env_3686_; uint8_t v___x_3687_; 
v___x_3685_ = lean_st_ref_get(v___y_3450_);
v_env_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc_ref(v_env_3686_);
lean_dec(v___x_3685_);
v___x_3687_ = l_Lean_Environment_containsOnBranch(v_env_3686_, v_fst_3553_);
lean_dec_ref(v_env_3686_);
if (v___x_3687_ == 0)
{
lean_del_object(v___x_3555_);
v___y_3659_ = v___y_3449_;
v___y_3660_ = v___y_3450_;
goto v___jp_3658_;
}
else
{
lean_object* v___x_3688_; lean_object* v_env_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec(v_exportedInfo_x3f_3448_);
lean_dec(v___x_3446_);
lean_dec(v_cls_3444_);
lean_dec_ref(v___x_3443_);
lean_dec(v_decl_3441_);
v___x_3688_ = lean_st_ref_get(v___y_3450_);
v_env_3689_ = lean_ctor_get(v___x_3688_, 0);
lean_inc_ref(v_env_3689_);
lean_dec(v___x_3688_);
v___x_3690_ = lean_elab_environment_to_kernel_env(v_env_3689_);
if (v_isShared_3556_ == 0)
{
lean_ctor_set_tag(v___x_3555_, 1);
lean_ctor_set(v___x_3555_, 1, v_fst_3553_);
lean_ctor_set(v___x_3555_, 0, v___x_3690_);
v___x_3692_ = v___x_3555_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3690_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_fst_3553_);
v___x_3692_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3692_, v___y_3449_, v___y_3450_);
return v___x_3693_;
}
}
v___jp_3562_:
{
lean_object* v_ref_3568_; uint8_t v___x_3569_; uint8_t v___x_3570_; lean_object* v___x_3571_; 
v_ref_3568_ = lean_ctor_get(v___y_3564_, 2);
v___x_3569_ = 0;
v___x_3570_ = lean_unbox(v_snd_3558_);
lean_dec(v_snd_3558_);
lean_inc_ref(v___y_3566_);
v___x_3571_ = l_Lean_Environment_addConstAsync(v___y_3566_, v_fst_3553_, v___x_3570_, v___y_3567_, v___x_3569_, v___x_3442_);
if (lean_obj_tag(v___x_3571_) == 0)
{
lean_object* v_a_3572_; lean_object* v_mainEnv_3573_; lean_object* v_asyncEnv_3574_; lean_object* v___f_3575_; lean_object* v___f_3576_; lean_object* v___x_3577_; 
lean_del_object(v___x_3560_);
v_a_3572_ = lean_ctor_get(v___x_3571_, 0);
lean_inc_n(v_a_3572_, 3);
lean_dec_ref_known(v___x_3571_, 1);
v_mainEnv_3573_ = lean_ctor_get(v_a_3572_, 0);
lean_inc_ref(v_mainEnv_3573_);
v_asyncEnv_3574_ = lean_ctor_get(v_a_3572_, 1);
lean_inc_ref_n(v_asyncEnv_3574_, 2);
lean_inc(v_ref_3568_);
lean_inc(v___y_3565_);
v___f_3575_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3575_, 0, v___y_3565_);
lean_closure_set(v___f_3575_, 1, v_a_3572_);
lean_closure_set(v___f_3575_, 2, v_ref_3568_);
lean_inc(v_decl_3441_);
v___f_3576_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3576_, 0, v_a_3572_);
lean_closure_set(v___f_3576_, 1, v_asyncEnv_3574_);
lean_closure_set(v___f_3576_, 2, v_decl_3441_);
v___x_3577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_fst_3557_);
if (lean_obj_tag(v___y_3563_) == 0)
{
lean_inc(v_ref_3568_);
lean_inc_ref(v___x_3577_);
v___y_3479_ = v___f_3575_;
v___y_3480_ = v_a_3572_;
v___y_3481_ = v_mainEnv_3573_;
v___y_3482_ = v___y_3566_;
v___y_3483_ = v___y_3565_;
v___y_3484_ = v___x_3577_;
v___y_3485_ = v_asyncEnv_3574_;
v___y_3486_ = v___x_3569_;
v___y_3487_ = v___f_3576_;
v___y_3488_ = v_ref_3568_;
v___y_3489_ = v___y_3564_;
v___y_3490_ = v___x_3577_;
goto v___jp_3478_;
}
else
{
lean_inc(v_ref_3568_);
v___y_3479_ = v___f_3575_;
v___y_3480_ = v_a_3572_;
v___y_3481_ = v_mainEnv_3573_;
v___y_3482_ = v___y_3566_;
v___y_3483_ = v___y_3565_;
v___y_3484_ = v___x_3577_;
v___y_3485_ = v_asyncEnv_3574_;
v___y_3486_ = v___x_3569_;
v___y_3487_ = v___f_3576_;
v___y_3488_ = v_ref_3568_;
v___y_3489_ = v___y_3564_;
v___y_3490_ = v___y_3563_;
goto v___jp_3478_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3591_; 
lean_dec_ref(v___y_3566_);
lean_dec(v___y_3563_);
lean_dec(v_fst_3557_);
lean_dec(v_decl_3441_);
v_a_3578_ = lean_ctor_get(v___x_3571_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3571_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3580_ = v___x_3571_;
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3571_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3591_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; lean_object* v___x_3586_; 
v___x_3582_ = lean_io_error_to_string(v_a_3578_);
v___x_3583_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
v___x_3584_ = l_Lean_MessageData_ofFormat(v___x_3583_);
lean_inc(v_ref_3568_);
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 1, v___x_3584_);
lean_ctor_set(v___x_3560_, 0, v_ref_3568_);
v___x_3586_ = v___x_3560_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_ref_3568_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v___x_3584_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3588_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 0, v___x_3586_);
v___x_3588_ = v___x_3580_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
v___jp_3592_:
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_st_ref_get(v___y_3595_);
if (lean_obj_tag(v_exportedInfo_x3f_3593_) == 0)
{
lean_object* v_env_3597_; lean_object* v___x_3598_; 
v_env_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_env_3597_);
lean_dec(v___x_3596_);
v___x_3598_ = lean_box(0);
v___y_3563_ = v_exportedInfo_x3f_3593_;
v___y_3564_ = v___y_3594_;
v___y_3565_ = v___y_3595_;
v___y_3566_ = v_env_3597_;
v___y_3567_ = v___x_3598_;
goto v___jp_3562_;
}
else
{
lean_object* v_env_3599_; lean_object* v_val_3600_; uint8_t v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v_env_3599_ = lean_ctor_get(v___x_3596_, 0);
lean_inc_ref(v_env_3599_);
lean_dec(v___x_3596_);
v_val_3600_ = lean_ctor_get(v_exportedInfo_x3f_3593_, 0);
v___x_3601_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3600_);
v___x_3602_ = lean_box(v___x_3601_);
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___y_3563_ = v_exportedInfo_x3f_3593_;
v___y_3564_ = v___y_3594_;
v___y_3565_ = v___y_3595_;
v___y_3566_ = v_env_3599_;
v___y_3567_ = v___x_3603_;
goto v___jp_3562_;
}
}
v___jp_3604_:
{
lean_object* v___x_3607_; 
lean_inc(v_fst_3557_);
v___x_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3607_, 0, v_fst_3557_);
v_exportedInfo_x3f_3593_ = v___x_3607_;
v___y_3594_ = v___y_3605_;
v___y_3595_ = v___y_3606_;
goto v___jp_3592_;
}
v___jp_3608_:
{
lean_object* v___x_3611_; 
lean_inc(v_fst_3557_);
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_fst_3557_);
v_exportedInfo_x3f_3593_ = v___x_3611_;
v___y_3594_ = v___y_3609_;
v___y_3595_ = v___y_3610_;
goto v___jp_3592_;
}
v___jp_3612_:
{
lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v_nextMacroScope_3619_; lean_object* v_ngen_3620_; lean_object* v_auxDeclNGen_3621_; lean_object* v_traceState_3622_; lean_object* v_recordedDeps_3623_; lean_object* v_messages_3624_; lean_object* v_infoState_3625_; lean_object* v_snapshotTasks_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3635_; 
v___x_3617_ = lean_st_ref_take(v___y_3616_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
v_nextMacroScope_3619_ = lean_ctor_get(v___x_3617_, 1);
v_ngen_3620_ = lean_ctor_get(v___x_3617_, 2);
v_auxDeclNGen_3621_ = lean_ctor_get(v___x_3617_, 3);
v_traceState_3622_ = lean_ctor_get(v___x_3617_, 4);
v_recordedDeps_3623_ = lean_ctor_get(v___x_3617_, 6);
v_messages_3624_ = lean_ctor_get(v___x_3617_, 7);
v_infoState_3625_ = lean_ctor_get(v___x_3617_, 8);
v_snapshotTasks_3626_ = lean_ctor_get(v___x_3617_, 9);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3635_ == 0)
{
lean_object* v_unused_3636_; 
v_unused_3636_ = lean_ctor_get(v___x_3617_, 5);
lean_dec(v_unused_3636_);
v___x_3628_ = v___x_3617_;
v_isShared_3629_ = v_isSharedCheck_3635_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_snapshotTasks_3626_);
lean_inc(v_infoState_3625_);
lean_inc(v_messages_3624_);
lean_inc(v_recordedDeps_3623_);
lean_inc(v_traceState_3622_);
lean_inc(v_auxDeclNGen_3621_);
lean_inc(v_ngen_3620_);
lean_inc(v_nextMacroScope_3619_);
lean_inc(v_env_3618_);
lean_dec(v___x_3617_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3635_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3630_; lean_object* v___x_3632_; 
lean_inc(v_snd_3558_);
lean_inc(v_fst_3553_);
lean_inc_ref(v___y_3614_);
v___x_3630_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_3614_, v_env_3618_, v_fst_3553_, v_snd_3558_, v___y_3613_);
if (v_isShared_3629_ == 0)
{
lean_ctor_set(v___x_3628_, 5, v___x_3443_);
lean_ctor_set(v___x_3628_, 0, v___x_3630_);
v___x_3632_ = v___x_3628_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v___x_3630_);
lean_ctor_set(v_reuseFailAlloc_3634_, 1, v_nextMacroScope_3619_);
lean_ctor_set(v_reuseFailAlloc_3634_, 2, v_ngen_3620_);
lean_ctor_set(v_reuseFailAlloc_3634_, 3, v_auxDeclNGen_3621_);
lean_ctor_set(v_reuseFailAlloc_3634_, 4, v_traceState_3622_);
lean_ctor_set(v_reuseFailAlloc_3634_, 5, v___x_3443_);
lean_ctor_set(v_reuseFailAlloc_3634_, 6, v_recordedDeps_3623_);
lean_ctor_set(v_reuseFailAlloc_3634_, 7, v_messages_3624_);
lean_ctor_set(v_reuseFailAlloc_3634_, 8, v_infoState_3625_);
lean_ctor_set(v_reuseFailAlloc_3634_, 9, v_snapshotTasks_3626_);
v___x_3632_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
lean_object* v___x_3633_; 
v___x_3633_ = lean_st_ref_put(v___y_3616_, v___x_3632_);
v_exportedInfo_x3f_3593_ = v_exportedInfo_x3f_3448_;
v___y_3594_ = v___y_3615_;
v___y_3595_ = v___y_3616_;
goto v___jp_3592_;
}
}
}
v___jp_3637_:
{
if (v___y_3641_ == 0)
{
lean_object* v_toCold_3642_; lean_object* v_options_3643_; uint8_t v_hasTrace_3644_; 
lean_dec(v_exportedInfo_x3f_3448_);
lean_dec_ref(v___x_3443_);
v_toCold_3642_ = lean_ctor_get(v___y_3639_, 0);
v_options_3643_ = lean_ctor_get(v_toCold_3642_, 2);
v_hasTrace_3644_ = lean_ctor_get_uint8(v_options_3643_, sizeof(void*)*1);
if (v_hasTrace_3644_ == 0)
{
lean_dec(v_cls_3444_);
v___y_3609_ = v___y_3639_;
v___y_3610_ = v___y_3640_;
goto v___jp_3608_;
}
else
{
lean_object* v_inheritedTraceOptions_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v_inheritedTraceOptions_3645_ = lean_ctor_get(v_toCold_3642_, 11);
v___x_3646_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3444_);
v___x_3647_ = l_Lean_Name_append(v___x_3646_, v_cls_3444_);
v___x_3648_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3645_, v_options_3643_, v___x_3647_);
lean_dec(v___x_3647_);
if (v___x_3648_ == 0)
{
lean_dec(v_cls_3444_);
v___y_3609_ = v___y_3639_;
v___y_3610_ = v___y_3640_;
goto v___jp_3608_;
}
else
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3650_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3444_, v___x_3649_, v___y_3639_, v___y_3640_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_dec_ref_known(v___x_3650_, 1);
v___y_3609_ = v___y_3639_;
v___y_3610_ = v___y_3640_;
goto v___jp_3608_;
}
else
{
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec(v_fst_3553_);
lean_dec(v_decl_3441_);
return v___x_3650_;
}
}
}
}
else
{
lean_object* v___x_3651_; lean_object* v_env_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
lean_dec(v_cls_3444_);
v___x_3651_ = lean_st_ref_get(v___y_3640_);
v_env_3652_ = lean_ctor_get(v___x_3651_, 0);
lean_inc_ref(v_env_3652_);
lean_dec(v___x_3651_);
v___x_3653_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3654_ = lean_box(1);
v___x_3655_ = 0;
v___x_3656_ = lean_box(v___x_3445_);
lean_inc(v_fst_3553_);
v___x_3657_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3656_, v___x_3653_, v_env_3652_, v_fst_3553_, v___x_3654_, v___x_3655_);
if (lean_obj_tag(v___x_3657_) == 0)
{
v___y_3613_ = v___y_3638_;
v___y_3614_ = v___x_3653_;
v___y_3615_ = v___y_3639_;
v___y_3616_ = v___y_3640_;
goto v___jp_3612_;
}
else
{
lean_dec_ref_known(v___x_3657_, 1);
if (v___y_3638_ == 0)
{
lean_dec_ref(v___x_3443_);
v_exportedInfo_x3f_3593_ = v_exportedInfo_x3f_3448_;
v___y_3594_ = v___y_3639_;
v___y_3595_ = v___y_3640_;
goto v___jp_3592_;
}
else
{
v___y_3613_ = v___y_3638_;
v___y_3614_ = v___x_3653_;
v___y_3615_ = v___y_3639_;
v___y_3616_ = v___y_3640_;
goto v___jp_3612_;
}
}
}
}
v___jp_3658_:
{
lean_object* v___x_3661_; uint8_t v___x_3662_; 
lean_inc(v_decl_3441_);
v___x_3661_ = l_Lean_Declaration_getTopLevelNames(v_decl_3441_);
v___x_3662_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3661_);
lean_dec(v___x_3661_);
if (v___x_3662_ == 0)
{
lean_dec(v___x_3446_);
if (lean_obj_tag(v_exportedInfo_x3f_3448_) == 0)
{
v___y_3638_ = v___x_3662_;
v___y_3639_ = v___y_3659_;
v___y_3640_ = v___y_3660_;
v___y_3641_ = v___x_3662_;
goto v___jp_3637_;
}
else
{
v___y_3638_ = v___x_3662_;
v___y_3639_ = v___y_3659_;
v___y_3640_ = v___y_3660_;
v___y_3641_ = v___x_3442_;
goto v___jp_3637_;
}
}
else
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v_a_3665_; uint8_t v___x_3666_; 
lean_dec(v_exportedInfo_x3f_3448_);
lean_dec_ref(v___x_3443_);
v___x_3663_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3664_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3663_, v___y_3659_);
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref(v___x_3664_);
v___x_3666_ = lean_unbox(v_a_3665_);
lean_dec(v_a_3665_);
if (v___x_3666_ == 0)
{
lean_object* v_toCold_3667_; lean_object* v_options_3668_; uint8_t v_hasTrace_3669_; 
v_toCold_3667_ = lean_ctor_get(v___y_3659_, 0);
v_options_3668_ = lean_ctor_get(v_toCold_3667_, 2);
v_hasTrace_3669_ = lean_ctor_get_uint8(v_options_3668_, sizeof(void*)*1);
if (v_hasTrace_3669_ == 0)
{
lean_dec(v_cls_3444_);
v_exportedInfo_x3f_3593_ = v___x_3446_;
v___y_3594_ = v___y_3659_;
v___y_3595_ = v___y_3660_;
goto v___jp_3592_;
}
else
{
lean_object* v_inheritedTraceOptions_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; uint8_t v___x_3673_; 
v_inheritedTraceOptions_3670_ = lean_ctor_get(v_toCold_3667_, 11);
v___x_3671_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3444_);
v___x_3672_ = l_Lean_Name_append(v___x_3671_, v_cls_3444_);
v___x_3673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3670_, v_options_3668_, v___x_3672_);
lean_dec(v___x_3672_);
if (v___x_3673_ == 0)
{
lean_dec(v_cls_3444_);
v_exportedInfo_x3f_3593_ = v___x_3446_;
v___y_3594_ = v___y_3659_;
v___y_3595_ = v___y_3660_;
goto v___jp_3592_;
}
else
{
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3675_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3444_, v___x_3674_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_dec_ref_known(v___x_3675_, 1);
v_exportedInfo_x3f_3593_ = v___x_3446_;
v___y_3594_ = v___y_3659_;
v___y_3595_ = v___y_3660_;
goto v___jp_3592_;
}
else
{
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec(v_fst_3553_);
lean_dec(v___x_3446_);
lean_dec(v_decl_3441_);
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_toCold_3676_; lean_object* v_options_3677_; uint8_t v_hasTrace_3678_; 
lean_dec(v___x_3446_);
v_toCold_3676_ = lean_ctor_get(v___y_3659_, 0);
v_options_3677_ = lean_ctor_get(v_toCold_3676_, 2);
v_hasTrace_3678_ = lean_ctor_get_uint8(v_options_3677_, sizeof(void*)*1);
if (v_hasTrace_3678_ == 0)
{
lean_dec(v_cls_3444_);
v___y_3605_ = v___y_3659_;
v___y_3606_ = v___y_3660_;
goto v___jp_3604_;
}
else
{
lean_object* v_inheritedTraceOptions_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; uint8_t v___x_3682_; 
v_inheritedTraceOptions_3679_ = lean_ctor_get(v_toCold_3676_, 11);
v___x_3680_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3444_);
v___x_3681_ = l_Lean_Name_append(v___x_3680_, v_cls_3444_);
v___x_3682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3679_, v_options_3677_, v___x_3681_);
lean_dec(v___x_3681_);
if (v___x_3682_ == 0)
{
lean_dec(v_cls_3444_);
v___y_3605_ = v___y_3659_;
v___y_3606_ = v___y_3660_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
v___x_3683_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3684_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3444_, v___x_3683_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_dec_ref_known(v___x_3684_, 1);
v___y_3605_ = v___y_3659_;
v___y_3606_ = v___y_3660_;
goto v___jp_3604_;
}
else
{
lean_del_object(v___x_3560_);
lean_dec(v_snd_3558_);
lean_dec(v_fst_3557_);
lean_dec(v_fst_3553_);
lean_dec(v_decl_3441_);
return v___x_3684_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3697_, lean_object* v___x_3698_, lean_object* v___x_3699_, lean_object* v_cls_3700_, lean_object* v___x_3701_, lean_object* v___x_3702_, lean_object* v_____x_3703_, lean_object* v_exportedInfo_x3f_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_){
_start:
{
uint8_t v___x_54907__boxed_3708_; uint8_t v___x_54910__boxed_3709_; lean_object* v_res_3710_; 
v___x_54907__boxed_3708_ = lean_unbox(v___x_3698_);
v___x_54910__boxed_3709_ = lean_unbox(v___x_3701_);
v_res_3710_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3697_, v___x_54907__boxed_3708_, v___x_3699_, v_cls_3700_, v___x_54910__boxed_3709_, v___x_3702_, v_____x_3703_, v_exportedInfo_x3f_3704_, v___y_3705_, v___y_3706_);
lean_dec(v___y_3706_);
lean_dec_ref(v___y_3705_);
return v_res_3710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3711_, uint8_t v_forceExpose_3712_, uint8_t v___x_3713_, lean_object* v___x_3714_, lean_object* v_cls_3715_, lean_object* v_defn_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_exportedInfo_x3f_3721_; lean_object* v___y_3722_; lean_object* v___y_3723_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; uint8_t v___y_3736_; lean_object* v___x_3740_; lean_object* v_env_3741_; lean_object* v___x_3742_; 
v___x_3740_ = lean_st_ref_get(v___y_3718_);
v_env_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc_ref(v_env_3741_);
lean_dec(v___x_3740_);
v___x_3742_ = lean_st_ref_get(v___y_3718_);
if (v_forceExpose_3712_ == 0)
{
if (v___x_3713_ == 0)
{
lean_dec(v___x_3742_);
lean_dec_ref(v_env_3741_);
lean_dec(v_cls_3715_);
v_exportedInfo_x3f_3721_ = v___x_3714_;
v___y_3722_ = v___y_3717_;
v___y_3723_ = v___y_3718_;
goto v___jp_3720_;
}
else
{
lean_object* v_env_3743_; lean_object* v___x_3744_; uint8_t v_isModule_3745_; 
v_env_3743_ = lean_ctor_get(v___x_3742_, 0);
lean_inc_ref(v_env_3743_);
lean_dec(v___x_3742_);
v___x_3744_ = l_Lean_Environment_header(v_env_3741_);
lean_dec_ref(v_env_3741_);
v_isModule_3745_ = lean_ctor_get_uint8(v___x_3744_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3744_);
if (v_isModule_3745_ == 0)
{
lean_dec_ref(v_env_3743_);
lean_dec(v_cls_3715_);
v_exportedInfo_x3f_3721_ = v___x_3714_;
v___y_3722_ = v___y_3717_;
v___y_3723_ = v___y_3718_;
goto v___jp_3720_;
}
else
{
uint8_t v_isExporting_3746_; lean_object* v___y_3748_; lean_object* v___y_3749_; 
v_isExporting_3746_ = lean_ctor_get_uint8(v_env_3743_, sizeof(void*)*13);
lean_dec_ref(v_env_3743_);
if (v_isExporting_3746_ == 0)
{
lean_object* v_toCold_3754_; lean_object* v_options_3755_; uint8_t v_hasTrace_3756_; 
lean_dec(v___x_3714_);
v_toCold_3754_ = lean_ctor_get(v___y_3717_, 0);
v_options_3755_ = lean_ctor_get(v_toCold_3754_, 2);
v_hasTrace_3756_ = lean_ctor_get_uint8(v_options_3755_, sizeof(void*)*1);
if (v_hasTrace_3756_ == 0)
{
lean_dec(v_cls_3715_);
v___y_3748_ = v___y_3717_;
v___y_3749_ = v___y_3718_;
goto v___jp_3747_;
}
else
{
lean_object* v_inheritedTraceOptions_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; uint8_t v___x_3760_; 
v_inheritedTraceOptions_3757_ = lean_ctor_get(v_toCold_3754_, 11);
v___x_3758_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3715_);
v___x_3759_ = l_Lean_Name_append(v___x_3758_, v_cls_3715_);
v___x_3760_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3757_, v_options_3755_, v___x_3759_);
lean_dec(v___x_3759_);
if (v___x_3760_ == 0)
{
lean_dec(v_cls_3715_);
v___y_3748_ = v___y_3717_;
v___y_3749_ = v___y_3718_;
goto v___jp_3747_;
}
else
{
lean_object* v_toConstantVal_3761_; lean_object* v_name_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v_toConstantVal_3761_ = lean_ctor_get(v_defn_3716_, 0);
v_name_3762_ = lean_ctor_get(v_toConstantVal_3761_, 0);
v___x_3763_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3762_);
v___x_3764_ = l_Lean_MessageData_ofName(v_name_3762_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3763_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3715_, v___x_3767_, v___y_3717_, v___y_3718_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_dec_ref_known(v___x_3768_, 1);
v___y_3748_ = v___y_3717_;
v___y_3749_ = v___y_3718_;
goto v___jp_3747_;
}
else
{
lean_dec_ref(v_defn_3716_);
lean_dec_ref(v___f_3711_);
return v___x_3768_;
}
}
}
}
else
{
lean_dec(v_cls_3715_);
v_exportedInfo_x3f_3721_ = v___x_3714_;
v___y_3722_ = v___y_3717_;
v___y_3723_ = v___y_3718_;
goto v___jp_3720_;
}
v___jp_3747_:
{
lean_object* v_toConstantVal_3750_; uint8_t v_safety_3751_; uint8_t v___x_3752_; uint8_t v___x_3753_; 
v_toConstantVal_3750_ = lean_ctor_get(v_defn_3716_, 0);
v_safety_3751_ = lean_ctor_get_uint8(v_defn_3716_, sizeof(void*)*4);
v___x_3752_ = 1;
v___x_3753_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3751_, v___x_3752_);
if (v___x_3753_ == 0)
{
lean_inc_ref(v_toConstantVal_3750_);
v___y_3733_ = v___y_3749_;
v___y_3734_ = v_toConstantVal_3750_;
v___y_3735_ = v___y_3748_;
v___y_3736_ = v_isModule_3745_;
goto v___jp_3732_;
}
else
{
lean_inc_ref(v_toConstantVal_3750_);
v___y_3733_ = v___y_3749_;
v___y_3734_ = v_toConstantVal_3750_;
v___y_3735_ = v___y_3748_;
v___y_3736_ = v_isExporting_3746_;
goto v___jp_3732_;
}
}
}
}
}
else
{
lean_dec(v___x_3742_);
lean_dec_ref(v_env_3741_);
lean_dec(v_cls_3715_);
v_exportedInfo_x3f_3721_ = v___x_3714_;
v___y_3722_ = v___y_3717_;
v___y_3723_ = v___y_3718_;
goto v___jp_3720_;
}
v___jp_3720_:
{
lean_object* v_toConstantVal_3724_; lean_object* v_name_3725_; lean_object* v___x_3726_; uint8_t v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_toConstantVal_3724_ = lean_ctor_get(v_defn_3716_, 0);
v_name_3725_ = lean_ctor_get(v_toConstantVal_3724_, 0);
lean_inc(v_name_3725_);
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v_defn_3716_);
v___x_3727_ = 0;
v___x_3728_ = lean_box(v___x_3727_);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3726_);
lean_ctor_set(v___x_3729_, 1, v___x_3728_);
v___x_3730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3730_, 0, v_name_3725_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
lean_inc(v___y_3723_);
lean_inc_ref(v___y_3722_);
v___x_3731_ = lean_apply_5(v___f_3711_, v___x_3730_, v_exportedInfo_x3f_3721_, v___y_3722_, v___y_3723_, lean_box(0));
return v___x_3731_;
}
v___jp_3732_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3737_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3737_, 0, v___y_3734_);
lean_ctor_set_uint8(v___x_3737_, sizeof(void*)*1, v___y_3736_);
v___x_3738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v___x_3738_);
v_exportedInfo_x3f_3721_ = v___x_3739_;
v___y_3722_ = v___y_3735_;
v___y_3723_ = v___y_3733_;
goto v___jp_3720_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3769_, lean_object* v_forceExpose_3770_, lean_object* v___x_3771_, lean_object* v___x_3772_, lean_object* v_cls_3773_, lean_object* v_defn_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_){
_start:
{
uint8_t v_forceExpose_boxed_3778_; uint8_t v___x_55408__boxed_3779_; lean_object* v_res_3780_; 
v_forceExpose_boxed_3778_ = lean_unbox(v_forceExpose_3770_);
v___x_55408__boxed_3779_ = lean_unbox(v___x_3771_);
v_res_3780_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3769_, v_forceExpose_boxed_3778_, v___x_55408__boxed_3779_, v___x_3772_, v_cls_3773_, v_defn_3774_, v___y_3775_, v___y_3776_);
lean_dec(v___y_3776_);
lean_dec_ref(v___y_3775_);
return v_res_3780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3781_, lean_object* v___f_3782_, lean_object* v_____r_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
lean_object* v_toConstantVal_3787_; uint8_t v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v_toConstantVal_3787_ = lean_ctor_get(v_val_3781_, 0);
v___x_3788_ = 0;
lean_inc_ref(v_toConstantVal_3787_);
v___x_3789_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3789_, 0, v_toConstantVal_3787_);
lean_ctor_set_uint8(v___x_3789_, sizeof(void*)*1, v___x_3788_);
v___x_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3790_, 0, v___x_3789_);
v___x_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3790_);
v___x_3792_ = lean_box(0);
lean_inc(v___y_3785_);
lean_inc_ref(v___y_3784_);
v___x_3793_ = lean_apply_5(v___f_3782_, v___x_3792_, v___x_3791_, v___y_3784_, v___y_3785_, lean_box(0));
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3794_, lean_object* v___f_3795_, lean_object* v_____r_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v_res_3800_; 
v_res_3800_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3794_, v___f_3795_, v_____r_3796_, v___y_3797_, v___y_3798_);
lean_dec(v___y_3798_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v_val_3794_);
return v_res_3800_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3801_, lean_object* v_x_3802_){
_start:
{
if (lean_obj_tag(v_x_3802_) == 0)
{
return v_x_3801_;
}
else
{
lean_object* v_head_3803_; lean_object* v_tail_3804_; lean_object* v___x_3805_; 
v_head_3803_ = lean_ctor_get(v_x_3802_, 0);
lean_inc(v_head_3803_);
v_tail_3804_ = lean_ctor_get(v_x_3802_, 1);
lean_inc(v_tail_3804_);
lean_dec_ref_known(v_x_3802_, 2);
v___x_3805_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3801_, v_head_3803_);
v_x_3801_ = v___x_3805_;
v_x_3802_ = v_tail_3804_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v_cls_3807_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3808_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3809_ = l_Lean_Name_append(v___x_3808_, v_cls_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3811_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3812_ = l_Lean_stringToMessageData(v___x_3811_);
return v___x_3812_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3815_ = l_Lean_stringToMessageData(v___x_3814_);
return v___x_3815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3816_, uint8_t v_forceExpose_3817_, lean_object* v_a_3818_, lean_object* v_a_3819_){
_start:
{
lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v_a_3824_; lean_object* v___y_3835_; lean_object* v___y_3836_; lean_object* v_a_3837_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v_a_3850_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v_a_3863_; lean_object* v_toCold_3873_; lean_object* v_options_3874_; lean_object* v_inheritedTraceOptions_3875_; uint8_t v_hasTrace_3876_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; lean_object* v___y_3881_; lean_object* v___y_3882_; uint8_t v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3952_; uint8_t v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; uint8_t v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v_exportedInfo_x3f_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; uint8_t v___x_4010_; lean_object* v_cls_4011_; lean_object* v___y_4013_; lean_object* v_options_4014_; lean_object* v_inheritedTraceOptions_4015_; lean_object* v___y_4016_; 
v_toCold_3873_ = lean_ctor_get(v_a_3818_, 0);
v_options_3874_ = lean_ctor_get(v_toCold_3873_, 2);
v_inheritedTraceOptions_3875_ = lean_ctor_get(v_toCold_3873_, 11);
v_hasTrace_3876_ = lean_ctor_get_uint8(v_options_3874_, sizeof(void*)*1);
v___x_4010_ = 0;
v_cls_4011_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3876_ == 0)
{
lean_object* v___x_4023_; lean_object* v_env_4024_; lean_object* v_nextMacroScope_4025_; lean_object* v_ngen_4026_; lean_object* v_auxDeclNGen_4027_; lean_object* v_traceState_4028_; lean_object* v_recordedDeps_4029_; lean_object* v_messages_4030_; lean_object* v_infoState_4031_; lean_object* v_snapshotTasks_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4250_; 
v___x_4023_ = lean_st_ref_take(v_a_3819_);
v_env_4024_ = lean_ctor_get(v___x_4023_, 0);
v_nextMacroScope_4025_ = lean_ctor_get(v___x_4023_, 1);
v_ngen_4026_ = lean_ctor_get(v___x_4023_, 2);
v_auxDeclNGen_4027_ = lean_ctor_get(v___x_4023_, 3);
v_traceState_4028_ = lean_ctor_get(v___x_4023_, 4);
v_recordedDeps_4029_ = lean_ctor_get(v___x_4023_, 6);
v_messages_4030_ = lean_ctor_get(v___x_4023_, 7);
v_infoState_4031_ = lean_ctor_get(v___x_4023_, 8);
v_snapshotTasks_4032_ = lean_ctor_get(v___x_4023_, 9);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4250_ == 0)
{
lean_object* v_unused_4251_; 
v_unused_4251_ = lean_ctor_get(v___x_4023_, 5);
lean_dec(v_unused_4251_);
v___x_4034_ = v___x_4023_;
v_isShared_4035_ = v_isSharedCheck_4250_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_snapshotTasks_4032_);
lean_inc(v_infoState_4031_);
lean_inc(v_messages_4030_);
lean_inc(v_recordedDeps_4029_);
lean_inc(v_traceState_4028_);
lean_inc(v_auxDeclNGen_4027_);
lean_inc(v_ngen_4026_);
lean_inc(v_nextMacroScope_4025_);
lean_inc(v_env_4024_);
lean_dec(v___x_4023_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4250_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___y_4040_; uint8_t v___y_4041_; uint8_t v___y_4042_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4070_; uint8_t v___y_4071_; uint8_t v___y_4072_; lean_object* v___y_4073_; lean_object* v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v___x_4085_; 
lean_inc(v_decl_3816_);
v___x_4036_ = l_Lean_Declaration_getNames(v_decl_3816_);
v___x_4037_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4024_, v___x_4036_);
v___x_4038_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 5, v___x_4038_);
lean_ctor_set(v___x_4034_, 0, v___x_4037_);
v___x_4085_ = v___x_4034_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v___x_4037_);
lean_ctor_set(v_reuseFailAlloc_4249_, 1, v_nextMacroScope_4025_);
lean_ctor_set(v_reuseFailAlloc_4249_, 2, v_ngen_4026_);
lean_ctor_set(v_reuseFailAlloc_4249_, 3, v_auxDeclNGen_4027_);
lean_ctor_set(v_reuseFailAlloc_4249_, 4, v_traceState_4028_);
lean_ctor_set(v_reuseFailAlloc_4249_, 5, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4249_, 6, v_recordedDeps_4029_);
lean_ctor_set(v_reuseFailAlloc_4249_, 7, v_messages_4030_);
lean_ctor_set(v_reuseFailAlloc_4249_, 8, v_infoState_4031_);
lean_ctor_set(v_reuseFailAlloc_4249_, 9, v_snapshotTasks_4032_);
v___x_4085_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4084_;
}
v___jp_4039_:
{
lean_object* v___x_4048_; lean_object* v_env_4049_; lean_object* v_nextMacroScope_4050_; lean_object* v_ngen_4051_; lean_object* v_auxDeclNGen_4052_; lean_object* v_traceState_4053_; lean_object* v_recordedDeps_4054_; lean_object* v_messages_4055_; lean_object* v_infoState_4056_; lean_object* v_snapshotTasks_4057_; lean_object* v___x_4059_; uint8_t v_isShared_4060_; uint8_t v_isSharedCheck_4067_; 
v___x_4048_ = lean_st_ref_take(v___y_4040_);
v_env_4049_ = lean_ctor_get(v___x_4048_, 0);
v_nextMacroScope_4050_ = lean_ctor_get(v___x_4048_, 1);
v_ngen_4051_ = lean_ctor_get(v___x_4048_, 2);
v_auxDeclNGen_4052_ = lean_ctor_get(v___x_4048_, 3);
v_traceState_4053_ = lean_ctor_get(v___x_4048_, 4);
v_recordedDeps_4054_ = lean_ctor_get(v___x_4048_, 6);
v_messages_4055_ = lean_ctor_get(v___x_4048_, 7);
v_infoState_4056_ = lean_ctor_get(v___x_4048_, 8);
v_snapshotTasks_4057_ = lean_ctor_get(v___x_4048_, 9);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v___x_4048_, 5);
lean_dec(v_unused_4068_);
v___x_4059_ = v___x_4048_;
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
else
{
lean_inc(v_snapshotTasks_4057_);
lean_inc(v_infoState_4056_);
lean_inc(v_messages_4055_);
lean_inc(v_recordedDeps_4054_);
lean_inc(v_traceState_4053_);
lean_inc(v_auxDeclNGen_4052_);
lean_inc(v_ngen_4051_);
lean_inc(v_nextMacroScope_4050_);
lean_inc(v_env_4049_);
lean_dec(v___x_4048_);
v___x_4059_ = lean_box(0);
v_isShared_4060_ = v_isSharedCheck_4067_;
goto v_resetjp_4058_;
}
v_resetjp_4058_:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4064_; 
v___x_4061_ = lean_box(v___y_4042_);
lean_inc(v___y_4043_);
lean_inc_ref(v___y_4044_);
v___x_4062_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_4044_, v_env_4049_, v___y_4043_, v___x_4061_, v___y_4041_);
if (v_isShared_4060_ == 0)
{
lean_ctor_set(v___x_4059_, 5, v___x_4038_);
lean_ctor_set(v___x_4059_, 0, v___x_4062_);
v___x_4064_ = v___x_4059_;
goto v_reusejp_4063_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v___x_4062_);
lean_ctor_set(v_reuseFailAlloc_4066_, 1, v_nextMacroScope_4050_);
lean_ctor_set(v_reuseFailAlloc_4066_, 2, v_ngen_4051_);
lean_ctor_set(v_reuseFailAlloc_4066_, 3, v_auxDeclNGen_4052_);
lean_ctor_set(v_reuseFailAlloc_4066_, 4, v_traceState_4053_);
lean_ctor_set(v_reuseFailAlloc_4066_, 5, v___x_4038_);
lean_ctor_set(v_reuseFailAlloc_4066_, 6, v_recordedDeps_4054_);
lean_ctor_set(v_reuseFailAlloc_4066_, 7, v_messages_4055_);
lean_ctor_set(v_reuseFailAlloc_4066_, 8, v_infoState_4056_);
lean_ctor_set(v_reuseFailAlloc_4066_, 9, v_snapshotTasks_4057_);
v___x_4064_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4063_;
}
v_reusejp_4063_:
{
lean_object* v___x_4065_; 
v___x_4065_ = lean_st_ref_put(v___y_4040_, v___x_4064_);
v___y_3982_ = v___y_4042_;
v___y_3983_ = v___y_4043_;
v___y_3984_ = v___y_4045_;
v_exportedInfo_x3f_3985_ = v___y_4047_;
v___y_3986_ = v___y_4046_;
v___y_3987_ = v___y_4040_;
goto v___jp_3981_;
}
}
}
v___jp_4069_:
{
lean_object* v___x_4077_; lean_object* v_env_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4077_ = lean_st_ref_get(v___y_4070_);
v_env_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc_ref(v_env_4078_);
lean_dec(v___x_4077_);
v___x_4079_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4080_ = lean_box(1);
v___x_4081_ = 0;
v___x_4082_ = lean_box(v___x_4010_);
lean_inc(v___y_4073_);
v___x_4083_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4082_, v___x_4079_, v_env_4078_, v___y_4073_, v___x_4080_, v___x_4081_);
if (lean_obj_tag(v___x_4083_) == 0)
{
v___y_4040_ = v___y_4070_;
v___y_4041_ = v___y_4072_;
v___y_4042_ = v___y_4071_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___x_4079_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4076_;
v___y_4047_ = v___y_4075_;
goto v___jp_4039_;
}
else
{
lean_dec_ref_known(v___x_4083_, 1);
if (v___y_4072_ == 0)
{
v___y_3982_ = v___y_4071_;
v___y_3983_ = v___y_4073_;
v___y_3984_ = v___y_4074_;
v_exportedInfo_x3f_3985_ = v___y_4075_;
v___y_3986_ = v___y_4076_;
v___y_3987_ = v___y_4070_;
goto v___jp_3981_;
}
else
{
v___y_4040_ = v___y_4070_;
v___y_4041_ = v___y_4072_;
v___y_4042_ = v___y_4071_;
v___y_4043_ = v___y_4073_;
v___y_4044_ = v___x_4079_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4076_;
v___y_4047_ = v___y_4075_;
goto v___jp_4039_;
}
}
}
v_reusejp_4084_:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; uint8_t v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v___y_4094_; lean_object* v_fst_4126_; lean_object* v_fst_4127_; uint8_t v_snd_4128_; lean_object* v_exportedInfo_x3f_4129_; lean_object* v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4141_; lean_object* v_exportedInfo_x3f_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___y_4151_; lean_object* v___y_4152_; uint8_t v___y_4153_; uint8_t v___y_4158_; lean_object* v___y_4159_; lean_object* v_toConstantVal_4160_; uint8_t v_safety_4161_; lean_object* v___y_4162_; lean_object* v___y_4163_; uint8_t v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4170_; lean_object* v_defn_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; 
v___x_4086_ = lean_st_ref_put(v_a_3819_, v___x_4085_);
v___x_4087_ = lean_box(0);
switch(lean_obj_tag(v_decl_3816_))
{
case 2:
{
lean_object* v_val_4199_; lean_object* v_exportedInfo_x3f_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___x_4208_; 
v_val_4199_ = lean_ctor_get(v_decl_3816_, 0);
v___x_4208_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4209_; lean_object* v___x_4210_; uint8_t v_isModule_4211_; 
v_env_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc_ref(v_env_4209_);
lean_dec(v___x_4208_);
v___x_4210_ = l_Lean_Environment_header(v_env_4209_);
lean_dec_ref(v_env_4209_);
v_isModule_4211_ = lean_ctor_get_uint8(v___x_4210_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4210_);
if (v_isModule_4211_ == 0)
{
v_exportedInfo_x3f_4201_ = v___x_4087_;
v___y_4202_ = v_a_3818_;
v___y_4203_ = v_a_3819_;
goto v___jp_4200_;
}
else
{
lean_object* v_toConstantVal_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v_toConstantVal_4212_ = lean_ctor_get(v_val_4199_, 0);
lean_inc_ref(v_toConstantVal_4212_);
v___x_4213_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4213_, 0, v_toConstantVal_4212_);
lean_ctor_set_uint8(v___x_4213_, sizeof(void*)*1, v_hasTrace_3876_);
v___x_4214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4214_);
v_exportedInfo_x3f_4201_ = v___x_4215_;
v___y_4202_ = v_a_3818_;
v___y_4203_ = v_a_3819_;
goto v___jp_4200_;
}
}
else
{
lean_dec(v___x_4208_);
v_exportedInfo_x3f_4201_ = v___x_4087_;
v___y_4202_ = v_a_3818_;
v___y_4203_ = v_a_3819_;
goto v___jp_4200_;
}
v___jp_4200_:
{
lean_object* v_toConstantVal_4204_; lean_object* v_name_4205_; lean_object* v___x_4206_; uint8_t v___x_4207_; 
v_toConstantVal_4204_ = lean_ctor_get(v_val_4199_, 0);
v_name_4205_ = lean_ctor_get(v_toConstantVal_4204_, 0);
lean_inc_ref(v_val_4199_);
v___x_4206_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4206_, 0, v_val_4199_);
v___x_4207_ = 1;
lean_inc(v_name_4205_);
v_fst_4126_ = v_name_4205_;
v_fst_4127_ = v___x_4206_;
v_snd_4128_ = v___x_4207_;
v_exportedInfo_x3f_4129_ = v_exportedInfo_x3f_4201_;
v___y_4130_ = v___y_4202_;
v___y_4131_ = v___y_4203_;
goto v___jp_4125_;
}
}
case 1:
{
lean_object* v_val_4216_; 
v_val_4216_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref(v_val_4216_);
v_defn_4174_ = v_val_4216_;
v___y_4175_ = v_a_3818_;
v___y_4176_ = v_a_3819_;
goto v___jp_4173_;
}
case 5:
{
lean_object* v_defns_4217_; 
v_defns_4217_ = lean_ctor_get(v_decl_3816_, 0);
if (lean_obj_tag(v_defns_4217_) == 1)
{
lean_object* v_tail_4218_; 
v_tail_4218_ = lean_ctor_get(v_defns_4217_, 1);
if (lean_obj_tag(v_tail_4218_) == 0)
{
lean_object* v_head_4219_; 
v_head_4219_ = lean_ctor_get(v_defns_4217_, 0);
lean_inc(v_head_4219_);
v_defn_4174_ = v_head_4219_;
v___y_4175_ = v_a_3818_;
v___y_4176_ = v_a_3819_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4220_; 
v___x_4220_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v_a_3818_, v_a_3819_);
return v___x_4220_;
}
}
else
{
lean_object* v___x_4221_; 
v___x_4221_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v_a_3818_, v_a_3819_);
return v___x_4221_;
}
}
case 3:
{
lean_object* v_val_4222_; lean_object* v_exportedInfo_x3f_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___x_4231_; lean_object* v_env_4232_; lean_object* v___x_4233_; 
v_val_4222_ = lean_ctor_get(v_decl_3816_, 0);
v___x_4231_ = lean_st_ref_get(v_a_3819_);
v_env_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc_ref(v_env_4232_);
lean_dec(v___x_4231_);
v___x_4233_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4234_; lean_object* v___x_4235_; uint8_t v_isModule_4236_; 
v_env_4234_ = lean_ctor_get(v___x_4233_, 0);
lean_inc_ref(v_env_4234_);
lean_dec(v___x_4233_);
v___x_4235_ = l_Lean_Environment_header(v_env_4232_);
lean_dec_ref(v_env_4232_);
v_isModule_4236_ = lean_ctor_get_uint8(v___x_4235_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4235_);
if (v_isModule_4236_ == 0)
{
lean_dec_ref(v_env_4234_);
v_exportedInfo_x3f_4224_ = v___x_4087_;
v___y_4225_ = v_a_3818_;
v___y_4226_ = v_a_3819_;
goto v___jp_4223_;
}
else
{
uint8_t v_isExporting_4237_; 
v_isExporting_4237_ = lean_ctor_get_uint8(v_env_4234_, sizeof(void*)*13);
lean_dec_ref(v_env_4234_);
if (v_isExporting_4237_ == 0)
{
lean_object* v_toConstantVal_4238_; uint8_t v_isUnsafe_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_toConstantVal_4238_ = lean_ctor_get(v_val_4222_, 0);
v_isUnsafe_4239_ = lean_ctor_get_uint8(v_val_4222_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4238_);
v___x_4240_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4240_, 0, v_toConstantVal_4238_);
lean_ctor_set_uint8(v___x_4240_, sizeof(void*)*1, v_isUnsafe_4239_);
v___x_4241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4240_);
v___x_4242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4242_, 0, v___x_4241_);
v_exportedInfo_x3f_4224_ = v___x_4242_;
v___y_4225_ = v_a_3818_;
v___y_4226_ = v_a_3819_;
goto v___jp_4223_;
}
else
{
v_exportedInfo_x3f_4224_ = v___x_4087_;
v___y_4225_ = v_a_3818_;
v___y_4226_ = v_a_3819_;
goto v___jp_4223_;
}
}
}
else
{
lean_dec(v___x_4233_);
lean_dec_ref(v_env_4232_);
v_exportedInfo_x3f_4224_ = v___x_4087_;
v___y_4225_ = v_a_3818_;
v___y_4226_ = v_a_3819_;
goto v___jp_4223_;
}
v___jp_4223_:
{
lean_object* v_toConstantVal_4227_; lean_object* v_name_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v_toConstantVal_4227_ = lean_ctor_get(v_val_4222_, 0);
v_name_4228_ = lean_ctor_get(v_toConstantVal_4227_, 0);
lean_inc_ref(v_val_4222_);
v___x_4229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4229_, 0, v_val_4222_);
v___x_4230_ = 3;
lean_inc(v_name_4228_);
v_fst_4126_ = v_name_4228_;
v_fst_4127_ = v___x_4229_;
v_snd_4128_ = v___x_4230_;
v_exportedInfo_x3f_4129_ = v_exportedInfo_x3f_4224_;
v___y_4130_ = v___y_4225_;
v___y_4131_ = v___y_4226_;
goto v___jp_4125_;
}
}
case 0:
{
lean_object* v_val_4243_; lean_object* v_toConstantVal_4244_; lean_object* v_name_4245_; lean_object* v___x_4246_; uint8_t v___x_4247_; 
v_val_4243_ = lean_ctor_get(v_decl_3816_, 0);
v_toConstantVal_4244_ = lean_ctor_get(v_val_4243_, 0);
v_name_4245_ = lean_ctor_get(v_toConstantVal_4244_, 0);
lean_inc_ref(v_val_4243_);
v___x_4246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4246_, 0, v_val_4243_);
v___x_4247_ = 2;
lean_inc(v_name_4245_);
v_fst_4126_ = v_name_4245_;
v_fst_4127_ = v___x_4246_;
v_snd_4128_ = v___x_4247_;
v_exportedInfo_x3f_4129_ = v___x_4087_;
v___y_4130_ = v_a_3818_;
v___y_4131_ = v_a_3819_;
goto v___jp_4125_;
}
default: 
{
lean_object* v___x_4248_; 
v___x_4248_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v_a_3818_, v_a_3819_);
return v___x_4248_;
}
}
v___jp_4088_:
{
lean_object* v___x_4095_; uint8_t v___x_4096_; 
lean_inc(v_decl_3816_);
v___x_4095_ = l_Lean_Declaration_getTopLevelNames(v_decl_3816_);
v___x_4096_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4095_);
lean_dec(v___x_4095_);
if (v___x_4096_ == 0)
{
if (lean_obj_tag(v___y_4092_) == 0)
{
if (v___x_4096_ == 0)
{
lean_object* v_toCold_4097_; lean_object* v_options_4098_; uint8_t v_hasTrace_4099_; 
v_toCold_4097_ = lean_ctor_get(v___y_4093_, 0);
v_options_4098_ = lean_ctor_get(v_toCold_4097_, 2);
v_hasTrace_4099_ = lean_ctor_get_uint8(v_options_4098_, sizeof(void*)*1);
if (v_hasTrace_4099_ == 0)
{
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4093_;
v___y_4001_ = v___y_4094_;
goto v___jp_3996_;
}
else
{
lean_object* v_inheritedTraceOptions_4100_; lean_object* v___x_4101_; uint8_t v___x_4102_; 
v_inheritedTraceOptions_4100_ = lean_ctor_get(v_toCold_4097_, 11);
v___x_4101_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4102_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4100_, v_options_4098_, v___x_4101_);
if (v___x_4102_ == 0)
{
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4093_;
v___y_4001_ = v___y_4094_;
goto v___jp_3996_;
}
else
{
lean_object* v___x_4103_; lean_object* v___x_4104_; 
v___x_4103_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4104_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4103_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_dec_ref_known(v___x_4104_, 1);
v___y_3997_ = v___y_4089_;
v___y_3998_ = v___y_4090_;
v___y_3999_ = v___y_4091_;
v___y_4000_ = v___y_4093_;
v___y_4001_ = v___y_4094_;
goto v___jp_3996_;
}
else
{
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v_decl_3816_);
return v___x_4104_;
}
}
}
}
else
{
v___y_4070_ = v___y_4094_;
v___y_4071_ = v___y_4089_;
v___y_4072_ = v___x_4096_;
v___y_4073_ = v___y_4090_;
v___y_4074_ = v___y_4091_;
v___y_4075_ = v___y_4092_;
v___y_4076_ = v___y_4093_;
goto v___jp_4069_;
}
}
else
{
v___y_4070_ = v___y_4094_;
v___y_4071_ = v___y_4089_;
v___y_4072_ = v___x_4096_;
v___y_4073_ = v___y_4090_;
v___y_4074_ = v___y_4091_;
v___y_4075_ = v___y_4092_;
v___y_4076_ = v___y_4093_;
goto v___jp_4069_;
}
}
else
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v_a_4107_; uint8_t v___x_4108_; 
lean_dec(v___y_4092_);
v___x_4105_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4106_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4105_, v___y_4093_);
v_a_4107_ = lean_ctor_get(v___x_4106_, 0);
lean_inc(v_a_4107_);
lean_dec_ref(v___x_4106_);
v___x_4108_ = lean_unbox(v_a_4107_);
lean_dec(v_a_4107_);
if (v___x_4108_ == 0)
{
lean_object* v_toCold_4109_; lean_object* v_options_4110_; uint8_t v_hasTrace_4111_; 
v_toCold_4109_ = lean_ctor_get(v___y_4093_, 0);
v_options_4110_ = lean_ctor_get(v_toCold_4109_, 2);
v_hasTrace_4111_ = lean_ctor_get_uint8(v_options_4110_, sizeof(void*)*1);
if (v_hasTrace_4111_ == 0)
{
v___y_3982_ = v___y_4089_;
v___y_3983_ = v___y_4090_;
v___y_3984_ = v___y_4091_;
v_exportedInfo_x3f_3985_ = v___x_4087_;
v___y_3986_ = v___y_4093_;
v___y_3987_ = v___y_4094_;
goto v___jp_3981_;
}
else
{
lean_object* v_inheritedTraceOptions_4112_; lean_object* v___x_4113_; uint8_t v___x_4114_; 
v_inheritedTraceOptions_4112_ = lean_ctor_get(v_toCold_4109_, 11);
v___x_4113_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4114_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4112_, v_options_4110_, v___x_4113_);
if (v___x_4114_ == 0)
{
v___y_3982_ = v___y_4089_;
v___y_3983_ = v___y_4090_;
v___y_3984_ = v___y_4091_;
v_exportedInfo_x3f_3985_ = v___x_4087_;
v___y_3986_ = v___y_4093_;
v___y_3987_ = v___y_4094_;
goto v___jp_3981_;
}
else
{
lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4115_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4116_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4115_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4116_) == 0)
{
lean_dec_ref_known(v___x_4116_, 1);
v___y_3982_ = v___y_4089_;
v___y_3983_ = v___y_4090_;
v___y_3984_ = v___y_4091_;
v_exportedInfo_x3f_3985_ = v___x_4087_;
v___y_3986_ = v___y_4093_;
v___y_3987_ = v___y_4094_;
goto v___jp_3981_;
}
else
{
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v_decl_3816_);
return v___x_4116_;
}
}
}
}
else
{
lean_object* v_toCold_4117_; lean_object* v_options_4118_; uint8_t v_hasTrace_4119_; 
v_toCold_4117_ = lean_ctor_get(v___y_4093_, 0);
v_options_4118_ = lean_ctor_get(v_toCold_4117_, 2);
v_hasTrace_4119_ = lean_ctor_get_uint8(v_options_4118_, sizeof(void*)*1);
if (v_hasTrace_4119_ == 0)
{
v___y_4004_ = v___y_4089_;
v___y_4005_ = v___y_4090_;
v___y_4006_ = v___y_4091_;
v___y_4007_ = v___y_4093_;
v___y_4008_ = v___y_4094_;
goto v___jp_4003_;
}
else
{
lean_object* v_inheritedTraceOptions_4120_; lean_object* v___x_4121_; uint8_t v___x_4122_; 
v_inheritedTraceOptions_4120_ = lean_ctor_get(v_toCold_4117_, 11);
v___x_4121_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4122_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4120_, v_options_4118_, v___x_4121_);
if (v___x_4122_ == 0)
{
v___y_4004_ = v___y_4089_;
v___y_4005_ = v___y_4090_;
v___y_4006_ = v___y_4091_;
v___y_4007_ = v___y_4093_;
v___y_4008_ = v___y_4094_;
goto v___jp_4003_;
}
else
{
lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4123_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4124_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4123_, v___y_4093_, v___y_4094_);
if (lean_obj_tag(v___x_4124_) == 0)
{
lean_dec_ref_known(v___x_4124_, 1);
v___y_4004_ = v___y_4089_;
v___y_4005_ = v___y_4090_;
v___y_4006_ = v___y_4091_;
v___y_4007_ = v___y_4093_;
v___y_4008_ = v___y_4094_;
goto v___jp_4003_;
}
else
{
lean_dec_ref(v___y_4091_);
lean_dec(v___y_4090_);
lean_dec(v_decl_3816_);
return v___x_4124_;
}
}
}
}
}
}
v___jp_4125_:
{
lean_object* v___x_4132_; lean_object* v_env_4133_; uint8_t v___x_4134_; 
v___x_4132_ = lean_st_ref_get(v___y_4131_);
v_env_4133_ = lean_ctor_get(v___x_4132_, 0);
lean_inc_ref(v_env_4133_);
lean_dec(v___x_4132_);
v___x_4134_ = l_Lean_Environment_containsOnBranch(v_env_4133_, v_fst_4126_);
lean_dec_ref(v_env_4133_);
if (v___x_4134_ == 0)
{
v___y_4089_ = v_snd_4128_;
v___y_4090_ = v_fst_4126_;
v___y_4091_ = v_fst_4127_;
v___y_4092_ = v_exportedInfo_x3f_4129_;
v___y_4093_ = v___y_4130_;
v___y_4094_ = v___y_4131_;
goto v___jp_4088_;
}
else
{
lean_object* v___x_4135_; lean_object* v_env_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; 
lean_dec(v_exportedInfo_x3f_4129_);
lean_dec_ref(v_fst_4127_);
lean_dec(v_decl_3816_);
v___x_4135_ = lean_st_ref_get(v___y_4131_);
v_env_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc_ref(v_env_4136_);
lean_dec(v___x_4135_);
v___x_4137_ = lean_elab_environment_to_kernel_env(v_env_4136_);
v___x_4138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v_fst_4126_);
v___x_4139_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4138_, v___y_4130_, v___y_4131_);
return v___x_4139_;
}
}
v___jp_4140_:
{
lean_object* v_toConstantVal_4145_; lean_object* v_name_4146_; lean_object* v___x_4147_; 
v_toConstantVal_4145_ = lean_ctor_get(v___y_4141_, 0);
v_name_4146_ = lean_ctor_get(v_toConstantVal_4145_, 0);
lean_inc(v_name_4146_);
v___x_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___y_4141_);
v_fst_4126_ = v_name_4146_;
v_fst_4127_ = v___x_4147_;
v_snd_4128_ = v___x_4010_;
v_exportedInfo_x3f_4129_ = v_exportedInfo_x3f_4142_;
v___y_4130_ = v___y_4143_;
v___y_4131_ = v___y_4144_;
goto v___jp_4125_;
}
v___jp_4148_:
{
lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4154_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4154_, 0, v___y_4150_);
lean_ctor_set_uint8(v___x_4154_, sizeof(void*)*1, v___y_4153_);
v___x_4155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4155_, 0, v___x_4154_);
v___x_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4155_);
v___y_4141_ = v___y_4151_;
v_exportedInfo_x3f_4142_ = v___x_4156_;
v___y_4143_ = v___y_4152_;
v___y_4144_ = v___y_4149_;
goto v___jp_4140_;
}
v___jp_4157_:
{
uint8_t v___x_4164_; uint8_t v___x_4165_; 
v___x_4164_ = 1;
v___x_4165_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4161_, v___x_4164_);
if (v___x_4165_ == 0)
{
v___y_4149_ = v___y_4163_;
v___y_4150_ = v_toConstantVal_4160_;
v___y_4151_ = v___y_4159_;
v___y_4152_ = v___y_4162_;
v___y_4153_ = v___y_4158_;
goto v___jp_4148_;
}
else
{
v___y_4149_ = v___y_4163_;
v___y_4150_ = v_toConstantVal_4160_;
v___y_4151_ = v___y_4159_;
v___y_4152_ = v___y_4162_;
v___y_4153_ = v_hasTrace_3876_;
goto v___jp_4148_;
}
}
v___jp_4166_:
{
lean_object* v_toConstantVal_4171_; uint8_t v_safety_4172_; 
v_toConstantVal_4171_ = lean_ctor_get(v___y_4168_, 0);
lean_inc_ref(v_toConstantVal_4171_);
v_safety_4172_ = lean_ctor_get_uint8(v___y_4168_, sizeof(void*)*4);
v___y_4158_ = v___y_4167_;
v___y_4159_ = v___y_4168_;
v_toConstantVal_4160_ = v_toConstantVal_4171_;
v_safety_4161_ = v_safety_4172_;
v___y_4162_ = v___y_4169_;
v___y_4163_ = v___y_4170_;
goto v___jp_4157_;
}
v___jp_4173_:
{
lean_object* v___x_4177_; lean_object* v_env_4178_; lean_object* v___x_4179_; 
v___x_4177_ = lean_st_ref_get(v___y_4176_);
v_env_4178_ = lean_ctor_get(v___x_4177_, 0);
lean_inc_ref(v_env_4178_);
lean_dec(v___x_4177_);
v___x_4179_ = lean_st_ref_get(v___y_4176_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4180_; lean_object* v___x_4181_; uint8_t v_isModule_4182_; 
v_env_4180_ = lean_ctor_get(v___x_4179_, 0);
lean_inc_ref(v_env_4180_);
lean_dec(v___x_4179_);
v___x_4181_ = l_Lean_Environment_header(v_env_4178_);
lean_dec_ref(v_env_4178_);
v_isModule_4182_ = lean_ctor_get_uint8(v___x_4181_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4181_);
if (v_isModule_4182_ == 0)
{
lean_dec_ref(v_env_4180_);
v___y_4141_ = v_defn_4174_;
v_exportedInfo_x3f_4142_ = v___x_4087_;
v___y_4143_ = v___y_4175_;
v___y_4144_ = v___y_4176_;
goto v___jp_4140_;
}
else
{
uint8_t v_isExporting_4183_; 
v_isExporting_4183_ = lean_ctor_get_uint8(v_env_4180_, sizeof(void*)*13);
lean_dec_ref(v_env_4180_);
if (v_isExporting_4183_ == 0)
{
lean_object* v_toCold_4184_; lean_object* v_options_4185_; uint8_t v_hasTrace_4186_; 
v_toCold_4184_ = lean_ctor_get(v___y_4175_, 0);
v_options_4185_ = lean_ctor_get(v_toCold_4184_, 2);
v_hasTrace_4186_ = lean_ctor_get_uint8(v_options_4185_, sizeof(void*)*1);
if (v_hasTrace_4186_ == 0)
{
v___y_4167_ = v_isModule_4182_;
v___y_4168_ = v_defn_4174_;
v___y_4169_ = v___y_4175_;
v___y_4170_ = v___y_4176_;
goto v___jp_4166_;
}
else
{
lean_object* v_inheritedTraceOptions_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; 
v_inheritedTraceOptions_4187_ = lean_ctor_get(v_toCold_4184_, 11);
v___x_4188_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4187_, v_options_4185_, v___x_4188_);
if (v___x_4189_ == 0)
{
v___y_4167_ = v_isModule_4182_;
v___y_4168_ = v_defn_4174_;
v___y_4169_ = v___y_4175_;
v___y_4170_ = v___y_4176_;
goto v___jp_4166_;
}
else
{
lean_object* v_toConstantVal_4190_; uint8_t v_safety_4191_; lean_object* v_name_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; 
v_toConstantVal_4190_ = lean_ctor_get(v_defn_4174_, 0);
lean_inc_ref(v_toConstantVal_4190_);
v_safety_4191_ = lean_ctor_get_uint8(v_defn_4174_, sizeof(void*)*4);
v_name_4192_ = lean_ctor_get(v_toConstantVal_4190_, 0);
v___x_4193_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4192_);
v___x_4194_ = l_Lean_MessageData_ofName(v_name_4192_);
v___x_4195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4197_, v___y_4175_, v___y_4176_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_dec_ref_known(v___x_4198_, 1);
v___y_4158_ = v_isModule_4182_;
v___y_4159_ = v_defn_4174_;
v_toConstantVal_4160_ = v_toConstantVal_4190_;
v_safety_4161_ = v_safety_4191_;
v___y_4162_ = v___y_4175_;
v___y_4163_ = v___y_4176_;
goto v___jp_4157_;
}
else
{
lean_dec_ref(v_toConstantVal_4190_);
lean_dec_ref(v_defn_4174_);
lean_dec(v_decl_3816_);
return v___x_4198_;
}
}
}
}
else
{
v___y_4141_ = v_defn_4174_;
v_exportedInfo_x3f_4142_ = v___x_4087_;
v___y_4143_ = v___y_4175_;
v___y_4144_ = v___y_4176_;
goto v___jp_4140_;
}
}
}
else
{
lean_dec(v___x_4179_);
lean_dec_ref(v_env_4178_);
v___y_4141_ = v_defn_4174_;
v_exportedInfo_x3f_4142_ = v___x_4087_;
v___y_4143_ = v___y_4175_;
v___y_4144_ = v___y_4176_;
goto v___jp_4140_;
}
}
}
}
}
else
{
lean_object* v___f_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; uint8_t v___x_4255_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v_a_4259_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4321_; lean_object* v___y_4322_; lean_object* v___y_4323_; lean_object* v___y_4324_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4341_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; uint8_t v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___y_4352_; lean_object* v___y_4353_; lean_object* v___y_4358_; lean_object* v___y_4359_; lean_object* v_a_4360_; lean_object* v___y_4370_; lean_object* v___y_4371_; lean_object* v___y_4372_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4397_; lean_object* v___y_4398_; lean_object* v___y_4399_; lean_object* v___y_4400_; 
lean_inc(v_decl_3816_);
v___f_4252_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4252_, 0, v_decl_3816_);
v___x_4253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4254_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4255_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3875_, v_options_3874_, v___x_4254_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4561_; uint8_t v___x_4562_; lean_object* v___y_4564_; lean_object* v___y_4565_; lean_object* v___y_4566_; lean_object* v___y_4567_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; uint8_t v___y_4637_; lean_object* v___y_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4641_; lean_object* v___y_4642_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4666_; uint8_t v___y_4667_; lean_object* v___y_4668_; lean_object* v_exportedInfo_x3f_4669_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4681_; uint8_t v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4685_; lean_object* v___y_4688_; uint8_t v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; 
v___x_4561_ = l_Lean_trace_profiler;
v___x_4562_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3874_, v___x_4561_);
if (v___x_4562_ == 0)
{
lean_object* v___x_4694_; lean_object* v_env_4695_; lean_object* v_nextMacroScope_4696_; lean_object* v_ngen_4697_; lean_object* v_auxDeclNGen_4698_; lean_object* v_traceState_4699_; lean_object* v_recordedDeps_4700_; lean_object* v_messages_4701_; lean_object* v_infoState_4702_; lean_object* v_snapshotTasks_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4951_; 
lean_dec_ref(v___f_4252_);
v___x_4694_ = lean_st_ref_take(v_a_3819_);
v_env_4695_ = lean_ctor_get(v___x_4694_, 0);
v_nextMacroScope_4696_ = lean_ctor_get(v___x_4694_, 1);
v_ngen_4697_ = lean_ctor_get(v___x_4694_, 2);
v_auxDeclNGen_4698_ = lean_ctor_get(v___x_4694_, 3);
v_traceState_4699_ = lean_ctor_get(v___x_4694_, 4);
v_recordedDeps_4700_ = lean_ctor_get(v___x_4694_, 6);
v_messages_4701_ = lean_ctor_get(v___x_4694_, 7);
v_infoState_4702_ = lean_ctor_get(v___x_4694_, 8);
v_snapshotTasks_4703_ = lean_ctor_get(v___x_4694_, 9);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4694_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v___x_4694_, 5);
lean_dec(v_unused_4952_);
v___x_4705_ = v___x_4694_;
v_isShared_4706_ = v_isSharedCheck_4951_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_snapshotTasks_4703_);
lean_inc(v_infoState_4702_);
lean_inc(v_messages_4701_);
lean_inc(v_recordedDeps_4700_);
lean_inc(v_traceState_4699_);
lean_inc(v_auxDeclNGen_4698_);
lean_inc(v_ngen_4697_);
lean_inc(v_nextMacroScope_4696_);
lean_inc(v_env_4695_);
lean_dec(v___x_4694_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4951_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; uint8_t v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; uint8_t v___y_4716_; lean_object* v___y_4717_; lean_object* v___y_4718_; uint8_t v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4743_; lean_object* v___y_4744_; uint8_t v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___x_4756_; 
lean_inc(v_decl_3816_);
v___x_4707_ = l_Lean_Declaration_getNames(v_decl_3816_);
v___x_4708_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4695_, v___x_4707_);
v___x_4709_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 5, v___x_4709_);
lean_ctor_set(v___x_4705_, 0, v___x_4708_);
v___x_4756_ = v___x_4705_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4708_);
lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_nextMacroScope_4696_);
lean_ctor_set(v_reuseFailAlloc_4950_, 2, v_ngen_4697_);
lean_ctor_set(v_reuseFailAlloc_4950_, 3, v_auxDeclNGen_4698_);
lean_ctor_set(v_reuseFailAlloc_4950_, 4, v_traceState_4699_);
lean_ctor_set(v_reuseFailAlloc_4950_, 5, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4950_, 6, v_recordedDeps_4700_);
lean_ctor_set(v_reuseFailAlloc_4950_, 7, v_messages_4701_);
lean_ctor_set(v_reuseFailAlloc_4950_, 8, v_infoState_4702_);
lean_ctor_set(v_reuseFailAlloc_4950_, 9, v_snapshotTasks_4703_);
v___x_4756_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4755_;
}
v___jp_4710_:
{
lean_object* v___x_4719_; lean_object* v_env_4720_; lean_object* v_nextMacroScope_4721_; lean_object* v_ngen_4722_; lean_object* v_auxDeclNGen_4723_; lean_object* v_traceState_4724_; lean_object* v_recordedDeps_4725_; lean_object* v_messages_4726_; lean_object* v_infoState_4727_; lean_object* v_snapshotTasks_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4738_; 
v___x_4719_ = lean_st_ref_take(v___y_4713_);
v_env_4720_ = lean_ctor_get(v___x_4719_, 0);
v_nextMacroScope_4721_ = lean_ctor_get(v___x_4719_, 1);
v_ngen_4722_ = lean_ctor_get(v___x_4719_, 2);
v_auxDeclNGen_4723_ = lean_ctor_get(v___x_4719_, 3);
v_traceState_4724_ = lean_ctor_get(v___x_4719_, 4);
v_recordedDeps_4725_ = lean_ctor_get(v___x_4719_, 6);
v_messages_4726_ = lean_ctor_get(v___x_4719_, 7);
v_infoState_4727_ = lean_ctor_get(v___x_4719_, 8);
v_snapshotTasks_4728_ = lean_ctor_get(v___x_4719_, 9);
v_isSharedCheck_4738_ = !lean_is_exclusive(v___x_4719_);
if (v_isSharedCheck_4738_ == 0)
{
lean_object* v_unused_4739_; 
v_unused_4739_ = lean_ctor_get(v___x_4719_, 5);
lean_dec(v_unused_4739_);
v___x_4730_ = v___x_4719_;
v_isShared_4731_ = v_isSharedCheck_4738_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_snapshotTasks_4728_);
lean_inc(v_infoState_4727_);
lean_inc(v_messages_4726_);
lean_inc(v_recordedDeps_4725_);
lean_inc(v_traceState_4724_);
lean_inc(v_auxDeclNGen_4723_);
lean_inc(v_ngen_4722_);
lean_inc(v_nextMacroScope_4721_);
lean_inc(v_env_4720_);
lean_dec(v___x_4719_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4738_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4735_; 
v___x_4732_ = lean_box(v___y_4716_);
lean_inc(v___y_4714_);
lean_inc_ref(v___y_4715_);
v___x_4733_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_4715_, v_env_4720_, v___y_4714_, v___x_4732_, v___y_4711_);
if (v_isShared_4731_ == 0)
{
lean_ctor_set(v___x_4730_, 5, v___x_4709_);
lean_ctor_set(v___x_4730_, 0, v___x_4733_);
v___x_4735_ = v___x_4730_;
goto v_reusejp_4734_;
}
else
{
lean_object* v_reuseFailAlloc_4737_; 
v_reuseFailAlloc_4737_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4737_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4737_, 1, v_nextMacroScope_4721_);
lean_ctor_set(v_reuseFailAlloc_4737_, 2, v_ngen_4722_);
lean_ctor_set(v_reuseFailAlloc_4737_, 3, v_auxDeclNGen_4723_);
lean_ctor_set(v_reuseFailAlloc_4737_, 4, v_traceState_4724_);
lean_ctor_set(v_reuseFailAlloc_4737_, 5, v___x_4709_);
lean_ctor_set(v_reuseFailAlloc_4737_, 6, v_recordedDeps_4725_);
lean_ctor_set(v_reuseFailAlloc_4737_, 7, v_messages_4726_);
lean_ctor_set(v_reuseFailAlloc_4737_, 8, v_infoState_4727_);
lean_ctor_set(v_reuseFailAlloc_4737_, 9, v_snapshotTasks_4728_);
v___x_4735_ = v_reuseFailAlloc_4737_;
goto v_reusejp_4734_;
}
v_reusejp_4734_:
{
lean_object* v___x_4736_; 
v___x_4736_ = lean_st_ref_put(v___y_4713_, v___x_4735_);
v___y_4666_ = v___y_4714_;
v___y_4667_ = v___y_4716_;
v___y_4668_ = v___y_4717_;
v_exportedInfo_x3f_4669_ = v___y_4712_;
v___y_4670_ = v___y_4718_;
v___y_4671_ = v___y_4713_;
goto v___jp_4665_;
}
}
}
v___jp_4740_:
{
lean_object* v___x_4748_; lean_object* v_env_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; uint8_t v___x_4752_; lean_object* v___x_4753_; lean_object* v___x_4754_; 
v___x_4748_ = lean_st_ref_get(v___y_4743_);
v_env_4749_ = lean_ctor_get(v___x_4748_, 0);
lean_inc_ref(v_env_4749_);
lean_dec(v___x_4748_);
v___x_4750_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4751_ = lean_box(1);
v___x_4752_ = 0;
v___x_4753_ = lean_box(v___x_4010_);
lean_inc(v___y_4744_);
v___x_4754_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4753_, v___x_4750_, v_env_4749_, v___y_4744_, v___x_4751_, v___x_4752_);
if (lean_obj_tag(v___x_4754_) == 0)
{
v___y_4711_ = v___y_4741_;
v___y_4712_ = v___y_4742_;
v___y_4713_ = v___y_4743_;
v___y_4714_ = v___y_4744_;
v___y_4715_ = v___x_4750_;
v___y_4716_ = v___y_4745_;
v___y_4717_ = v___y_4747_;
v___y_4718_ = v___y_4746_;
goto v___jp_4710_;
}
else
{
lean_dec_ref_known(v___x_4754_, 1);
if (v___y_4741_ == 0)
{
v___y_4666_ = v___y_4744_;
v___y_4667_ = v___y_4745_;
v___y_4668_ = v___y_4747_;
v_exportedInfo_x3f_4669_ = v___y_4742_;
v___y_4670_ = v___y_4746_;
v___y_4671_ = v___y_4743_;
goto v___jp_4665_;
}
else
{
v___y_4711_ = v___y_4741_;
v___y_4712_ = v___y_4742_;
v___y_4713_ = v___y_4743_;
v___y_4714_ = v___y_4744_;
v___y_4715_ = v___x_4750_;
v___y_4716_ = v___y_4745_;
v___y_4717_ = v___y_4747_;
v___y_4718_ = v___y_4746_;
goto v___jp_4710_;
}
}
}
v_reusejp_4755_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___y_4760_; lean_object* v___y_4761_; uint8_t v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; lean_object* v_fst_4794_; lean_object* v_fst_4795_; uint8_t v_snd_4796_; lean_object* v_exportedInfo_x3f_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4809_; lean_object* v_exportedInfo_x3f_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4819_; lean_object* v___y_4820_; uint8_t v___y_4821_; lean_object* v___y_4826_; lean_object* v_toConstantVal_4827_; uint8_t v_safety_4828_; uint8_t v___y_4829_; lean_object* v___y_4830_; lean_object* v___y_4831_; lean_object* v___y_4835_; uint8_t v___y_4836_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4844_; uint8_t v___y_4845_; lean_object* v___y_4861_; lean_object* v___y_4862_; lean_object* v___y_4863_; lean_object* v___y_4864_; lean_object* v___y_4865_; lean_object* v_defn_4870_; lean_object* v___y_4871_; lean_object* v___y_4872_; 
v___x_4757_ = lean_st_ref_put(v_a_3819_, v___x_4756_);
v___x_4758_ = lean_box(0);
switch(lean_obj_tag(v_decl_3816_))
{
case 2:
{
lean_object* v_val_4878_; lean_object* v_exportedInfo_x3f_4880_; lean_object* v___y_4881_; lean_object* v___y_4882_; lean_object* v___y_4888_; lean_object* v___y_4889_; lean_object* v___x_4894_; lean_object* v_env_4895_; 
v_val_4878_ = lean_ctor_get(v_decl_3816_, 0);
v___x_4894_ = lean_st_ref_get(v_a_3819_);
v_env_4895_ = lean_ctor_get(v___x_4894_, 0);
lean_inc_ref(v_env_4895_);
lean_dec(v___x_4894_);
if (v_forceExpose_3817_ == 0)
{
goto v___jp_4896_;
}
else
{
if (v___x_4562_ == 0)
{
lean_dec_ref(v_env_4895_);
v_exportedInfo_x3f_4880_ = v___x_4758_;
v___y_4881_ = v_a_3818_;
v___y_4882_ = v_a_3819_;
goto v___jp_4879_;
}
else
{
goto v___jp_4896_;
}
}
v___jp_4879_:
{
lean_object* v_toConstantVal_4883_; lean_object* v_name_4884_; lean_object* v___x_4885_; uint8_t v___x_4886_; 
v_toConstantVal_4883_ = lean_ctor_get(v_val_4878_, 0);
v_name_4884_ = lean_ctor_get(v_toConstantVal_4883_, 0);
lean_inc_ref(v_val_4878_);
v___x_4885_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4885_, 0, v_val_4878_);
v___x_4886_ = 1;
lean_inc(v_name_4884_);
v_fst_4794_ = v_name_4884_;
v_fst_4795_ = v___x_4885_;
v_snd_4796_ = v___x_4886_;
v_exportedInfo_x3f_4797_ = v_exportedInfo_x3f_4880_;
v___y_4798_ = v___y_4881_;
v___y_4799_ = v___y_4882_;
goto v___jp_4793_;
}
v___jp_4887_:
{
lean_object* v_toConstantVal_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; 
v_toConstantVal_4890_ = lean_ctor_get(v_val_4878_, 0);
lean_inc_ref(v_toConstantVal_4890_);
v___x_4891_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4891_, 0, v_toConstantVal_4890_);
lean_ctor_set_uint8(v___x_4891_, sizeof(void*)*1, v___x_4562_);
v___x_4892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4892_, 0, v___x_4891_);
v___x_4893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
v_exportedInfo_x3f_4880_ = v___x_4893_;
v___y_4881_ = v___y_4888_;
v___y_4882_ = v___y_4889_;
goto v___jp_4879_;
}
v___jp_4896_:
{
lean_object* v___x_4897_; uint8_t v_isModule_4898_; 
v___x_4897_ = l_Lean_Environment_header(v_env_4895_);
lean_dec_ref(v_env_4895_);
v_isModule_4898_ = lean_ctor_get_uint8(v___x_4897_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4897_);
if (v_isModule_4898_ == 0)
{
v_exportedInfo_x3f_4880_ = v___x_4758_;
v___y_4881_ = v_a_3818_;
v___y_4882_ = v_a_3819_;
goto v___jp_4879_;
}
else
{
if (v___x_4255_ == 0)
{
v___y_4888_ = v_a_3818_;
v___y_4889_ = v_a_3819_;
goto v___jp_4887_;
}
else
{
lean_object* v_toConstantVal_4899_; lean_object* v_name_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v_toConstantVal_4899_ = lean_ctor_get(v_val_4878_, 0);
v_name_4900_ = lean_ctor_get(v_toConstantVal_4899_, 0);
v___x_4901_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4900_);
v___x_4902_ = l_Lean_MessageData_ofName(v_name_4900_);
v___x_4903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4903_, 0, v___x_4901_);
lean_ctor_set(v___x_4903_, 1, v___x_4902_);
v___x_4904_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4903_);
lean_ctor_set(v___x_4905_, 1, v___x_4904_);
v___x_4906_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4905_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_dec_ref_known(v___x_4906_, 1);
v___y_4888_ = v_a_3818_;
v___y_4889_ = v_a_3819_;
goto v___jp_4887_;
}
else
{
lean_dec_ref_known(v_decl_3816_, 1);
return v___x_4906_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4907_; 
v_val_4907_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref(v_val_4907_);
v_defn_4870_ = v_val_4907_;
v___y_4871_ = v_a_3818_;
v___y_4872_ = v_a_3819_;
goto v___jp_4869_;
}
case 5:
{
lean_object* v_defns_4908_; 
v_defns_4908_ = lean_ctor_get(v_decl_3816_, 0);
if (lean_obj_tag(v_defns_4908_) == 1)
{
lean_object* v_tail_4909_; 
v_tail_4909_ = lean_ctor_get(v_defns_4908_, 1);
if (lean_obj_tag(v_tail_4909_) == 0)
{
lean_object* v_head_4910_; 
v_head_4910_ = lean_ctor_get(v_defns_4908_, 0);
lean_inc(v_head_4910_);
v_defn_4870_ = v_head_4910_;
v___y_4871_ = v_a_3818_;
v___y_4872_ = v_a_3819_;
goto v___jp_4869_;
}
else
{
v___y_4013_ = v_a_3818_;
v_options_4014_ = v_options_3874_;
v_inheritedTraceOptions_4015_ = v_inheritedTraceOptions_3875_;
v___y_4016_ = v_a_3819_;
goto v___jp_4012_;
}
}
else
{
v___y_4013_ = v_a_3818_;
v_options_4014_ = v_options_3874_;
v_inheritedTraceOptions_4015_ = v_inheritedTraceOptions_3875_;
v___y_4016_ = v_a_3819_;
goto v___jp_4012_;
}
}
case 3:
{
lean_object* v_val_4911_; lean_object* v_exportedInfo_x3f_4913_; lean_object* v___y_4914_; lean_object* v___y_4915_; lean_object* v___y_4921_; lean_object* v___y_4922_; lean_object* v___x_4928_; lean_object* v_env_4929_; lean_object* v___x_4930_; lean_object* v_env_4940_; 
v_val_4911_ = lean_ctor_get(v_decl_3816_, 0);
v___x_4928_ = lean_st_ref_get(v_a_3819_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
lean_inc_ref(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4930_ = lean_st_ref_get(v_a_3819_);
v_env_4940_ = lean_ctor_get(v___x_4930_, 0);
lean_inc_ref(v_env_4940_);
lean_dec(v___x_4930_);
if (v_forceExpose_3817_ == 0)
{
goto v___jp_4941_;
}
else
{
if (v___x_4562_ == 0)
{
lean_dec_ref(v_env_4940_);
lean_dec_ref(v_env_4929_);
v_exportedInfo_x3f_4913_ = v___x_4758_;
v___y_4914_ = v_a_3818_;
v___y_4915_ = v_a_3819_;
goto v___jp_4912_;
}
else
{
goto v___jp_4941_;
}
}
v___jp_4912_:
{
lean_object* v_toConstantVal_4916_; lean_object* v_name_4917_; lean_object* v___x_4918_; uint8_t v___x_4919_; 
v_toConstantVal_4916_ = lean_ctor_get(v_val_4911_, 0);
v_name_4917_ = lean_ctor_get(v_toConstantVal_4916_, 0);
lean_inc_ref(v_val_4911_);
v___x_4918_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4918_, 0, v_val_4911_);
v___x_4919_ = 3;
lean_inc(v_name_4917_);
v_fst_4794_ = v_name_4917_;
v_fst_4795_ = v___x_4918_;
v_snd_4796_ = v___x_4919_;
v_exportedInfo_x3f_4797_ = v_exportedInfo_x3f_4913_;
v___y_4798_ = v___y_4914_;
v___y_4799_ = v___y_4915_;
goto v___jp_4793_;
}
v___jp_4920_:
{
lean_object* v_toConstantVal_4923_; uint8_t v_isUnsafe_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_toConstantVal_4923_ = lean_ctor_get(v_val_4911_, 0);
v_isUnsafe_4924_ = lean_ctor_get_uint8(v_val_4911_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4923_);
v___x_4925_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4925_, 0, v_toConstantVal_4923_);
lean_ctor_set_uint8(v___x_4925_, sizeof(void*)*1, v_isUnsafe_4924_);
v___x_4926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4926_, 0, v___x_4925_);
v___x_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4926_);
v_exportedInfo_x3f_4913_ = v___x_4927_;
v___y_4914_ = v___y_4921_;
v___y_4915_ = v___y_4922_;
goto v___jp_4912_;
}
v___jp_4931_:
{
if (v___x_4255_ == 0)
{
v___y_4921_ = v_a_3818_;
v___y_4922_ = v_a_3819_;
goto v___jp_4920_;
}
else
{
lean_object* v_toConstantVal_4932_; lean_object* v_name_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4936_; lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; 
v_toConstantVal_4932_ = lean_ctor_get(v_val_4911_, 0);
v_name_4933_ = lean_ctor_get(v_toConstantVal_4932_, 0);
v___x_4934_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4933_);
v___x_4935_ = l_Lean_MessageData_ofName(v_name_4933_);
v___x_4936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4936_, 0, v___x_4934_);
lean_ctor_set(v___x_4936_, 1, v___x_4935_);
v___x_4937_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4936_);
lean_ctor_set(v___x_4938_, 1, v___x_4937_);
v___x_4939_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4938_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4939_) == 0)
{
lean_dec_ref_known(v___x_4939_, 1);
v___y_4921_ = v_a_3818_;
v___y_4922_ = v_a_3819_;
goto v___jp_4920_;
}
else
{
lean_dec_ref_known(v_decl_3816_, 1);
return v___x_4939_;
}
}
}
v___jp_4941_:
{
lean_object* v___x_4942_; uint8_t v_isModule_4943_; 
v___x_4942_ = l_Lean_Environment_header(v_env_4929_);
lean_dec_ref(v_env_4929_);
v_isModule_4943_ = lean_ctor_get_uint8(v___x_4942_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4942_);
if (v_isModule_4943_ == 0)
{
lean_dec_ref(v_env_4940_);
v_exportedInfo_x3f_4913_ = v___x_4758_;
v___y_4914_ = v_a_3818_;
v___y_4915_ = v_a_3819_;
goto v___jp_4912_;
}
else
{
uint8_t v_isExporting_4944_; 
v_isExporting_4944_ = lean_ctor_get_uint8(v_env_4940_, sizeof(void*)*13);
lean_dec_ref(v_env_4940_);
if (v_isExporting_4944_ == 0)
{
goto v___jp_4931_;
}
else
{
if (v___x_4562_ == 0)
{
v_exportedInfo_x3f_4913_ = v___x_4758_;
v___y_4914_ = v_a_3818_;
v___y_4915_ = v_a_3819_;
goto v___jp_4912_;
}
else
{
goto v___jp_4931_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4945_; lean_object* v_toConstantVal_4946_; lean_object* v_name_4947_; lean_object* v___x_4948_; uint8_t v___x_4949_; 
v_val_4945_ = lean_ctor_get(v_decl_3816_, 0);
v_toConstantVal_4946_ = lean_ctor_get(v_val_4945_, 0);
v_name_4947_ = lean_ctor_get(v_toConstantVal_4946_, 0);
lean_inc_ref(v_val_4945_);
v___x_4948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4948_, 0, v_val_4945_);
v___x_4949_ = 2;
lean_inc(v_name_4947_);
v_fst_4794_ = v_name_4947_;
v_fst_4795_ = v___x_4948_;
v_snd_4796_ = v___x_4949_;
v_exportedInfo_x3f_4797_ = v___x_4758_;
v___y_4798_ = v_a_3818_;
v___y_4799_ = v_a_3819_;
goto v___jp_4793_;
}
default: 
{
v___y_4013_ = v_a_3818_;
v_options_4014_ = v_options_3874_;
v_inheritedTraceOptions_4015_ = v_inheritedTraceOptions_3875_;
v___y_4016_ = v_a_3819_;
goto v___jp_4012_;
}
}
v___jp_4759_:
{
lean_object* v___x_4766_; uint8_t v___x_4767_; 
lean_inc(v_decl_3816_);
v___x_4766_ = l_Lean_Declaration_getTopLevelNames(v_decl_3816_);
v___x_4767_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4766_);
lean_dec(v___x_4766_);
if (v___x_4767_ == 0)
{
if (lean_obj_tag(v___y_4760_) == 0)
{
if (v___x_4767_ == 0)
{
lean_object* v_toCold_4768_; lean_object* v_options_4769_; uint8_t v_hasTrace_4770_; 
v_toCold_4768_ = lean_ctor_get(v___y_4764_, 0);
v_options_4769_ = lean_ctor_get(v_toCold_4768_, 2);
v_hasTrace_4770_ = lean_ctor_get_uint8(v_options_4769_, sizeof(void*)*1);
if (v_hasTrace_4770_ == 0)
{
v___y_4681_ = v___y_4761_;
v___y_4682_ = v___y_4762_;
v___y_4683_ = v___y_4763_;
v___y_4684_ = v___y_4764_;
v___y_4685_ = v___y_4765_;
goto v___jp_4680_;
}
else
{
lean_object* v_inheritedTraceOptions_4771_; uint8_t v___x_4772_; 
v_inheritedTraceOptions_4771_ = lean_ctor_get(v_toCold_4768_, 11);
v___x_4772_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4771_, v_options_4769_, v___x_4254_);
if (v___x_4772_ == 0)
{
v___y_4681_ = v___y_4761_;
v___y_4682_ = v___y_4762_;
v___y_4683_ = v___y_4763_;
v___y_4684_ = v___y_4764_;
v___y_4685_ = v___y_4765_;
goto v___jp_4680_;
}
else
{
lean_object* v___x_4773_; lean_object* v___x_4774_; 
v___x_4773_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4774_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4773_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4774_) == 0)
{
lean_dec_ref_known(v___x_4774_, 1);
v___y_4681_ = v___y_4761_;
v___y_4682_ = v___y_4762_;
v___y_4683_ = v___y_4763_;
v___y_4684_ = v___y_4764_;
v___y_4685_ = v___y_4765_;
goto v___jp_4680_;
}
else
{
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4761_);
lean_dec(v_decl_3816_);
return v___x_4774_;
}
}
}
}
else
{
v___y_4741_ = v___x_4767_;
v___y_4742_ = v___y_4760_;
v___y_4743_ = v___y_4765_;
v___y_4744_ = v___y_4761_;
v___y_4745_ = v___y_4762_;
v___y_4746_ = v___y_4764_;
v___y_4747_ = v___y_4763_;
goto v___jp_4740_;
}
}
else
{
v___y_4741_ = v___x_4767_;
v___y_4742_ = v___y_4760_;
v___y_4743_ = v___y_4765_;
v___y_4744_ = v___y_4761_;
v___y_4745_ = v___y_4762_;
v___y_4746_ = v___y_4764_;
v___y_4747_ = v___y_4763_;
goto v___jp_4740_;
}
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v_a_4777_; uint8_t v___x_4778_; 
lean_dec(v___y_4760_);
v___x_4775_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4776_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4775_, v___y_4764_);
v_a_4777_ = lean_ctor_get(v___x_4776_, 0);
lean_inc(v_a_4777_);
lean_dec_ref(v___x_4776_);
v___x_4778_ = lean_unbox(v_a_4777_);
lean_dec(v_a_4777_);
if (v___x_4778_ == 0)
{
lean_object* v_toCold_4779_; lean_object* v_options_4780_; uint8_t v_hasTrace_4781_; 
v_toCold_4779_ = lean_ctor_get(v___y_4764_, 0);
v_options_4780_ = lean_ctor_get(v_toCold_4779_, 2);
v_hasTrace_4781_ = lean_ctor_get_uint8(v_options_4780_, sizeof(void*)*1);
if (v_hasTrace_4781_ == 0)
{
v___y_4666_ = v___y_4761_;
v___y_4667_ = v___y_4762_;
v___y_4668_ = v___y_4763_;
v_exportedInfo_x3f_4669_ = v___x_4758_;
v___y_4670_ = v___y_4764_;
v___y_4671_ = v___y_4765_;
goto v___jp_4665_;
}
else
{
lean_object* v_inheritedTraceOptions_4782_; uint8_t v___x_4783_; 
v_inheritedTraceOptions_4782_ = lean_ctor_get(v_toCold_4779_, 11);
v___x_4783_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4782_, v_options_4780_, v___x_4254_);
if (v___x_4783_ == 0)
{
v___y_4666_ = v___y_4761_;
v___y_4667_ = v___y_4762_;
v___y_4668_ = v___y_4763_;
v_exportedInfo_x3f_4669_ = v___x_4758_;
v___y_4670_ = v___y_4764_;
v___y_4671_ = v___y_4765_;
goto v___jp_4665_;
}
else
{
lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4784_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4785_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4784_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_dec_ref_known(v___x_4785_, 1);
v___y_4666_ = v___y_4761_;
v___y_4667_ = v___y_4762_;
v___y_4668_ = v___y_4763_;
v_exportedInfo_x3f_4669_ = v___x_4758_;
v___y_4670_ = v___y_4764_;
v___y_4671_ = v___y_4765_;
goto v___jp_4665_;
}
else
{
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4761_);
lean_dec(v_decl_3816_);
return v___x_4785_;
}
}
}
}
else
{
lean_object* v_toCold_4786_; lean_object* v_options_4787_; uint8_t v_hasTrace_4788_; 
v_toCold_4786_ = lean_ctor_get(v___y_4764_, 0);
v_options_4787_ = lean_ctor_get(v_toCold_4786_, 2);
v_hasTrace_4788_ = lean_ctor_get_uint8(v_options_4787_, sizeof(void*)*1);
if (v_hasTrace_4788_ == 0)
{
v___y_4688_ = v___y_4761_;
v___y_4689_ = v___y_4762_;
v___y_4690_ = v___y_4763_;
v___y_4691_ = v___y_4764_;
v___y_4692_ = v___y_4765_;
goto v___jp_4687_;
}
else
{
lean_object* v_inheritedTraceOptions_4789_; uint8_t v___x_4790_; 
v_inheritedTraceOptions_4789_ = lean_ctor_get(v_toCold_4786_, 11);
v___x_4790_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4789_, v_options_4787_, v___x_4254_);
if (v___x_4790_ == 0)
{
v___y_4688_ = v___y_4761_;
v___y_4689_ = v___y_4762_;
v___y_4690_ = v___y_4763_;
v___y_4691_ = v___y_4764_;
v___y_4692_ = v___y_4765_;
goto v___jp_4687_;
}
else
{
lean_object* v___x_4791_; lean_object* v___x_4792_; 
v___x_4791_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4792_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4791_, v___y_4764_, v___y_4765_);
if (lean_obj_tag(v___x_4792_) == 0)
{
lean_dec_ref_known(v___x_4792_, 1);
v___y_4688_ = v___y_4761_;
v___y_4689_ = v___y_4762_;
v___y_4690_ = v___y_4763_;
v___y_4691_ = v___y_4764_;
v___y_4692_ = v___y_4765_;
goto v___jp_4687_;
}
else
{
lean_dec_ref(v___y_4763_);
lean_dec(v___y_4761_);
lean_dec(v_decl_3816_);
return v___x_4792_;
}
}
}
}
}
}
v___jp_4793_:
{
lean_object* v___x_4800_; lean_object* v_env_4801_; uint8_t v___x_4802_; 
v___x_4800_ = lean_st_ref_get(v___y_4799_);
v_env_4801_ = lean_ctor_get(v___x_4800_, 0);
lean_inc_ref(v_env_4801_);
lean_dec(v___x_4800_);
v___x_4802_ = l_Lean_Environment_containsOnBranch(v_env_4801_, v_fst_4794_);
lean_dec_ref(v_env_4801_);
if (v___x_4802_ == 0)
{
v___y_4760_ = v_exportedInfo_x3f_4797_;
v___y_4761_ = v_fst_4794_;
v___y_4762_ = v_snd_4796_;
v___y_4763_ = v_fst_4795_;
v___y_4764_ = v___y_4798_;
v___y_4765_ = v___y_4799_;
goto v___jp_4759_;
}
else
{
lean_object* v___x_4803_; lean_object* v_env_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; 
lean_dec(v_exportedInfo_x3f_4797_);
lean_dec_ref(v_fst_4795_);
lean_dec(v_decl_3816_);
v___x_4803_ = lean_st_ref_get(v___y_4799_);
v_env_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc_ref(v_env_4804_);
lean_dec(v___x_4803_);
v___x_4805_ = lean_elab_environment_to_kernel_env(v_env_4804_);
v___x_4806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4806_, 0, v___x_4805_);
lean_ctor_set(v___x_4806_, 1, v_fst_4794_);
v___x_4807_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4806_, v___y_4798_, v___y_4799_);
return v___x_4807_;
}
}
v___jp_4808_:
{
lean_object* v_toConstantVal_4813_; lean_object* v_name_4814_; lean_object* v___x_4815_; 
v_toConstantVal_4813_ = lean_ctor_get(v___y_4809_, 0);
v_name_4814_ = lean_ctor_get(v_toConstantVal_4813_, 0);
lean_inc(v_name_4814_);
v___x_4815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___y_4809_);
v_fst_4794_ = v_name_4814_;
v_fst_4795_ = v___x_4815_;
v_snd_4796_ = v___x_4010_;
v_exportedInfo_x3f_4797_ = v_exportedInfo_x3f_4810_;
v___y_4798_ = v___y_4811_;
v___y_4799_ = v___y_4812_;
goto v___jp_4793_;
}
v___jp_4816_:
{
lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v___x_4824_; 
v___x_4822_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4822_, 0, v___y_4817_);
lean_ctor_set_uint8(v___x_4822_, sizeof(void*)*1, v___y_4821_);
v___x_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4823_, 0, v___x_4822_);
v___x_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4824_, 0, v___x_4823_);
v___y_4809_ = v___y_4818_;
v_exportedInfo_x3f_4810_ = v___x_4824_;
v___y_4811_ = v___y_4820_;
v___y_4812_ = v___y_4819_;
goto v___jp_4808_;
}
v___jp_4825_:
{
uint8_t v___x_4832_; uint8_t v___x_4833_; 
v___x_4832_ = 1;
v___x_4833_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4828_, v___x_4832_);
if (v___x_4833_ == 0)
{
v___y_4817_ = v_toConstantVal_4827_;
v___y_4818_ = v___y_4826_;
v___y_4819_ = v___y_4831_;
v___y_4820_ = v___y_4830_;
v___y_4821_ = v___y_4829_;
goto v___jp_4816_;
}
else
{
v___y_4817_ = v_toConstantVal_4827_;
v___y_4818_ = v___y_4826_;
v___y_4819_ = v___y_4831_;
v___y_4820_ = v___y_4830_;
v___y_4821_ = v___x_4562_;
goto v___jp_4816_;
}
}
v___jp_4834_:
{
lean_object* v_toConstantVal_4839_; uint8_t v_safety_4840_; 
v_toConstantVal_4839_ = lean_ctor_get(v___y_4835_, 0);
lean_inc_ref(v_toConstantVal_4839_);
v_safety_4840_ = lean_ctor_get_uint8(v___y_4835_, sizeof(void*)*4);
v___y_4826_ = v___y_4835_;
v_toConstantVal_4827_ = v_toConstantVal_4839_;
v_safety_4828_ = v_safety_4840_;
v___y_4829_ = v___y_4836_;
v___y_4830_ = v___y_4837_;
v___y_4831_ = v___y_4838_;
goto v___jp_4825_;
}
v___jp_4841_:
{
lean_object* v_toCold_4846_; lean_object* v_options_4847_; uint8_t v_hasTrace_4848_; 
v_toCold_4846_ = lean_ctor_get(v___y_4843_, 0);
v_options_4847_ = lean_ctor_get(v_toCold_4846_, 2);
v_hasTrace_4848_ = lean_ctor_get_uint8(v_options_4847_, sizeof(void*)*1);
if (v_hasTrace_4848_ == 0)
{
v___y_4835_ = v___y_4842_;
v___y_4836_ = v___y_4845_;
v___y_4837_ = v___y_4843_;
v___y_4838_ = v___y_4844_;
goto v___jp_4834_;
}
else
{
lean_object* v_inheritedTraceOptions_4849_; uint8_t v___x_4850_; 
v_inheritedTraceOptions_4849_ = lean_ctor_get(v_toCold_4846_, 11);
v___x_4850_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4849_, v_options_4847_, v___x_4254_);
if (v___x_4850_ == 0)
{
v___y_4835_ = v___y_4842_;
v___y_4836_ = v___y_4845_;
v___y_4837_ = v___y_4843_;
v___y_4838_ = v___y_4844_;
goto v___jp_4834_;
}
else
{
lean_object* v_toConstantVal_4851_; uint8_t v_safety_4852_; lean_object* v_name_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v_toConstantVal_4851_ = lean_ctor_get(v___y_4842_, 0);
lean_inc_ref(v_toConstantVal_4851_);
v_safety_4852_ = lean_ctor_get_uint8(v___y_4842_, sizeof(void*)*4);
v_name_4853_ = lean_ctor_get(v_toConstantVal_4851_, 0);
v___x_4854_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4853_);
v___x_4855_ = l_Lean_MessageData_ofName(v_name_4853_);
v___x_4856_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4856_, 0, v___x_4854_);
lean_ctor_set(v___x_4856_, 1, v___x_4855_);
v___x_4857_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4858_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4856_);
lean_ctor_set(v___x_4858_, 1, v___x_4857_);
v___x_4859_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4858_, v___y_4843_, v___y_4844_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_dec_ref_known(v___x_4859_, 1);
v___y_4826_ = v___y_4842_;
v_toConstantVal_4827_ = v_toConstantVal_4851_;
v_safety_4828_ = v_safety_4852_;
v___y_4829_ = v___y_4845_;
v___y_4830_ = v___y_4843_;
v___y_4831_ = v___y_4844_;
goto v___jp_4825_;
}
else
{
lean_dec_ref(v_toConstantVal_4851_);
lean_dec_ref(v___y_4842_);
lean_dec(v_decl_3816_);
return v___x_4859_;
}
}
}
}
v___jp_4860_:
{
lean_object* v___x_4866_; uint8_t v_isModule_4867_; 
v___x_4866_ = l_Lean_Environment_header(v___y_4863_);
lean_dec_ref(v___y_4863_);
v_isModule_4867_ = lean_ctor_get_uint8(v___x_4866_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4866_);
if (v_isModule_4867_ == 0)
{
lean_dec_ref(v___y_4864_);
v___y_4809_ = v___y_4861_;
v_exportedInfo_x3f_4810_ = v___x_4758_;
v___y_4811_ = v___y_4862_;
v___y_4812_ = v___y_4865_;
goto v___jp_4808_;
}
else
{
uint8_t v_isExporting_4868_; 
v_isExporting_4868_ = lean_ctor_get_uint8(v___y_4864_, sizeof(void*)*13);
lean_dec_ref(v___y_4864_);
if (v_isExporting_4868_ == 0)
{
v___y_4842_ = v___y_4861_;
v___y_4843_ = v___y_4862_;
v___y_4844_ = v___y_4865_;
v___y_4845_ = v_isModule_4867_;
goto v___jp_4841_;
}
else
{
if (v___x_4562_ == 0)
{
v___y_4809_ = v___y_4861_;
v_exportedInfo_x3f_4810_ = v___x_4758_;
v___y_4811_ = v___y_4862_;
v___y_4812_ = v___y_4865_;
goto v___jp_4808_;
}
else
{
v___y_4842_ = v___y_4861_;
v___y_4843_ = v___y_4862_;
v___y_4844_ = v___y_4865_;
v___y_4845_ = v___x_4562_;
goto v___jp_4841_;
}
}
}
}
v___jp_4869_:
{
lean_object* v___x_4873_; lean_object* v_env_4874_; lean_object* v___x_4875_; 
v___x_4873_ = lean_st_ref_get(v___y_4872_);
v_env_4874_ = lean_ctor_get(v___x_4873_, 0);
lean_inc_ref(v_env_4874_);
lean_dec(v___x_4873_);
v___x_4875_ = lean_st_ref_get(v___y_4872_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4876_; 
v_env_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc_ref(v_env_4876_);
lean_dec(v___x_4875_);
v___y_4861_ = v_defn_4870_;
v___y_4862_ = v___y_4871_;
v___y_4863_ = v_env_4874_;
v___y_4864_ = v_env_4876_;
v___y_4865_ = v___y_4872_;
goto v___jp_4860_;
}
else
{
if (v___x_4562_ == 0)
{
lean_dec(v___x_4875_);
lean_dec_ref(v_env_4874_);
v___y_4809_ = v_defn_4870_;
v_exportedInfo_x3f_4810_ = v___x_4758_;
v___y_4811_ = v___y_4871_;
v___y_4812_ = v___y_4872_;
goto v___jp_4808_;
}
else
{
lean_object* v_env_4877_; 
v_env_4877_ = lean_ctor_get(v___x_4875_, 0);
lean_inc_ref(v_env_4877_);
lean_dec(v___x_4875_);
v___y_4861_ = v_defn_4870_;
v___y_4862_ = v___y_4871_;
v___y_4863_ = v_env_4874_;
v___y_4864_ = v_env_4877_;
v___y_4865_ = v___y_4872_;
goto v___jp_4860_;
}
}
}
}
}
}
else
{
goto v___jp_4403_;
}
v___jp_4563_:
{
lean_object* v___x_4575_; 
lean_inc_ref(v___y_4566_);
v___x_4575_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4571_, v___y_4566_, v___y_4573_, v___y_4574_);
if (lean_obj_tag(v___x_4575_) == 0)
{
lean_object* v___x_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4622_; 
lean_dec_ref_known(v___x_4575_, 1);
lean_dec(v___y_4564_);
lean_inc_ref(v___y_4569_);
v___x_4576_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4569_, v___y_4565_);
v_isSharedCheck_4622_ = !lean_is_exclusive(v___x_4576_);
if (v_isSharedCheck_4622_ == 0)
{
lean_object* v_unused_4623_; 
v_unused_4623_ = lean_ctor_get(v___x_4576_, 0);
lean_dec(v_unused_4623_);
v___x_4578_ = v___x_4576_;
v_isShared_4579_ = v_isSharedCheck_4622_;
goto v_resetjp_4577_;
}
else
{
lean_dec(v___x_4576_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4622_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; uint8_t v___x_4582_; 
v___x_4580_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4572_);
v___x_4581_ = l_Lean_Elab_async;
v___x_4582_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4580_, v___x_4581_);
lean_dec_ref(v___x_4580_);
if (v___x_4582_ == 0)
{
lean_object* v___x_4583_; lean_object* v_r_4584_; 
lean_del_object(v___x_4578_);
lean_dec_ref(v___y_4570_);
lean_dec_ref(v___y_4567_);
v___x_4583_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4566_, v___y_4565_);
lean_dec_ref(v___x_4583_);
v_r_4584_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v___y_4572_, v___y_4565_);
if (lean_obj_tag(v_r_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4594_; 
v_a_4585_ = lean_ctor_get(v_r_4584_, 0);
v_isSharedCheck_4594_ = !lean_is_exclusive(v_r_4584_);
if (v_isSharedCheck_4594_ == 0)
{
v___x_4587_ = v_r_4584_;
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v_r_4584_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4594_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4590_; 
lean_inc(v_a_4585_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set_tag(v___x_4587_, 1);
v___x_4590_ = v___x_4587_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4593_; 
v_reuseFailAlloc_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4593_, 0, v_a_4585_);
v___x_4590_ = v_reuseFailAlloc_4593_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_apply_2(v___y_4568_, v___x_4590_, lean_box(0));
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_dec_ref_known(v___x_4591_, 1);
v___y_3848_ = v___y_4565_;
v___y_3849_ = v___y_4569_;
v_a_3850_ = v_a_4585_;
goto v___jp_3847_;
}
else
{
lean_object* v_a_4592_; 
lean_dec(v_a_4585_);
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc(v_a_4592_);
lean_dec_ref_known(v___x_4591_, 1);
v___y_3861_ = v___y_4565_;
v___y_3862_ = v___y_4569_;
v_a_3863_ = v_a_4592_;
goto v___jp_3860_;
}
}
}
}
else
{
lean_object* v_a_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v_a_4595_ = lean_ctor_get(v_r_4584_, 0);
lean_inc(v_a_4595_);
lean_dec_ref_known(v_r_4584_, 1);
v___x_4596_ = lean_box(0);
v___x_4597_ = lean_apply_2(v___y_4568_, v___x_4596_, lean_box(0));
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_dec_ref_known(v___x_4597_, 1);
v___y_3861_ = v___y_4565_;
v___y_3862_ = v___y_4569_;
v_a_3863_ = v_a_4595_;
goto v___jp_3860_;
}
else
{
lean_object* v_a_4598_; 
lean_dec(v_a_4595_);
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
lean_inc(v_a_4598_);
lean_dec_ref_known(v___x_4597_, 1);
v___y_3861_ = v___y_4565_;
v___y_3862_ = v___y_4569_;
v_a_3863_ = v_a_4598_;
goto v___jp_3860_;
}
}
}
else
{
lean_object* v___x_4599_; lean_object* v___x_4601_; 
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v___y_4566_);
lean_dec(v_decl_3816_);
v___x_4599_ = l_IO_CancelToken_new();
if (v_isShared_4579_ == 0)
{
lean_ctor_set_tag(v___x_4578_, 1);
lean_ctor_set(v___x_4578_, 0, v___x_4599_);
v___x_4601_ = v___x_4578_;
goto v_reusejp_4600_;
}
else
{
lean_object* v_reuseFailAlloc_4621_; 
v_reuseFailAlloc_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4621_, 0, v___x_4599_);
v___x_4601_ = v_reuseFailAlloc_4621_;
goto v_reusejp_4600_;
}
v_reusejp_4600_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v___x_4602_ = lean_unsigned_to_nat(0u);
v___x_4603_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4604_ = l_Lean_Name_toString(v___x_4603_, v_hasTrace_3876_);
lean_inc_ref(v___x_4601_);
v___x_4605_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4567_, v___x_4601_, v___x_4604_, v___y_4572_, v___y_4565_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v_checked_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v_checked_4607_ = lean_ctor_get(v___y_4570_, 2);
lean_inc_ref(v_checked_4607_);
lean_dec_ref(v___y_4570_);
v___x_4608_ = lean_io_map_task(v_a_4606_, v_checked_4607_, v___x_4602_, v___x_4562_);
v___x_4609_ = lean_box(0);
v___x_4610_ = lean_box(2);
v___x_4611_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4609_);
lean_ctor_set(v___x_4611_, 1, v___x_4610_);
lean_ctor_set(v___x_4611_, 2, v___x_4601_);
lean_ctor_set(v___x_4611_, 3, v___x_4608_);
v___x_4612_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4611_, v___y_4565_);
return v___x_4612_;
}
else
{
lean_object* v_a_4613_; lean_object* v___x_4615_; uint8_t v_isShared_4616_; uint8_t v_isSharedCheck_4620_; 
lean_dec_ref(v___x_4601_);
lean_dec_ref(v___y_4570_);
v_a_4613_ = lean_ctor_get(v___x_4605_, 0);
v_isSharedCheck_4620_ = !lean_is_exclusive(v___x_4605_);
if (v_isSharedCheck_4620_ == 0)
{
v___x_4615_ = v___x_4605_;
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
else
{
lean_inc(v_a_4613_);
lean_dec(v___x_4605_);
v___x_4615_ = lean_box(0);
v_isShared_4616_ = v_isSharedCheck_4620_;
goto v_resetjp_4614_;
}
v_resetjp_4614_:
{
lean_object* v___x_4618_; 
if (v_isShared_4616_ == 0)
{
v___x_4618_ = v___x_4615_;
goto v_reusejp_4617_;
}
else
{
lean_object* v_reuseFailAlloc_4619_; 
v_reuseFailAlloc_4619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4619_, 0, v_a_4613_);
v___x_4618_ = v_reuseFailAlloc_4619_;
goto v_reusejp_4617_;
}
v_reusejp_4617_:
{
return v___x_4618_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4635_; 
lean_dec_ref(v___y_4570_);
lean_dec_ref(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v_decl_3816_);
v_a_4624_ = lean_ctor_get(v___x_4575_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4575_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4626_ = v___x_4575_;
v_isShared_4627_ = v_isSharedCheck_4635_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4575_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4635_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4633_; 
v___x_4628_ = lean_io_error_to_string(v_a_4624_);
v___x_4629_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4629_, 0, v___x_4628_);
v___x_4630_ = l_Lean_MessageData_ofFormat(v___x_4629_);
v___x_4631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___y_4564_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 0, v___x_4631_);
v___x_4633_ = v___x_4626_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4631_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
v___jp_4636_:
{
lean_object* v_ref_4645_; lean_object* v___x_4646_; 
v_ref_4645_ = lean_ctor_get(v___y_4641_, 2);
lean_inc_ref(v___y_4643_);
v___x_4646_ = l_Lean_Environment_addConstAsync(v___y_4643_, v___y_4640_, v___y_4637_, v___y_4644_, v___x_4562_, v_hasTrace_3876_);
if (lean_obj_tag(v___x_4646_) == 0)
{
lean_object* v_a_4647_; lean_object* v_mainEnv_4648_; lean_object* v_asyncEnv_4649_; lean_object* v___f_4650_; lean_object* v___f_4651_; lean_object* v___x_4652_; 
v_a_4647_ = lean_ctor_get(v___x_4646_, 0);
lean_inc_n(v_a_4647_, 3);
lean_dec_ref_known(v___x_4646_, 1);
v_mainEnv_4648_ = lean_ctor_get(v_a_4647_, 0);
lean_inc_ref(v_mainEnv_4648_);
v_asyncEnv_4649_ = lean_ctor_get(v_a_4647_, 1);
lean_inc_ref_n(v_asyncEnv_4649_, 2);
lean_inc(v_ref_4645_);
lean_inc(v___y_4638_);
v___f_4650_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4650_, 0, v___y_4638_);
lean_closure_set(v___f_4650_, 1, v_a_4647_);
lean_closure_set(v___f_4650_, 2, v_ref_4645_);
lean_inc(v_decl_3816_);
v___f_4651_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4651_, 0, v_a_4647_);
lean_closure_set(v___f_4651_, 1, v_asyncEnv_4649_);
lean_closure_set(v___f_4651_, 2, v_decl_3816_);
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v___y_4639_);
if (lean_obj_tag(v___y_4642_) == 0)
{
lean_inc_ref(v___x_4652_);
lean_inc(v_ref_4645_);
v___y_4564_ = v_ref_4645_;
v___y_4565_ = v___y_4638_;
v___y_4566_ = v_asyncEnv_4649_;
v___y_4567_ = v___f_4651_;
v___y_4568_ = v___f_4650_;
v___y_4569_ = v_mainEnv_4648_;
v___y_4570_ = v___y_4643_;
v___y_4571_ = v_a_4647_;
v___y_4572_ = v___y_4641_;
v___y_4573_ = v___x_4652_;
v___y_4574_ = v___x_4652_;
goto v___jp_4563_;
}
else
{
lean_inc(v_ref_4645_);
v___y_4564_ = v_ref_4645_;
v___y_4565_ = v___y_4638_;
v___y_4566_ = v_asyncEnv_4649_;
v___y_4567_ = v___f_4651_;
v___y_4568_ = v___f_4650_;
v___y_4569_ = v_mainEnv_4648_;
v___y_4570_ = v___y_4643_;
v___y_4571_ = v_a_4647_;
v___y_4572_ = v___y_4641_;
v___y_4573_ = v___x_4652_;
v___y_4574_ = v___y_4642_;
goto v___jp_4563_;
}
}
else
{
lean_object* v_a_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4664_; 
lean_dec_ref(v___y_4643_);
lean_dec(v___y_4642_);
lean_dec_ref(v___y_4639_);
lean_dec(v_decl_3816_);
v_a_4653_ = lean_ctor_get(v___x_4646_, 0);
v_isSharedCheck_4664_ = !lean_is_exclusive(v___x_4646_);
if (v_isSharedCheck_4664_ == 0)
{
v___x_4655_ = v___x_4646_;
v_isShared_4656_ = v_isSharedCheck_4664_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_a_4653_);
lean_dec(v___x_4646_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4664_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4662_; 
v___x_4657_ = lean_io_error_to_string(v_a_4653_);
v___x_4658_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4658_, 0, v___x_4657_);
v___x_4659_ = l_Lean_MessageData_ofFormat(v___x_4658_);
lean_inc(v_ref_4645_);
v___x_4660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4660_, 0, v_ref_4645_);
lean_ctor_set(v___x_4660_, 1, v___x_4659_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4660_);
v___x_4662_ = v___x_4655_;
goto v_reusejp_4661_;
}
else
{
lean_object* v_reuseFailAlloc_4663_; 
v_reuseFailAlloc_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4663_, 0, v___x_4660_);
v___x_4662_ = v_reuseFailAlloc_4663_;
goto v_reusejp_4661_;
}
v_reusejp_4661_:
{
return v___x_4662_;
}
}
}
}
v___jp_4665_:
{
lean_object* v___x_4672_; 
v___x_4672_ = lean_st_ref_get(v___y_4671_);
if (lean_obj_tag(v_exportedInfo_x3f_4669_) == 0)
{
lean_object* v_env_4673_; lean_object* v___x_4674_; 
v_env_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc_ref(v_env_4673_);
lean_dec(v___x_4672_);
v___x_4674_ = lean_box(0);
v___y_4637_ = v___y_4667_;
v___y_4638_ = v___y_4671_;
v___y_4639_ = v___y_4668_;
v___y_4640_ = v___y_4666_;
v___y_4641_ = v___y_4670_;
v___y_4642_ = v_exportedInfo_x3f_4669_;
v___y_4643_ = v_env_4673_;
v___y_4644_ = v___x_4674_;
goto v___jp_4636_;
}
else
{
lean_object* v_env_4675_; lean_object* v_val_4676_; uint8_t v___x_4677_; lean_object* v___x_4678_; lean_object* v___x_4679_; 
v_env_4675_ = lean_ctor_get(v___x_4672_, 0);
lean_inc_ref(v_env_4675_);
lean_dec(v___x_4672_);
v_val_4676_ = lean_ctor_get(v_exportedInfo_x3f_4669_, 0);
v___x_4677_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4676_);
v___x_4678_ = lean_box(v___x_4677_);
v___x_4679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4679_, 0, v___x_4678_);
v___y_4637_ = v___y_4667_;
v___y_4638_ = v___y_4671_;
v___y_4639_ = v___y_4668_;
v___y_4640_ = v___y_4666_;
v___y_4641_ = v___y_4670_;
v___y_4642_ = v_exportedInfo_x3f_4669_;
v___y_4643_ = v_env_4675_;
v___y_4644_ = v___x_4679_;
goto v___jp_4636_;
}
}
v___jp_4680_:
{
lean_object* v___x_4686_; 
lean_inc_ref(v___y_4683_);
v___x_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___y_4683_);
v___y_4666_ = v___y_4681_;
v___y_4667_ = v___y_4682_;
v___y_4668_ = v___y_4683_;
v_exportedInfo_x3f_4669_ = v___x_4686_;
v___y_4670_ = v___y_4684_;
v___y_4671_ = v___y_4685_;
goto v___jp_4665_;
}
v___jp_4687_:
{
lean_object* v___x_4693_; 
lean_inc_ref(v___y_4690_);
v___x_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4693_, 0, v___y_4690_);
v___y_4666_ = v___y_4688_;
v___y_4667_ = v___y_4689_;
v___y_4668_ = v___y_4690_;
v_exportedInfo_x3f_4669_ = v___x_4693_;
v___y_4670_ = v___y_4691_;
v___y_4671_ = v___y_4692_;
goto v___jp_4665_;
}
}
else
{
goto v___jp_4403_;
}
v___jp_4256_:
{
lean_object* v___x_4260_; double v___x_4261_; double v___x_4262_; double v___x_4263_; double v___x_4264_; double v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; 
v___x_4260_ = lean_io_mono_nanos_now();
v___x_4261_ = lean_float_of_nat(v___y_4257_);
v___x_4262_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4263_ = lean_float_div(v___x_4261_, v___x_4262_);
v___x_4264_ = lean_float_of_nat(v___x_4260_);
v___x_4265_ = lean_float_div(v___x_4264_, v___x_4262_);
v___x_4266_ = lean_box_float(v___x_4263_);
v___x_4267_ = lean_box_float(v___x_4265_);
v___x_4268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4266_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_a_4259_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
v___x_4270_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4011_, v_hasTrace_3876_, v___x_4253_, v_options_3874_, v___x_4255_, v___y_4258_, v___f_4252_, v___x_4269_, v_a_3818_, v_a_3819_);
return v___x_4270_;
}
v___jp_4271_:
{
if (lean_obj_tag(v___y_4274_) == 0)
{
lean_object* v_a_4275_; lean_object* v___x_4277_; uint8_t v_isShared_4278_; uint8_t v_isSharedCheck_4282_; 
v_a_4275_ = lean_ctor_get(v___y_4274_, 0);
v_isSharedCheck_4282_ = !lean_is_exclusive(v___y_4274_);
if (v_isSharedCheck_4282_ == 0)
{
v___x_4277_ = v___y_4274_;
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
else
{
lean_inc(v_a_4275_);
lean_dec(v___y_4274_);
v___x_4277_ = lean_box(0);
v_isShared_4278_ = v_isSharedCheck_4282_;
goto v_resetjp_4276_;
}
v_resetjp_4276_:
{
lean_object* v___x_4280_; 
if (v_isShared_4278_ == 0)
{
lean_ctor_set_tag(v___x_4277_, 1);
v___x_4280_ = v___x_4277_;
goto v_reusejp_4279_;
}
else
{
lean_object* v_reuseFailAlloc_4281_; 
v_reuseFailAlloc_4281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_a_4275_);
v___x_4280_ = v_reuseFailAlloc_4281_;
goto v_reusejp_4279_;
}
v_reusejp_4279_:
{
v___y_4257_ = v___y_4272_;
v___y_4258_ = v___y_4273_;
v_a_4259_ = v___x_4280_;
goto v___jp_4256_;
}
}
}
else
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4290_; 
v_a_4283_ = lean_ctor_get(v___y_4274_, 0);
v_isSharedCheck_4290_ = !lean_is_exclusive(v___y_4274_);
if (v_isSharedCheck_4290_ == 0)
{
v___x_4285_ = v___y_4274_;
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___y_4274_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4290_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4288_; 
if (v_isShared_4286_ == 0)
{
lean_ctor_set_tag(v___x_4285_, 0);
v___x_4288_ = v___x_4285_;
goto v_reusejp_4287_;
}
else
{
lean_object* v_reuseFailAlloc_4289_; 
v_reuseFailAlloc_4289_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
v___x_4288_ = v_reuseFailAlloc_4289_;
goto v_reusejp_4287_;
}
v_reusejp_4287_:
{
v___y_4257_ = v___y_4272_;
v___y_4258_ = v___y_4273_;
v_a_4259_ = v___x_4288_;
goto v___jp_4256_;
}
}
}
}
v___jp_4291_:
{
lean_object* v___x_4296_; lean_object* v___x_4297_; 
v___x_4296_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4297_ = lean_apply_5(v___y_4295_, v___x_4296_, v___y_4293_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4292_;
v___y_4273_ = v___y_4294_;
v___y_4274_ = v___x_4297_;
goto v___jp_4271_;
}
v___jp_4298_:
{
lean_object* v___x_4306_; uint8_t v_isModule_4307_; 
v___x_4306_ = l_Lean_Environment_header(v___y_4305_);
lean_dec_ref(v___y_4305_);
v_isModule_4307_ = lean_ctor_get_uint8(v___x_4306_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4306_);
if (v_isModule_4307_ == 0)
{
lean_dec_ref(v___y_4304_);
lean_dec_ref(v___y_4303_);
v___y_4292_ = v___y_4299_;
v___y_4293_ = v___y_4300_;
v___y_4294_ = v___y_4302_;
v___y_4295_ = v___y_4301_;
goto v___jp_4291_;
}
else
{
lean_dec_ref(v___y_4301_);
lean_dec(v___y_4300_);
if (v___x_4255_ == 0)
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
lean_dec_ref(v___y_4303_);
v___x_4308_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4309_ = lean_apply_4(v___y_4304_, v___x_4308_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4299_;
v___y_4273_ = v___y_4302_;
v___y_4274_ = v___x_4309_;
goto v___jp_4271_;
}
else
{
lean_object* v_toConstantVal_4310_; lean_object* v_name_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; 
v_toConstantVal_4310_ = lean_ctor_get(v___y_4303_, 0);
lean_inc_ref(v_toConstantVal_4310_);
lean_dec_ref(v___y_4303_);
v_name_4311_ = lean_ctor_get(v_toConstantVal_4310_, 0);
lean_inc(v_name_4311_);
lean_dec_ref(v_toConstantVal_4310_);
v___x_4312_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4313_ = l_Lean_MessageData_ofName(v_name_4311_);
v___x_4314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4314_, 0, v___x_4312_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4316_, 0, v___x_4314_);
lean_ctor_set(v___x_4316_, 1, v___x_4315_);
v___x_4317_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4316_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; lean_object* v___x_4319_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc(v_a_4318_);
lean_dec_ref_known(v___x_4317_, 1);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4319_ = lean_apply_4(v___y_4304_, v_a_4318_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4299_;
v___y_4273_ = v___y_4302_;
v___y_4274_ = v___x_4319_;
goto v___jp_4271_;
}
else
{
lean_dec_ref(v___y_4304_);
v___y_4272_ = v___y_4299_;
v___y_4273_ = v___y_4302_;
v___y_4274_ = v___x_4317_;
goto v___jp_4271_;
}
}
}
}
v___jp_4320_:
{
if (v___x_4255_ == 0)
{
lean_object* v___x_4325_; lean_object* v___x_4326_; 
lean_dec_ref(v___y_4321_);
v___x_4325_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4326_ = lean_apply_4(v___y_4323_, v___x_4325_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4322_;
v___y_4273_ = v___y_4324_;
v___y_4274_ = v___x_4326_;
goto v___jp_4271_;
}
else
{
lean_object* v_toConstantVal_4327_; lean_object* v_name_4328_; lean_object* v___x_4329_; lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_toConstantVal_4327_ = lean_ctor_get(v___y_4321_, 0);
lean_inc_ref(v_toConstantVal_4327_);
lean_dec_ref(v___y_4321_);
v_name_4328_ = lean_ctor_get(v_toConstantVal_4327_, 0);
lean_inc(v_name_4328_);
lean_dec_ref(v_toConstantVal_4327_);
v___x_4329_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4330_ = l_Lean_MessageData_ofName(v_name_4328_);
v___x_4331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4331_, 0, v___x_4329_);
lean_ctor_set(v___x_4331_, 1, v___x_4330_);
v___x_4332_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4333_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4331_);
lean_ctor_set(v___x_4333_, 1, v___x_4332_);
v___x_4334_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4333_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; lean_object* v___x_4336_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4336_ = lean_apply_4(v___y_4323_, v_a_4335_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4322_;
v___y_4273_ = v___y_4324_;
v___y_4274_ = v___x_4336_;
goto v___jp_4271_;
}
else
{
lean_dec_ref(v___y_4323_);
v___y_4272_ = v___y_4322_;
v___y_4273_ = v___y_4324_;
v___y_4274_ = v___x_4334_;
goto v___jp_4271_;
}
}
}
v___jp_4337_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4343_ = lean_apply_5(v___y_4340_, v___x_4342_, v___y_4339_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4272_ = v___y_4338_;
v___y_4273_ = v___y_4341_;
v___y_4274_ = v___x_4343_;
goto v___jp_4271_;
}
v___jp_4344_:
{
lean_object* v___x_4354_; uint8_t v_isModule_4355_; 
v___x_4354_ = l_Lean_Environment_header(v___y_4353_);
lean_dec_ref(v___y_4353_);
v_isModule_4355_ = lean_ctor_get_uint8(v___x_4354_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4354_);
if (v_isModule_4355_ == 0)
{
lean_dec_ref(v___y_4352_);
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4345_);
v___y_4338_ = v___y_4346_;
v___y_4339_ = v___y_4347_;
v___y_4340_ = v___y_4350_;
v___y_4341_ = v___y_4351_;
goto v___jp_4337_;
}
else
{
uint8_t v_isExporting_4356_; 
v_isExporting_4356_ = lean_ctor_get_uint8(v___y_4352_, sizeof(void*)*13);
lean_dec_ref(v___y_4352_);
if (v_isExporting_4356_ == 0)
{
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4347_);
v___y_4321_ = v___y_4345_;
v___y_4322_ = v___y_4346_;
v___y_4323_ = v___y_4349_;
v___y_4324_ = v___y_4351_;
goto v___jp_4320_;
}
else
{
if (v___y_4348_ == 0)
{
lean_dec_ref(v___y_4349_);
lean_dec_ref(v___y_4345_);
v___y_4338_ = v___y_4346_;
v___y_4339_ = v___y_4347_;
v___y_4340_ = v___y_4350_;
v___y_4341_ = v___y_4351_;
goto v___jp_4337_;
}
else
{
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4347_);
v___y_4321_ = v___y_4345_;
v___y_4322_ = v___y_4346_;
v___y_4323_ = v___y_4349_;
v___y_4324_ = v___y_4351_;
goto v___jp_4320_;
}
}
}
}
v___jp_4357_:
{
lean_object* v___x_4361_; double v___x_4362_; double v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4361_ = lean_io_get_num_heartbeats();
v___x_4362_ = lean_float_of_nat(v___y_4358_);
v___x_4363_ = lean_float_of_nat(v___x_4361_);
v___x_4364_ = lean_box_float(v___x_4362_);
v___x_4365_ = lean_box_float(v___x_4363_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v_a_4360_);
lean_ctor_set(v___x_4367_, 1, v___x_4366_);
v___x_4368_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4011_, v_hasTrace_3876_, v___x_4253_, v_options_3874_, v___x_4255_, v___y_4359_, v___f_4252_, v___x_4367_, v_a_3818_, v_a_3819_);
return v___x_4368_;
}
v___jp_4369_:
{
if (lean_obj_tag(v___y_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
v_a_4373_ = lean_ctor_get(v___y_4372_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___y_4372_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___y_4372_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___y_4372_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
lean_ctor_set_tag(v___x_4375_, 1);
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
v___y_4358_ = v___y_4370_;
v___y_4359_ = v___y_4371_;
v_a_4360_ = v___x_4378_;
goto v___jp_4357_;
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
v_a_4381_ = lean_ctor_get(v___y_4372_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___y_4372_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___y_4372_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___y_4372_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
lean_ctor_set_tag(v___x_4383_, 0);
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
v___y_4358_ = v___y_4370_;
v___y_4359_ = v___y_4371_;
v_a_4360_ = v___x_4386_;
goto v___jp_4357_;
}
}
}
}
v___jp_4389_:
{
lean_object* v___x_4394_; lean_object* v___x_4395_; 
v___x_4394_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4395_ = lean_apply_5(v___y_4390_, v___x_4394_, v___y_4393_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4370_ = v___y_4391_;
v___y_4371_ = v___y_4392_;
v___y_4372_ = v___x_4395_;
goto v___jp_4369_;
}
v___jp_4396_:
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_box(0);
lean_inc(v_a_3819_);
lean_inc_ref(v_a_3818_);
v___x_4402_ = lean_apply_5(v___y_4399_, v___x_4401_, v___y_4400_, v_a_3818_, v_a_3819_, lean_box(0));
v___y_4370_ = v___y_4397_;
v___y_4371_ = v___y_4398_;
v___y_4372_ = v___x_4402_;
goto v___jp_4369_;
}
v___jp_4403_:
{
lean_object* v___x_4404_; lean_object* v_a_4405_; lean_object* v___x_4407_; uint8_t v_isShared_4408_; uint8_t v_isSharedCheck_4560_; 
v___x_4404_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3819_);
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4560_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4560_ == 0)
{
v___x_4407_ = v___x_4404_;
v_isShared_4408_ = v_isSharedCheck_4560_;
goto v_resetjp_4406_;
}
else
{
lean_inc(v_a_4405_);
lean_dec(v___x_4404_);
v___x_4407_ = lean_box(0);
v_isShared_4408_ = v_isSharedCheck_4560_;
goto v_resetjp_4406_;
}
v_resetjp_4406_:
{
lean_object* v___x_4409_; uint8_t v___x_4410_; 
v___x_4409_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4410_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3874_, v___x_4409_);
if (v___x_4410_ == 0)
{
lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v_env_4413_; lean_object* v_nextMacroScope_4414_; lean_object* v_ngen_4415_; lean_object* v_auxDeclNGen_4416_; lean_object* v_traceState_4417_; lean_object* v_recordedDeps_4418_; lean_object* v_messages_4419_; lean_object* v_infoState_4420_; lean_object* v_snapshotTasks_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4472_; 
v___x_4411_ = lean_io_mono_nanos_now();
v___x_4412_ = lean_st_ref_take(v_a_3819_);
v_env_4413_ = lean_ctor_get(v___x_4412_, 0);
v_nextMacroScope_4414_ = lean_ctor_get(v___x_4412_, 1);
v_ngen_4415_ = lean_ctor_get(v___x_4412_, 2);
v_auxDeclNGen_4416_ = lean_ctor_get(v___x_4412_, 3);
v_traceState_4417_ = lean_ctor_get(v___x_4412_, 4);
v_recordedDeps_4418_ = lean_ctor_get(v___x_4412_, 6);
v_messages_4419_ = lean_ctor_get(v___x_4412_, 7);
v_infoState_4420_ = lean_ctor_get(v___x_4412_, 8);
v_snapshotTasks_4421_ = lean_ctor_get(v___x_4412_, 9);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4472_ == 0)
{
lean_object* v_unused_4473_; 
v_unused_4473_ = lean_ctor_get(v___x_4412_, 5);
lean_dec(v_unused_4473_);
v___x_4423_ = v___x_4412_;
v_isShared_4424_ = v_isSharedCheck_4472_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_snapshotTasks_4421_);
lean_inc(v_infoState_4420_);
lean_inc(v_messages_4419_);
lean_inc(v_recordedDeps_4418_);
lean_inc(v_traceState_4417_);
lean_inc(v_auxDeclNGen_4416_);
lean_inc(v_ngen_4415_);
lean_inc(v_nextMacroScope_4414_);
lean_inc(v_env_4413_);
lean_dec(v___x_4412_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4472_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; 
lean_inc(v_decl_3816_);
v___x_4425_ = l_Lean_Declaration_getNames(v_decl_3816_);
v___x_4426_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4413_, v___x_4425_);
v___x_4427_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4424_ == 0)
{
lean_ctor_set(v___x_4423_, 5, v___x_4427_);
lean_ctor_set(v___x_4423_, 0, v___x_4426_);
v___x_4429_ = v___x_4423_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4471_, 1, v_nextMacroScope_4414_);
lean_ctor_set(v_reuseFailAlloc_4471_, 2, v_ngen_4415_);
lean_ctor_set(v_reuseFailAlloc_4471_, 3, v_auxDeclNGen_4416_);
lean_ctor_set(v_reuseFailAlloc_4471_, 4, v_traceState_4417_);
lean_ctor_set(v_reuseFailAlloc_4471_, 5, v___x_4427_);
lean_ctor_set(v_reuseFailAlloc_4471_, 6, v_recordedDeps_4418_);
lean_ctor_set(v_reuseFailAlloc_4471_, 7, v_messages_4419_);
lean_ctor_set(v_reuseFailAlloc_4471_, 8, v_infoState_4420_);
lean_ctor_set(v_reuseFailAlloc_4471_, 9, v_snapshotTasks_4421_);
v___x_4429_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___f_4435_; 
v___x_4430_ = lean_st_ref_put(v_a_3819_, v___x_4429_);
v___x_4431_ = lean_box(0);
v___x_4432_ = lean_box(v_hasTrace_3876_);
v___x_4433_ = lean_box(v___x_4410_);
v___x_4434_ = lean_box(v___x_4010_);
lean_inc(v_decl_3816_);
v___f_4435_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 12, 7);
lean_closure_set(v___f_4435_, 0, v_decl_3816_);
lean_closure_set(v___f_4435_, 1, v___x_4432_);
lean_closure_set(v___f_4435_, 2, v___x_4433_);
lean_closure_set(v___f_4435_, 3, v___x_4427_);
lean_closure_set(v___f_4435_, 4, v___x_4434_);
lean_closure_set(v___f_4435_, 5, v_cls_4011_);
lean_closure_set(v___f_4435_, 6, v___x_4431_);
switch(lean_obj_tag(v_decl_3816_))
{
case 2:
{
lean_object* v_val_4436_; lean_object* v___f_4437_; lean_object* v___x_4438_; lean_object* v___f_4439_; lean_object* v___x_4440_; 
lean_del_object(v___x_4407_);
v_val_4436_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref_n(v_val_4436_, 3);
lean_dec_ref_known(v_decl_3816_, 1);
v___f_4437_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4437_, 0, v_val_4436_);
lean_closure_set(v___f_4437_, 1, v___f_4435_);
v___x_4438_ = lean_box(v___x_4410_);
lean_inc_ref(v___f_4437_);
v___f_4439_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4439_, 0, v_val_4436_);
lean_closure_set(v___f_4439_, 1, v___x_4438_);
lean_closure_set(v___f_4439_, 2, v___f_4437_);
v___x_4440_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4441_; 
v_env_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc_ref(v_env_4441_);
lean_dec(v___x_4440_);
v___y_4299_ = v___x_4411_;
v___y_4300_ = v___x_4431_;
v___y_4301_ = v___f_4437_;
v___y_4302_ = v_a_4405_;
v___y_4303_ = v_val_4436_;
v___y_4304_ = v___f_4439_;
v___y_4305_ = v_env_4441_;
goto v___jp_4298_;
}
else
{
if (v___x_4410_ == 0)
{
lean_dec(v___x_4440_);
lean_dec_ref(v___f_4439_);
lean_dec_ref(v_val_4436_);
v___y_4292_ = v___x_4411_;
v___y_4293_ = v___x_4431_;
v___y_4294_ = v_a_4405_;
v___y_4295_ = v___f_4437_;
goto v___jp_4291_;
}
else
{
lean_object* v_env_4442_; 
v_env_4442_ = lean_ctor_get(v___x_4440_, 0);
lean_inc_ref(v_env_4442_);
lean_dec(v___x_4440_);
v___y_4299_ = v___x_4411_;
v___y_4300_ = v___x_4431_;
v___y_4301_ = v___f_4437_;
v___y_4302_ = v_a_4405_;
v___y_4303_ = v_val_4436_;
v___y_4304_ = v___f_4439_;
v___y_4305_ = v_env_4442_;
goto v___jp_4298_;
}
}
}
case 1:
{
lean_object* v_val_4443_; lean_object* v___x_4444_; 
lean_del_object(v___x_4407_);
v_val_4443_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref(v_val_4443_);
lean_dec_ref_known(v_decl_3816_, 1);
v___x_4444_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4435_, v___x_4410_, v_cls_4011_, v___x_4431_, v_forceExpose_3817_, v_val_4443_, v_a_3818_, v_a_3819_);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4444_;
goto v___jp_4271_;
}
case 5:
{
lean_object* v_defns_4445_; 
lean_del_object(v___x_4407_);
v_defns_4445_ = lean_ctor_get(v_decl_3816_, 0);
if (lean_obj_tag(v_defns_4445_) == 1)
{
lean_object* v_tail_4446_; 
v_tail_4446_ = lean_ctor_get(v_defns_4445_, 1);
if (lean_obj_tag(v_tail_4446_) == 0)
{
lean_object* v_head_4447_; lean_object* v___x_4448_; 
lean_inc_ref(v_defns_4445_);
lean_dec_ref_known(v_decl_3816_, 1);
v_head_4447_ = lean_ctor_get(v_defns_4445_, 0);
lean_inc(v_head_4447_);
lean_dec_ref_known(v_defns_4445_, 2);
v___x_4448_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4435_, v___x_4410_, v_cls_4011_, v___x_4431_, v_forceExpose_3817_, v_head_4447_, v_a_3818_, v_a_3819_);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4448_;
goto v___jp_4271_;
}
else
{
lean_object* v___x_4449_; 
lean_dec_ref(v___f_4435_);
lean_inc_ref(v_decl_3816_);
v___x_4449_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec_ref_known(v_decl_3816_, 1);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4449_;
goto v___jp_4271_;
}
}
else
{
lean_object* v___x_4450_; 
lean_dec_ref(v___f_4435_);
lean_inc_ref(v_decl_3816_);
v___x_4450_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec_ref_known(v_decl_3816_, 1);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4450_;
goto v___jp_4271_;
}
}
case 3:
{
lean_object* v_val_4451_; lean_object* v___f_4452_; lean_object* v___f_4453_; lean_object* v___x_4454_; lean_object* v_env_4455_; lean_object* v___x_4456_; 
lean_del_object(v___x_4407_);
v_val_4451_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref_n(v_val_4451_, 3);
lean_dec_ref_known(v_decl_3816_, 1);
v___f_4452_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4452_, 0, v_val_4451_);
lean_closure_set(v___f_4452_, 1, v___f_4435_);
lean_inc_ref(v___f_4452_);
v___f_4453_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4453_, 0, v_val_4451_);
lean_closure_set(v___f_4453_, 1, v___f_4452_);
v___x_4454_ = lean_st_ref_get(v_a_3819_);
v_env_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc_ref(v_env_4455_);
lean_dec(v___x_4454_);
v___x_4456_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
lean_object* v_env_4457_; 
v_env_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc_ref(v_env_4457_);
lean_dec(v___x_4456_);
v___y_4345_ = v_val_4451_;
v___y_4346_ = v___x_4411_;
v___y_4347_ = v___x_4431_;
v___y_4348_ = v___x_4410_;
v___y_4349_ = v___f_4453_;
v___y_4350_ = v___f_4452_;
v___y_4351_ = v_a_4405_;
v___y_4352_ = v_env_4457_;
v___y_4353_ = v_env_4455_;
goto v___jp_4344_;
}
else
{
if (v___x_4410_ == 0)
{
lean_dec(v___x_4456_);
lean_dec_ref(v_env_4455_);
lean_dec_ref(v___f_4453_);
lean_dec_ref(v_val_4451_);
v___y_4338_ = v___x_4411_;
v___y_4339_ = v___x_4431_;
v___y_4340_ = v___f_4452_;
v___y_4341_ = v_a_4405_;
goto v___jp_4337_;
}
else
{
lean_object* v_env_4458_; 
v_env_4458_ = lean_ctor_get(v___x_4456_, 0);
lean_inc_ref(v_env_4458_);
lean_dec(v___x_4456_);
v___y_4345_ = v_val_4451_;
v___y_4346_ = v___x_4411_;
v___y_4347_ = v___x_4431_;
v___y_4348_ = v___x_4410_;
v___y_4349_ = v___f_4453_;
v___y_4350_ = v___f_4452_;
v___y_4351_ = v_a_4405_;
v___y_4352_ = v_env_4458_;
v___y_4353_ = v_env_4455_;
goto v___jp_4344_;
}
}
}
case 0:
{
lean_object* v_val_4459_; lean_object* v_toConstantVal_4460_; lean_object* v_name_4461_; lean_object* v___x_4463_; 
lean_dec_ref(v___f_4435_);
v_val_4459_ = lean_ctor_get(v_decl_3816_, 0);
v_toConstantVal_4460_ = lean_ctor_get(v_val_4459_, 0);
v_name_4461_ = lean_ctor_get(v_toConstantVal_4460_, 0);
lean_inc_ref(v_val_4459_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v_val_4459_);
v___x_4463_ = v___x_4407_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4469_; 
v_reuseFailAlloc_4469_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_val_4459_);
v___x_4463_ = v_reuseFailAlloc_4469_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
uint8_t v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4464_ = 2;
v___x_4465_ = lean_box(v___x_4464_);
v___x_4466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4463_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
lean_inc(v_name_4461_);
v___x_4467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4467_, 0, v_name_4461_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3816_, v_hasTrace_3876_, v___x_4410_, v___x_4427_, v___x_4010_, v_cls_4011_, v___x_4431_, v___x_4467_, v___x_4431_, v_a_3818_, v_a_3819_);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4468_;
goto v___jp_4271_;
}
}
default: 
{
lean_object* v___x_4470_; 
lean_dec_ref(v___f_4435_);
lean_del_object(v___x_4407_);
lean_inc(v_decl_3816_);
v___x_4470_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec(v_decl_3816_);
v___y_4272_ = v___x_4411_;
v___y_4273_ = v_a_4405_;
v___y_4274_ = v___x_4470_;
goto v___jp_4271_;
}
}
}
}
}
else
{
lean_object* v___x_4474_; lean_object* v___x_4475_; lean_object* v_env_4476_; lean_object* v_nextMacroScope_4477_; lean_object* v_ngen_4478_; lean_object* v_auxDeclNGen_4479_; lean_object* v_traceState_4480_; lean_object* v_recordedDeps_4481_; lean_object* v_messages_4482_; lean_object* v_infoState_4483_; lean_object* v_snapshotTasks_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4558_; 
v___x_4474_ = lean_io_get_num_heartbeats();
v___x_4475_ = lean_st_ref_take(v_a_3819_);
v_env_4476_ = lean_ctor_get(v___x_4475_, 0);
v_nextMacroScope_4477_ = lean_ctor_get(v___x_4475_, 1);
v_ngen_4478_ = lean_ctor_get(v___x_4475_, 2);
v_auxDeclNGen_4479_ = lean_ctor_get(v___x_4475_, 3);
v_traceState_4480_ = lean_ctor_get(v___x_4475_, 4);
v_recordedDeps_4481_ = lean_ctor_get(v___x_4475_, 6);
v_messages_4482_ = lean_ctor_get(v___x_4475_, 7);
v_infoState_4483_ = lean_ctor_get(v___x_4475_, 8);
v_snapshotTasks_4484_ = lean_ctor_get(v___x_4475_, 9);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4558_ == 0)
{
lean_object* v_unused_4559_; 
v_unused_4559_ = lean_ctor_get(v___x_4475_, 5);
lean_dec(v_unused_4559_);
v___x_4486_ = v___x_4475_;
v_isShared_4487_ = v_isSharedCheck_4558_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_snapshotTasks_4484_);
lean_inc(v_infoState_4483_);
lean_inc(v_messages_4482_);
lean_inc(v_recordedDeps_4481_);
lean_inc(v_traceState_4480_);
lean_inc(v_auxDeclNGen_4479_);
lean_inc(v_ngen_4478_);
lean_inc(v_nextMacroScope_4477_);
lean_inc(v_env_4476_);
lean_dec(v___x_4475_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4558_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4488_; lean_object* v___x_4489_; lean_object* v___x_4490_; lean_object* v___x_4492_; 
lean_inc(v_decl_3816_);
v___x_4488_ = l_Lean_Declaration_getNames(v_decl_3816_);
v___x_4489_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4476_, v___x_4488_);
v___x_4490_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4487_ == 0)
{
lean_ctor_set(v___x_4486_, 5, v___x_4490_);
lean_ctor_set(v___x_4486_, 0, v___x_4489_);
v___x_4492_ = v___x_4486_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4489_);
lean_ctor_set(v_reuseFailAlloc_4557_, 1, v_nextMacroScope_4477_);
lean_ctor_set(v_reuseFailAlloc_4557_, 2, v_ngen_4478_);
lean_ctor_set(v_reuseFailAlloc_4557_, 3, v_auxDeclNGen_4479_);
lean_ctor_set(v_reuseFailAlloc_4557_, 4, v_traceState_4480_);
lean_ctor_set(v_reuseFailAlloc_4557_, 5, v___x_4490_);
lean_ctor_set(v_reuseFailAlloc_4557_, 6, v_recordedDeps_4481_);
lean_ctor_set(v_reuseFailAlloc_4557_, 7, v_messages_4482_);
lean_ctor_set(v_reuseFailAlloc_4557_, 8, v_infoState_4483_);
lean_ctor_set(v_reuseFailAlloc_4557_, 9, v_snapshotTasks_4484_);
v___x_4492_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___f_4497_; 
v___x_4493_ = lean_st_ref_put(v_a_3819_, v___x_4492_);
v___x_4494_ = lean_box(0);
v___x_4495_ = lean_box(v___x_4410_);
v___x_4496_ = lean_box(v___x_4010_);
lean_inc(v_decl_3816_);
v___f_4497_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 11, 6);
lean_closure_set(v___f_4497_, 0, v_decl_3816_);
lean_closure_set(v___f_4497_, 1, v___x_4495_);
lean_closure_set(v___f_4497_, 2, v___x_4490_);
lean_closure_set(v___f_4497_, 3, v_cls_4011_);
lean_closure_set(v___f_4497_, 4, v___x_4496_);
lean_closure_set(v___f_4497_, 5, v___x_4494_);
switch(lean_obj_tag(v_decl_3816_))
{
case 2:
{
lean_object* v_val_4498_; lean_object* v___f_4499_; lean_object* v___x_4500_; 
lean_del_object(v___x_4407_);
v_val_4498_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref_n(v_val_4498_, 2);
lean_dec_ref_known(v_decl_3816_, 1);
v___f_4499_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4499_, 0, v_val_4498_);
lean_closure_set(v___f_4499_, 1, v___f_4497_);
v___x_4500_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
if (v___x_4410_ == 0)
{
lean_dec(v___x_4500_);
lean_dec_ref(v_val_4498_);
v___y_4390_ = v___f_4499_;
v___y_4391_ = v___x_4474_;
v___y_4392_ = v_a_4405_;
v___y_4393_ = v___x_4494_;
goto v___jp_4389_;
}
else
{
lean_object* v_env_4501_; lean_object* v___x_4502_; uint8_t v_isModule_4503_; 
v_env_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc_ref(v_env_4501_);
lean_dec(v___x_4500_);
v___x_4502_ = l_Lean_Environment_header(v_env_4501_);
lean_dec_ref(v_env_4501_);
v_isModule_4503_ = lean_ctor_get_uint8(v___x_4502_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4502_);
if (v_isModule_4503_ == 0)
{
lean_dec_ref(v_val_4498_);
v___y_4390_ = v___f_4499_;
v___y_4391_ = v___x_4474_;
v___y_4392_ = v_a_4405_;
v___y_4393_ = v___x_4494_;
goto v___jp_4389_;
}
else
{
if (v___x_4255_ == 0)
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_box(0);
v___x_4505_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4498_, v___f_4499_, v___x_4504_, v_a_3818_, v_a_3819_);
lean_dec_ref(v_val_4498_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4505_;
goto v___jp_4369_;
}
else
{
lean_object* v_toConstantVal_4506_; lean_object* v_name_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4513_; 
v_toConstantVal_4506_ = lean_ctor_get(v_val_4498_, 0);
v_name_4507_ = lean_ctor_get(v_toConstantVal_4506_, 0);
v___x_4508_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4507_);
v___x_4509_ = l_Lean_MessageData_ofName(v_name_4507_);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4512_, 0, v___x_4510_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
v___x_4513_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4512_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4513_) == 0)
{
lean_object* v_a_4514_; lean_object* v___x_4515_; 
v_a_4514_ = lean_ctor_get(v___x_4513_, 0);
lean_inc(v_a_4514_);
lean_dec_ref_known(v___x_4513_, 1);
v___x_4515_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4498_, v___f_4499_, v_a_4514_, v_a_3818_, v_a_3819_);
lean_dec_ref(v_val_4498_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4515_;
goto v___jp_4369_;
}
else
{
lean_dec_ref(v___f_4499_);
lean_dec_ref(v_val_4498_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4513_;
goto v___jp_4369_;
}
}
}
}
}
else
{
lean_dec(v___x_4500_);
lean_dec_ref(v_val_4498_);
v___y_4390_ = v___f_4499_;
v___y_4391_ = v___x_4474_;
v___y_4392_ = v_a_4405_;
v___y_4393_ = v___x_4494_;
goto v___jp_4389_;
}
}
case 1:
{
lean_object* v_val_4516_; lean_object* v___x_4517_; 
lean_del_object(v___x_4407_);
v_val_4516_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref(v_val_4516_);
lean_dec_ref_known(v_decl_3816_, 1);
v___x_4517_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4497_, v_forceExpose_3817_, v___x_4410_, v___x_4494_, v_cls_4011_, v_val_4516_, v_a_3818_, v_a_3819_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4517_;
goto v___jp_4369_;
}
case 5:
{
lean_object* v_defns_4518_; 
lean_del_object(v___x_4407_);
v_defns_4518_ = lean_ctor_get(v_decl_3816_, 0);
if (lean_obj_tag(v_defns_4518_) == 1)
{
lean_object* v_tail_4519_; 
v_tail_4519_ = lean_ctor_get(v_defns_4518_, 1);
if (lean_obj_tag(v_tail_4519_) == 0)
{
lean_object* v_head_4520_; lean_object* v___x_4521_; 
lean_inc_ref(v_defns_4518_);
lean_dec_ref_known(v_decl_3816_, 1);
v_head_4520_ = lean_ctor_get(v_defns_4518_, 0);
lean_inc(v_head_4520_);
lean_dec_ref_known(v_defns_4518_, 2);
v___x_4521_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4497_, v_forceExpose_3817_, v___x_4410_, v___x_4494_, v_cls_4011_, v_head_4520_, v_a_3818_, v_a_3819_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4521_;
goto v___jp_4369_;
}
else
{
lean_object* v___x_4522_; 
lean_dec_ref(v___f_4497_);
lean_inc_ref(v_decl_3816_);
v___x_4522_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec_ref_known(v_decl_3816_, 1);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4522_;
goto v___jp_4369_;
}
}
else
{
lean_object* v___x_4523_; 
lean_dec_ref(v___f_4497_);
lean_inc_ref(v_decl_3816_);
v___x_4523_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec_ref_known(v_decl_3816_, 1);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4523_;
goto v___jp_4369_;
}
}
case 3:
{
lean_object* v_val_4524_; lean_object* v___f_4525_; lean_object* v___x_4526_; lean_object* v_env_4527_; lean_object* v___x_4528_; 
lean_del_object(v___x_4407_);
v_val_4524_ = lean_ctor_get(v_decl_3816_, 0);
lean_inc_ref_n(v_val_4524_, 2);
lean_dec_ref_known(v_decl_3816_, 1);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4525_, 0, v_val_4524_);
lean_closure_set(v___f_4525_, 1, v___f_4497_);
v___x_4526_ = lean_st_ref_get(v_a_3819_);
v_env_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc_ref(v_env_4527_);
lean_dec(v___x_4526_);
v___x_4528_ = lean_st_ref_get(v_a_3819_);
if (v_forceExpose_3817_ == 0)
{
if (v___x_4410_ == 0)
{
lean_dec(v___x_4528_);
lean_dec_ref(v_env_4527_);
lean_dec_ref(v_val_4524_);
v___y_4397_ = v___x_4474_;
v___y_4398_ = v_a_4405_;
v___y_4399_ = v___f_4525_;
v___y_4400_ = v___x_4494_;
goto v___jp_4396_;
}
else
{
lean_object* v_env_4529_; lean_object* v___x_4530_; uint8_t v_isModule_4531_; 
v_env_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc_ref(v_env_4529_);
lean_dec(v___x_4528_);
v___x_4530_ = l_Lean_Environment_header(v_env_4527_);
lean_dec_ref(v_env_4527_);
v_isModule_4531_ = lean_ctor_get_uint8(v___x_4530_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4530_);
if (v_isModule_4531_ == 0)
{
lean_dec_ref(v_env_4529_);
lean_dec_ref(v_val_4524_);
v___y_4397_ = v___x_4474_;
v___y_4398_ = v_a_4405_;
v___y_4399_ = v___f_4525_;
v___y_4400_ = v___x_4494_;
goto v___jp_4396_;
}
else
{
uint8_t v_isExporting_4532_; 
v_isExporting_4532_ = lean_ctor_get_uint8(v_env_4529_, sizeof(void*)*13);
lean_dec_ref(v_env_4529_);
if (v_isExporting_4532_ == 0)
{
if (v___x_4255_ == 0)
{
lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4533_ = lean_box(0);
v___x_4534_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4524_, v___f_4525_, v___x_4533_, v_a_3818_, v_a_3819_);
lean_dec_ref(v_val_4524_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4534_;
goto v___jp_4369_;
}
else
{
lean_object* v_toConstantVal_4535_; lean_object* v_name_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; 
v_toConstantVal_4535_ = lean_ctor_get(v_val_4524_, 0);
v_name_4536_ = lean_ctor_get(v_toConstantVal_4535_, 0);
v___x_4537_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4536_);
v___x_4538_ = l_Lean_MessageData_ofName(v_name_4536_);
v___x_4539_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4539_, 0, v___x_4537_);
lean_ctor_set(v___x_4539_, 1, v___x_4538_);
v___x_4540_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4541_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4541_, 0, v___x_4539_);
lean_ctor_set(v___x_4541_, 1, v___x_4540_);
v___x_4542_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4541_, v_a_3818_, v_a_3819_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_object* v_a_4543_; lean_object* v___x_4544_; 
v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc(v_a_4543_);
lean_dec_ref_known(v___x_4542_, 1);
v___x_4544_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4524_, v___f_4525_, v_a_4543_, v_a_3818_, v_a_3819_);
lean_dec_ref(v_val_4524_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4544_;
goto v___jp_4369_;
}
else
{
lean_dec_ref(v___f_4525_);
lean_dec_ref(v_val_4524_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4542_;
goto v___jp_4369_;
}
}
}
else
{
lean_dec_ref(v_val_4524_);
v___y_4397_ = v___x_4474_;
v___y_4398_ = v_a_4405_;
v___y_4399_ = v___f_4525_;
v___y_4400_ = v___x_4494_;
goto v___jp_4396_;
}
}
}
}
else
{
lean_dec(v___x_4528_);
lean_dec_ref(v_env_4527_);
lean_dec_ref(v_val_4524_);
v___y_4397_ = v___x_4474_;
v___y_4398_ = v_a_4405_;
v___y_4399_ = v___f_4525_;
v___y_4400_ = v___x_4494_;
goto v___jp_4396_;
}
}
case 0:
{
lean_object* v_val_4545_; lean_object* v_toConstantVal_4546_; lean_object* v_name_4547_; lean_object* v___x_4549_; 
lean_dec_ref(v___f_4497_);
v_val_4545_ = lean_ctor_get(v_decl_3816_, 0);
v_toConstantVal_4546_ = lean_ctor_get(v_val_4545_, 0);
v_name_4547_ = lean_ctor_get(v_toConstantVal_4546_, 0);
lean_inc_ref(v_val_4545_);
if (v_isShared_4408_ == 0)
{
lean_ctor_set(v___x_4407_, 0, v_val_4545_);
v___x_4549_ = v___x_4407_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_val_4545_);
v___x_4549_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
uint8_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; 
v___x_4550_ = 2;
v___x_4551_ = lean_box(v___x_4550_);
v___x_4552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4549_);
lean_ctor_set(v___x_4552_, 1, v___x_4551_);
lean_inc(v_name_4547_);
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v_name_4547_);
lean_ctor_set(v___x_4553_, 1, v___x_4552_);
v___x_4554_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3816_, v___x_4410_, v___x_4490_, v_cls_4011_, v___x_4010_, v___x_4494_, v___x_4553_, v___x_4494_, v_a_3818_, v_a_3819_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4554_;
goto v___jp_4369_;
}
}
default: 
{
lean_object* v___x_4556_; 
lean_dec_ref(v___f_4497_);
lean_del_object(v___x_4407_);
lean_inc(v_decl_3816_);
v___x_4556_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3816_, v_cls_4011_, v_decl_3816_, v_a_3818_, v_a_3819_);
lean_dec(v_decl_3816_);
v___y_4370_ = v___x_4474_;
v___y_4371_ = v_a_4405_;
v___y_4372_ = v___x_4556_;
goto v___jp_4369_;
}
}
}
}
}
}
}
}
v___jp_3821_:
{
lean_object* v___x_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3832_; 
v___x_3825_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3822_, v___y_3823_);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3825_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v___x_3825_, 0);
lean_dec(v_unused_3833_);
v___x_3827_ = v___x_3825_;
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
else
{
lean_dec(v___x_3825_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3832_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3830_; 
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v_a_3824_);
v___x_3830_ = v___x_3827_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v_a_3824_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
}
v___jp_3834_:
{
lean_object* v___x_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
v___x_3838_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3835_, v___y_3836_);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3838_);
if (v_isSharedCheck_3845_ == 0)
{
lean_object* v_unused_3846_; 
v_unused_3846_ = lean_ctor_get(v___x_3838_, 0);
lean_dec(v_unused_3846_);
v___x_3840_ = v___x_3838_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_dec(v___x_3838_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
lean_ctor_set_tag(v___x_3840_, 1);
lean_ctor_set(v___x_3840_, 0, v_a_3837_);
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3837_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
v___jp_3847_:
{
lean_object* v___x_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
v___x_3851_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3849_, v___y_3848_);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3851_);
if (v_isSharedCheck_3858_ == 0)
{
lean_object* v_unused_3859_; 
v_unused_3859_ = lean_ctor_get(v___x_3851_, 0);
lean_dec(v_unused_3859_);
v___x_3853_ = v___x_3851_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_dec(v___x_3851_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
lean_ctor_set(v___x_3853_, 0, v_a_3850_);
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3850_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
v___jp_3860_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3871_; 
v___x_3864_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3862_, v___y_3861_);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3871_ == 0)
{
lean_object* v_unused_3872_; 
v_unused_3872_ = lean_ctor_get(v___x_3864_, 0);
lean_dec(v_unused_3872_);
v___x_3866_ = v___x_3864_;
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
else
{
lean_dec(v___x_3864_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3871_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
lean_ctor_set(v___x_3866_, 0, v_a_3863_);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v_a_3863_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
v___jp_3877_:
{
lean_object* v___x_3890_; 
lean_inc_ref(v___y_3886_);
v___x_3890_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3881_, v___y_3886_, v___y_3884_, v___y_3889_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v___x_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3937_; 
lean_dec_ref_known(v___x_3890_, 1);
lean_dec(v___y_3885_);
lean_inc_ref(v___y_3878_);
v___x_3891_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3878_, v___y_3887_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v___x_3891_, 0);
lean_dec(v_unused_3938_);
v___x_3893_ = v___x_3891_;
v_isShared_3894_ = v_isSharedCheck_3937_;
goto v_resetjp_3892_;
}
else
{
lean_dec(v___x_3891_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3937_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; uint8_t v___x_3897_; 
v___x_3895_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3880_);
v___x_3896_ = l_Lean_Elab_async;
v___x_3897_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3895_, v___x_3896_);
lean_dec_ref(v___x_3895_);
if (v___x_3897_ == 0)
{
lean_object* v___x_3898_; lean_object* v_r_3899_; 
lean_del_object(v___x_3893_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v___y_3879_);
v___x_3898_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3886_, v___y_3887_);
lean_dec_ref(v___x_3898_);
v_r_3899_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v___y_3880_, v___y_3887_);
if (lean_obj_tag(v_r_3899_) == 0)
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3909_; 
v_a_3900_ = lean_ctor_get(v_r_3899_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_r_3899_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3902_ = v_r_3899_;
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v_r_3899_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3909_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
lean_inc(v_a_3900_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set_tag(v___x_3902_, 1);
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; 
v___x_3906_ = lean_apply_2(v___y_3888_, v___x_3905_, lean_box(0));
if (lean_obj_tag(v___x_3906_) == 0)
{
lean_dec_ref_known(v___x_3906_, 1);
v___y_3822_ = v___y_3878_;
v___y_3823_ = v___y_3887_;
v_a_3824_ = v_a_3900_;
goto v___jp_3821_;
}
else
{
lean_object* v_a_3907_; 
lean_dec(v_a_3900_);
v_a_3907_ = lean_ctor_get(v___x_3906_, 0);
lean_inc(v_a_3907_);
lean_dec_ref_known(v___x_3906_, 1);
v___y_3835_ = v___y_3878_;
v___y_3836_ = v___y_3887_;
v_a_3837_ = v_a_3907_;
goto v___jp_3834_;
}
}
}
}
else
{
lean_object* v_a_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_a_3910_ = lean_ctor_get(v_r_3899_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v_r_3899_, 1);
v___x_3911_ = lean_box(0);
v___x_3912_ = lean_apply_2(v___y_3888_, v___x_3911_, lean_box(0));
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_dec_ref_known(v___x_3912_, 1);
v___y_3835_ = v___y_3878_;
v___y_3836_ = v___y_3887_;
v_a_3837_ = v_a_3910_;
goto v___jp_3834_;
}
else
{
lean_object* v_a_3913_; 
lean_dec(v_a_3910_);
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___y_3835_ = v___y_3878_;
v___y_3836_ = v___y_3887_;
v_a_3837_ = v_a_3913_;
goto v___jp_3834_;
}
}
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3916_; 
lean_dec_ref(v___y_3888_);
lean_dec_ref(v___y_3886_);
lean_dec_ref(v___y_3878_);
lean_dec(v_decl_3816_);
v___x_3914_ = l_IO_CancelToken_new();
if (v_isShared_3894_ == 0)
{
lean_ctor_set_tag(v___x_3893_, 1);
lean_ctor_set(v___x_3893_, 0, v___x_3914_);
v___x_3916_ = v___x_3893_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3917_ = lean_unsigned_to_nat(0u);
v___x_3918_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3919_ = l_Lean_Name_toString(v___x_3918_, v___y_3883_);
lean_inc_ref(v___x_3916_);
v___x_3920_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3879_, v___x_3916_, v___x_3919_, v___y_3880_, v___y_3887_);
if (lean_obj_tag(v___x_3920_) == 0)
{
lean_object* v_a_3921_; lean_object* v_checked_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_a_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc(v_a_3921_);
lean_dec_ref_known(v___x_3920_, 1);
v_checked_3922_ = lean_ctor_get(v___y_3882_, 2);
lean_inc_ref(v_checked_3922_);
lean_dec_ref(v___y_3882_);
v___x_3923_ = lean_io_map_task(v_a_3921_, v_checked_3922_, v___x_3917_, v_hasTrace_3876_);
v___x_3924_ = lean_box(0);
v___x_3925_ = lean_box(2);
v___x_3926_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3924_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
lean_ctor_set(v___x_3926_, 2, v___x_3916_);
lean_ctor_set(v___x_3926_, 3, v___x_3923_);
v___x_3927_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3926_, v___y_3887_);
return v___x_3927_;
}
else
{
lean_object* v_a_3928_; lean_object* v___x_3930_; uint8_t v_isShared_3931_; uint8_t v_isSharedCheck_3935_; 
lean_dec_ref(v___x_3916_);
lean_dec_ref(v___y_3882_);
v_a_3928_ = lean_ctor_get(v___x_3920_, 0);
v_isSharedCheck_3935_ = !lean_is_exclusive(v___x_3920_);
if (v_isSharedCheck_3935_ == 0)
{
v___x_3930_ = v___x_3920_;
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
else
{
lean_inc(v_a_3928_);
lean_dec(v___x_3920_);
v___x_3930_ = lean_box(0);
v_isShared_3931_ = v_isSharedCheck_3935_;
goto v_resetjp_3929_;
}
v_resetjp_3929_:
{
lean_object* v___x_3933_; 
if (v_isShared_3931_ == 0)
{
v___x_3933_ = v___x_3930_;
goto v_reusejp_3932_;
}
else
{
lean_object* v_reuseFailAlloc_3934_; 
v_reuseFailAlloc_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
v___x_3933_ = v_reuseFailAlloc_3934_;
goto v_reusejp_3932_;
}
v_reusejp_3932_:
{
return v___x_3933_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3950_; 
lean_dec_ref(v___y_3888_);
lean_dec_ref(v___y_3886_);
lean_dec_ref(v___y_3882_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v___y_3878_);
lean_dec(v_decl_3816_);
v_a_3939_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3950_ == 0)
{
v___x_3941_ = v___x_3890_;
v_isShared_3942_ = v_isSharedCheck_3950_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3890_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3950_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3943_ = lean_io_error_to_string(v_a_3939_);
v___x_3944_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
v___x_3945_ = l_Lean_MessageData_ofFormat(v___x_3944_);
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___y_3885_);
lean_ctor_set(v___x_3946_, 1, v___x_3945_);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3946_);
v___x_3948_ = v___x_3941_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
}
v___jp_3951_:
{
lean_object* v_ref_3960_; uint8_t v___x_3961_; lean_object* v___x_3962_; 
v_ref_3960_ = lean_ctor_get(v___y_3954_, 2);
v___x_3961_ = 1;
lean_inc_ref(v___y_3958_);
v___x_3962_ = l_Lean_Environment_addConstAsync(v___y_3958_, v___y_3952_, v___y_3953_, v___y_3959_, v_hasTrace_3876_, v___x_3961_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v_mainEnv_3964_; lean_object* v_asyncEnv_3965_; lean_object* v___f_3966_; lean_object* v___f_3967_; lean_object* v___x_3968_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc_n(v_a_3963_, 3);
lean_dec_ref_known(v___x_3962_, 1);
v_mainEnv_3964_ = lean_ctor_get(v_a_3963_, 0);
lean_inc_ref(v_mainEnv_3964_);
v_asyncEnv_3965_ = lean_ctor_get(v_a_3963_, 1);
lean_inc_ref_n(v_asyncEnv_3965_, 2);
lean_inc(v_ref_3960_);
lean_inc(v___y_3957_);
v___f_3966_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3966_, 0, v___y_3957_);
lean_closure_set(v___f_3966_, 1, v_a_3963_);
lean_closure_set(v___f_3966_, 2, v_ref_3960_);
lean_inc(v_decl_3816_);
v___f_3967_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3967_, 0, v_a_3963_);
lean_closure_set(v___f_3967_, 1, v_asyncEnv_3965_);
lean_closure_set(v___f_3967_, 2, v_decl_3816_);
v___x_3968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___y_3956_);
if (lean_obj_tag(v___y_3955_) == 0)
{
lean_inc(v_ref_3960_);
lean_inc_ref(v___x_3968_);
v___y_3878_ = v_mainEnv_3964_;
v___y_3879_ = v___f_3967_;
v___y_3880_ = v___y_3954_;
v___y_3881_ = v_a_3963_;
v___y_3882_ = v___y_3958_;
v___y_3883_ = v___x_3961_;
v___y_3884_ = v___x_3968_;
v___y_3885_ = v_ref_3960_;
v___y_3886_ = v_asyncEnv_3965_;
v___y_3887_ = v___y_3957_;
v___y_3888_ = v___f_3966_;
v___y_3889_ = v___x_3968_;
goto v___jp_3877_;
}
else
{
lean_inc(v_ref_3960_);
v___y_3878_ = v_mainEnv_3964_;
v___y_3879_ = v___f_3967_;
v___y_3880_ = v___y_3954_;
v___y_3881_ = v_a_3963_;
v___y_3882_ = v___y_3958_;
v___y_3883_ = v___x_3961_;
v___y_3884_ = v___x_3968_;
v___y_3885_ = v_ref_3960_;
v___y_3886_ = v_asyncEnv_3965_;
v___y_3887_ = v___y_3957_;
v___y_3888_ = v___f_3966_;
v___y_3889_ = v___y_3955_;
goto v___jp_3877_;
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___y_3958_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec(v_decl_3816_);
v_a_3969_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3971_ = v___x_3962_;
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3962_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3980_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3978_; 
v___x_3973_ = lean_io_error_to_string(v_a_3969_);
v___x_3974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3973_);
v___x_3975_ = l_Lean_MessageData_ofFormat(v___x_3974_);
lean_inc(v_ref_3960_);
v___x_3976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3976_, 0, v_ref_3960_);
lean_ctor_set(v___x_3976_, 1, v___x_3975_);
if (v_isShared_3972_ == 0)
{
lean_ctor_set(v___x_3971_, 0, v___x_3976_);
v___x_3978_ = v___x_3971_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3976_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
v___jp_3981_:
{
lean_object* v___x_3988_; 
v___x_3988_ = lean_st_ref_get(v___y_3987_);
if (lean_obj_tag(v_exportedInfo_x3f_3985_) == 0)
{
lean_object* v_env_3989_; lean_object* v___x_3990_; 
v_env_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_3989_);
lean_dec(v___x_3988_);
v___x_3990_ = lean_box(0);
v___y_3952_ = v___y_3983_;
v___y_3953_ = v___y_3982_;
v___y_3954_ = v___y_3986_;
v___y_3955_ = v_exportedInfo_x3f_3985_;
v___y_3956_ = v___y_3984_;
v___y_3957_ = v___y_3987_;
v___y_3958_ = v_env_3989_;
v___y_3959_ = v___x_3990_;
goto v___jp_3951_;
}
else
{
lean_object* v_env_3991_; lean_object* v_val_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v_env_3991_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_3991_);
lean_dec(v___x_3988_);
v_val_3992_ = lean_ctor_get(v_exportedInfo_x3f_3985_, 0);
v___x_3993_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3992_);
v___x_3994_ = lean_box(v___x_3993_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
v___y_3952_ = v___y_3983_;
v___y_3953_ = v___y_3982_;
v___y_3954_ = v___y_3986_;
v___y_3955_ = v_exportedInfo_x3f_3985_;
v___y_3956_ = v___y_3984_;
v___y_3957_ = v___y_3987_;
v___y_3958_ = v_env_3991_;
v___y_3959_ = v___x_3995_;
goto v___jp_3951_;
}
}
v___jp_3996_:
{
lean_object* v___x_4002_; 
lean_inc_ref(v___y_3999_);
v___x_4002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4002_, 0, v___y_3999_);
v___y_3982_ = v___y_3997_;
v___y_3983_ = v___y_3998_;
v___y_3984_ = v___y_3999_;
v_exportedInfo_x3f_3985_ = v___x_4002_;
v___y_3986_ = v___y_4000_;
v___y_3987_ = v___y_4001_;
goto v___jp_3981_;
}
v___jp_4003_:
{
lean_object* v___x_4009_; 
lean_inc_ref(v___y_4006_);
v___x_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4009_, 0, v___y_4006_);
v___y_3982_ = v___y_4004_;
v___y_3983_ = v___y_4005_;
v___y_3984_ = v___y_4006_;
v_exportedInfo_x3f_3985_ = v___x_4009_;
v___y_3986_ = v___y_4007_;
v___y_3987_ = v___y_4008_;
goto v___jp_3981_;
}
v___jp_4012_:
{
lean_object* v___x_4017_; uint8_t v___x_4018_; 
v___x_4017_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4018_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4015_, v_options_4014_, v___x_4017_);
if (v___x_4018_ == 0)
{
lean_object* v___x_4019_; 
v___x_4019_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v___y_4013_, v___y_4016_);
return v___x_4019_;
}
else
{
lean_object* v___x_4020_; lean_object* v___x_4021_; 
v___x_4020_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_4021_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4011_, v___x_4020_, v___y_4013_, v___y_4016_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v___x_4022_; 
lean_dec_ref_known(v___x_4021_, 1);
v___x_4022_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3816_, v___y_4013_, v___y_4016_);
return v___x_4022_;
}
else
{
lean_dec(v_decl_3816_);
return v___x_4021_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4953_, lean_object* v_forceExpose_4954_, lean_object* v_a_4955_, lean_object* v_a_4956_, lean_object* v_a_4957_){
_start:
{
uint8_t v_forceExpose_boxed_4958_; lean_object* v_res_4959_; 
v_forceExpose_boxed_4958_ = lean_unbox(v_forceExpose_4954_);
v_res_4959_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4953_, v_forceExpose_boxed_4958_, v_a_4955_, v_a_4956_);
lean_dec(v_a_4956_);
lean_dec_ref(v_a_4955_);
return v_res_4959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v___x_4964_; 
v___x_4964_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4960_, v___y_4961_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4965_, lean_object* v___y_4966_, lean_object* v___y_4967_, lean_object* v___y_4968_){
_start:
{
lean_object* v_res_4969_; 
v_res_4969_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4965_, v___y_4966_, v___y_4967_);
lean_dec(v___y_4967_);
lean_dec_ref(v___y_4966_);
lean_dec_ref(v_opt_4965_);
return v_res_4969_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4970_, lean_object* v_x_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
if (lean_obj_tag(v_x_4970_) == 0)
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = l_List_reverse___redArg(v_x_4971_);
v___x_4976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
return v___x_4976_;
}
else
{
lean_object* v_head_4977_; lean_object* v_tail_4978_; lean_object* v___x_4980_; uint8_t v_isShared_4981_; uint8_t v_isSharedCheck_4996_; 
v_head_4977_ = lean_ctor_get(v_x_4970_, 0);
v_tail_4978_ = lean_ctor_get(v_x_4970_, 1);
v_isSharedCheck_4996_ = !lean_is_exclusive(v_x_4970_);
if (v_isSharedCheck_4996_ == 0)
{
v___x_4980_ = v_x_4970_;
v_isShared_4981_ = v_isSharedCheck_4996_;
goto v_resetjp_4979_;
}
else
{
lean_inc(v_tail_4978_);
lean_inc(v_head_4977_);
lean_dec(v_x_4970_);
v___x_4980_ = lean_box(0);
v_isShared_4981_ = v_isSharedCheck_4996_;
goto v_resetjp_4979_;
}
v_resetjp_4979_:
{
lean_object* v___x_4982_; 
v___x_4982_ = l_Lean_snapshotEnvLinterOptions(v_head_4977_, v___y_4972_, v___y_4973_);
if (lean_obj_tag(v___x_4982_) == 0)
{
lean_object* v_a_4983_; lean_object* v___x_4985_; 
v_a_4983_ = lean_ctor_get(v___x_4982_, 0);
lean_inc(v_a_4983_);
lean_dec_ref_known(v___x_4982_, 1);
if (v_isShared_4981_ == 0)
{
lean_ctor_set(v___x_4980_, 1, v_x_4971_);
lean_ctor_set(v___x_4980_, 0, v_a_4983_);
v___x_4985_ = v___x_4980_;
goto v_reusejp_4984_;
}
else
{
lean_object* v_reuseFailAlloc_4987_; 
v_reuseFailAlloc_4987_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_a_4983_);
lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_x_4971_);
v___x_4985_ = v_reuseFailAlloc_4987_;
goto v_reusejp_4984_;
}
v_reusejp_4984_:
{
v_x_4970_ = v_tail_4978_;
v_x_4971_ = v___x_4985_;
goto _start;
}
}
else
{
lean_object* v_a_4988_; lean_object* v___x_4990_; uint8_t v_isShared_4991_; uint8_t v_isSharedCheck_4995_; 
lean_del_object(v___x_4980_);
lean_dec(v_tail_4978_);
lean_dec(v_x_4971_);
v_a_4988_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4990_ = v___x_4982_;
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
else
{
lean_inc(v_a_4988_);
lean_dec(v___x_4982_);
v___x_4990_ = lean_box(0);
v_isShared_4991_ = v_isSharedCheck_4995_;
goto v_resetjp_4989_;
}
v_resetjp_4989_:
{
lean_object* v___x_4993_; 
if (v_isShared_4991_ == 0)
{
v___x_4993_ = v___x_4990_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v_a_4988_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4997_, lean_object* v_x_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_, lean_object* v___y_5001_){
_start:
{
lean_object* v_res_5002_; 
v_res_5002_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4997_, v_x_4998_, v___y_4999_, v___y_5000_);
lean_dec(v___y_5000_);
lean_dec_ref(v___y_4999_);
return v_res_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_5003_, uint8_t v_forceExpose_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
lean_object* v___x_5008_; 
lean_inc(v_decl_5003_);
v___x_5008_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_5003_, v_forceExpose_5004_, v_a_5005_, v_a_5006_);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v___x_5009_; lean_object* v___x_5010_; lean_object* v___x_5011_; lean_object* v___x_5012_; 
lean_dec_ref_known(v___x_5008_, 1);
v___x_5009_ = l_Lean_Declaration_getTopLevelNames(v_decl_5003_);
v___x_5010_ = lean_box(0);
v___x_5011_ = lean_box(0);
v___x_5012_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_5009_, v___x_5010_, v_a_5005_, v_a_5006_);
if (lean_obj_tag(v___x_5012_) == 0)
{
lean_object* v___x_5014_; uint8_t v_isShared_5015_; uint8_t v_isSharedCheck_5019_; 
v_isSharedCheck_5019_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5019_ == 0)
{
lean_object* v_unused_5020_; 
v_unused_5020_ = lean_ctor_get(v___x_5012_, 0);
lean_dec(v_unused_5020_);
v___x_5014_ = v___x_5012_;
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
else
{
lean_dec(v___x_5012_);
v___x_5014_ = lean_box(0);
v_isShared_5015_ = v_isSharedCheck_5019_;
goto v_resetjp_5013_;
}
v_resetjp_5013_:
{
lean_object* v___x_5017_; 
if (v_isShared_5015_ == 0)
{
lean_ctor_set(v___x_5014_, 0, v___x_5011_);
v___x_5017_ = v___x_5014_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5018_; 
v_reuseFailAlloc_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5018_, 0, v___x_5011_);
v___x_5017_ = v_reuseFailAlloc_5018_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
return v___x_5017_;
}
}
}
else
{
lean_object* v_a_5021_; lean_object* v___x_5023_; uint8_t v_isShared_5024_; uint8_t v_isSharedCheck_5028_; 
v_a_5021_ = lean_ctor_get(v___x_5012_, 0);
v_isSharedCheck_5028_ = !lean_is_exclusive(v___x_5012_);
if (v_isSharedCheck_5028_ == 0)
{
v___x_5023_ = v___x_5012_;
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
else
{
lean_inc(v_a_5021_);
lean_dec(v___x_5012_);
v___x_5023_ = lean_box(0);
v_isShared_5024_ = v_isSharedCheck_5028_;
goto v_resetjp_5022_;
}
v_resetjp_5022_:
{
lean_object* v___x_5026_; 
if (v_isShared_5024_ == 0)
{
v___x_5026_ = v___x_5023_;
goto v_reusejp_5025_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v_a_5021_);
v___x_5026_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5025_;
}
v_reusejp_5025_:
{
return v___x_5026_;
}
}
}
}
else
{
lean_dec(v_decl_5003_);
return v___x_5008_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_5029_, lean_object* v_forceExpose_5030_, lean_object* v_a_5031_, lean_object* v_a_5032_, lean_object* v_a_5033_){
_start:
{
uint8_t v_forceExpose_boxed_5034_; lean_object* v_res_5035_; 
v_forceExpose_boxed_5034_ = lean_unbox(v_forceExpose_5030_);
v_res_5035_ = l_Lean_addDecl(v_decl_5029_, v_forceExpose_boxed_5034_, v_a_5031_, v_a_5032_);
lean_dec(v_a_5032_);
lean_dec_ref(v_a_5031_);
return v_res_5035_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_5036_, lean_object* v_b_5037_, lean_object* v___y_5038_){
_start:
{
if (lean_obj_tag(v_as_x27_5036_) == 0)
{
lean_object* v___x_5040_; 
v___x_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5040_, 0, v_b_5037_);
return v___x_5040_;
}
else
{
lean_object* v_head_5041_; lean_object* v_tail_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v_env_5045_; lean_object* v_nextMacroScope_5046_; lean_object* v_ngen_5047_; lean_object* v_auxDeclNGen_5048_; lean_object* v_traceState_5049_; lean_object* v_recordedDeps_5050_; lean_object* v_messages_5051_; lean_object* v_infoState_5052_; lean_object* v_snapshotTasks_5053_; lean_object* v___x_5055_; uint8_t v_isShared_5056_; uint8_t v_isSharedCheck_5064_; 
v_head_5041_ = lean_ctor_get(v_as_x27_5036_, 0);
v_tail_5042_ = lean_ctor_get(v_as_x27_5036_, 1);
v___x_5043_ = lean_box(0);
v___x_5044_ = lean_st_ref_take(v___y_5038_);
v_env_5045_ = lean_ctor_get(v___x_5044_, 0);
v_nextMacroScope_5046_ = lean_ctor_get(v___x_5044_, 1);
v_ngen_5047_ = lean_ctor_get(v___x_5044_, 2);
v_auxDeclNGen_5048_ = lean_ctor_get(v___x_5044_, 3);
v_traceState_5049_ = lean_ctor_get(v___x_5044_, 4);
v_recordedDeps_5050_ = lean_ctor_get(v___x_5044_, 6);
v_messages_5051_ = lean_ctor_get(v___x_5044_, 7);
v_infoState_5052_ = lean_ctor_get(v___x_5044_, 8);
v_snapshotTasks_5053_ = lean_ctor_get(v___x_5044_, 9);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5044_);
if (v_isSharedCheck_5064_ == 0)
{
lean_object* v_unused_5065_; 
v_unused_5065_ = lean_ctor_get(v___x_5044_, 5);
lean_dec(v_unused_5065_);
v___x_5055_ = v___x_5044_;
v_isShared_5056_ = v_isSharedCheck_5064_;
goto v_resetjp_5054_;
}
else
{
lean_inc(v_snapshotTasks_5053_);
lean_inc(v_infoState_5052_);
lean_inc(v_messages_5051_);
lean_inc(v_recordedDeps_5050_);
lean_inc(v_traceState_5049_);
lean_inc(v_auxDeclNGen_5048_);
lean_inc(v_ngen_5047_);
lean_inc(v_nextMacroScope_5046_);
lean_inc(v_env_5045_);
lean_dec(v___x_5044_);
v___x_5055_ = lean_box(0);
v_isShared_5056_ = v_isSharedCheck_5064_;
goto v_resetjp_5054_;
}
v_resetjp_5054_:
{
lean_object* v___x_5057_; lean_object* v___x_5058_; lean_object* v___x_5060_; 
lean_inc(v_head_5041_);
v___x_5057_ = l_Lean_markMeta(v_env_5045_, v_head_5041_);
v___x_5058_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_5056_ == 0)
{
lean_ctor_set(v___x_5055_, 5, v___x_5058_);
lean_ctor_set(v___x_5055_, 0, v___x_5057_);
v___x_5060_ = v___x_5055_;
goto v_reusejp_5059_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v___x_5057_);
lean_ctor_set(v_reuseFailAlloc_5063_, 1, v_nextMacroScope_5046_);
lean_ctor_set(v_reuseFailAlloc_5063_, 2, v_ngen_5047_);
lean_ctor_set(v_reuseFailAlloc_5063_, 3, v_auxDeclNGen_5048_);
lean_ctor_set(v_reuseFailAlloc_5063_, 4, v_traceState_5049_);
lean_ctor_set(v_reuseFailAlloc_5063_, 5, v___x_5058_);
lean_ctor_set(v_reuseFailAlloc_5063_, 6, v_recordedDeps_5050_);
lean_ctor_set(v_reuseFailAlloc_5063_, 7, v_messages_5051_);
lean_ctor_set(v_reuseFailAlloc_5063_, 8, v_infoState_5052_);
lean_ctor_set(v_reuseFailAlloc_5063_, 9, v_snapshotTasks_5053_);
v___x_5060_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5059_;
}
v_reusejp_5059_:
{
lean_object* v___x_5061_; 
v___x_5061_ = lean_st_ref_put(v___y_5038_, v___x_5060_);
v_as_x27_5036_ = v_tail_5042_;
v_b_5037_ = v___x_5043_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_5066_, lean_object* v_b_5067_, lean_object* v___y_5068_, lean_object* v___y_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5066_, v_b_5067_, v___y_5068_);
lean_dec(v___y_5068_);
lean_dec(v_as_x27_5066_);
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_5071_, uint8_t v_logCompileErrors_5072_, uint8_t v_markMeta_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_){
_start:
{
uint8_t v___x_5077_; lean_object* v___x_5078_; 
v___x_5077_ = 0;
lean_inc(v_decl_5071_);
v___x_5078_ = l_Lean_addDecl(v_decl_5071_, v___x_5077_, v_a_5074_, v_a_5075_);
if (lean_obj_tag(v___x_5078_) == 0)
{
lean_dec_ref_known(v___x_5078_, 1);
if (v_markMeta_5073_ == 0)
{
lean_object* v___x_5079_; 
v___x_5079_ = l_Lean_compileDecl(v_decl_5071_, v_logCompileErrors_5072_, v_a_5074_, v_a_5075_);
return v___x_5079_;
}
else
{
lean_object* v___x_5080_; lean_object* v___x_5081_; lean_object* v___x_5082_; lean_object* v___x_5083_; 
lean_inc(v_decl_5071_);
v___x_5080_ = l_Lean_Declaration_getNames(v_decl_5071_);
v___x_5081_ = lean_box(0);
v___x_5082_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5080_, v___x_5081_, v_a_5075_);
lean_dec(v___x_5080_);
lean_dec_ref(v___x_5082_);
v___x_5083_ = l_Lean_compileDecl(v_decl_5071_, v_logCompileErrors_5072_, v_a_5074_, v_a_5075_);
return v___x_5083_;
}
}
else
{
lean_dec(v_decl_5071_);
return v___x_5078_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5084_, lean_object* v_logCompileErrors_5085_, lean_object* v_markMeta_5086_, lean_object* v_a_5087_, lean_object* v_a_5088_, lean_object* v_a_5089_){
_start:
{
uint8_t v_logCompileErrors_boxed_5090_; uint8_t v_markMeta_boxed_5091_; lean_object* v_res_5092_; 
v_logCompileErrors_boxed_5090_ = lean_unbox(v_logCompileErrors_5085_);
v_markMeta_boxed_5091_ = lean_unbox(v_markMeta_5086_);
v_res_5092_ = l_Lean_addAndCompile(v_decl_5084_, v_logCompileErrors_boxed_5090_, v_markMeta_boxed_5091_, v_a_5087_, v_a_5088_);
lean_dec(v_a_5088_);
lean_dec_ref(v_a_5087_);
return v_res_5092_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5093_, lean_object* v_as_x27_5094_, lean_object* v_b_5095_, lean_object* v_a_5096_, lean_object* v___y_5097_, lean_object* v___y_5098_){
_start:
{
lean_object* v___x_5100_; 
v___x_5100_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5094_, v_b_5095_, v___y_5098_);
return v___x_5100_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5101_, lean_object* v_as_x27_5102_, lean_object* v_b_5103_, lean_object* v_a_5104_, lean_object* v___y_5105_, lean_object* v___y_5106_, lean_object* v___y_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5101_, v_as_x27_5102_, v_b_5103_, v_a_5104_, v___y_5105_, v___y_5106_);
lean_dec(v___y_5106_);
lean_dec_ref(v___y_5105_);
lean_dec(v_as_x27_5102_);
lean_dec(v_as_5101_);
return v_res_5108_;
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
