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
uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object* v_opts_1_, lean_object* v_opt_2_){
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
LEAN_EXPORT void l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_opts_1_ = stack[0].m_obj;
lean_object* v_opt_2_ = stack[1].m_obj;
uint8_t v_res_11_;
v_res_11_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_1_, v_opt_2_);
stack->m_num = v_res_11_;
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object* v_opts_12_, lean_object* v_opt_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_12_, v_opt_13_);
lean_dec_ref(v_opt_13_);
lean_dec_ref(v_opts_12_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(lean_object* v_opts_16_, lean_object* v_opt_17_){
_start:
{
lean_object* v_name_18_; lean_object* v_defValue_19_; lean_object* v_map_20_; lean_object* v___x_21_; 
v_name_18_ = lean_ctor_get(v_opt_17_, 0);
v_defValue_19_ = lean_ctor_get(v_opt_17_, 1);
v_map_20_ = lean_ctor_get(v_opts_16_, 0);
v___x_21_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_20_, v_name_18_);
if (lean_obj_tag(v___x_21_) == 0)
{
lean_inc(v_defValue_19_);
return v_defValue_19_;
}
else
{
lean_object* v_val_22_; 
v_val_22_ = lean_ctor_get(v___x_21_, 0);
lean_inc(v_val_22_);
lean_dec_ref_known(v___x_21_, 1);
if (lean_obj_tag(v_val_22_) == 3)
{
lean_object* v_v_23_; 
v_v_23_ = lean_ctor_get(v_val_22_, 0);
lean_inc(v_v_23_);
lean_dec_ref_known(v_val_22_, 1);
return v_v_23_;
}
else
{
lean_dec(v_val_22_);
lean_inc(v_defValue_19_);
return v_defValue_19_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1___boxed(lean_object* v_opts_24_, lean_object* v_opt_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_24_, v_opt_25_);
lean_dec_ref(v_opt_25_);
lean_dec_ref(v_opts_24_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* v_env_27_, lean_object* v_opts_28_, lean_object* v_decl_29_, lean_object* v_cancelTk_x3f_30_){
_start:
{
lean_object* v___x_31_; uint8_t v___x_32_; 
v___x_31_ = l_Lean_debug_skipKernelTC;
v___x_32_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_28_, v___x_31_);
if (v___x_32_ == 0)
{
lean_object* v___x_33_; size_t v___x_34_; lean_object* v___x_35_; lean_object* v___x_36_; size_t v___x_37_; lean_object* v___x_38_; 
v___x_33_ = l_Lean_Core_getMaxHeartbeats(v_opts_28_);
v___x_34_ = lean_usize_of_nat(v___x_33_);
lean_dec(v___x_33_);
v___x_35_ = l_Lean_maxRecDepth;
v___x_36_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_28_, v___x_35_);
v___x_37_ = lean_usize_of_nat(v___x_36_);
lean_dec(v___x_36_);
v___x_38_ = lean_add_decl(v_env_27_, v___x_34_, v___x_37_, v_decl_29_, v_cancelTk_x3f_30_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
v___x_39_ = lean_add_decl_without_checking(v_env_27_, v_decl_29_);
return v___x_39_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* v_env_40_, lean_object* v_opts_41_, lean_object* v_decl_42_, lean_object* v_cancelTk_x3f_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_Kernel_Environment_addDecl(v_env_40_, v_opts_41_, v_decl_42_, v_cancelTk_x3f_43_);
lean_dec(v_cancelTk_x3f_43_);
lean_dec(v_decl_42_);
lean_dec_ref(v_opts_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* v_env_45_, lean_object* v_opts_46_, lean_object* v_decl_47_, lean_object* v_cancelTk_x3f_48_){
_start:
{
lean_object* v___x_49_; size_t v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; size_t v___x_53_; lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_49_ = l_Lean_Core_getMaxHeartbeats(v_opts_46_);
v___x_50_ = lean_usize_of_nat(v___x_49_);
lean_dec(v___x_49_);
v___x_51_ = l_Lean_maxRecDepth;
v___x_52_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_46_, v___x_51_);
v___x_53_ = lean_usize_of_nat(v___x_52_);
lean_dec(v___x_52_);
v___x_54_ = l_Lean_debug_skipKernelTC;
v___x_55_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_46_, v___x_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; lean_object* v___x_57_; 
v___x_56_ = 1;
v___x_57_ = l_Lean_Environment_addDeclCore(v_env_45_, v___x_50_, v___x_53_, v_decl_47_, v_cancelTk_x3f_48_, v___x_56_);
return v___x_57_;
}
else
{
uint8_t v___x_58_; lean_object* v___x_59_; 
v___x_58_ = 0;
v___x_59_ = l_Lean_Environment_addDeclCore(v_env_45_, v___x_50_, v___x_53_, v_decl_47_, v_cancelTk_x3f_48_, v___x_58_);
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* v_env_60_, lean_object* v_opts_61_, lean_object* v_decl_62_, lean_object* v_cancelTk_x3f_63_){
_start:
{
lean_object* v_res_64_; 
v_res_64_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_60_, v_opts_61_, v_decl_62_, v_cancelTk_x3f_63_);
lean_dec(v_cancelTk_x3f_63_);
lean_dec(v_decl_62_);
lean_dec_ref(v_opts_61_);
return v_res_64_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object* v_a_65_, lean_object* v_as_66_, size_t v_sz_67_, size_t v_i_68_, lean_object* v_b_69_){
_start:
{
uint8_t v___x_71_; 
v___x_71_ = lean_usize_dec_lt(v_i_68_, v_sz_67_);
if (v___x_71_ == 0)
{
lean_object* v___x_72_; 
v___x_72_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_72_, 0, v_b_69_);
return v___x_72_;
}
else
{
lean_object* v_a_73_; lean_object* v_name_74_; uint8_t v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; size_t v___x_78_; size_t v___x_79_; 
v_a_73_ = lean_array_uget_borrowed(v_as_66_, v_i_68_);
v_name_74_ = lean_ctor_get(v_a_73_, 0);
v___x_75_ = l_Lean_Linter_getLinterValue(v_a_73_, v_a_65_);
v___x_76_ = lean_box(v___x_75_);
lean_inc(v_name_74_);
v___x_77_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_74_, v___x_76_, v_b_69_);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_add(v_i_68_, v___x_78_);
v_i_68_ = v___x_79_;
v_b_69_ = v___x_77_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_65_ = stack[0].m_obj;
lean_object* v_as_66_ = stack[1].m_obj;
size_t v_sz_67_ = stack[2].m_num;
size_t v_i_68_ = stack[3].m_num;
lean_object* v_b_69_ = stack[4].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_65_, v_as_66_, v_sz_67_, v_i_68_, v_b_69_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object* v_a_82_, lean_object* v_as_83_, lean_object* v_sz_84_, lean_object* v_i_85_, lean_object* v_b_86_, lean_object* v___y_87_){
_start:
{
size_t v_sz_boxed_88_; size_t v_i_boxed_89_; lean_object* v_res_90_; 
v_sz_boxed_88_ = lean_unbox_usize(v_sz_84_);
lean_dec(v_sz_84_);
v_i_boxed_89_ = lean_unbox_usize(v_i_85_);
lean_dec(v_i_85_);
v_res_90_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_82_, v_as_83_, v_sz_boxed_88_, v_i_boxed_89_, v_b_86_);
lean_dec_ref(v_as_83_);
lean_dec_ref(v_a_82_);
return v_res_90_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object* v_o_91_, lean_object* v___y_92_){
_start:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v_env_96_; lean_object* v___x_97_; lean_object* v_toEnvExtension_98_; lean_object* v_asyncMode_99_; lean_object* v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v_merged_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_111_; 
v___x_94_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_95_ = lean_st_ref_get(v___y_92_);
v_env_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc_ref(v_env_96_);
lean_dec(v___x_95_);
v___x_97_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_98_ = lean_ctor_get(v___x_97_, 0);
v_asyncMode_99_ = lean_ctor_get(v_toEnvExtension_98_, 2);
v___x_100_ = lean_box(0);
v___x_101_ = 0;
v___x_102_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_94_, v___x_97_, v_env_96_, v_asyncMode_99_, v___x_100_, v___x_101_);
v_merged_103_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_111_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_111_ == 0)
{
lean_object* v_unused_112_; 
v_unused_112_ = lean_ctor_get(v___x_102_, 1);
lean_dec(v_unused_112_);
v___x_105_ = v___x_102_;
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_merged_103_);
lean_dec(v___x_102_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_111_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_108_; 
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_merged_103_);
lean_ctor_set(v___x_105_, 0, v_o_91_);
v___x_108_ = v___x_105_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v_o_91_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v_merged_103_);
v___x_108_ = v_reuseFailAlloc_110_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; 
v___x_109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
return v___x_109_;
}
}
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_91_ = stack[0].m_obj;
lean_object* v___y_92_ = stack[1].m_obj;
lean_object* v_res_113_;
v_res_113_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_91_, v___y_92_);
stack->m_obj
 = v_res_113_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_114_, v___y_115_);
lean_dec(v___y_115_);
return v_res_117_;
}
}
lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v___x_121_; lean_object* v___x_122_; 
v___x_121_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_118_);
v___x_122_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v___x_121_, v___y_119_);
return v___x_122_;
}
}
LEAN_EXPORT void l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_118_ = stack[0].m_obj;
lean_object* v___y_119_ = stack[1].m_obj;
lean_object* v_res_123_;
v_res_123_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_118_, v___y_119_);
stack->m_obj
 = v_res_123_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_){
_start:
{
lean_object* v_res_127_; 
v_res_127_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_124_, v___y_125_);
lean_dec(v___y_125_);
lean_dec_ref(v___y_124_);
return v_res_127_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_128_; 
v___x_128_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_128_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; 
v___x_129_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_130_, 0, v___x_129_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; 
v___x_131_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_132_, 0, v___x_131_);
lean_ctor_set(v___x_132_, 1, v___x_131_);
return v___x_132_;
}
}
lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_133_, lean_object* v_a_134_, lean_object* v_a_135_){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v___x_137_ = l_Lean_Linter_envLinterOptionsRef;
v___x_138_ = lean_st_ref_get(v___x_137_);
v___x_139_ = lean_array_get_size(v___x_138_);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_nat_dec_eq(v___x_139_, v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; lean_object* v_a_143_; lean_object* v___x_144_; 
v___x_142_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_134_, v_a_135_);
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref(v___x_142_);
lean_inc(v_declName_133_);
v___x_144_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_133_, v_a_135_);
if (lean_obj_tag(v___x_144_) == 0)
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_198_; 
v_a_145_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_198_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_198_ == 0)
{
v___x_147_ = v___x_144_;
v_isShared_148_ = v_isSharedCheck_198_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_144_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_198_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
uint8_t v___x_149_; 
v___x_149_ = lean_unbox(v_a_145_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; size_t v_sz_151_; size_t v___x_152_; lean_object* v___x_153_; 
lean_del_object(v___x_147_);
v___x_150_ = lean_box(1);
v_sz_151_ = lean_array_size(v___x_138_);
v___x_152_ = ((size_t)0ULL);
v___x_153_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_143_, v___x_138_, v_sz_151_, v___x_152_, v___x_150_);
lean_dec(v___x_138_);
lean_dec(v_a_143_);
if (lean_obj_tag(v___x_153_) == 0)
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_185_; 
v_a_154_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_185_ == 0)
{
v___x_156_ = v___x_153_;
v_isShared_157_ = v_isSharedCheck_185_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_153_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_185_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_158_; lean_object* v_env_159_; lean_object* v_nextMacroScope_160_; lean_object* v_ngen_161_; lean_object* v_auxDeclNGen_162_; lean_object* v_traceState_163_; lean_object* v_recordedDeps_164_; lean_object* v_messages_165_; lean_object* v_infoState_166_; lean_object* v_snapshotTasks_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_183_; 
v___x_158_ = lean_st_ref_take(v_a_135_);
v_env_159_ = lean_ctor_get(v___x_158_, 0);
v_nextMacroScope_160_ = lean_ctor_get(v___x_158_, 1);
v_ngen_161_ = lean_ctor_get(v___x_158_, 2);
v_auxDeclNGen_162_ = lean_ctor_get(v___x_158_, 3);
v_traceState_163_ = lean_ctor_get(v___x_158_, 4);
v_recordedDeps_164_ = lean_ctor_get(v___x_158_, 6);
v_messages_165_ = lean_ctor_get(v___x_158_, 7);
v_infoState_166_ = lean_ctor_get(v___x_158_, 8);
v_snapshotTasks_167_ = lean_ctor_get(v___x_158_, 9);
v_isSharedCheck_183_ = !lean_is_exclusive(v___x_158_);
if (v_isSharedCheck_183_ == 0)
{
lean_object* v_unused_184_; 
v_unused_184_ = lean_ctor_get(v___x_158_, 5);
lean_dec(v_unused_184_);
v___x_169_ = v___x_158_;
v_isShared_170_ = v_isSharedCheck_183_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_snapshotTasks_167_);
lean_inc(v_infoState_166_);
lean_inc(v_messages_165_);
lean_inc(v_recordedDeps_164_);
lean_inc(v_traceState_163_);
lean_inc(v_auxDeclNGen_162_);
lean_inc(v_ngen_161_);
lean_inc(v_nextMacroScope_160_);
lean_inc(v_env_159_);
lean_dec(v___x_158_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_183_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v___x_171_; lean_object* v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_171_ = lean_box(0);
v___x_172_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_173_ = lean_unbox(v_a_145_);
lean_dec(v_a_145_);
v___x_174_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_172_, v_env_159_, v_declName_133_, v_a_154_, v___x_173_);
v___x_175_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 5, v___x_175_);
lean_ctor_set(v___x_169_, 0, v___x_174_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_182_; 
v_reuseFailAlloc_182_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_182_, 0, v___x_174_);
lean_ctor_set(v_reuseFailAlloc_182_, 1, v_nextMacroScope_160_);
lean_ctor_set(v_reuseFailAlloc_182_, 2, v_ngen_161_);
lean_ctor_set(v_reuseFailAlloc_182_, 3, v_auxDeclNGen_162_);
lean_ctor_set(v_reuseFailAlloc_182_, 4, v_traceState_163_);
lean_ctor_set(v_reuseFailAlloc_182_, 5, v___x_175_);
lean_ctor_set(v_reuseFailAlloc_182_, 6, v_recordedDeps_164_);
lean_ctor_set(v_reuseFailAlloc_182_, 7, v_messages_165_);
lean_ctor_set(v_reuseFailAlloc_182_, 8, v_infoState_166_);
lean_ctor_set(v_reuseFailAlloc_182_, 9, v_snapshotTasks_167_);
v___x_177_ = v_reuseFailAlloc_182_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
lean_object* v___x_178_; lean_object* v___x_180_; 
v___x_178_ = lean_st_ref_put(v_a_135_, v___x_177_);
if (v_isShared_157_ == 0)
{
lean_ctor_set(v___x_156_, 0, v___x_171_);
v___x_180_ = v___x_156_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_171_);
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
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_a_145_);
lean_dec(v_declName_133_);
v_a_186_ = lean_ctor_get(v___x_153_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_153_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_153_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v___x_194_; lean_object* v___x_196_; 
lean_dec(v_a_145_);
lean_dec(v_a_143_);
lean_dec(v___x_138_);
lean_dec(v_declName_133_);
v___x_194_ = lean_box(0);
if (v_isShared_148_ == 0)
{
lean_ctor_set(v___x_147_, 0, v___x_194_);
v___x_196_ = v___x_147_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_197_; 
v_reuseFailAlloc_197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_197_, 0, v___x_194_);
v___x_196_ = v_reuseFailAlloc_197_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
return v___x_196_;
}
}
}
}
else
{
lean_object* v_a_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_206_; 
lean_dec(v_a_143_);
lean_dec(v___x_138_);
lean_dec(v_declName_133_);
v_a_199_ = lean_ctor_get(v___x_144_, 0);
v_isSharedCheck_206_ = !lean_is_exclusive(v___x_144_);
if (v_isSharedCheck_206_ == 0)
{
v___x_201_ = v___x_144_;
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_a_199_);
lean_dec(v___x_144_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_206_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___x_204_; 
if (v_isShared_202_ == 0)
{
v___x_204_ = v___x_201_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v_a_199_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
else
{
lean_object* v___x_207_; lean_object* v___x_208_; 
lean_dec(v___x_138_);
lean_dec(v_declName_133_);
v___x_207_ = lean_box(0);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT void l_Lean_snapshotEnvLinterOptions_0interp(lean_interpreter_value* stack)
{
lean_object* v_declName_133_ = stack[0].m_obj;
lean_object* v_a_134_ = stack[1].m_obj;
lean_object* v_a_135_ = stack[2].m_obj;
lean_object* v_res_209_;
v_res_209_ = l_Lean_snapshotEnvLinterOptions(v_declName_133_, v_a_134_, v_a_135_);
stack->m_obj
 = v_res_209_;
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_snapshotEnvLinterOptions(v_declName_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
return v_res_214_;
}
}
lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_215_, v___y_217_);
return v___x_219_;
}
}
LEAN_EXPORT void l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_o_215_ = stack[0].m_obj;
lean_object* v___y_216_ = stack[1].m_obj;
lean_object* v___y_217_ = stack[2].m_obj;
lean_object* v_res_220_;
v_res_220_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_215_, v___y_216_, v___y_217_);
stack->m_obj
 = v_res_220_;
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v_res_225_; 
v_res_225_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_221_, v___y_222_, v___y_223_);
lean_dec(v___y_223_);
lean_dec_ref(v___y_222_);
return v_res_225_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_226_, lean_object* v_as_227_, size_t v_sz_228_, size_t v_i_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v___x_234_; 
v___x_234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_226_, v_as_227_, v_sz_228_, v_i_229_, v_b_230_);
return v___x_234_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_226_ = stack[0].m_obj;
lean_object* v_as_227_ = stack[1].m_obj;
size_t v_sz_228_ = stack[2].m_num;
size_t v_i_229_ = stack[3].m_num;
lean_object* v_b_230_ = stack[4].m_obj;
lean_object* v___y_231_ = stack[5].m_obj;
lean_object* v___y_232_ = stack[6].m_obj;
lean_object* v_res_235_;
v_res_235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_226_, v_as_227_, v_sz_228_, v_i_229_, v_b_230_, v___y_231_, v___y_232_);
stack->m_obj
 = v_res_235_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_236_, lean_object* v_as_237_, lean_object* v_sz_238_, lean_object* v_i_239_, lean_object* v_b_240_, lean_object* v___y_241_, lean_object* v___y_242_, lean_object* v___y_243_){
_start:
{
size_t v_sz_boxed_244_; size_t v_i_boxed_245_; lean_object* v_res_246_; 
v_sz_boxed_244_ = lean_unbox_usize(v_sz_238_);
lean_dec(v_sz_238_);
v_i_boxed_245_ = lean_unbox_usize(v_i_239_);
lean_dec(v_i_239_);
v_res_246_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_236_, v_as_237_, v_sz_boxed_244_, v_i_boxed_245_, v_b_240_, v___y_241_, v___y_242_);
lean_dec(v___y_242_);
lean_dec_ref(v___y_241_);
lean_dec_ref(v_as_237_);
lean_dec_ref(v_a_236_);
return v_res_246_;
}
}
uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 1)
{
lean_object* v_pre_248_; 
v_pre_248_ = lean_ctor_get(v_x_247_, 0);
if (lean_obj_tag(v_pre_248_) == 0)
{
uint8_t v___x_249_; 
v___x_249_ = 1;
return v___x_249_;
}
else
{
v_x_247_ = v_pre_248_;
goto _start;
}
}
else
{
uint8_t v___x_251_; 
v___x_251_ = 0;
return v___x_251_;
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_isNamespaceName_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_247_ = stack[0].m_obj;
uint8_t v_res_252_;
v_res_252_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_247_);
stack->m_num = v_res_252_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_253_){
_start:
{
uint8_t v_res_254_; lean_object* v_r_255_; 
v_res_254_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_253_);
lean_dec(v_x_253_);
v_r_255_ = lean_box(v_res_254_);
return v_r_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_256_, lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 1)
{
lean_object* v_pre_258_; uint8_t v___x_259_; 
v_pre_258_ = lean_ctor_get(v_x_257_, 0);
lean_inc(v_pre_258_);
lean_dec_ref_known(v_x_257_, 2);
v___x_259_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_258_);
if (v___x_259_ == 0)
{
lean_dec(v_pre_258_);
return v_env_256_;
}
else
{
lean_object* v___x_260_; 
lean_inc(v_pre_258_);
v___x_260_ = l_Lean_Environment_registerNamespace(v_env_256_, v_pre_258_);
v_env_256_ = v___x_260_;
v_x_257_ = v_pre_258_;
goto _start;
}
}
else
{
lean_dec(v_x_257_);
return v_env_256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_262_, lean_object* v_name_263_){
_start:
{
lean_object* v_name_264_; uint32_t v___y_266_; 
v_name_264_ = l_Lean_privateToUserName(v_name_263_);
if (lean_obj_tag(v_name_264_) == 1)
{
lean_object* v_str_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_str_270_ = lean_ctor_get(v_name_264_, 1);
v___x_271_ = lean_unsigned_to_nat(0u);
v___x_272_ = lean_string_utf8_byte_size(v_str_270_);
lean_inc_ref(v_str_270_);
v___x_273_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_273_, 0, v_str_270_);
lean_ctor_set(v___x_273_, 1, v___x_271_);
lean_ctor_set(v___x_273_, 2, v___x_272_);
v___x_274_ = l_String_Slice_Pos_get_x3f(v___x_273_, v___x_271_);
lean_dec_ref_known(v___x_273_, 3);
if (lean_obj_tag(v___x_274_) == 0)
{
uint32_t v___x_275_; 
v___x_275_ = 65;
v___y_266_ = v___x_275_;
goto v___jp_265_;
}
else
{
lean_object* v_val_276_; uint32_t v___x_277_; 
v_val_276_ = lean_ctor_get(v___x_274_, 0);
lean_inc(v_val_276_);
lean_dec_ref_known(v___x_274_, 1);
v___x_277_ = lean_unbox_uint32(v_val_276_);
lean_dec(v_val_276_);
v___y_266_ = v___x_277_;
goto v___jp_265_;
}
}
else
{
lean_dec(v_name_264_);
return v_env_262_;
}
v___jp_265_:
{
uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 95;
v___x_268_ = lean_uint32_dec_eq(v___y_266_, v___x_267_);
if (v___x_268_ == 0)
{
lean_object* v___x_269_; 
v___x_269_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_262_, v_name_264_);
return v___x_269_;
}
else
{
lean_dec(v_name_264_);
return v_env_262_;
}
}
}
}
lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_278_, lean_object* v_decl_279_, lean_object* v_ref_280_){
_start:
{
lean_object* v_defValue_282_; lean_object* v_descr_283_; lean_object* v_deprecation_x3f_284_; lean_object* v___x_285_; uint8_t v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_defValue_282_ = lean_ctor_get(v_decl_279_, 0);
v_descr_283_ = lean_ctor_get(v_decl_279_, 1);
v_deprecation_x3f_284_ = lean_ctor_get(v_decl_279_, 2);
v___x_285_ = lean_alloc_ctor(1, 0, 1);
v___x_286_ = lean_unbox(v_defValue_282_);
lean_ctor_set_uint8(v___x_285_, 0, v___x_286_);
lean_inc(v_deprecation_x3f_284_);
lean_inc_ref(v_descr_283_);
lean_inc_n(v_name_278_, 2);
v___x_287_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_287_, 0, v_name_278_);
lean_ctor_set(v___x_287_, 1, v_ref_280_);
lean_ctor_set(v___x_287_, 2, v___x_285_);
lean_ctor_set(v___x_287_, 3, v_descr_283_);
lean_ctor_set(v___x_287_, 4, v_deprecation_x3f_284_);
v___x_288_ = lean_register_option(v_name_278_, v___x_287_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_296_; 
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_296_ == 0)
{
lean_object* v_unused_297_; 
v_unused_297_ = lean_ctor_get(v___x_288_, 0);
lean_dec(v_unused_297_);
v___x_290_ = v___x_288_;
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
else
{
lean_dec(v___x_288_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_296_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_292_; lean_object* v___x_294_; 
lean_inc(v_defValue_282_);
v___x_292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_292_, 0, v_name_278_);
lean_ctor_set(v___x_292_, 1, v_defValue_282_);
if (v_isShared_291_ == 0)
{
lean_ctor_set(v___x_290_, 0, v___x_292_);
v___x_294_ = v___x_290_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_292_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
else
{
lean_object* v_a_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_305_; 
lean_dec(v_name_278_);
v_a_298_ = lean_ctor_get(v___x_288_, 0);
v_isSharedCheck_305_ = !lean_is_exclusive(v___x_288_);
if (v_isSharedCheck_305_ == 0)
{
v___x_300_ = v___x_288_;
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_a_298_);
lean_dec(v___x_288_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_305_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_303_; 
if (v_isShared_301_ == 0)
{
v___x_303_ = v___x_300_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_a_298_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_278_ = stack[0].m_obj;
lean_object* v_decl_279_ = stack[1].m_obj;
lean_object* v_ref_280_ = stack[2].m_obj;
lean_object* v_res_306_;
v_res_306_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_278_, v_decl_279_, v_ref_280_);
stack->m_obj
 = v_res_306_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_307_, lean_object* v_decl_308_, lean_object* v_ref_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_307_, v_decl_308_, v_ref_309_);
lean_dec_ref(v_decl_308_);
return v_res_311_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_329_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_330_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_331_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_332_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_329_, v___x_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_333_;
v_res_333_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
stack->m_obj
 = v_res_333_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_335_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v___x_342_; lean_object* v_env_343_; uint8_t v___x_344_; lean_object* v_env_345_; lean_object* v___x_346_; lean_object* v_toCold_347_; lean_object* v_mctx_348_; lean_object* v_lctx_349_; lean_object* v_options_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_342_ = lean_st_ref_get(v___y_340_);
v_env_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc_ref(v_env_343_);
lean_dec(v___x_342_);
v___x_344_ = 0;
v_env_345_ = l_Lean_Environment_setRecordingDeps(v_env_343_, v___x_344_);
v___x_346_ = lean_st_ref_get(v___y_338_);
v_toCold_347_ = lean_ctor_get(v___y_339_, 0);
v_mctx_348_ = lean_ctor_get(v___x_346_, 0);
lean_inc_ref(v_mctx_348_);
lean_dec(v___x_346_);
v_lctx_349_ = lean_ctor_get(v___y_337_, 2);
v_options_350_ = lean_ctor_get(v_toCold_347_, 2);
lean_inc_ref(v_options_350_);
lean_inc_ref(v_lctx_349_);
v___x_351_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_351_, 0, v_env_345_);
lean_ctor_set(v___x_351_, 1, v_mctx_348_);
lean_ctor_set(v___x_351_, 2, v_lctx_349_);
lean_ctor_set(v___x_351_, 3, v_options_350_);
v___x_352_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v_msgData_336_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_336_ = stack[0].m_obj;
lean_object* v___y_337_ = stack[1].m_obj;
lean_object* v___y_338_ = stack[2].m_obj;
lean_object* v___y_339_ = stack[3].m_obj;
lean_object* v___y_340_ = stack[4].m_obj;
lean_object* v_res_354_;
v_res_354_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
stack->m_obj
 = v_res_354_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v_res_361_; 
v_res_361_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
return v_res_361_;
}
}
lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_){
_start:
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v_a_371_; lean_object* v___x_373_; uint8_t v_isShared_374_; uint8_t v_isSharedCheck_385_; 
lean_inc_ref(v_s_362_);
v___x_369_ = l_Lean_MessageData_ofExpr(v_s_362_);
v___x_370_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_369_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
v_a_371_ = lean_ctor_get(v___x_370_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v___x_370_);
if (v_isSharedCheck_385_ == 0)
{
v___x_373_ = v___x_370_;
v_isShared_374_ = v_isSharedCheck_385_;
goto v_resetjp_372_;
}
else
{
lean_inc(v_a_371_);
lean_dec(v___x_370_);
v___x_373_ = lean_box(0);
v_isShared_374_ = v_isSharedCheck_385_;
goto v_resetjp_372_;
}
v_resetjp_372_:
{
lean_object* v___x_375_; lean_object* v___x_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_375_ = lean_st_ref_take(v___y_363_);
v___x_376_ = lean_box(0);
v___x_377_ = l_Lean_Expr_isSyntheticSorry(v_s_362_);
lean_dec_ref(v_s_362_);
v___x_378_ = lean_box(v___x_377_);
v___x_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_379_, 0, v___x_378_);
lean_ctor_set(v___x_379_, 1, v_a_371_);
v___x_380_ = lean_array_push(v___x_375_, v___x_379_);
v___x_381_ = lean_st_ref_put(v___y_363_, v___x_380_);
if (v_isShared_374_ == 0)
{
lean_ctor_set(v___x_373_, 0, v___x_376_);
v___x_383_ = v___x_373_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_376_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
LEAN_EXPORT void l_Lean_warnIfUsesSorry___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_362_ = stack[0].m_obj;
lean_object* v___y_363_ = stack[1].m_obj;
lean_object* v___y_364_ = stack[2].m_obj;
lean_object* v___y_365_ = stack[3].m_obj;
lean_object* v___y_366_ = stack[4].m_obj;
lean_object* v___y_367_ = stack[5].m_obj;
lean_object* v_res_386_;
v_res_386_ = l_Lean_warnIfUsesSorry___lam__0(v_s_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_);
stack->m_obj
 = v_res_386_;
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l_Lean_warnIfUsesSorry___lam__0(v_s_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
lean_dec(v___y_390_);
lean_dec_ref(v___y_389_);
lean_dec(v___y_388_);
return v_res_394_;
}
}
uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v_suppressElabErrors_403_, uint8_t v___y_404_, lean_object* v_x_405_){
_start:
{
if (lean_obj_tag(v_x_405_) == 1)
{
lean_object* v_pre_406_; 
v_pre_406_ = lean_ctor_get(v_x_405_, 0);
switch(lean_obj_tag(v_pre_406_))
{
case 1:
{
lean_object* v_pre_407_; 
v_pre_407_ = lean_ctor_get(v_pre_406_, 0);
switch(lean_obj_tag(v_pre_407_))
{
case 0:
{
lean_object* v_str_408_; lean_object* v_str_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v_str_408_ = lean_ctor_get(v_x_405_, 1);
v_str_409_ = lean_ctor_get(v_pre_406_, 1);
v___x_410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_411_ = lean_string_dec_eq(v_str_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; uint8_t v___x_413_; 
v___x_412_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_413_ = lean_string_dec_eq(v_str_409_, v___x_412_);
if (v___x_413_ == 0)
{
return v___x_413_;
}
else
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_415_ = lean_string_dec_eq(v_str_408_, v___x_414_);
if (v___x_415_ == 0)
{
return v___x_415_;
}
else
{
return v_suppressElabErrors_403_;
}
}
}
else
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_417_ = lean_string_dec_eq(v_str_408_, v___x_416_);
if (v___x_417_ == 0)
{
return v___x_417_;
}
else
{
return v_suppressElabErrors_403_;
}
}
}
case 1:
{
lean_object* v_pre_418_; 
v_pre_418_ = lean_ctor_get(v_pre_407_, 0);
if (lean_obj_tag(v_pre_418_) == 0)
{
lean_object* v_str_419_; lean_object* v_str_420_; lean_object* v_str_421_; lean_object* v___x_422_; uint8_t v___x_423_; 
v_str_419_ = lean_ctor_get(v_x_405_, 1);
v_str_420_ = lean_ctor_get(v_pre_406_, 1);
v_str_421_ = lean_ctor_get(v_pre_407_, 1);
v___x_422_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_423_ = lean_string_dec_eq(v_str_421_, v___x_422_);
if (v___x_423_ == 0)
{
return v___x_423_;
}
else
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_425_ = lean_string_dec_eq(v_str_420_, v___x_424_);
if (v___x_425_ == 0)
{
return v___x_425_;
}
else
{
lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_426_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_427_ = lean_string_dec_eq(v_str_419_, v___x_426_);
if (v___x_427_ == 0)
{
return v___x_427_;
}
else
{
return v_suppressElabErrors_403_;
}
}
}
}
else
{
return v___y_404_;
}
}
default: 
{
return v___y_404_;
}
}
}
case 0:
{
lean_object* v_str_428_; lean_object* v___x_429_; uint8_t v___x_430_; 
v_str_428_ = lean_ctor_get(v_x_405_, 1);
v___x_429_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_430_ = lean_string_dec_eq(v_str_428_, v___x_429_);
if (v___x_430_ == 0)
{
return v___x_430_;
}
else
{
return v_suppressElabErrors_403_;
}
}
default: 
{
return v___y_404_;
}
}
}
else
{
return v___y_404_;
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_suppressElabErrors_403_ = stack[0].m_num;
uint8_t v___y_404_ = stack[1].m_num;
lean_object* v_x_405_ = stack[2].m_obj;
uint8_t v_res_431_;
v_res_431_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_403_, v___y_404_, v_x_405_);
stack->m_num = v_res_431_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_suppressElabErrors_432_, lean_object* v___y_433_, lean_object* v_x_434_){
_start:
{
uint8_t v_suppressElabErrors_boxed_435_; uint8_t v___y_15129__boxed_436_; uint8_t v_res_437_; lean_object* v_r_438_; 
v_suppressElabErrors_boxed_435_ = lean_unbox(v_suppressElabErrors_432_);
v___y_15129__boxed_436_ = lean_unbox(v___y_433_);
v_res_437_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_435_, v___y_15129__boxed_436_, v_x_434_);
lean_dec(v_x_434_);
v_r_438_ = lean_box(v_res_437_);
return v_r_438_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_439_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
return v___x_440_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; 
v___x_441_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_442_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_443_ = lean_unsigned_to_nat(0u);
v___x_444_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_444_, 0, v___x_443_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
lean_ctor_set(v___x_444_, 2, v___x_443_);
lean_ctor_set(v___x_444_, 3, v___x_443_);
lean_ctor_set(v___x_444_, 4, v___x_442_);
lean_ctor_set(v___x_444_, 5, v___x_442_);
lean_ctor_set(v___x_444_, 6, v___x_442_);
lean_ctor_set(v___x_444_, 7, v___x_442_);
lean_ctor_set(v___x_444_, 8, v___x_442_);
lean_ctor_set(v___x_444_, 9, v___x_442_);
lean_ctor_set(v___x_444_, 10, v___x_442_);
lean_ctor_set(v___x_444_, 11, v___x_441_);
return v___x_444_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; 
v___x_445_ = lean_unsigned_to_nat(32u);
v___x_446_ = lean_mk_empty_array_with_capacity(v___x_445_);
v___x_447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
return v___x_447_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_448_ = ((size_t)5ULL);
v___x_449_ = lean_unsigned_to_nat(0u);
v___x_450_ = lean_unsigned_to_nat(32u);
v___x_451_ = lean_mk_empty_array_with_capacity(v___x_450_);
v___x_452_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_453_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_453_, 0, v___x_452_);
lean_ctor_set(v___x_453_, 1, v___x_451_);
lean_ctor_set(v___x_453_, 2, v___x_449_);
lean_ctor_set(v___x_453_, 3, v___x_449_);
lean_ctor_set_usize(v___x_453_, 4, v___x_448_);
return v___x_453_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_454_ = lean_box(1);
v___x_455_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_456_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_457_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_457_, 0, v___x_456_);
lean_ctor_set(v___x_457_, 1, v___x_455_);
lean_ctor_set(v___x_457_, 2, v___x_454_);
return v___x_457_;
}
}
lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v___x_462_; lean_object* v_toCold_463_; lean_object* v_env_464_; lean_object* v_options_465_; uint8_t v___x_466_; lean_object* v_env_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_462_ = lean_st_ref_get(v___y_460_);
v_toCold_463_ = lean_ctor_get(v___y_459_, 0);
v_env_464_ = lean_ctor_get(v___x_462_, 0);
lean_inc_ref(v_env_464_);
lean_dec(v___x_462_);
v_options_465_ = lean_ctor_get(v_toCold_463_, 2);
v___x_466_ = 0;
v_env_467_ = l_Lean_Environment_setRecordingDeps(v_env_464_, v___x_466_);
v___x_468_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_469_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
lean_inc_ref(v_options_465_);
v___x_470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_470_, 0, v_env_467_);
lean_ctor_set(v___x_470_, 1, v___x_468_);
lean_ctor_set(v___x_470_, 2, v___x_469_);
lean_ctor_set(v___x_470_, 3, v_options_465_);
v___x_471_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_msgData_458_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_458_ = stack[0].m_obj;
lean_object* v___y_459_ = stack[1].m_obj;
lean_object* v___y_460_ = stack[2].m_obj;
lean_object* v_res_473_;
v_res_473_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_458_, v___y_459_, v___y_460_);
stack->m_obj
 = v_res_473_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_474_, v___y_475_, v___y_476_);
lean_dec(v___y_476_);
lean_dec_ref(v___y_475_);
return v_res_478_;
}
}
lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_480_, lean_object* v_msgData_481_, uint8_t v_severity_482_, uint8_t v_isSilent_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
uint8_t v___y_488_; uint8_t v___y_489_; lean_object* v___y_490_; lean_object* v___y_491_; lean_object* v___y_492_; lean_object* v___y_493_; lean_object* v___y_494_; lean_object* v_toCold_495_; lean_object* v___y_496_; lean_object* v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; uint8_t v___y_556_; lean_object* v___y_557_; lean_object* v___y_558_; uint8_t v___y_562_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___x_575_; uint8_t v___y_577_; uint8_t v___y_578_; uint8_t v___y_579_; uint8_t v___y_581_; uint8_t v___x_589_; 
v___x_575_ = 2;
v___x_589_ = l_Lean_instBEqMessageSeverity_beq(v_severity_482_, v___x_575_);
if (v___x_589_ == 0)
{
v___y_581_ = v___x_589_;
goto v___jp_580_;
}
else
{
uint8_t v___x_590_; 
lean_inc_ref(v_msgData_481_);
v___x_590_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_481_);
v___y_581_ = v___x_590_;
goto v___jp_580_;
}
v___jp_487_:
{
lean_object* v_currNamespace_497_; lean_object* v_openDecls_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; lean_object* v_env_503_; lean_object* v_nextMacroScope_504_; lean_object* v_ngen_505_; lean_object* v_auxDeclNGen_506_; lean_object* v_traceState_507_; lean_object* v_cache_508_; lean_object* v_recordedDeps_509_; lean_object* v_messages_510_; lean_object* v_infoState_511_; lean_object* v_snapshotTasks_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_523_; 
v_currNamespace_497_ = lean_ctor_get(v_toCold_495_, 4);
v_openDecls_498_ = lean_ctor_get(v_toCold_495_, 5);
lean_inc(v_openDecls_498_);
lean_inc(v_currNamespace_497_);
v___x_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_499_, 0, v_currNamespace_497_);
lean_ctor_set(v___x_499_, 1, v_openDecls_498_);
v___x_500_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
lean_ctor_set(v___x_500_, 1, v___y_490_);
lean_inc_ref(v___y_494_);
lean_inc_ref(v___y_492_);
v___x_501_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_501_, 0, v___y_492_);
lean_ctor_set(v___x_501_, 1, v___y_493_);
lean_ctor_set(v___x_501_, 2, v___y_491_);
lean_ctor_set(v___x_501_, 3, v___y_494_);
lean_ctor_set(v___x_501_, 4, v___x_500_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5, v___y_489_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5 + 1, v___y_488_);
lean_ctor_set_uint8(v___x_501_, sizeof(void*)*5 + 2, v_isSilent_483_);
v___x_502_ = lean_st_ref_take(v___y_496_);
v_env_503_ = lean_ctor_get(v___x_502_, 0);
v_nextMacroScope_504_ = lean_ctor_get(v___x_502_, 1);
v_ngen_505_ = lean_ctor_get(v___x_502_, 2);
v_auxDeclNGen_506_ = lean_ctor_get(v___x_502_, 3);
v_traceState_507_ = lean_ctor_get(v___x_502_, 4);
v_cache_508_ = lean_ctor_get(v___x_502_, 5);
v_recordedDeps_509_ = lean_ctor_get(v___x_502_, 6);
v_messages_510_ = lean_ctor_get(v___x_502_, 7);
v_infoState_511_ = lean_ctor_get(v___x_502_, 8);
v_snapshotTasks_512_ = lean_ctor_get(v___x_502_, 9);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_523_ == 0)
{
v___x_514_ = v___x_502_;
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snapshotTasks_512_);
lean_inc(v_infoState_511_);
lean_inc(v_messages_510_);
lean_inc(v_recordedDeps_509_);
lean_inc(v_cache_508_);
lean_inc(v_traceState_507_);
lean_inc(v_auxDeclNGen_506_);
lean_inc(v_ngen_505_);
lean_inc(v_nextMacroScope_504_);
lean_inc(v_env_503_);
lean_dec(v___x_502_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_523_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_519_; 
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_MessageLog_add(v___x_501_, v_messages_510_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 7, v___x_517_);
v___x_519_ = v___x_514_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_env_503_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_nextMacroScope_504_);
lean_ctor_set(v_reuseFailAlloc_522_, 2, v_ngen_505_);
lean_ctor_set(v_reuseFailAlloc_522_, 3, v_auxDeclNGen_506_);
lean_ctor_set(v_reuseFailAlloc_522_, 4, v_traceState_507_);
lean_ctor_set(v_reuseFailAlloc_522_, 5, v_cache_508_);
lean_ctor_set(v_reuseFailAlloc_522_, 6, v_recordedDeps_509_);
lean_ctor_set(v_reuseFailAlloc_522_, 7, v___x_517_);
lean_ctor_set(v_reuseFailAlloc_522_, 8, v_infoState_511_);
lean_ctor_set(v_reuseFailAlloc_522_, 9, v_snapshotTasks_512_);
v___x_519_ = v_reuseFailAlloc_522_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = lean_st_ref_put(v___y_496_, v___x_519_);
v___x_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_516_);
return v___x_521_;
}
}
}
v___jp_524_:
{
lean_object* v_fileName_533_; lean_object* v_fileMap_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v_a_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_550_; 
v_fileName_533_ = lean_ctor_get(v___y_531_, 0);
v_fileMap_534_ = lean_ctor_get(v___y_531_, 1);
v___x_535_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_481_);
v___x_536_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_535_, v___y_484_, v___y_485_);
v_a_537_ = lean_ctor_get(v___x_536_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v___x_536_);
if (v_isSharedCheck_550_ == 0)
{
v___x_539_ = v___x_536_;
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_a_537_);
lean_dec(v___x_536_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_550_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
lean_inc_ref_n(v_fileMap_534_, 2);
v___x_541_ = l_Lean_FileMap_toPosition(v_fileMap_534_, v___y_528_);
lean_dec(v___y_528_);
v___x_542_ = l_Lean_FileMap_toPosition(v_fileMap_534_, v___y_532_);
lean_dec(v___y_532_);
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v___x_542_);
v___x_544_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_527_ == 0)
{
lean_del_object(v___x_539_);
lean_dec_ref(v___y_525_);
v___y_488_ = v___y_530_;
v___y_489_ = v___y_529_;
v___y_490_ = v_a_537_;
v___y_491_ = v___x_543_;
v___y_492_ = v_fileName_533_;
v___y_493_ = v___x_541_;
v___y_494_ = v___x_544_;
v_toCold_495_ = v___y_526_;
v___y_496_ = v___y_485_;
goto v___jp_487_;
}
else
{
uint8_t v___x_545_; 
lean_inc(v_a_537_);
v___x_545_ = l_Lean_MessageData_hasTag(v___y_525_, v_a_537_);
if (v___x_545_ == 0)
{
lean_object* v___x_546_; lean_object* v___x_548_; 
lean_dec_ref_known(v___x_543_, 1);
lean_dec_ref(v___x_541_);
lean_dec(v_a_537_);
v___x_546_ = lean_box(0);
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_546_);
v___x_548_ = v___x_539_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
return v___x_548_;
}
}
else
{
lean_del_object(v___x_539_);
v___y_488_ = v___y_530_;
v___y_489_ = v___y_529_;
v___y_490_ = v_a_537_;
v___y_491_ = v___x_543_;
v___y_492_ = v_fileName_533_;
v___y_493_ = v___x_541_;
v___y_494_ = v___x_544_;
v_toCold_495_ = v___y_526_;
v___y_496_ = v___y_485_;
goto v___jp_487_;
}
}
}
}
v___jp_551_:
{
lean_object* v___x_559_; 
v___x_559_ = l_Lean_Syntax_getTailPos_x3f(v___y_557_, v___y_556_);
lean_dec(v___y_557_);
if (lean_obj_tag(v___x_559_) == 0)
{
lean_inc(v___y_558_);
v___y_525_ = v___y_553_;
v___y_526_ = v___y_554_;
v___y_527_ = v___y_552_;
v___y_528_ = v___y_558_;
v___y_529_ = v___y_556_;
v___y_530_ = v___y_555_;
v___y_531_ = v___y_554_;
v___y_532_ = v___y_558_;
goto v___jp_524_;
}
else
{
lean_object* v_val_560_; 
v_val_560_ = lean_ctor_get(v___x_559_, 0);
lean_inc(v_val_560_);
lean_dec_ref_known(v___x_559_, 1);
v___y_525_ = v___y_553_;
v___y_526_ = v___y_554_;
v___y_527_ = v___y_552_;
v___y_528_ = v___y_558_;
v___y_529_ = v___y_556_;
v___y_530_ = v___y_555_;
v___y_531_ = v___y_554_;
v___y_532_ = v_val_560_;
goto v___jp_524_;
}
}
v___jp_561_:
{
lean_object* v_toCold_565_; lean_object* v_ref_566_; uint8_t v_suppressElabErrors_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___f_570_; lean_object* v_ref_571_; lean_object* v___x_572_; 
v_toCold_565_ = lean_ctor_get(v___y_484_, 0);
v_ref_566_ = lean_ctor_get(v___y_484_, 2);
v_suppressElabErrors_567_ = lean_ctor_get_uint8(v___y_484_, sizeof(void*)*3 + 2);
v___x_568_ = lean_box(v_suppressElabErrors_567_);
v___x_569_ = lean_box(v___y_562_);
v___f_570_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_570_, 0, v___x_568_);
lean_closure_set(v___f_570_, 1, v___x_569_);
v_ref_571_ = l_Lean_replaceRef(v_ref_480_, v_ref_566_);
v___x_572_ = l_Lean_Syntax_getPos_x3f(v_ref_571_, v___y_563_);
if (lean_obj_tag(v___x_572_) == 0)
{
lean_object* v___x_573_; 
v___x_573_ = lean_unsigned_to_nat(0u);
v___y_552_ = v_suppressElabErrors_567_;
v___y_553_ = v___f_570_;
v___y_554_ = v_toCold_565_;
v___y_555_ = v___y_564_;
v___y_556_ = v___y_563_;
v___y_557_ = v_ref_571_;
v___y_558_ = v___x_573_;
goto v___jp_551_;
}
else
{
lean_object* v_val_574_; 
v_val_574_ = lean_ctor_get(v___x_572_, 0);
lean_inc(v_val_574_);
lean_dec_ref_known(v___x_572_, 1);
v___y_552_ = v_suppressElabErrors_567_;
v___y_553_ = v___f_570_;
v___y_554_ = v_toCold_565_;
v___y_555_ = v___y_564_;
v___y_556_ = v___y_563_;
v___y_557_ = v_ref_571_;
v___y_558_ = v_val_574_;
goto v___jp_551_;
}
}
v___jp_576_:
{
if (v___y_579_ == 0)
{
v___y_562_ = v___y_577_;
v___y_563_ = v___y_578_;
v___y_564_ = v_severity_482_;
goto v___jp_561_;
}
else
{
v___y_562_ = v___y_577_;
v___y_563_ = v___y_578_;
v___y_564_ = v___x_575_;
goto v___jp_561_;
}
}
v___jp_580_:
{
if (v___y_581_ == 0)
{
uint8_t v___x_582_; uint8_t v___x_583_; 
v___x_582_ = 1;
v___x_583_ = l_Lean_instBEqMessageSeverity_beq(v_severity_482_, v___x_582_);
if (v___x_583_ == 0)
{
v___y_577_ = v___y_581_;
v___y_578_ = v___y_581_;
v___y_579_ = v___x_583_;
goto v___jp_576_;
}
else
{
lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_584_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_484_);
v___x_585_ = l_Lean_warningAsError;
v___x_586_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_584_, v___x_585_);
lean_dec_ref(v___x_584_);
v___y_577_ = v___y_581_;
v___y_578_ = v___y_581_;
v___y_579_ = v___x_586_;
goto v___jp_576_;
}
}
else
{
lean_object* v___x_587_; lean_object* v___x_588_; 
lean_dec_ref(v_msgData_481_);
v___x_587_ = lean_box(0);
v___x_588_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_588_, 0, v___x_587_);
return v___x_588_;
}
}
}
}
LEAN_EXPORT void l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_ref_480_ = stack[0].m_obj;
lean_object* v_msgData_481_ = stack[1].m_obj;
uint8_t v_severity_482_ = stack[2].m_num;
uint8_t v_isSilent_483_ = stack[3].m_num;
lean_object* v___y_484_ = stack[4].m_obj;
lean_object* v___y_485_ = stack[5].m_obj;
lean_object* v_res_591_;
v_res_591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_480_, v_msgData_481_, v_severity_482_, v_isSilent_483_, v___y_484_, v___y_485_);
stack->m_obj
 = v_res_591_;
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_592_, lean_object* v_msgData_593_, lean_object* v_severity_594_, lean_object* v_isSilent_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
uint8_t v_severity_boxed_599_; uint8_t v_isSilent_boxed_600_; lean_object* v_res_601_; 
v_severity_boxed_599_ = lean_unbox(v_severity_594_);
v_isSilent_boxed_600_ = lean_unbox(v_isSilent_595_);
v_res_601_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_592_, v_msgData_593_, v_severity_boxed_599_, v_isSilent_boxed_600_, v___y_596_, v___y_597_);
lean_dec(v___y_597_);
lean_dec_ref(v___y_596_);
lean_dec(v_ref_592_);
return v_res_601_;
}
}
lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_602_, uint8_t v_severity_603_, uint8_t v_isSilent_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
lean_object* v_ref_608_; lean_object* v___x_609_; 
v_ref_608_ = lean_ctor_get(v___y_605_, 2);
v___x_609_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_608_, v_msgData_602_, v_severity_603_, v_isSilent_604_, v___y_605_, v___y_606_);
return v___x_609_;
}
}
LEAN_EXPORT void l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_602_ = stack[0].m_obj;
uint8_t v_severity_603_ = stack[1].m_num;
uint8_t v_isSilent_604_ = stack[2].m_num;
lean_object* v___y_605_ = stack[3].m_obj;
lean_object* v___y_606_ = stack[4].m_obj;
lean_object* v_res_610_;
v_res_610_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_602_, v_severity_603_, v_isSilent_604_, v___y_605_, v___y_606_);
stack->m_obj
 = v_res_610_;
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_611_, lean_object* v_severity_612_, lean_object* v_isSilent_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v_severity_boxed_617_; uint8_t v_isSilent_boxed_618_; lean_object* v_res_619_; 
v_severity_boxed_617_ = lean_unbox(v_severity_612_);
v_isSilent_boxed_618_ = lean_unbox(v_isSilent_613_);
v_res_619_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_611_, v_severity_boxed_617_, v_isSilent_boxed_618_, v___y_614_, v___y_615_);
lean_dec(v___y_615_);
lean_dec_ref(v___y_614_);
return v_res_619_;
}
}
lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_620_, lean_object* v___y_621_, lean_object* v___y_622_){
_start:
{
uint8_t v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; 
v___x_624_ = 1;
v___x_625_ = 0;
v___x_626_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_620_, v___x_624_, v___x_625_, v___y_621_, v___y_622_);
return v___x_626_;
}
}
LEAN_EXPORT void l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_620_ = stack[0].m_obj;
lean_object* v___y_621_ = stack[1].m_obj;
lean_object* v___y_622_ = stack[2].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_620_, v___y_621_, v___y_622_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
return v_res_632_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_636_, size_t v_sz_637_, size_t v_i_638_, lean_object* v_b_639_){
_start:
{
uint8_t v___x_640_; 
v___x_640_ = lean_usize_dec_lt(v_i_638_, v_sz_637_);
if (v___x_640_ == 0)
{
lean_inc_ref(v_b_639_);
return v_b_639_;
}
else
{
lean_object* v_a_641_; lean_object* v_fst_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_a_641_ = lean_array_uget_borrowed(v_as_636_, v_i_638_);
v_fst_642_ = lean_ctor_get(v_a_641_, 0);
v___x_643_ = lean_box(0);
v___x_644_ = lean_unbox(v_fst_642_);
if (v___x_644_ == 0)
{
lean_object* v___x_645_; size_t v___x_646_; size_t v___x_647_; 
v___x_645_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_646_ = ((size_t)1ULL);
v___x_647_ = lean_usize_add(v_i_638_, v___x_646_);
v_i_638_ = v___x_647_;
v_b_639_ = v___x_645_;
goto _start;
}
else
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; 
lean_inc(v_a_641_);
v___x_649_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_649_, 0, v_a_641_);
v___x_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_650_, 0, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v___x_643_);
return v___x_651_;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_636_ = stack[0].m_obj;
size_t v_sz_637_ = stack[1].m_num;
size_t v_i_638_ = stack[2].m_num;
lean_object* v_b_639_ = stack[3].m_obj;
lean_object* v_res_652_;
v_res_652_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_636_, v_sz_637_, v_i_638_, v_b_639_);
stack->m_obj
 = v_res_652_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_653_, lean_object* v_sz_654_, lean_object* v_i_655_, lean_object* v_b_656_){
_start:
{
size_t v_sz_boxed_657_; size_t v_i_boxed_658_; lean_object* v_res_659_; 
v_sz_boxed_657_ = lean_unbox_usize(v_sz_654_);
lean_dec(v_sz_654_);
v_i_boxed_658_ = lean_unbox_usize(v_i_655_);
lean_dec(v_i_655_);
v_res_659_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_653_, v_sz_boxed_657_, v_i_boxed_658_, v_b_656_);
lean_dec_ref(v_b_656_);
lean_dec_ref(v_as_653_);
return v_res_659_;
}
}
lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_660_, lean_object* v_e_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_, lean_object* v___y_666_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Expr_getSorry_x3f(v_e_661_);
if (lean_obj_tag(v___x_668_) == 1)
{
lean_object* v_val_669_; lean_object* v___x_670_; 
v_val_669_ = lean_ctor_get(v___x_668_, 0);
lean_inc(v_val_669_);
lean_dec_ref_known(v___x_668_, 1);
lean_inc(v___y_666_);
lean_inc_ref(v___y_665_);
lean_inc(v___y_664_);
lean_inc_ref(v___y_663_);
lean_inc(v___y_662_);
v___x_670_ = lean_apply_7(v_fn_660_, v_val_669_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_, lean_box(0));
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_679_; 
v_isSharedCheck_679_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_679_ == 0)
{
lean_object* v_unused_680_; 
v_unused_680_ = lean_ctor_get(v___x_670_, 0);
lean_dec(v_unused_680_);
v___x_672_ = v___x_670_;
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
else
{
lean_dec(v___x_670_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_679_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_674_ = 0;
v___x_675_ = lean_box(v___x_674_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_675_);
v___x_677_ = v___x_672_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
v___x_677_ = v_reuseFailAlloc_678_;
goto v_reusejp_676_;
}
v_reusejp_676_:
{
return v___x_677_;
}
}
}
else
{
lean_object* v_a_681_; lean_object* v___x_683_; uint8_t v_isShared_684_; uint8_t v_isSharedCheck_688_; 
v_a_681_ = lean_ctor_get(v___x_670_, 0);
v_isSharedCheck_688_ = !lean_is_exclusive(v___x_670_);
if (v_isSharedCheck_688_ == 0)
{
v___x_683_ = v___x_670_;
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
else
{
lean_inc(v_a_681_);
lean_dec(v___x_670_);
v___x_683_ = lean_box(0);
v_isShared_684_ = v_isSharedCheck_688_;
goto v_resetjp_682_;
}
v_resetjp_682_:
{
lean_object* v___x_686_; 
if (v_isShared_684_ == 0)
{
v___x_686_ = v___x_683_;
goto v_reusejp_685_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_a_681_);
v___x_686_ = v_reuseFailAlloc_687_;
goto v_reusejp_685_;
}
v_reusejp_685_:
{
return v___x_686_;
}
}
}
}
else
{
uint8_t v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
lean_dec(v___x_668_);
lean_dec_ref(v_fn_660_);
v___x_689_ = 1;
v___x_690_ = lean_box(v___x_689_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_660_ = stack[0].m_obj;
lean_object* v_e_661_ = stack[1].m_obj;
lean_object* v___y_662_ = stack[2].m_obj;
lean_object* v___y_663_ = stack[3].m_obj;
lean_object* v___y_664_ = stack[4].m_obj;
lean_object* v___y_665_ = stack[5].m_obj;
lean_object* v___y_666_ = stack[6].m_obj;
lean_object* v_res_692_;
v_res_692_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_660_, v_e_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_, v___y_666_);
stack->m_obj
 = v_res_692_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_693_, lean_object* v_e_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_693_, v_e_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_);
lean_dec(v___y_699_);
lean_dec_ref(v___y_698_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v_e_694_);
return v_res_701_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_702_, lean_object* v_x_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_){
_start:
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = lean_apply_1(v_x_703_, lean_box(0));
v___x_711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
return v___x_711_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_703_ = stack[1].m_obj;
lean_object* v___y_704_ = stack[2].m_obj;
lean_object* v___y_705_ = stack[3].m_obj;
lean_object* v___y_706_ = stack[4].m_obj;
lean_object* v___y_707_ = stack[5].m_obj;
lean_object* v___y_708_ = stack[6].m_obj;
lean_object* v_res_712_;
v_res_712_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v_x_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
stack->m_obj
 = v_res_712_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_713_, lean_object* v_x_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_713_, v_x_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
return v_res_721_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___x_731_; 
lean_inc(v___y_729_);
lean_inc_ref(v___y_728_);
lean_inc(v___y_727_);
lean_inc_ref(v___y_726_);
lean_inc(v___y_724_);
lean_inc(v___y_723_);
v___x_731_ = lean_apply_8(v_k_722_, v_b_725_, v___y_723_, v___y_724_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, lean_box(0));
return v___x_731_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_722_ = stack[0].m_obj;
lean_object* v___y_723_ = stack[1].m_obj;
lean_object* v___y_724_ = stack[2].m_obj;
lean_object* v_b_725_ = stack[3].m_obj;
lean_object* v___y_726_ = stack[4].m_obj;
lean_object* v___y_727_ = stack[5].m_obj;
lean_object* v___y_728_ = stack[6].m_obj;
lean_object* v___y_729_ = stack[7].m_obj;
lean_object* v_res_732_;
v_res_732_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_722_, v___y_723_, v___y_724_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
stack->m_obj
 = v_res_732_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v_b_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_){
_start:
{
lean_object* v_res_742_; 
v_res_742_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_733_, v___y_734_, v___y_735_, v_b_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec_ref(v___y_737_);
lean_dec(v___y_735_);
lean_dec(v___y_734_);
return v_res_742_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_743_, lean_object* v_type_744_, lean_object* v_val_745_, lean_object* v_k_746_, uint8_t v_nondep_747_, uint8_t v_kind_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___f_756_; lean_object* v___x_757_; 
lean_inc(v___y_750_);
lean_inc(v___y_749_);
v___f_756_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_756_, 0, v_k_746_);
lean_closure_set(v___f_756_, 1, v___y_749_);
lean_closure_set(v___f_756_, 2, v___y_750_);
v___x_757_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_743_, v_type_744_, v_val_745_, v___f_756_, v_nondep_747_, v_kind_748_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
if (lean_obj_tag(v___x_757_) == 0)
{
return v___x_757_;
}
else
{
lean_object* v_a_758_; lean_object* v___x_760_; uint8_t v_isShared_761_; uint8_t v_isSharedCheck_765_; 
v_a_758_ = lean_ctor_get(v___x_757_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_757_);
if (v_isSharedCheck_765_ == 0)
{
v___x_760_ = v___x_757_;
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
else
{
lean_inc(v_a_758_);
lean_dec(v___x_757_);
v___x_760_ = lean_box(0);
v_isShared_761_ = v_isSharedCheck_765_;
goto v_resetjp_759_;
}
v_resetjp_759_:
{
lean_object* v___x_763_; 
if (v_isShared_761_ == 0)
{
v___x_763_ = v___x_760_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_a_758_);
v___x_763_ = v_reuseFailAlloc_764_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_743_ = stack[0].m_obj;
lean_object* v_type_744_ = stack[1].m_obj;
lean_object* v_val_745_ = stack[2].m_obj;
lean_object* v_k_746_ = stack[3].m_obj;
uint8_t v_nondep_747_ = stack[4].m_num;
uint8_t v_kind_748_ = stack[5].m_num;
lean_object* v___y_749_ = stack[6].m_obj;
lean_object* v___y_750_ = stack[7].m_obj;
lean_object* v___y_751_ = stack[8].m_obj;
lean_object* v___y_752_ = stack[9].m_obj;
lean_object* v___y_753_ = stack[10].m_obj;
lean_object* v___y_754_ = stack[11].m_obj;
lean_object* v_res_766_;
v_res_766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_743_, v_type_744_, v_val_745_, v_k_746_, v_nondep_747_, v_kind_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
stack->m_obj
 = v_res_766_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_767_, lean_object* v_type_768_, lean_object* v_val_769_, lean_object* v_k_770_, lean_object* v_nondep_771_, lean_object* v_kind_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
uint8_t v_nondep_boxed_780_; uint8_t v_kind_boxed_781_; lean_object* v_res_782_; 
v_nondep_boxed_780_ = lean_unbox(v_nondep_771_);
v_kind_boxed_781_ = lean_unbox(v_kind_772_);
v_res_782_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_767_, v_type_768_, v_val_769_, v_k_770_, v_nondep_boxed_780_, v_kind_boxed_781_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec(v___y_773_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_783_, lean_object* v_f_784_, lean_object* v_body_785_, lean_object* v_x_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_783_, v_f_784_, v_body_785_, v_x_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
lean_dec(v___y_792_);
lean_dec_ref(v___y_791_);
lean_dec(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___y_788_);
lean_dec(v___y_787_);
return v_res_794_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_795_, lean_object* v_fvars_796_, lean_object* v_a_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_){
_start:
{
if (lean_obj_tag(v_a_797_) == 8)
{
lean_object* v_declName_805_; lean_object* v_type_806_; lean_object* v_value_807_; lean_object* v_body_808_; lean_object* v___f_809_; lean_object* v_d_810_; lean_object* v_v_811_; lean_object* v___x_812_; 
v_declName_805_ = lean_ctor_get(v_a_797_, 0);
lean_inc(v_declName_805_);
v_type_806_ = lean_ctor_get(v_a_797_, 1);
lean_inc_ref(v_type_806_);
v_value_807_ = lean_ctor_get(v_a_797_, 2);
lean_inc_ref(v_value_807_);
v_body_808_ = lean_ctor_get(v_a_797_, 3);
lean_inc_ref(v_body_808_);
lean_dec_ref_known(v_a_797_, 4);
lean_inc_ref_n(v_f_795_, 2);
lean_inc_ref(v_fvars_796_);
v___f_809_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_809_, 0, v_fvars_796_);
lean_closure_set(v___f_809_, 1, v_f_795_);
lean_closure_set(v___f_809_, 2, v_body_808_);
v_d_810_ = lean_expr_instantiate_rev(v_type_806_, v_fvars_796_);
lean_dec_ref(v_type_806_);
v_v_811_ = lean_expr_instantiate_rev(v_value_807_, v_fvars_796_);
lean_dec_ref(v_fvars_796_);
lean_dec_ref(v_value_807_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v_d_810_);
v___x_812_ = lean_apply_8(v_f_795_, v_d_810_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, lean_box(0));
if (lean_obj_tag(v___x_812_) == 0)
{
lean_object* v___x_813_; 
lean_dec_ref_known(v___x_812_, 1);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc(v___y_798_);
lean_inc_ref(v_v_811_);
v___x_813_ = lean_apply_8(v_f_795_, v_v_811_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, lean_box(0));
if (lean_obj_tag(v___x_813_) == 0)
{
uint8_t v___x_814_; uint8_t v___x_815_; lean_object* v___x_816_; 
lean_dec_ref_known(v___x_813_, 1);
v___x_814_ = 0;
v___x_815_ = 0;
v___x_816_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_805_, v_d_810_, v_v_811_, v___f_809_, v___x_814_, v___x_815_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
return v___x_816_;
}
else
{
lean_dec_ref(v_v_811_);
lean_dec_ref(v_d_810_);
lean_dec_ref(v___f_809_);
lean_dec(v_declName_805_);
return v___x_813_;
}
}
else
{
lean_dec_ref(v_v_811_);
lean_dec_ref(v_d_810_);
lean_dec_ref(v___f_809_);
lean_dec(v_declName_805_);
lean_dec_ref(v_f_795_);
return v___x_812_;
}
}
else
{
lean_object* v___x_817_; lean_object* v___x_818_; 
v___x_817_ = lean_expr_instantiate_rev(v_a_797_, v_fvars_796_);
lean_dec_ref(v_fvars_796_);
lean_dec_ref(v_a_797_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v___y_799_);
lean_inc(v___y_798_);
v___x_818_ = lean_apply_8(v_f_795_, v___x_817_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, lean_box(0));
return v___x_818_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_795_ = stack[0].m_obj;
lean_object* v_fvars_796_ = stack[1].m_obj;
lean_object* v_a_797_ = stack[2].m_obj;
lean_object* v___y_798_ = stack[3].m_obj;
lean_object* v___y_799_ = stack[4].m_obj;
lean_object* v___y_800_ = stack[5].m_obj;
lean_object* v___y_801_ = stack[6].m_obj;
lean_object* v___y_802_ = stack[7].m_obj;
lean_object* v___y_803_ = stack[8].m_obj;
lean_object* v_res_819_;
v_res_819_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_795_, v_fvars_796_, v_a_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
stack->m_obj
 = v_res_819_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_820_, lean_object* v_f_821_, lean_object* v_body_822_, lean_object* v_x_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_array_push(v_fvars_820_, v_x_823_);
v___x_832_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_821_, v___x_831_, v_body_822_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
return v___x_832_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_820_ = stack[0].m_obj;
lean_object* v_f_821_ = stack[1].m_obj;
lean_object* v_body_822_ = stack[2].m_obj;
lean_object* v_x_823_ = stack[3].m_obj;
lean_object* v___y_824_ = stack[4].m_obj;
lean_object* v___y_825_ = stack[5].m_obj;
lean_object* v___y_826_ = stack[6].m_obj;
lean_object* v___y_827_ = stack[7].m_obj;
lean_object* v___y_828_ = stack[8].m_obj;
lean_object* v___y_829_ = stack[9].m_obj;
lean_object* v_res_833_;
v_res_833_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_820_, v_f_821_, v_body_822_, v_x_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_833_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_834_, lean_object* v_fvars_835_, lean_object* v_a_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_){
_start:
{
lean_object* v_res_844_; 
v_res_844_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_834_, v_fvars_835_, v_a_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
return v_res_844_;
}
}
lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_847_, lean_object* v_e_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_){
_start:
{
lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_856_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_857_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_847_, v___x_856_, v_e_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
return v___x_857_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_847_ = stack[0].m_obj;
lean_object* v_e_848_ = stack[1].m_obj;
lean_object* v___y_849_ = stack[2].m_obj;
lean_object* v___y_850_ = stack[3].m_obj;
lean_object* v___y_851_ = stack[4].m_obj;
lean_object* v___y_852_ = stack[5].m_obj;
lean_object* v___y_853_ = stack[6].m_obj;
lean_object* v___y_854_ = stack[7].m_obj;
lean_object* v_res_858_;
v_res_858_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_847_, v_e_848_, v___y_849_, v___y_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
stack->m_obj
 = v_res_858_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_859_, lean_object* v_e_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_859_, v_e_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
return v_res_868_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_869_, uint8_t v_bi_870_, lean_object* v_type_871_, lean_object* v_k_872_, uint8_t v_kind_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
lean_object* v___f_881_; lean_object* v___x_882_; 
lean_inc(v___y_875_);
lean_inc(v___y_874_);
v___f_881_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_881_, 0, v_k_872_);
lean_closure_set(v___f_881_, 1, v___y_874_);
lean_closure_set(v___f_881_, 2, v___y_875_);
v___x_882_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_869_, v_bi_870_, v_type_871_, v___f_881_, v_kind_873_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
if (lean_obj_tag(v___x_882_) == 0)
{
return v___x_882_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_882_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_882_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_869_ = stack[0].m_obj;
uint8_t v_bi_870_ = stack[1].m_num;
lean_object* v_type_871_ = stack[2].m_obj;
lean_object* v_k_872_ = stack[3].m_obj;
uint8_t v_kind_873_ = stack[4].m_num;
lean_object* v___y_874_ = stack[5].m_obj;
lean_object* v___y_875_ = stack[6].m_obj;
lean_object* v___y_876_ = stack[7].m_obj;
lean_object* v___y_877_ = stack[8].m_obj;
lean_object* v___y_878_ = stack[9].m_obj;
lean_object* v___y_879_ = stack[10].m_obj;
lean_object* v_res_891_;
v_res_891_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_869_, v_bi_870_, v_type_871_, v_k_872_, v_kind_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
stack->m_obj
 = v_res_891_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_892_, lean_object* v_bi_893_, lean_object* v_type_894_, lean_object* v_k_895_, lean_object* v_kind_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_){
_start:
{
uint8_t v_bi_boxed_904_; uint8_t v_kind_boxed_905_; lean_object* v_res_906_; 
v_bi_boxed_904_ = lean_unbox(v_bi_893_);
v_kind_boxed_905_ = lean_unbox(v_kind_896_);
v_res_906_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_892_, v_bi_boxed_904_, v_type_894_, v_k_895_, v_kind_boxed_905_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_);
lean_dec(v___y_902_);
lean_dec_ref(v___y_901_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec(v___y_897_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_907_, lean_object* v_f_908_, lean_object* v_body_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_907_, v_f_908_, v_body_909_, v_x_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec(v___y_911_);
return v_res_918_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_919_, lean_object* v_fvars_920_, lean_object* v_a_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_){
_start:
{
if (lean_obj_tag(v_a_921_) == 7)
{
lean_object* v_binderName_929_; lean_object* v_binderType_930_; lean_object* v_body_931_; uint8_t v_binderInfo_932_; lean_object* v___f_933_; lean_object* v_d_934_; lean_object* v___x_935_; 
v_binderName_929_ = lean_ctor_get(v_a_921_, 0);
lean_inc(v_binderName_929_);
v_binderType_930_ = lean_ctor_get(v_a_921_, 1);
lean_inc_ref(v_binderType_930_);
v_body_931_ = lean_ctor_get(v_a_921_, 2);
lean_inc_ref(v_body_931_);
v_binderInfo_932_ = lean_ctor_get_uint8(v_a_921_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_921_, 3);
lean_inc_ref(v_f_919_);
lean_inc_ref(v_fvars_920_);
v___f_933_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_933_, 0, v_fvars_920_);
lean_closure_set(v___f_933_, 1, v_f_919_);
lean_closure_set(v___f_933_, 2, v_body_931_);
v_d_934_ = lean_expr_instantiate_rev(v_binderType_930_, v_fvars_920_);
lean_dec_ref(v_fvars_920_);
lean_dec_ref(v_binderType_930_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc(v___y_922_);
lean_inc_ref(v_d_934_);
v___x_935_ = lean_apply_8(v_f_919_, v_d_934_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
if (lean_obj_tag(v___x_935_) == 0)
{
uint8_t v___x_936_; lean_object* v___x_937_; 
lean_dec_ref_known(v___x_935_, 1);
v___x_936_ = 0;
v___x_937_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_929_, v_binderInfo_932_, v_d_934_, v___f_933_, v___x_936_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
return v___x_937_;
}
else
{
lean_dec_ref(v_d_934_);
lean_dec_ref(v___f_933_);
lean_dec(v_binderName_929_);
return v___x_935_;
}
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; 
v___x_938_ = lean_expr_instantiate_rev(v_a_921_, v_fvars_920_);
lean_dec_ref(v_fvars_920_);
lean_dec_ref(v_a_921_);
lean_inc(v___y_927_);
lean_inc_ref(v___y_926_);
lean_inc(v___y_925_);
lean_inc_ref(v___y_924_);
lean_inc(v___y_923_);
lean_inc(v___y_922_);
v___x_939_ = lean_apply_8(v_f_919_, v___x_938_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, lean_box(0));
return v___x_939_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_919_ = stack[0].m_obj;
lean_object* v_fvars_920_ = stack[1].m_obj;
lean_object* v_a_921_ = stack[2].m_obj;
lean_object* v___y_922_ = stack[3].m_obj;
lean_object* v___y_923_ = stack[4].m_obj;
lean_object* v___y_924_ = stack[5].m_obj;
lean_object* v___y_925_ = stack[6].m_obj;
lean_object* v___y_926_ = stack[7].m_obj;
lean_object* v___y_927_ = stack[8].m_obj;
lean_object* v_res_940_;
v_res_940_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_919_, v_fvars_920_, v_a_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_);
stack->m_obj
 = v_res_940_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_941_, lean_object* v_f_942_, lean_object* v_body_943_, lean_object* v_x_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v___x_952_; lean_object* v___x_953_; 
v___x_952_ = lean_array_push(v_fvars_941_, v_x_944_);
v___x_953_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_942_, v___x_952_, v_body_943_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
return v___x_953_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_941_ = stack[0].m_obj;
lean_object* v_f_942_ = stack[1].m_obj;
lean_object* v_body_943_ = stack[2].m_obj;
lean_object* v_x_944_ = stack[3].m_obj;
lean_object* v___y_945_ = stack[4].m_obj;
lean_object* v___y_946_ = stack[5].m_obj;
lean_object* v___y_947_ = stack[6].m_obj;
lean_object* v___y_948_ = stack[7].m_obj;
lean_object* v___y_949_ = stack[8].m_obj;
lean_object* v___y_950_ = stack[9].m_obj;
lean_object* v_res_954_;
v_res_954_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_941_, v_f_942_, v_body_943_, v_x_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_);
stack->m_obj
 = v_res_954_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_955_, lean_object* v_fvars_956_, lean_object* v_a_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_955_, v_fvars_956_, v_a_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_);
lean_dec(v___y_963_);
lean_dec_ref(v___y_962_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec(v___y_958_);
return v_res_965_;
}
}
lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_966_, lean_object* v_e_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_){
_start:
{
lean_object* v___x_975_; lean_object* v___x_976_; 
v___x_975_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_976_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_966_, v___x_975_, v_e_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
return v___x_976_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_966_ = stack[0].m_obj;
lean_object* v_e_967_ = stack[1].m_obj;
lean_object* v___y_968_ = stack[2].m_obj;
lean_object* v___y_969_ = stack[3].m_obj;
lean_object* v___y_970_ = stack[4].m_obj;
lean_object* v___y_971_ = stack[5].m_obj;
lean_object* v___y_972_ = stack[6].m_obj;
lean_object* v___y_973_ = stack[7].m_obj;
lean_object* v_res_977_;
v_res_977_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_966_, v_e_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
stack->m_obj
 = v_res_977_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_978_, lean_object* v_e_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_){
_start:
{
lean_object* v_res_987_; 
v_res_987_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_978_, v_e_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_, v___y_985_);
lean_dec(v___y_985_);
lean_dec_ref(v___y_984_);
lean_dec(v___y_983_);
lean_dec_ref(v___y_982_);
lean_dec(v___y_981_);
lean_dec(v___y_980_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_988_, lean_object* v_f_989_, lean_object* v_body_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_988_, v_f_989_, v_body_990_, v_x_991_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
lean_dec(v___y_993_);
lean_dec(v___y_992_);
return v_res_999_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_1000_, lean_object* v_fvars_1001_, lean_object* v_a_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
if (lean_obj_tag(v_a_1002_) == 6)
{
lean_object* v_binderName_1010_; lean_object* v_binderType_1011_; lean_object* v_body_1012_; uint8_t v_binderInfo_1013_; lean_object* v___f_1014_; lean_object* v_d_1015_; lean_object* v___x_1016_; 
v_binderName_1010_ = lean_ctor_get(v_a_1002_, 0);
lean_inc(v_binderName_1010_);
v_binderType_1011_ = lean_ctor_get(v_a_1002_, 1);
lean_inc_ref(v_binderType_1011_);
v_body_1012_ = lean_ctor_get(v_a_1002_, 2);
lean_inc_ref(v_body_1012_);
v_binderInfo_1013_ = lean_ctor_get_uint8(v_a_1002_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_1002_, 3);
lean_inc_ref(v_f_1000_);
lean_inc_ref(v_fvars_1001_);
v___f_1014_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_1014_, 0, v_fvars_1001_);
lean_closure_set(v___f_1014_, 1, v_f_1000_);
lean_closure_set(v___f_1014_, 2, v_body_1012_);
v_d_1015_ = lean_expr_instantiate_rev(v_binderType_1011_, v_fvars_1001_);
lean_dec_ref(v_fvars_1001_);
lean_dec_ref(v_binderType_1011_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
lean_inc_ref(v_d_1015_);
v___x_1016_ = lean_apply_8(v_f_1000_, v_d_1015_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
if (lean_obj_tag(v___x_1016_) == 0)
{
uint8_t v___x_1017_; lean_object* v___x_1018_; 
lean_dec_ref_known(v___x_1016_, 1);
v___x_1017_ = 0;
v___x_1018_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_1010_, v_binderInfo_1013_, v_d_1015_, v___f_1014_, v___x_1017_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
return v___x_1018_;
}
else
{
lean_dec_ref(v_d_1015_);
lean_dec_ref(v___f_1014_);
lean_dec(v_binderName_1010_);
return v___x_1016_;
}
}
else
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_expr_instantiate_rev(v_a_1002_, v_fvars_1001_);
lean_dec_ref(v_fvars_1001_);
lean_dec_ref(v_a_1002_);
lean_inc(v___y_1008_);
lean_inc_ref(v___y_1007_);
lean_inc(v___y_1006_);
lean_inc_ref(v___y_1005_);
lean_inc(v___y_1004_);
lean_inc(v___y_1003_);
v___x_1020_ = lean_apply_8(v_f_1000_, v___x_1019_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, lean_box(0));
return v___x_1020_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1000_ = stack[0].m_obj;
lean_object* v_fvars_1001_ = stack[1].m_obj;
lean_object* v_a_1002_ = stack[2].m_obj;
lean_object* v___y_1003_ = stack[3].m_obj;
lean_object* v___y_1004_ = stack[4].m_obj;
lean_object* v___y_1005_ = stack[5].m_obj;
lean_object* v___y_1006_ = stack[6].m_obj;
lean_object* v___y_1007_ = stack[7].m_obj;
lean_object* v___y_1008_ = stack[8].m_obj;
lean_object* v_res_1021_;
v_res_1021_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1000_, v_fvars_1001_, v_a_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
stack->m_obj
 = v_res_1021_;
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_1022_, lean_object* v_f_1023_, lean_object* v_body_1024_, lean_object* v_x_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = lean_array_push(v_fvars_1022_, v_x_1025_);
v___x_1034_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1023_, v___x_1033_, v_body_1024_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
return v___x_1034_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvars_1022_ = stack[0].m_obj;
lean_object* v_f_1023_ = stack[1].m_obj;
lean_object* v_body_1024_ = stack[2].m_obj;
lean_object* v_x_1025_ = stack[3].m_obj;
lean_object* v___y_1026_ = stack[4].m_obj;
lean_object* v___y_1027_ = stack[5].m_obj;
lean_object* v___y_1028_ = stack[6].m_obj;
lean_object* v___y_1029_ = stack[7].m_obj;
lean_object* v___y_1030_ = stack[8].m_obj;
lean_object* v___y_1031_ = stack[9].m_obj;
lean_object* v_res_1035_;
v_res_1035_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_1022_, v_f_1023_, v_body_1024_, v_x_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
stack->m_obj
 = v_res_1035_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1036_, lean_object* v_fvars_1037_, lean_object* v_a_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1036_, v_fvars_1037_, v_a_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
return v_res_1046_;
}
}
lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1047_, lean_object* v_e_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_, lean_object* v___y_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1057_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1047_, v___x_1056_, v_e_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
return v___x_1057_;
}
}
LEAN_EXPORT void l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_0interp(lean_interpreter_value* stack)
{
lean_object* v_f_1047_ = stack[0].m_obj;
lean_object* v_e_1048_ = stack[1].m_obj;
lean_object* v___y_1049_ = stack[2].m_obj;
lean_object* v___y_1050_ = stack[3].m_obj;
lean_object* v___y_1051_ = stack[4].m_obj;
lean_object* v___y_1052_ = stack[5].m_obj;
lean_object* v___y_1053_ = stack[6].m_obj;
lean_object* v___y_1054_ = stack[7].m_obj;
lean_object* v_res_1058_;
v_res_1058_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1047_, v_e_1048_, v___y_1049_, v___y_1050_, v___y_1051_, v___y_1052_, v___y_1053_, v___y_1054_);
stack->m_obj
 = v_res_1058_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1059_, lean_object* v_e_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1059_, v_e_1060_, v___y_1061_, v___y_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec(v___y_1064_);
lean_dec_ref(v___y_1063_);
lean_dec(v___y_1062_);
lean_dec(v___y_1061_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1069_, lean_object* v_x_1070_){
_start:
{
if (lean_obj_tag(v_x_1070_) == 0)
{
lean_object* v___x_1071_; 
v___x_1071_ = lean_box(0);
return v___x_1071_;
}
else
{
lean_object* v_key_1072_; lean_object* v_value_1073_; lean_object* v_tail_1074_; uint8_t v___x_1075_; 
v_key_1072_ = lean_ctor_get(v_x_1070_, 0);
v_value_1073_ = lean_ctor_get(v_x_1070_, 1);
v_tail_1074_ = lean_ctor_get(v_x_1070_, 2);
v___x_1075_ = lean_expr_eqv(v_key_1072_, v_a_1069_);
if (v___x_1075_ == 0)
{
v_x_1070_ = v_tail_1074_;
goto _start;
}
else
{
lean_object* v___x_1077_; 
lean_inc(v_value_1073_);
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v_value_1073_);
return v___x_1077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1078_, lean_object* v_x_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1078_, v_x_1079_);
lean_dec(v_x_1079_);
lean_dec_ref(v_a_1078_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1081_, lean_object* v_a_1082_){
_start:
{
lean_object* v_buckets_1083_; lean_object* v___x_1084_; uint64_t v___x_1085_; uint64_t v___x_1086_; uint64_t v___x_1087_; uint64_t v_fold_1088_; uint64_t v___x_1089_; uint64_t v___x_1090_; uint64_t v___x_1091_; size_t v___x_1092_; size_t v___x_1093_; size_t v___x_1094_; size_t v___x_1095_; size_t v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; 
v_buckets_1083_ = lean_ctor_get(v_m_1081_, 1);
v___x_1084_ = lean_array_get_size(v_buckets_1083_);
v___x_1085_ = l_Lean_Expr_hash(v_a_1082_);
v___x_1086_ = 32ULL;
v___x_1087_ = lean_uint64_shift_right(v___x_1085_, v___x_1086_);
v_fold_1088_ = lean_uint64_xor(v___x_1085_, v___x_1087_);
v___x_1089_ = 16ULL;
v___x_1090_ = lean_uint64_shift_right(v_fold_1088_, v___x_1089_);
v___x_1091_ = lean_uint64_xor(v_fold_1088_, v___x_1090_);
v___x_1092_ = lean_uint64_to_usize(v___x_1091_);
v___x_1093_ = lean_usize_of_nat(v___x_1084_);
v___x_1094_ = ((size_t)1ULL);
v___x_1095_ = lean_usize_sub(v___x_1093_, v___x_1094_);
v___x_1096_ = lean_usize_land(v___x_1092_, v___x_1095_);
v___x_1097_ = lean_array_uget_borrowed(v_buckets_1083_, v___x_1096_);
v___x_1098_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1082_, v___x_1097_);
return v___x_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1099_, v_a_1100_);
lean_dec_ref(v_a_1100_);
lean_dec_ref(v_m_1099_);
return v_res_1101_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1102_, lean_object* v_x_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_, lean_object* v___y_1108_){
_start:
{
lean_object* v___x_1110_; lean_object* v___x_1111_; 
v___x_1110_ = lean_apply_1(v_x_1103_, lean_box(0));
v___x_1111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1111_, 0, v___x_1110_);
return v___x_1111_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1103_ = stack[1].m_obj;
lean_object* v___y_1104_ = stack[2].m_obj;
lean_object* v___y_1105_ = stack[3].m_obj;
lean_object* v___y_1106_ = stack[4].m_obj;
lean_object* v___y_1107_ = stack[5].m_obj;
lean_object* v___y_1108_ = stack[6].m_obj;
lean_object* v_res_1112_;
v_res_1112_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v_x_1103_, v___y_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
stack->m_obj
 = v_res_1112_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1113_, lean_object* v_x_1114_, lean_object* v___y_1115_, lean_object* v___y_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1113_, v_x_1114_, v___y_1115_, v___y_1116_, v___y_1117_, v___y_1118_, v___y_1119_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
lean_dec(v___y_1117_);
lean_dec_ref(v___y_1116_);
lean_dec(v___y_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1122_, lean_object* v_x_1123_){
_start:
{
if (lean_obj_tag(v_x_1123_) == 0)
{
return v_x_1122_;
}
else
{
lean_object* v_key_1124_; lean_object* v_value_1125_; lean_object* v_tail_1126_; lean_object* v___x_1128_; uint8_t v_isShared_1129_; uint8_t v_isSharedCheck_1149_; 
v_key_1124_ = lean_ctor_get(v_x_1123_, 0);
v_value_1125_ = lean_ctor_get(v_x_1123_, 1);
v_tail_1126_ = lean_ctor_get(v_x_1123_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1123_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1128_ = v_x_1123_;
v_isShared_1129_ = v_isSharedCheck_1149_;
goto v_resetjp_1127_;
}
else
{
lean_inc(v_tail_1126_);
lean_inc(v_value_1125_);
lean_inc(v_key_1124_);
lean_dec(v_x_1123_);
v___x_1128_ = lean_box(0);
v_isShared_1129_ = v_isSharedCheck_1149_;
goto v_resetjp_1127_;
}
v_resetjp_1127_:
{
lean_object* v___x_1130_; uint64_t v___x_1131_; uint64_t v___x_1132_; uint64_t v___x_1133_; uint64_t v_fold_1134_; uint64_t v___x_1135_; uint64_t v___x_1136_; uint64_t v___x_1137_; size_t v___x_1138_; size_t v___x_1139_; size_t v___x_1140_; size_t v___x_1141_; size_t v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1145_; 
v___x_1130_ = lean_array_get_size(v_x_1122_);
v___x_1131_ = l_Lean_Expr_hash(v_key_1124_);
v___x_1132_ = 32ULL;
v___x_1133_ = lean_uint64_shift_right(v___x_1131_, v___x_1132_);
v_fold_1134_ = lean_uint64_xor(v___x_1131_, v___x_1133_);
v___x_1135_ = 16ULL;
v___x_1136_ = lean_uint64_shift_right(v_fold_1134_, v___x_1135_);
v___x_1137_ = lean_uint64_xor(v_fold_1134_, v___x_1136_);
v___x_1138_ = lean_uint64_to_usize(v___x_1137_);
v___x_1139_ = lean_usize_of_nat(v___x_1130_);
v___x_1140_ = ((size_t)1ULL);
v___x_1141_ = lean_usize_sub(v___x_1139_, v___x_1140_);
v___x_1142_ = lean_usize_land(v___x_1138_, v___x_1141_);
v___x_1143_ = lean_array_uget_borrowed(v_x_1122_, v___x_1142_);
lean_inc(v___x_1143_);
if (v_isShared_1129_ == 0)
{
lean_ctor_set(v___x_1128_, 2, v___x_1143_);
v___x_1145_ = v___x_1128_;
goto v_reusejp_1144_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_key_1124_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_value_1125_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v___x_1143_);
v___x_1145_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1144_;
}
v_reusejp_1144_:
{
lean_object* v___x_1146_; 
v___x_1146_ = lean_array_uset(v_x_1122_, v___x_1142_, v___x_1145_);
v_x_1122_ = v___x_1146_;
v_x_1123_ = v_tail_1126_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1150_, lean_object* v_source_1151_, lean_object* v_target_1152_){
_start:
{
lean_object* v___x_1153_; uint8_t v___x_1154_; 
v___x_1153_ = lean_array_get_size(v_source_1151_);
v___x_1154_ = lean_nat_dec_lt(v_i_1150_, v___x_1153_);
if (v___x_1154_ == 0)
{
lean_dec_ref(v_source_1151_);
lean_dec(v_i_1150_);
return v_target_1152_;
}
else
{
lean_object* v_es_1155_; lean_object* v___x_1156_; lean_object* v_source_1157_; lean_object* v_target_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; 
v_es_1155_ = lean_array_fget(v_source_1151_, v_i_1150_);
v___x_1156_ = lean_box(0);
v_source_1157_ = lean_array_fset(v_source_1151_, v_i_1150_, v___x_1156_);
v_target_1158_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1152_, v_es_1155_);
v___x_1159_ = lean_unsigned_to_nat(1u);
v___x_1160_ = lean_nat_add(v_i_1150_, v___x_1159_);
lean_dec(v_i_1150_);
v_i_1150_ = v___x_1160_;
v_source_1151_ = v_source_1157_;
v_target_1152_ = v_target_1158_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1162_){
_start:
{
lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v_nbuckets_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
v___x_1163_ = lean_array_get_size(v_data_1162_);
v___x_1164_ = lean_unsigned_to_nat(2u);
v_nbuckets_1165_ = lean_nat_mul(v___x_1163_, v___x_1164_);
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_box(0);
v___x_1168_ = lean_mk_array(v_nbuckets_1165_, v___x_1167_);
v___x_1169_ = lean_array_propagate_mark(v_data_1162_, v___x_1168_);
v___x_1170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1166_, v_data_1162_, v___x_1169_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1171_, lean_object* v_b_1172_, lean_object* v_x_1173_){
_start:
{
if (lean_obj_tag(v_x_1173_) == 0)
{
lean_dec(v_b_1172_);
lean_dec_ref(v_a_1171_);
return v_x_1173_;
}
else
{
lean_object* v_key_1174_; lean_object* v_value_1175_; lean_object* v_tail_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1188_; 
v_key_1174_ = lean_ctor_get(v_x_1173_, 0);
v_value_1175_ = lean_ctor_get(v_x_1173_, 1);
v_tail_1176_ = lean_ctor_get(v_x_1173_, 2);
v_isSharedCheck_1188_ = !lean_is_exclusive(v_x_1173_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1178_ = v_x_1173_;
v_isShared_1179_ = v_isSharedCheck_1188_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_tail_1176_);
lean_inc(v_value_1175_);
lean_inc(v_key_1174_);
lean_dec(v_x_1173_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1188_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint8_t v___x_1180_; 
v___x_1180_ = lean_expr_eqv(v_key_1174_, v_a_1171_);
if (v___x_1180_ == 0)
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1171_, v_b_1172_, v_tail_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 2, v___x_1181_);
v___x_1183_ = v___x_1178_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v_key_1174_);
lean_ctor_set(v_reuseFailAlloc_1184_, 1, v_value_1175_);
lean_ctor_set(v_reuseFailAlloc_1184_, 2, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
else
{
lean_object* v___x_1186_; 
lean_dec(v_value_1175_);
lean_dec(v_key_1174_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 1, v_b_1172_);
lean_ctor_set(v___x_1178_, 0, v_a_1171_);
v___x_1186_ = v___x_1178_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1171_);
lean_ctor_set(v_reuseFailAlloc_1187_, 1, v_b_1172_);
lean_ctor_set(v_reuseFailAlloc_1187_, 2, v_tail_1176_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1189_, lean_object* v_x_1190_){
_start:
{
if (lean_obj_tag(v_x_1190_) == 0)
{
uint8_t v___x_1191_; 
v___x_1191_ = 0;
return v___x_1191_;
}
else
{
lean_object* v_key_1192_; lean_object* v_tail_1193_; uint8_t v___x_1194_; 
v_key_1192_ = lean_ctor_get(v_x_1190_, 0);
v_tail_1193_ = lean_ctor_get(v_x_1190_, 2);
v___x_1194_ = lean_expr_eqv(v_key_1192_, v_a_1189_);
if (v___x_1194_ == 0)
{
v_x_1190_ = v_tail_1193_;
goto _start;
}
else
{
return v___x_1194_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1189_ = stack[0].m_obj;
lean_object* v_x_1190_ = stack[1].m_obj;
uint8_t v_res_1196_;
v_res_1196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1189_, v_x_1190_);
stack->m_num = v_res_1196_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1197_, lean_object* v_x_1198_){
_start:
{
uint8_t v_res_1199_; lean_object* v_r_1200_; 
v_res_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1197_, v_x_1198_);
lean_dec(v_x_1198_);
lean_dec_ref(v_a_1197_);
v_r_1200_ = lean_box(v_res_1199_);
return v_r_1200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1201_, lean_object* v_a_1202_, lean_object* v_b_1203_){
_start:
{
lean_object* v_size_1204_; lean_object* v_buckets_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1248_; 
v_size_1204_ = lean_ctor_get(v_m_1201_, 0);
v_buckets_1205_ = lean_ctor_get(v_m_1201_, 1);
v_isSharedCheck_1248_ = !lean_is_exclusive(v_m_1201_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1207_ = v_m_1201_;
v_isShared_1208_ = v_isSharedCheck_1248_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_buckets_1205_);
lean_inc(v_size_1204_);
lean_dec(v_m_1201_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1248_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; uint64_t v___x_1210_; uint64_t v___x_1211_; uint64_t v___x_1212_; uint64_t v_fold_1213_; uint64_t v___x_1214_; uint64_t v___x_1215_; uint64_t v___x_1216_; size_t v___x_1217_; size_t v___x_1218_; size_t v___x_1219_; size_t v___x_1220_; size_t v___x_1221_; lean_object* v_bkt_1222_; uint8_t v___x_1223_; 
v___x_1209_ = lean_array_get_size(v_buckets_1205_);
v___x_1210_ = l_Lean_Expr_hash(v_a_1202_);
v___x_1211_ = 32ULL;
v___x_1212_ = lean_uint64_shift_right(v___x_1210_, v___x_1211_);
v_fold_1213_ = lean_uint64_xor(v___x_1210_, v___x_1212_);
v___x_1214_ = 16ULL;
v___x_1215_ = lean_uint64_shift_right(v_fold_1213_, v___x_1214_);
v___x_1216_ = lean_uint64_xor(v_fold_1213_, v___x_1215_);
v___x_1217_ = lean_uint64_to_usize(v___x_1216_);
v___x_1218_ = lean_usize_of_nat(v___x_1209_);
v___x_1219_ = ((size_t)1ULL);
v___x_1220_ = lean_usize_sub(v___x_1218_, v___x_1219_);
v___x_1221_ = lean_usize_land(v___x_1217_, v___x_1220_);
v_bkt_1222_ = lean_array_uget_borrowed(v_buckets_1205_, v___x_1221_);
v___x_1223_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1202_, v_bkt_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v_size_x27_1225_; lean_object* v___x_1226_; lean_object* v_buckets_x27_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; uint8_t v___x_1233_; 
v___x_1224_ = lean_unsigned_to_nat(1u);
v_size_x27_1225_ = lean_nat_add(v_size_1204_, v___x_1224_);
lean_dec(v_size_1204_);
lean_inc(v_bkt_1222_);
v___x_1226_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1226_, 0, v_a_1202_);
lean_ctor_set(v___x_1226_, 1, v_b_1203_);
lean_ctor_set(v___x_1226_, 2, v_bkt_1222_);
v_buckets_x27_1227_ = lean_array_uset(v_buckets_1205_, v___x_1221_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(4u);
v___x_1229_ = lean_nat_mul(v_size_x27_1225_, v___x_1228_);
v___x_1230_ = lean_unsigned_to_nat(3u);
v___x_1231_ = lean_nat_div(v___x_1229_, v___x_1230_);
lean_dec(v___x_1229_);
v___x_1232_ = lean_array_get_size(v_buckets_x27_1227_);
v___x_1233_ = lean_nat_dec_le(v___x_1231_, v___x_1232_);
lean_dec(v___x_1231_);
if (v___x_1233_ == 0)
{
lean_object* v_val_1234_; lean_object* v___x_1236_; 
v_val_1234_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1227_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v_val_1234_);
lean_ctor_set(v___x_1207_, 0, v_size_x27_1225_);
v___x_1236_ = v___x_1207_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1237_; 
v_reuseFailAlloc_1237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1237_, 0, v_size_x27_1225_);
lean_ctor_set(v_reuseFailAlloc_1237_, 1, v_val_1234_);
v___x_1236_ = v_reuseFailAlloc_1237_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
return v___x_1236_;
}
}
else
{
lean_object* v___x_1239_; 
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v_buckets_x27_1227_);
lean_ctor_set(v___x_1207_, 0, v_size_x27_1225_);
v___x_1239_ = v___x_1207_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v_size_x27_1225_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v_buckets_x27_1227_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
else
{
lean_object* v___x_1241_; lean_object* v_buckets_x27_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1246_; 
lean_inc(v_bkt_1222_);
v___x_1241_ = lean_box(0);
v_buckets_x27_1242_ = lean_array_uset(v_buckets_1205_, v___x_1221_, v___x_1241_);
v___x_1243_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1202_, v_b_1203_, v_bkt_1222_);
v___x_1244_ = lean_array_uset(v_buckets_x27_1242_, v___x_1221_, v___x_1243_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1244_);
v___x_1246_ = v___x_1207_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_size_1204_);
lean_ctor_set(v_reuseFailAlloc_1247_, 1, v___x_1244_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1249_, lean_object* v_e_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1253_ = lean_st_ref_take(v_a_1249_);
v___x_1254_ = lean_box(0);
v___x_1255_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1253_, v_e_1250_, v_a_1251_);
v___x_1256_ = lean_st_ref_put(v_a_1249_, v___x_1255_);
return v___x_1254_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1249_ = stack[0].m_obj;
lean_object* v_e_1250_ = stack[1].m_obj;
lean_object* v_a_1251_ = stack[2].m_obj;
lean_object* v_res_1257_;
v_res_1257_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1249_, v_e_1250_, v_a_1251_);
stack->m_obj
 = v_res_1257_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1258_, lean_object* v_e_1259_, lean_object* v_a_1260_, lean_object* v___y_1261_){
_start:
{
lean_object* v_res_1262_; 
v_res_1262_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1258_, v_e_1259_, v_a_1260_);
lean_dec(v_a_1258_);
return v_res_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1263_, lean_object* v_e_1264_, lean_object* v_a_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
lean_object* v_res_1272_; 
v_res_1272_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1263_, v_e_1264_, v_a_1265_, v___y_1266_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec(v_a_1265_);
return v_res_1272_;
}
}
lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1273_, lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v___y_1276_, lean_object* v___y_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_, lean_object* v___y_1280_){
_start:
{
lean_object* v_a_1283_; lean_object* v___y_1295_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
lean_inc(v_a_1275_);
v___x_1297_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1297_, 0, lean_box(0));
lean_closure_set(v___x_1297_, 1, lean_box(0));
lean_closure_set(v___x_1297_, 2, v_a_1275_);
v___x_1298_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1297_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; lean_object* v___x_1301_; uint8_t v_isShared_1302_; uint8_t v_isSharedCheck_1335_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1335_ == 0)
{
v___x_1301_ = v___x_1298_;
v_isShared_1302_ = v_isSharedCheck_1335_;
goto v_resetjp_1300_;
}
else
{
lean_inc(v_a_1299_);
lean_dec(v___x_1298_);
v___x_1301_ = lean_box(0);
v_isShared_1302_ = v_isSharedCheck_1335_;
goto v_resetjp_1300_;
}
v_resetjp_1300_:
{
lean_object* v___x_1303_; 
v___x_1303_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1299_, v_e_1274_);
lean_dec(v_a_1299_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_object* v___x_1304_; 
lean_del_object(v___x_1301_);
lean_inc_ref(v_fn_1273_);
lean_inc(v___y_1280_);
lean_inc_ref(v___y_1279_);
lean_inc(v___y_1278_);
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1276_);
lean_inc_ref(v_e_1274_);
v___x_1304_ = lean_apply_7(v_fn_1273_, v_e_1274_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_, lean_box(0));
if (lean_obj_tag(v___x_1304_) == 0)
{
lean_object* v_a_1305_; uint8_t v___x_1306_; 
v_a_1305_ = lean_ctor_get(v___x_1304_, 0);
lean_inc(v_a_1305_);
lean_dec_ref_known(v___x_1304_, 1);
v___x_1306_ = lean_unbox(v_a_1305_);
lean_dec(v_a_1305_);
if (v___x_1306_ == 0)
{
lean_object* v___x_1307_; 
lean_dec_ref(v_fn_1273_);
v___x_1307_ = lean_box(0);
v_a_1283_ = v___x_1307_;
goto v___jp_1282_;
}
else
{
switch(lean_obj_tag(v_e_1274_))
{
case 7:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1308_, 0, v_fn_1273_);
lean_inc_ref(v_e_1274_);
v___x_1309_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1308_, v_e_1274_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1309_;
goto v___jp_1294_;
}
case 6:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1310_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1310_, 0, v_fn_1273_);
lean_inc_ref(v_e_1274_);
v___x_1311_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1310_, v_e_1274_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1311_;
goto v___jp_1294_;
}
case 8:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1312_, 0, v_fn_1273_);
lean_inc_ref(v_e_1274_);
v___x_1313_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1312_, v_e_1274_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1313_;
goto v___jp_1294_;
}
case 5:
{
lean_object* v_fn_1314_; lean_object* v_arg_1315_; lean_object* v___x_1316_; 
v_fn_1314_ = lean_ctor_get(v_e_1274_, 0);
v_arg_1315_ = lean_ctor_get(v_e_1274_, 1);
lean_inc_ref(v_fn_1314_);
lean_inc_ref(v_fn_1273_);
v___x_1316_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1273_, v_fn_1314_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1316_) == 0)
{
lean_object* v___x_1317_; 
lean_dec_ref_known(v___x_1316_, 1);
lean_inc_ref(v_arg_1315_);
v___x_1317_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1273_, v_arg_1315_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1317_;
goto v___jp_1294_;
}
else
{
lean_dec_ref(v_fn_1273_);
v___y_1295_ = v___x_1316_;
goto v___jp_1294_;
}
}
case 10:
{
lean_object* v_expr_1318_; lean_object* v___x_1319_; 
v_expr_1318_ = lean_ctor_get(v_e_1274_, 1);
lean_inc_ref(v_expr_1318_);
v___x_1319_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1273_, v_expr_1318_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1319_;
goto v___jp_1294_;
}
case 11:
{
lean_object* v_struct_1320_; lean_object* v___x_1321_; 
v_struct_1320_ = lean_ctor_get(v_e_1274_, 2);
lean_inc_ref(v_struct_1320_);
v___x_1321_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1273_, v_struct_1320_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
v___y_1295_ = v___x_1321_;
goto v___jp_1294_;
}
default: 
{
lean_object* v___x_1322_; 
lean_dec_ref(v_fn_1273_);
v___x_1322_ = lean_box(0);
v_a_1283_ = v___x_1322_;
goto v___jp_1282_;
}
}
}
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_fn_1273_);
v_a_1323_ = lean_ctor_get(v___x_1304_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1304_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1304_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1304_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
else
{
lean_object* v_val_1331_; lean_object* v___x_1333_; 
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_fn_1273_);
v_val_1331_ = lean_ctor_get(v___x_1303_, 0);
lean_inc(v_val_1331_);
lean_dec_ref_known(v___x_1303_, 1);
if (v_isShared_1302_ == 0)
{
lean_ctor_set(v___x_1301_, 0, v_val_1331_);
v___x_1333_ = v___x_1301_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_val_1331_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
}
else
{
lean_object* v_a_1336_; lean_object* v___x_1338_; uint8_t v_isShared_1339_; uint8_t v_isSharedCheck_1343_; 
lean_dec_ref(v_e_1274_);
lean_dec_ref(v_fn_1273_);
v_a_1336_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1343_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1343_ == 0)
{
v___x_1338_ = v___x_1298_;
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
else
{
lean_inc(v_a_1336_);
lean_dec(v___x_1298_);
v___x_1338_ = lean_box(0);
v_isShared_1339_ = v_isSharedCheck_1343_;
goto v_resetjp_1337_;
}
v_resetjp_1337_:
{
lean_object* v___x_1341_; 
if (v_isShared_1339_ == 0)
{
v___x_1341_ = v___x_1338_;
goto v_reusejp_1340_;
}
else
{
lean_object* v_reuseFailAlloc_1342_; 
v_reuseFailAlloc_1342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1342_, 0, v_a_1336_);
v___x_1341_ = v_reuseFailAlloc_1342_;
goto v_reusejp_1340_;
}
v_reusejp_1340_:
{
return v___x_1341_;
}
}
}
v___jp_1282_:
{
lean_object* v___f_1284_; lean_object* v___x_1285_; 
lean_inc(v_a_1275_);
v___f_1284_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1284_, 0, v_a_1275_);
lean_closure_set(v___f_1284_, 1, v_e_1274_);
lean_closure_set(v___f_1284_, 2, v_a_1283_);
v___x_1285_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1284_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1292_ == 0)
{
lean_object* v_unused_1293_; 
v_unused_1293_ = lean_ctor_get(v___x_1285_, 0);
lean_dec(v_unused_1293_);
v___x_1287_ = v___x_1285_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_dec(v___x_1285_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v_a_1283_);
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1283_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
else
{
return v___x_1285_;
}
}
v___jp_1294_:
{
if (lean_obj_tag(v___y_1295_) == 0)
{
lean_object* v_a_1296_; 
v_a_1296_ = lean_ctor_get(v___y_1295_, 0);
lean_inc(v_a_1296_);
lean_dec_ref_known(v___y_1295_, 1);
v_a_1283_ = v_a_1296_;
goto v___jp_1282_;
}
else
{
lean_dec_ref(v_e_1274_);
return v___y_1295_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1273_ = stack[0].m_obj;
lean_object* v_e_1274_ = stack[1].m_obj;
lean_object* v_a_1275_ = stack[2].m_obj;
lean_object* v___y_1276_ = stack[3].m_obj;
lean_object* v___y_1277_ = stack[4].m_obj;
lean_object* v___y_1278_ = stack[5].m_obj;
lean_object* v___y_1279_ = stack[6].m_obj;
lean_object* v___y_1280_ = stack[7].m_obj;
lean_object* v_res_1344_;
v_res_1344_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1273_, v_e_1274_, v_a_1275_, v___y_1276_, v___y_1277_, v___y_1278_, v___y_1279_, v___y_1280_);
stack->m_obj
 = v_res_1344_;
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = lean_box(0);
v___x_1346_ = lean_unsigned_to_nat(16u);
v___x_1347_ = lean_mk_array(v___x_1346_, v___x_1345_);
return v___x_1347_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___x_1348_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1349_ = lean_unsigned_to_nat(0u);
v___x_1350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1349_);
lean_ctor_set(v___x_1350_, 1, v___x_1348_);
return v___x_1350_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1352_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1352_, 0, lean_box(0));
lean_closure_set(v___x_1352_, 1, lean_box(0));
lean_closure_set(v___x_1352_, 2, v___x_1351_);
return v___x_1352_;
}
}
lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1353_, lean_object* v_fn_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v_a_1363_; lean_object* v___x_1364_; 
v___x_1361_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1362_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1361_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1354_, v_input_1353_, v_a_1363_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v___x_1366_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1366_, 0, lean_box(0));
lean_closure_set(v___x_1366_, 1, lean_box(0));
lean_closure_set(v___x_1366_, 2, v_a_1363_);
v___x_1367_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1366_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1367_, 0);
lean_dec(v_unused_1375_);
v___x_1369_ = v___x_1367_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_dec(v___x_1367_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v_a_1365_);
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1365_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_dec(v_a_1363_);
return v___x_1364_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1353_ = stack[0].m_obj;
lean_object* v_fn_1354_ = stack[1].m_obj;
lean_object* v___y_1355_ = stack[2].m_obj;
lean_object* v___y_1356_ = stack[3].m_obj;
lean_object* v___y_1357_ = stack[4].m_obj;
lean_object* v___y_1358_ = stack[5].m_obj;
lean_object* v___y_1359_ = stack[6].m_obj;
lean_object* v_res_1376_;
v_res_1376_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1353_, v_fn_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
stack->m_obj
 = v_res_1376_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1377_, lean_object* v_fn_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_){
_start:
{
lean_object* v_res_1385_; 
v_res_1385_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1377_, v_fn_1378_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
lean_dec_ref(v___y_1380_);
lean_dec(v___y_1379_);
return v_res_1385_;
}
}
lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1386_, lean_object* v_fn_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
lean_object* v___f_1394_; lean_object* v___x_1395_; 
v___f_1394_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1394_, 0, v_fn_1387_);
v___x_1395_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1386_, v___f_1394_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
return v___x_1395_;
}
}
LEAN_EXPORT void l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_input_1386_ = stack[0].m_obj;
lean_object* v_fn_1387_ = stack[1].m_obj;
lean_object* v___y_1388_ = stack[2].m_obj;
lean_object* v___y_1389_ = stack[3].m_obj;
lean_object* v___y_1390_ = stack[4].m_obj;
lean_object* v___y_1391_ = stack[5].m_obj;
lean_object* v___y_1392_ = stack[6].m_obj;
lean_object* v_res_1396_;
v_res_1396_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1386_, v_fn_1387_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
stack->m_obj
 = v_res_1396_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1397_, lean_object* v_fn_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
lean_object* v_res_1405_; 
v_res_1405_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1397_, v_fn_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
lean_dec(v___y_1403_);
lean_dec_ref(v___y_1402_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
return v_res_1405_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1406_, lean_object* v_x_1407_, lean_object* v_x_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_){
_start:
{
if (lean_obj_tag(v_x_1408_) == 0)
{
lean_object* v___x_1415_; 
lean_dec_ref(v_fn_1406_);
v___x_1415_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1415_, 0, v_x_1407_);
return v___x_1415_;
}
else
{
lean_object* v_head_1416_; lean_object* v_tail_1417_; lean_object* v_type_1418_; lean_object* v___x_1419_; 
v_head_1416_ = lean_ctor_get(v_x_1408_, 0);
lean_inc(v_head_1416_);
v_tail_1417_ = lean_ctor_get(v_x_1408_, 1);
lean_inc(v_tail_1417_);
lean_dec_ref_known(v_x_1408_, 2);
v_type_1418_ = lean_ctor_get(v_head_1416_, 1);
lean_inc_ref(v_type_1418_);
lean_dec(v_head_1416_);
lean_inc_ref(v_fn_1406_);
v___x_1419_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1418_, v_fn_1406_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v_x_1407_ = v_a_1420_;
v_x_1408_ = v_tail_1417_;
goto _start;
}
else
{
lean_dec(v_tail_1417_);
lean_dec_ref(v_fn_1406_);
return v___x_1419_;
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1406_ = stack[0].m_obj;
lean_object* v_x_1407_ = stack[1].m_obj;
lean_object* v_x_1408_ = stack[2].m_obj;
lean_object* v___y_1409_ = stack[3].m_obj;
lean_object* v___y_1410_ = stack[4].m_obj;
lean_object* v___y_1411_ = stack[5].m_obj;
lean_object* v___y_1412_ = stack[6].m_obj;
lean_object* v___y_1413_ = stack[7].m_obj;
lean_object* v_res_1422_;
v_res_1422_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1406_, v_x_1407_, v_x_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
stack->m_obj
 = v_res_1422_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1423_, lean_object* v_x_1424_, lean_object* v_x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_){
_start:
{
lean_object* v_res_1432_; 
v_res_1432_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1423_, v_x_1424_, v_x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_, v___y_1430_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
return v_res_1432_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1433_, lean_object* v_x_1434_, lean_object* v_x_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_){
_start:
{
if (lean_obj_tag(v_x_1435_) == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref(v_fn_1433_);
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v_x_1434_);
return v___x_1442_;
}
else
{
lean_object* v_head_1443_; lean_object* v_tail_1444_; lean_object* v___y_1446_; lean_object* v_type_1449_; lean_object* v_ctors_1450_; lean_object* v___x_1451_; 
v_head_1443_ = lean_ctor_get(v_x_1435_, 0);
lean_inc(v_head_1443_);
v_tail_1444_ = lean_ctor_get(v_x_1435_, 1);
lean_inc(v_tail_1444_);
lean_dec_ref_known(v_x_1435_, 2);
v_type_1449_ = lean_ctor_get(v_head_1443_, 1);
lean_inc_ref(v_type_1449_);
v_ctors_1450_ = lean_ctor_get(v_head_1443_, 2);
lean_inc(v_ctors_1450_);
lean_dec(v_head_1443_);
lean_inc_ref(v_fn_1433_);
v___x_1451_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1449_, v_fn_1433_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
if (lean_obj_tag(v___x_1451_) == 0)
{
lean_object* v_a_1452_; lean_object* v___x_1453_; 
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref_known(v___x_1451_, 1);
lean_inc_ref(v_fn_1433_);
v___x_1453_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1433_, v_a_1452_, v_ctors_1450_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
v___y_1446_ = v___x_1453_;
goto v___jp_1445_;
}
else
{
lean_dec(v_ctors_1450_);
v___y_1446_ = v___x_1451_;
goto v___jp_1445_;
}
v___jp_1445_:
{
if (lean_obj_tag(v___y_1446_) == 0)
{
lean_object* v_a_1447_; 
v_a_1447_ = lean_ctor_get(v___y_1446_, 0);
lean_inc(v_a_1447_);
lean_dec_ref_known(v___y_1446_, 1);
v_x_1434_ = v_a_1447_;
v_x_1435_ = v_tail_1444_;
goto _start;
}
else
{
lean_dec(v_tail_1444_);
lean_dec_ref(v_fn_1433_);
return v___y_1446_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1433_ = stack[0].m_obj;
lean_object* v_x_1434_ = stack[1].m_obj;
lean_object* v_x_1435_ = stack[2].m_obj;
lean_object* v___y_1436_ = stack[3].m_obj;
lean_object* v___y_1437_ = stack[4].m_obj;
lean_object* v___y_1438_ = stack[5].m_obj;
lean_object* v___y_1439_ = stack[6].m_obj;
lean_object* v___y_1440_ = stack[7].m_obj;
lean_object* v_res_1454_;
v_res_1454_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1433_, v_x_1434_, v_x_1435_, v___y_1436_, v___y_1437_, v___y_1438_, v___y_1439_, v___y_1440_);
stack->m_obj
 = v_res_1454_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1455_, lean_object* v_x_1456_, lean_object* v_x_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
lean_object* v_res_1464_; 
v_res_1464_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1455_, v_x_1456_, v_x_1457_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec(v___y_1458_);
return v_res_1464_;
}
}
lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1465_, lean_object* v_x_1466_, lean_object* v_x_1467_, lean_object* v___y_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
if (lean_obj_tag(v_x_1467_) == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref(v_fn_1465_);
v___x_1474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1474_, 0, v_x_1466_);
return v___x_1474_;
}
else
{
lean_object* v_head_1475_; lean_object* v_tail_1476_; lean_object* v___y_1478_; lean_object* v_toConstantVal_1481_; lean_object* v_value_1482_; lean_object* v_type_1483_; lean_object* v___x_1484_; 
v_head_1475_ = lean_ctor_get(v_x_1467_, 0);
lean_inc(v_head_1475_);
v_tail_1476_ = lean_ctor_get(v_x_1467_, 1);
lean_inc(v_tail_1476_);
lean_dec_ref_known(v_x_1467_, 2);
v_toConstantVal_1481_ = lean_ctor_get(v_head_1475_, 0);
lean_inc_ref(v_toConstantVal_1481_);
v_value_1482_ = lean_ctor_get(v_head_1475_, 1);
lean_inc_ref(v_value_1482_);
lean_dec(v_head_1475_);
v_type_1483_ = lean_ctor_get(v_toConstantVal_1481_, 2);
lean_inc_ref(v_type_1483_);
lean_dec_ref(v_toConstantVal_1481_);
lean_inc_ref(v_fn_1465_);
v___x_1484_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1483_, v_fn_1465_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1484_) == 0)
{
lean_object* v___x_1485_; 
lean_dec_ref_known(v___x_1484_, 1);
lean_inc_ref(v_fn_1465_);
v___x_1485_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1482_, v_fn_1465_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
v___y_1478_ = v___x_1485_;
goto v___jp_1477_;
}
else
{
lean_dec_ref(v_value_1482_);
v___y_1478_ = v___x_1484_;
goto v___jp_1477_;
}
v___jp_1477_:
{
if (lean_obj_tag(v___y_1478_) == 0)
{
lean_object* v_a_1479_; 
v_a_1479_ = lean_ctor_get(v___y_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___y_1478_, 1);
v_x_1466_ = v_a_1479_;
v_x_1467_ = v_tail_1476_;
goto _start;
}
else
{
lean_dec(v_tail_1476_);
lean_dec_ref(v_fn_1465_);
return v___y_1478_;
}
}
}
}
}
LEAN_EXPORT void l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1465_ = stack[0].m_obj;
lean_object* v_x_1466_ = stack[1].m_obj;
lean_object* v_x_1467_ = stack[2].m_obj;
lean_object* v___y_1468_ = stack[3].m_obj;
lean_object* v___y_1469_ = stack[4].m_obj;
lean_object* v___y_1470_ = stack[5].m_obj;
lean_object* v___y_1471_ = stack[6].m_obj;
lean_object* v___y_1472_ = stack[7].m_obj;
lean_object* v_res_1486_;
v_res_1486_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1465_, v_x_1466_, v_x_1467_, v___y_1468_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
stack->m_obj
 = v_res_1486_;
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1487_, lean_object* v_x_1488_, lean_object* v_x_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_){
_start:
{
lean_object* v_res_1496_; 
v_res_1496_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1487_, v_x_1488_, v_x_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_, v___y_1494_);
lean_dec(v___y_1494_);
lean_dec_ref(v___y_1493_);
lean_dec(v___y_1492_);
lean_dec_ref(v___y_1491_);
lean_dec(v___y_1490_);
return v_res_1496_;
}
}
lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1497_, lean_object* v_d_1498_, lean_object* v_a_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
switch(lean_obj_tag(v_d_1498_))
{
case 0:
{
lean_object* v_val_1506_; lean_object* v_toConstantVal_1507_; lean_object* v_type_1508_; lean_object* v___x_1509_; 
v_val_1506_ = lean_ctor_get(v_d_1498_, 0);
lean_inc_ref(v_val_1506_);
lean_dec_ref_known(v_d_1498_, 1);
v_toConstantVal_1507_ = lean_ctor_get(v_val_1506_, 0);
lean_inc_ref(v_toConstantVal_1507_);
lean_dec_ref(v_val_1506_);
v_type_1508_ = lean_ctor_get(v_toConstantVal_1507_, 2);
lean_inc_ref(v_type_1508_);
lean_dec_ref(v_toConstantVal_1507_);
v___x_1509_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1508_, v_fn_1497_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1509_;
}
case 4:
{
lean_object* v___x_1510_; 
lean_dec_ref(v_fn_1497_);
v___x_1510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1510_, 0, v_a_1499_);
return v___x_1510_;
}
case 5:
{
lean_object* v_defns_1511_; lean_object* v___x_1512_; 
v_defns_1511_ = lean_ctor_get(v_d_1498_, 0);
lean_inc(v_defns_1511_);
lean_dec_ref_known(v_d_1498_, 1);
v___x_1512_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1497_, v_a_1499_, v_defns_1511_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1512_;
}
case 6:
{
lean_object* v_types_1513_; lean_object* v___x_1514_; 
v_types_1513_ = lean_ctor_get(v_d_1498_, 2);
lean_inc(v_types_1513_);
lean_dec_ref_known(v_d_1498_, 3);
v___x_1514_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1497_, v_a_1499_, v_types_1513_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1514_;
}
default: 
{
lean_object* v_val_1515_; lean_object* v_toConstantVal_1516_; lean_object* v_value_1517_; lean_object* v_type_1518_; lean_object* v___x_1519_; 
v_val_1515_ = lean_ctor_get(v_d_1498_, 0);
lean_inc_ref(v_val_1515_);
lean_dec(v_d_1498_);
v_toConstantVal_1516_ = lean_ctor_get(v_val_1515_, 0);
lean_inc_ref(v_toConstantVal_1516_);
v_value_1517_ = lean_ctor_get(v_val_1515_, 1);
lean_inc_ref(v_value_1517_);
lean_dec_ref(v_val_1515_);
v_type_1518_ = lean_ctor_get(v_toConstantVal_1516_, 2);
lean_inc_ref(v_type_1518_);
lean_dec_ref(v_toConstantVal_1516_);
lean_inc_ref(v_fn_1497_);
v___x_1519_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1518_, v_fn_1497_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
if (lean_obj_tag(v___x_1519_) == 0)
{
lean_object* v___x_1520_; 
lean_dec_ref_known(v___x_1519_, 1);
v___x_1520_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1517_, v_fn_1497_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
return v___x_1520_;
}
else
{
lean_dec_ref(v_value_1517_);
lean_dec_ref(v_fn_1497_);
return v___x_1519_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_fn_1497_ = stack[0].m_obj;
lean_object* v_d_1498_ = stack[1].m_obj;
lean_object* v_a_1499_ = stack[2].m_obj;
lean_object* v___y_1500_ = stack[3].m_obj;
lean_object* v___y_1501_ = stack[4].m_obj;
lean_object* v___y_1502_ = stack[5].m_obj;
lean_object* v___y_1503_ = stack[6].m_obj;
lean_object* v___y_1504_ = stack[7].m_obj;
lean_object* v_res_1521_;
v_res_1521_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1497_, v_d_1498_, v_a_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
stack->m_obj
 = v_res_1521_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1522_, lean_object* v_d_1523_, lean_object* v_a_1524_, lean_object* v___y_1525_, lean_object* v___y_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1522_, v_d_1523_, v_a_1524_, v___y_1525_, v___y_1526_, v___y_1527_, v___y_1528_, v___y_1529_);
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
lean_dec(v___y_1525_);
return v_res_1531_;
}
}
lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1532_, lean_object* v_fn_1533_, lean_object* v___y_1534_, lean_object* v___y_1535_, lean_object* v___y_1536_, lean_object* v___y_1537_, lean_object* v___y_1538_){
_start:
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1540_ = lean_box(0);
v___x_1541_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1533_, v_decl_1532_, v___x_1540_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
return v___x_1541_;
}
}
LEAN_EXPORT void l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1532_ = stack[0].m_obj;
lean_object* v_fn_1533_ = stack[1].m_obj;
lean_object* v___y_1534_ = stack[2].m_obj;
lean_object* v___y_1535_ = stack[3].m_obj;
lean_object* v___y_1536_ = stack[4].m_obj;
lean_object* v___y_1537_ = stack[5].m_obj;
lean_object* v___y_1538_ = stack[6].m_obj;
lean_object* v_res_1542_;
v_res_1542_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1532_, v_fn_1533_, v___y_1534_, v___y_1535_, v___y_1536_, v___y_1537_, v___y_1538_);
stack->m_obj
 = v_res_1542_;
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1543_, lean_object* v_fn_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_){
_start:
{
lean_object* v_res_1551_; 
v_res_1551_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1543_, v_fn_1544_, v___y_1545_, v___y_1546_, v___y_1547_, v___y_1548_, v___y_1549_);
lean_dec(v___y_1549_);
lean_dec_ref(v___y_1548_);
lean_dec(v___y_1547_);
lean_dec_ref(v___y_1546_);
lean_dec(v___y_1545_);
return v_res_1551_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = lean_box(1);
v___x_1558_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1559_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1560_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
lean_ctor_set(v___x_1560_, 2, v___x_1557_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_1562_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1563_ = lean_unsigned_to_nat(0u);
v___x_1564_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_1564_, 0, v___x_1563_);
lean_ctor_set(v___x_1564_, 1, v___x_1563_);
lean_ctor_set(v___x_1564_, 2, v___x_1563_);
lean_ctor_set(v___x_1564_, 3, v___x_1563_);
lean_ctor_set(v___x_1564_, 4, v___x_1562_);
lean_ctor_set(v___x_1564_, 5, v___x_1562_);
lean_ctor_set(v___x_1564_, 6, v___x_1562_);
lean_ctor_set(v___x_1564_, 7, v___x_1562_);
lean_ctor_set(v___x_1564_, 8, v___x_1562_);
lean_ctor_set(v___x_1564_, 9, v___x_1562_);
lean_ctor_set(v___x_1564_, 10, v___x_1562_);
lean_ctor_set(v___x_1564_, 11, v___x_1561_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1566_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1565_);
lean_ctor_set(v___x_1566_, 2, v___x_1565_);
lean_ctor_set(v___x_1566_, 3, v___x_1565_);
lean_ctor_set(v___x_1566_, 4, v___x_1565_);
lean_ctor_set(v___x_1566_, 5, v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1567_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
lean_ctor_set(v___x_1568_, 1, v___x_1567_);
lean_ctor_set(v___x_1568_, 2, v___x_1567_);
lean_ctor_set(v___x_1568_, 3, v___x_1567_);
lean_ctor_set(v___x_1568_, 4, v___x_1567_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1569_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1570_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1571_ = lean_box(1);
v___x_1572_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1573_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
lean_ctor_set(v___x_1574_, 1, v___x_1572_);
lean_ctor_set(v___x_1574_, 2, v___x_1571_);
lean_ctor_set(v___x_1574_, 3, v___x_1570_);
lean_ctor_set(v___x_1574_, 4, v___x_1569_);
return v___x_1574_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1579_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1580_ = l_Lean_stringToMessageData(v___x_1579_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1582_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1583_ = l_Lean_stringToMessageData(v___x_1582_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1585_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1586_ = l_Lean_stringToMessageData(v___x_1585_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1588_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1589_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1588_);
lean_ctor_set(v___x_1589_, 1, v___x_1587_);
return v___x_1589_;
}
}
lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1593_, lean_object* v_a_1594_, lean_object* v_a_1595_){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; uint8_t v___x_1599_; 
v___x_1597_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1594_);
v___x_1598_ = l_Lean_warn_sorry;
v___x_1599_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_1597_, v___x_1598_);
lean_dec_ref(v___x_1597_);
if (v___x_1599_ == 0)
{
lean_object* v___x_1600_; lean_object* v___x_1601_; 
lean_dec(v_decl_1593_);
v___x_1600_ = lean_box(0);
v___x_1601_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1600_);
return v___x_1601_;
}
else
{
lean_object* v___f_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v_messages_1608_; uint8_t v___x_1609_; 
v___f_1602_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1603_ = lean_box(1);
v___x_1604_ = lean_st_ref_get(v_a_1595_);
v_messages_1608_ = lean_ctor_get(v___x_1604_, 7);
lean_inc_ref(v_messages_1608_);
lean_dec(v___x_1604_);
v___x_1609_ = l_Lean_MessageLog_hasErrors(v_messages_1608_);
lean_dec_ref(v_messages_1608_);
if (v___x_1609_ == 0)
{
if (v___x_1599_ == 0)
{
lean_dec(v_decl_1593_);
goto v___jp_1605_;
}
else
{
uint8_t v___x_1610_; 
v___x_1610_ = l_Lean_Declaration_hasSorry(v_decl_1593_);
if (v___x_1610_ == 0)
{
lean_dec(v_decl_1593_);
goto v___jp_1605_;
}
else
{
lean_object* v___x_1611_; lean_object* v___x_1612_; uint8_t v___x_1613_; uint8_t v___x_1614_; uint8_t v___x_1615_; lean_object* v___x_1616_; uint64_t v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1611_ = lean_unsigned_to_nat(0u);
v___x_1612_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1613_ = 1;
v___x_1614_ = 0;
v___x_1615_ = 2;
v___x_1616_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1616_, 0, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 1, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 2, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 3, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 4, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 5, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 6, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 7, v___x_1609_);
lean_ctor_set_uint8(v___x_1616_, 8, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 9, v___x_1613_);
lean_ctor_set_uint8(v___x_1616_, 10, v___x_1614_);
lean_ctor_set_uint8(v___x_1616_, 11, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 12, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 13, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 14, v___x_1615_);
lean_ctor_set_uint8(v___x_1616_, 15, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 16, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 17, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 18, v___x_1610_);
lean_ctor_set_uint8(v___x_1616_, 19, v___x_1609_);
v___x_1617_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1616_);
v___x_1618_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1618_, 0, v___x_1616_);
lean_ctor_set_uint64(v___x_1618_, sizeof(void*)*1, v___x_1617_);
v___x_1619_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1620_ = lean_box(0);
v___x_1621_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1621_, 0, v___x_1618_);
lean_ctor_set(v___x_1621_, 1, v___x_1603_);
lean_ctor_set(v___x_1621_, 2, v___x_1619_);
lean_ctor_set(v___x_1621_, 3, v___x_1612_);
lean_ctor_set(v___x_1621_, 4, v___x_1620_);
lean_ctor_set(v___x_1621_, 5, v___x_1611_);
lean_ctor_set(v___x_1621_, 6, v___x_1620_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*7, v___x_1609_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*7 + 1, v___x_1609_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*7 + 2, v___x_1609_);
lean_ctor_set_uint8(v___x_1621_, sizeof(void*)*7 + 3, v___x_1599_);
v___x_1622_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1623_ = lean_st_mk_ref(v___x_1622_);
v___x_1624_ = lean_st_mk_ref(v___x_1612_);
v___x_1625_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1593_, v___f_1602_, v___x_1624_, v___x_1621_, v___x_1623_, v_a_1594_, v_a_1595_);
lean_dec_ref_known(v___x_1621_, 7);
if (lean_obj_tag(v___x_1625_) == 0)
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v_val_1629_; lean_object* v___x_1651_; size_t v_sz_1652_; size_t v___x_1653_; lean_object* v___x_1654_; lean_object* v_fst_1655_; 
lean_dec_ref_known(v___x_1625_, 1);
v___x_1626_ = lean_st_ref_get(v___x_1624_);
lean_dec(v___x_1624_);
v___x_1627_ = lean_st_ref_get(v___x_1623_);
lean_dec(v___x_1623_);
lean_dec(v___x_1627_);
v___x_1651_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1652_ = lean_array_size(v___x_1626_);
v___x_1653_ = ((size_t)0ULL);
v___x_1654_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1626_, v_sz_1652_, v___x_1653_, v___x_1651_);
v_fst_1655_ = lean_ctor_get(v___x_1654_, 0);
lean_inc(v_fst_1655_);
lean_dec_ref(v___x_1654_);
if (lean_obj_tag(v_fst_1655_) == 0)
{
goto v___jp_1645_;
}
else
{
lean_object* v_val_1656_; 
v_val_1656_ = lean_ctor_get(v_fst_1655_, 0);
lean_inc(v_val_1656_);
lean_dec_ref_known(v_fst_1655_, 1);
if (lean_obj_tag(v_val_1656_) == 0)
{
goto v___jp_1645_;
}
else
{
lean_object* v_val_1657_; 
lean_dec(v___x_1626_);
v_val_1657_ = lean_ctor_get(v_val_1656_, 0);
lean_inc(v_val_1657_);
lean_dec_ref_known(v_val_1656_, 1);
v_val_1629_ = v_val_1657_;
goto v___jp_1628_;
}
}
v___jp_1628_:
{
lean_object* v_snd_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1643_; 
v_snd_1630_ = lean_ctor_get(v_val_1629_, 1);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_val_1629_);
if (v_isSharedCheck_1643_ == 0)
{
lean_object* v_unused_1644_; 
v_unused_1644_ = lean_ctor_get(v_val_1629_, 0);
lean_dec(v_unused_1644_);
v___x_1632_ = v_val_1629_;
v_isShared_1633_ = v_isSharedCheck_1643_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_snd_1630_);
lean_dec(v_val_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1643_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1634_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1635_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1633_ == 0)
{
lean_ctor_set_tag(v___x_1632_, 7);
lean_ctor_set(v___x_1632_, 0, v___x_1635_);
v___x_1637_ = v___x_1632_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1635_);
lean_ctor_set(v_reuseFailAlloc_1642_, 1, v_snd_1630_);
v___x_1637_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; 
v___x_1638_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1639_, 0, v___x_1637_);
lean_ctor_set(v___x_1639_, 1, v___x_1638_);
v___x_1640_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1634_);
lean_ctor_set(v___x_1640_, 1, v___x_1639_);
v___x_1641_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1640_, v_a_1594_, v_a_1595_);
return v___x_1641_;
}
}
}
v___jp_1645_:
{
lean_object* v___x_1646_; uint8_t v___x_1647_; 
v___x_1646_ = lean_array_get_size(v___x_1626_);
v___x_1647_ = lean_nat_dec_lt(v___x_1611_, v___x_1646_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; lean_object* v___x_1649_; 
lean_dec(v___x_1626_);
v___x_1648_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1649_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1648_, v_a_1594_, v_a_1595_);
return v___x_1649_;
}
else
{
lean_object* v___x_1650_; 
v___x_1650_ = lean_array_fget(v___x_1626_, v___x_1611_);
lean_dec(v___x_1626_);
v_val_1629_ = v___x_1650_;
goto v___jp_1628_;
}
}
}
else
{
lean_dec(v___x_1624_);
lean_dec(v___x_1623_);
return v___x_1625_;
}
}
}
}
else
{
lean_dec(v_decl_1593_);
goto v___jp_1605_;
}
v___jp_1605_:
{
lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1606_ = lean_box(0);
v___x_1607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1606_);
return v___x_1607_;
}
}
}
}
LEAN_EXPORT void l_Lean_warnIfUsesSorry_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_1593_ = stack[0].m_obj;
lean_object* v_a_1594_ = stack[1].m_obj;
lean_object* v_a_1595_ = stack[2].m_obj;
lean_object* v_res_1658_;
v_res_1658_ = l_Lean_warnIfUsesSorry(v_decl_1593_, v_a_1594_, v_a_1595_);
stack->m_obj
 = v_res_1658_;
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1659_, lean_object* v_a_1660_, lean_object* v_a_1661_, lean_object* v_a_1662_){
_start:
{
lean_object* v_res_1663_; 
v_res_1663_ = l_Lean_warnIfUsesSorry(v_decl_1659_, v_a_1660_, v_a_1661_);
lean_dec(v_a_1661_);
lean_dec_ref(v_a_1660_);
return v_res_1663_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1664_, lean_object* v_m_1665_, lean_object* v_a_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1665_, v_a_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1668_, lean_object* v_m_1669_, lean_object* v_a_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1668_, v_m_1669_, v_a_1670_);
lean_dec_ref(v_a_1670_);
lean_dec_ref(v_m_1669_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1672_, lean_object* v_m_1673_, lean_object* v_a_1674_, lean_object* v_b_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1673_, v_a_1674_, v_b_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1677_, lean_object* v_a_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1681_, lean_object* v_a_1682_, lean_object* v_x_1683_){
_start:
{
lean_object* v_res_1684_; 
v_res_1684_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1681_, v_a_1682_, v_x_1683_);
lean_dec(v_x_1683_);
lean_dec_ref(v_a_1682_);
return v_res_1684_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1685_, lean_object* v_a_1686_, lean_object* v_x_1687_){
_start:
{
uint8_t v___x_1688_; 
v___x_1688_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1686_, v_x_1687_);
return v___x_1688_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1686_ = stack[1].m_obj;
lean_object* v_x_1687_ = stack[2].m_obj;
uint8_t v_res_1689_;
v_res_1689_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_box(0), v_a_1686_, v_x_1687_);
stack->m_num = v_res_1689_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1690_, lean_object* v_a_1691_, lean_object* v_x_1692_){
_start:
{
uint8_t v_res_1693_; lean_object* v_r_1694_; 
v_res_1693_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1690_, v_a_1691_, v_x_1692_);
lean_dec(v_x_1692_);
lean_dec_ref(v_a_1691_);
v_r_1694_ = lean_box(v_res_1693_);
return v_r_1694_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1695_, lean_object* v_data_1696_){
_start:
{
lean_object* v___x_1697_; 
v___x_1697_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1696_);
return v___x_1697_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1698_, lean_object* v_a_1699_, lean_object* v_b_1700_, lean_object* v_x_1701_){
_start:
{
lean_object* v___x_1702_; 
v___x_1702_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1699_, v_b_1700_, v_x_1701_);
return v___x_1702_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1703_, lean_object* v_name_1704_, uint8_t v_bi_1705_, lean_object* v_type_1706_, lean_object* v_k_1707_, uint8_t v_kind_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1704_, v_bi_1705_, v_type_1706_, v_k_1707_, v_kind_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
return v___x_1716_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1704_ = stack[1].m_obj;
uint8_t v_bi_1705_ = stack[2].m_num;
lean_object* v_type_1706_ = stack[3].m_obj;
lean_object* v_k_1707_ = stack[4].m_obj;
uint8_t v_kind_1708_ = stack[5].m_num;
lean_object* v___y_1709_ = stack[6].m_obj;
lean_object* v___y_1710_ = stack[7].m_obj;
lean_object* v___y_1711_ = stack[8].m_obj;
lean_object* v___y_1712_ = stack[9].m_obj;
lean_object* v___y_1713_ = stack[10].m_obj;
lean_object* v___y_1714_ = stack[11].m_obj;
lean_object* v_res_1717_;
v_res_1717_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_box(0), v_name_1704_, v_bi_1705_, v_type_1706_, v_k_1707_, v_kind_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_, v___y_1714_);
stack->m_obj
 = v_res_1717_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1718_, lean_object* v_name_1719_, lean_object* v_bi_1720_, lean_object* v_type_1721_, lean_object* v_k_1722_, lean_object* v_kind_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_){
_start:
{
uint8_t v_bi_boxed_1731_; uint8_t v_kind_boxed_1732_; lean_object* v_res_1733_; 
v_bi_boxed_1731_ = lean_unbox(v_bi_1720_);
v_kind_boxed_1732_ = lean_unbox(v_kind_1723_);
v_res_1733_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1718_, v_name_1719_, v_bi_boxed_1731_, v_type_1721_, v_k_1722_, v_kind_boxed_1732_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_, v___y_1729_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
lean_dec(v___y_1727_);
lean_dec_ref(v___y_1726_);
lean_dec(v___y_1725_);
lean_dec(v___y_1724_);
return v_res_1733_;
}
}
lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1734_, lean_object* v_name_1735_, lean_object* v_type_1736_, lean_object* v_val_1737_, lean_object* v_k_1738_, uint8_t v_nondep_1739_, uint8_t v_kind_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
lean_object* v___x_1748_; 
v___x_1748_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1735_, v_type_1736_, v_val_1737_, v_k_1738_, v_nondep_1739_, v_kind_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
return v___x_1748_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1735_ = stack[1].m_obj;
lean_object* v_type_1736_ = stack[2].m_obj;
lean_object* v_val_1737_ = stack[3].m_obj;
lean_object* v_k_1738_ = stack[4].m_obj;
uint8_t v_nondep_1739_ = stack[5].m_num;
uint8_t v_kind_1740_ = stack[6].m_num;
lean_object* v___y_1741_ = stack[7].m_obj;
lean_object* v___y_1742_ = stack[8].m_obj;
lean_object* v___y_1743_ = stack[9].m_obj;
lean_object* v___y_1744_ = stack[10].m_obj;
lean_object* v___y_1745_ = stack[11].m_obj;
lean_object* v___y_1746_ = stack[12].m_obj;
lean_object* v_res_1749_;
v_res_1749_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_box(0), v_name_1735_, v_type_1736_, v_val_1737_, v_k_1738_, v_nondep_1739_, v_kind_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_, v___y_1746_);
stack->m_obj
 = v_res_1749_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1750_, lean_object* v_name_1751_, lean_object* v_type_1752_, lean_object* v_val_1753_, lean_object* v_k_1754_, lean_object* v_nondep_1755_, lean_object* v_kind_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_, lean_object* v___y_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v_nondep_boxed_1764_; uint8_t v_kind_boxed_1765_; lean_object* v_res_1766_; 
v_nondep_boxed_1764_ = lean_unbox(v_nondep_1755_);
v_kind_boxed_1765_ = lean_unbox(v_kind_1756_);
v_res_1766_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1750_, v_name_1751_, v_type_1752_, v_val_1753_, v_k_1754_, v_nondep_boxed_1764_, v_kind_boxed_1765_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_, v___y_1761_, v___y_1762_);
lean_dec(v___y_1762_);
lean_dec_ref(v___y_1761_);
lean_dec(v___y_1760_);
lean_dec_ref(v___y_1759_);
lean_dec(v___y_1758_);
lean_dec(v___y_1757_);
return v_res_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1767_, lean_object* v_i_1768_, lean_object* v_source_1769_, lean_object* v_target_1770_){
_start:
{
lean_object* v___x_1771_; 
v___x_1771_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1768_, v_source_1769_, v_target_1770_);
return v___x_1771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1772_, lean_object* v_x_1773_, lean_object* v_x_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1773_, v_x_1774_);
return v___x_1775_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1825_; uint8_t v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; 
v___x_1825_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1826_ = 0;
v___x_1827_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1828_ = l_Lean_registerTraceClass(v___x_1825_, v___x_1826_, v___x_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1829_;
v_res_1829_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
stack->m_obj
 = v_res_1829_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1831_;
}
}
lean_object* l_Lean_recordOriginalConstKind(lean_object* v_env_1832_, lean_object* v_declName_1833_, uint8_t v_kind_1834_){
_start:
{
lean_object* v___x_1835_; uint8_t v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; 
v___x_1835_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_1836_ = 0;
v___x_1837_ = lean_box(v_kind_1834_);
v___x_1838_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_1835_, v_env_1832_, v_declName_1833_, v___x_1837_, v___x_1836_);
return v___x_1838_;
}
}
LEAN_EXPORT void l_Lean_recordOriginalConstKind_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1832_ = stack[0].m_obj;
lean_object* v_declName_1833_ = stack[1].m_obj;
uint8_t v_kind_1834_ = stack[2].m_num;
lean_object* v_res_1839_;
v_res_1839_ = l_Lean_recordOriginalConstKind(v_env_1832_, v_declName_1833_, v_kind_1834_);
stack->m_obj
 = v_res_1839_;
}
LEAN_EXPORT lean_object* l_Lean_recordOriginalConstKind___boxed(lean_object* v_env_1840_, lean_object* v_declName_1841_, lean_object* v_kind_1842_){
_start:
{
uint8_t v_kind_boxed_1843_; lean_object* v_res_1844_; 
v_kind_boxed_1843_ = lean_unbox(v_kind_1842_);
v_res_1844_ = l_Lean_recordOriginalConstKind(v_env_1840_, v_declName_1841_, v_kind_boxed_1843_);
return v_res_1844_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___x_1848_; lean_object* v_nextMacroScope_1849_; lean_object* v_ngen_1850_; lean_object* v_auxDeclNGen_1851_; lean_object* v_traceState_1852_; lean_object* v_recordedDeps_1853_; lean_object* v_messages_1854_; lean_object* v_infoState_1855_; lean_object* v_snapshotTasks_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1867_; 
v___x_1848_ = lean_st_ref_take(v___y_1846_);
v_nextMacroScope_1849_ = lean_ctor_get(v___x_1848_, 1);
v_ngen_1850_ = lean_ctor_get(v___x_1848_, 2);
v_auxDeclNGen_1851_ = lean_ctor_get(v___x_1848_, 3);
v_traceState_1852_ = lean_ctor_get(v___x_1848_, 4);
v_recordedDeps_1853_ = lean_ctor_get(v___x_1848_, 6);
v_messages_1854_ = lean_ctor_get(v___x_1848_, 7);
v_infoState_1855_ = lean_ctor_get(v___x_1848_, 8);
v_snapshotTasks_1856_ = lean_ctor_get(v___x_1848_, 9);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1867_ == 0)
{
lean_object* v_unused_1868_; lean_object* v_unused_1869_; 
v_unused_1868_ = lean_ctor_get(v___x_1848_, 5);
lean_dec(v_unused_1868_);
v_unused_1869_ = lean_ctor_get(v___x_1848_, 0);
lean_dec(v_unused_1869_);
v___x_1858_ = v___x_1848_;
v_isShared_1859_ = v_isSharedCheck_1867_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_snapshotTasks_1856_);
lean_inc(v_infoState_1855_);
lean_inc(v_messages_1854_);
lean_inc(v_recordedDeps_1853_);
lean_inc(v_traceState_1852_);
lean_inc(v_auxDeclNGen_1851_);
lean_inc(v_ngen_1850_);
lean_inc(v_nextMacroScope_1849_);
lean_dec(v___x_1848_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1867_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1860_ = lean_box(0);
v___x_1861_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 5, v___x_1861_);
lean_ctor_set(v___x_1858_, 0, v_env_1845_);
v___x_1863_ = v___x_1858_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_env_1845_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_nextMacroScope_1849_);
lean_ctor_set(v_reuseFailAlloc_1866_, 2, v_ngen_1850_);
lean_ctor_set(v_reuseFailAlloc_1866_, 3, v_auxDeclNGen_1851_);
lean_ctor_set(v_reuseFailAlloc_1866_, 4, v_traceState_1852_);
lean_ctor_set(v_reuseFailAlloc_1866_, 5, v___x_1861_);
lean_ctor_set(v_reuseFailAlloc_1866_, 6, v_recordedDeps_1853_);
lean_ctor_set(v_reuseFailAlloc_1866_, 7, v_messages_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 8, v_infoState_1855_);
lean_ctor_set(v_reuseFailAlloc_1866_, 9, v_snapshotTasks_1856_);
v___x_1863_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_st_ref_put(v___y_1846_, v___x_1863_);
v___x_1865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1860_);
return v___x_1865_;
}
}
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1845_ = stack[0].m_obj;
lean_object* v___y_1846_ = stack[1].m_obj;
lean_object* v_res_1870_;
v_res_1870_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1845_, v___y_1846_);
stack->m_obj
 = v_res_1870_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1871_, v___y_1872_);
lean_dec(v___y_1872_);
return v_res_1874_;
}
}
lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v___x_1879_; 
v___x_1879_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1875_, v___y_1877_);
return v___x_1879_;
}
}
LEAN_EXPORT void l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_1875_ = stack[0].m_obj;
lean_object* v___y_1876_ = stack[1].m_obj;
lean_object* v___y_1877_ = stack[2].m_obj;
lean_object* v_res_1880_;
v_res_1880_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1875_, v___y_1876_, v___y_1877_);
stack->m_obj
 = v_res_1880_;
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1885_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_box(0);
v___x_1887_ = l_Lean_interruptExceptionId;
v___x_1888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1887_);
lean_ctor_set(v___x_1888_, 1, v___x_1886_);
return v___x_1888_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1892_;
v_res_1892_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
stack->m_obj
 = v_res_1892_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1893_){
_start:
{
lean_object* v_res_1894_; 
v_res_1894_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1894_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_){
_start:
{
lean_object* v_ref_1899_; lean_object* v___x_1900_; lean_object* v_a_1901_; lean_object* v___x_1903_; uint8_t v_isShared_1904_; uint8_t v_isSharedCheck_1909_; 
v_ref_1899_ = lean_ctor_get(v___y_1896_, 2);
v___x_1900_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1895_, v___y_1896_, v___y_1897_);
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1903_ = v___x_1900_;
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
else
{
lean_inc(v_a_1901_);
lean_dec(v___x_1900_);
v___x_1903_ = lean_box(0);
v_isShared_1904_ = v_isSharedCheck_1909_;
goto v_resetjp_1902_;
}
v_resetjp_1902_:
{
lean_object* v___x_1905_; lean_object* v___x_1907_; 
lean_inc(v_ref_1899_);
v___x_1905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_ref_1899_);
lean_ctor_set(v___x_1905_, 1, v_a_1901_);
if (v_isShared_1904_ == 0)
{
lean_ctor_set_tag(v___x_1903_, 1);
lean_ctor_set(v___x_1903_, 0, v___x_1905_);
v___x_1907_ = v___x_1903_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_1895_ = stack[0].m_obj;
lean_object* v___y_1896_ = stack[1].m_obj;
lean_object* v___y_1897_ = stack[2].m_obj;
lean_object* v_res_1910_;
v_res_1910_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1895_, v___y_1896_, v___y_1897_);
stack->m_obj
 = v_res_1910_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1911_, lean_object* v___y_1912_, lean_object* v___y_1913_, lean_object* v___y_1914_){
_start:
{
lean_object* v_res_1915_; 
v_res_1915_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1911_, v___y_1912_, v___y_1913_);
lean_dec(v___y_1913_);
lean_dec_ref(v___y_1912_);
return v_res_1915_;
}
}
lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1916_, lean_object* v___y_1917_, lean_object* v___y_1918_){
_start:
{
lean_object* v___y_1921_; lean_object* v___y_1922_; 
if (lean_obj_tag(v_ex_1916_) == 16)
{
lean_object* v___x_1926_; lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v___x_1926_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1927_ = lean_ctor_get(v___x_1926_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1926_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1926_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1926_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
else
{
v___y_1921_ = v___y_1917_;
v___y_1922_ = v___y_1918_;
goto v___jp_1920_;
}
v___jp_1920_:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1921_);
v___x_1924_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1916_, v___x_1923_);
v___x_1925_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1924_, v___y_1921_, v___y_1922_);
return v___x_1925_;
}
}
}
LEAN_EXPORT void l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_1916_ = stack[0].m_obj;
lean_object* v___y_1917_ = stack[1].m_obj;
lean_object* v___y_1918_ = stack[2].m_obj;
lean_object* v_res_1935_;
v_res_1935_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1916_, v___y_1917_, v___y_1918_);
stack->m_obj
 = v_res_1935_;
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1936_, lean_object* v___y_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_){
_start:
{
lean_object* v_res_1940_; 
v_res_1940_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1936_, v___y_1937_, v___y_1938_);
lean_dec(v___y_1938_);
lean_dec_ref(v___y_1937_);
return v_res_1940_;
}
}
lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
if (lean_obj_tag(v_x_1941_) == 0)
{
lean_object* v_a_1945_; lean_object* v___x_1946_; 
v_a_1945_ = lean_ctor_get(v_x_1941_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v_x_1941_, 1);
v___x_1946_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1945_, v___y_1942_, v___y_1943_);
return v___x_1946_;
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
v_a_1947_ = lean_ctor_get(v_x_1941_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v_x_1941_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v_x_1941_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v_x_1941_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set_tag(v___x_1949_, 0);
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1941_ = stack[0].m_obj;
lean_object* v___y_1942_ = stack[1].m_obj;
lean_object* v___y_1943_ = stack[2].m_obj;
lean_object* v_res_1955_;
v_res_1955_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1941_, v___y_1942_, v___y_1943_);
stack->m_obj
 = v_res_1955_;
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1956_, v___y_1957_, v___y_1958_);
lean_dec(v___y_1958_);
lean_dec_ref(v___y_1957_);
return v_res_1960_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; 
v___x_1967_ = lean_unsigned_to_nat(1u);
v___x_1968_ = l_Lean_Level_ofNat(v___x_1967_);
return v___x_1968_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_box(0);
v___x_1970_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v___x_1970_);
lean_ctor_set(v___x_1971_, 1, v___x_1969_);
return v___x_1971_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1972_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1973_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1974_ = l_Lean_mkConst(v___x_1973_, v___x_1972_);
return v___x_1974_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
v___x_1975_ = lean_unsigned_to_nat(0u);
v___x_1976_ = l_Lean_Level_ofNat(v___x_1975_);
return v___x_1976_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1978_ = l_Lean_mkSort(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; 
v___x_1984_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1986_ = l_Lean_mkConst(v___x_1985_, v___x_1984_);
return v___x_1986_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1987_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1988_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1989_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1990_ = l_Lean_mkAppB(v___x_1989_, v___x_1988_, v___x_1987_);
return v___x_1990_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1996_, lean_object* v_b_1997_, lean_object* v___y_1998_, lean_object* v___y_1999_){
_start:
{
if (lean_obj_tag(v_as_x27_1996_) == 0)
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2001_, 0, v_b_1997_);
return v___x_2001_;
}
else
{
lean_object* v_head_2002_; lean_object* v_tail_2003_; lean_object* v___x_2004_; lean_object* v___y_2006_; uint8_t v___y_2007_; lean_object* v_a_2011_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; uint8_t v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v_toCold_2021_; lean_object* v_env_2022_; lean_object* v_cancelTk_x3f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; 
lean_dec_ref(v_b_1997_);
v_head_2002_ = lean_ctor_get(v_as_x27_1996_, 0);
v_tail_2003_ = lean_ctor_get(v_as_x27_1996_, 1);
v___x_2004_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_2002_);
v___x_2016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2016_, 0, v_head_2002_);
lean_ctor_set(v___x_2016_, 1, v___x_2014_);
lean_ctor_set(v___x_2016_, 2, v___x_2015_);
v___x_2017_ = 0;
v___x_2018_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2018_, 0, v___x_2016_);
lean_ctor_set_uint8(v___x_2018_, sizeof(void*)*1, v___x_2017_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v___x_2018_);
v___x_2020_ = lean_st_ref_get(v___y_1999_);
v_toCold_2021_ = lean_ctor_get(v___y_1998_, 0);
v_env_2022_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_ref(v_env_2022_);
lean_dec(v___x_2020_);
v_cancelTk_x3f_2023_ = lean_ctor_get(v_toCold_2021_, 10);
v___x_2024_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1998_);
v___x_2025_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2022_, v___x_2024_, v___x_2019_, v_cancelTk_x3f_2023_);
lean_dec_ref_known(v___x_2019_, 1);
lean_dec_ref(v___x_2024_);
v___x_2026_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2025_, v___y_1998_, v___y_1999_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2036_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
v___x_2028_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2027_, v___y_1999_);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2028_, 0);
lean_dec(v_unused_2037_);
v___x_2030_ = v___x_2028_;
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v___x_2028_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2036_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2034_; 
v___x_2032_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2032_);
v___x_2034_ = v___x_2030_;
goto v_reusejp_2033_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
v___x_2034_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2033_;
}
v_reusejp_2033_:
{
return v___x_2034_;
}
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2026_, 1);
v_a_2011_ = v_a_2038_;
goto v___jp_2010_;
}
v___jp_2005_:
{
if (v___y_2007_ == 0)
{
lean_dec_ref(v___y_2006_);
v_as_x27_1996_ = v_tail_2003_;
v_b_1997_ = v___x_2004_;
goto _start;
}
else
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2009_, 0, v___y_2006_);
return v___x_2009_;
}
}
v___jp_2010_:
{
uint8_t v___x_2012_; 
v___x_2012_ = l_Lean_Exception_isInterrupt(v_a_2011_);
if (v___x_2012_ == 0)
{
uint8_t v___x_2013_; 
lean_inc_ref(v_a_2011_);
v___x_2013_ = l_Lean_Exception_isRuntime(v_a_2011_);
v___y_2006_ = v_a_2011_;
v___y_2007_ = v___x_2013_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v_a_2011_;
v___y_2007_ = v___x_2012_;
goto v___jp_2005_;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_1996_ = stack[0].m_obj;
lean_object* v_b_1997_ = stack[1].m_obj;
lean_object* v___y_1998_ = stack[2].m_obj;
lean_object* v___y_1999_ = stack[3].m_obj;
lean_object* v_res_2039_;
v_res_2039_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1996_, v_b_1997_, v___y_1998_, v___y_1999_);
stack->m_obj
 = v_res_2039_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_2040_, lean_object* v_b_2041_, lean_object* v___y_2042_, lean_object* v___y_2043_, lean_object* v___y_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2040_, v_b_2041_, v___y_2042_, v___y_2043_);
lean_dec(v___y_2043_);
lean_dec_ref(v___y_2042_);
lean_dec(v_as_x27_2040_);
return v_res_2045_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_){
_start:
{
lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2079_; uint8_t v___y_2080_; lean_object* v_a_2083_; lean_object* v___y_2087_; uint8_t v___y_2088_; lean_object* v_a_2091_; 
switch(lean_obj_tag(v_decl_2046_))
{
case 1:
{
lean_object* v_val_2094_; lean_object* v_toConstantVal_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v_fallbackDecl_2098_; lean_object* v___x_2099_; lean_object* v_toCold_2100_; lean_object* v_env_2101_; lean_object* v_cancelTk_x3f_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; 
v_val_2094_ = lean_ctor_get(v_decl_2046_, 0);
v_toConstantVal_2095_ = lean_ctor_get(v_val_2094_, 0);
v___x_2096_ = 0;
lean_inc_ref(v_toConstantVal_2095_);
v___x_2097_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2097_, 0, v_toConstantVal_2095_);
lean_ctor_set_uint8(v___x_2097_, sizeof(void*)*1, v___x_2096_);
v_fallbackDecl_2098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2098_, 0, v___x_2097_);
v___x_2099_ = lean_st_ref_get(v_a_2048_);
v_toCold_2100_ = lean_ctor_get(v_a_2047_, 0);
v_env_2101_ = lean_ctor_get(v___x_2099_, 0);
lean_inc_ref(v_env_2101_);
lean_dec(v___x_2099_);
v_cancelTk_x3f_2102_ = lean_ctor_get(v_toCold_2100_, 10);
v___x_2103_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2047_);
v___x_2104_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2101_, v___x_2103_, v_fallbackDecl_2098_, v_cancelTk_x3f_2102_);
lean_dec_ref_known(v_fallbackDecl_2098_, 1);
lean_dec_ref(v___x_2103_);
v___x_2105_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2104_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; lean_object* v___x_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2115_; 
lean_dec_ref_known(v_decl_2046_, 1);
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2106_, v_a_2048_);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2107_, 0);
lean_dec(v_unused_2116_);
v___x_2109_ = v___x_2107_;
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
else
{
lean_dec(v___x_2107_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2115_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2111_; lean_object* v___x_2113_; 
v___x_2111_ = lean_box(0);
if (v_isShared_2110_ == 0)
{
lean_ctor_set(v___x_2109_, 0, v___x_2111_);
v___x_2113_ = v___x_2109_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v___x_2111_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
else
{
lean_object* v_a_2117_; 
v_a_2117_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2117_);
lean_dec_ref_known(v___x_2105_, 1);
v_a_2083_ = v_a_2117_;
goto v___jp_2082_;
}
}
case 2:
{
lean_object* v_val_2118_; lean_object* v_toConstantVal_2119_; uint8_t v___x_2120_; lean_object* v___x_2121_; lean_object* v_fallbackDecl_2122_; lean_object* v___x_2123_; lean_object* v_toCold_2124_; lean_object* v_env_2125_; lean_object* v_cancelTk_x3f_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; 
v_val_2118_ = lean_ctor_get(v_decl_2046_, 0);
v_toConstantVal_2119_ = lean_ctor_get(v_val_2118_, 0);
v___x_2120_ = 0;
lean_inc_ref(v_toConstantVal_2119_);
v___x_2121_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2121_, 0, v_toConstantVal_2119_);
lean_ctor_set_uint8(v___x_2121_, sizeof(void*)*1, v___x_2120_);
v_fallbackDecl_2122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2122_, 0, v___x_2121_);
v___x_2123_ = lean_st_ref_get(v_a_2048_);
v_toCold_2124_ = lean_ctor_get(v_a_2047_, 0);
v_env_2125_ = lean_ctor_get(v___x_2123_, 0);
lean_inc_ref(v_env_2125_);
lean_dec(v___x_2123_);
v_cancelTk_x3f_2126_ = lean_ctor_get(v_toCold_2124_, 10);
v___x_2127_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2047_);
v___x_2128_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2125_, v___x_2127_, v_fallbackDecl_2122_, v_cancelTk_x3f_2126_);
lean_dec_ref_known(v_fallbackDecl_2122_, 1);
lean_dec_ref(v___x_2127_);
v___x_2129_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2128_, v_a_2047_, v_a_2048_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref_known(v_decl_2046_, 1);
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2130_, v_a_2048_);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2139_ == 0)
{
lean_object* v_unused_2140_; 
v_unused_2140_ = lean_ctor_get(v___x_2131_, 0);
lean_dec(v_unused_2140_);
v___x_2133_ = v___x_2131_;
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
else
{
lean_dec(v___x_2131_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2139_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2135_; lean_object* v___x_2137_; 
v___x_2135_ = lean_box(0);
if (v_isShared_2134_ == 0)
{
lean_ctor_set(v___x_2133_, 0, v___x_2135_);
v___x_2137_ = v___x_2133_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v___x_2135_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
else
{
lean_object* v_a_2141_; 
v_a_2141_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2129_, 1);
v_a_2091_ = v_a_2141_;
goto v___jp_2090_;
}
}
default: 
{
v___y_2051_ = v_a_2047_;
v___y_2052_ = v_a_2048_;
goto v___jp_2050_;
}
}
v___jp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2053_ = l_Lean_Declaration_getNames(v_decl_2046_);
v___x_2054_ = lean_box(0);
v___x_2055_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_2056_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_2053_, v___x_2055_, v___y_2051_, v___y_2052_);
lean_dec(v___x_2053_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2069_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_2059_ = v___x_2056_;
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2056_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2069_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v_fst_2061_; 
v_fst_2061_ = lean_ctor_get(v_a_2057_, 0);
lean_inc(v_fst_2061_);
lean_dec(v_a_2057_);
if (lean_obj_tag(v_fst_2061_) == 0)
{
lean_object* v___x_2063_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2054_);
v___x_2063_ = v___x_2059_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2064_; 
v_reuseFailAlloc_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v___x_2054_);
v___x_2063_ = v_reuseFailAlloc_2064_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
return v___x_2063_;
}
}
else
{
lean_object* v_val_2065_; lean_object* v___x_2067_; 
v_val_2065_ = lean_ctor_get(v_fst_2061_, 0);
lean_inc(v_val_2065_);
lean_dec_ref_known(v_fst_2061_, 1);
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v_val_2065_);
v___x_2067_ = v___x_2059_;
goto v_reusejp_2066_;
}
else
{
lean_object* v_reuseFailAlloc_2068_; 
v_reuseFailAlloc_2068_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2068_, 0, v_val_2065_);
v___x_2067_ = v_reuseFailAlloc_2068_;
goto v_reusejp_2066_;
}
v_reusejp_2066_:
{
return v___x_2067_;
}
}
}
}
else
{
lean_object* v_a_2070_; lean_object* v___x_2072_; uint8_t v_isShared_2073_; uint8_t v_isSharedCheck_2077_; 
v_a_2070_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_2072_ = v___x_2056_;
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
else
{
lean_inc(v_a_2070_);
lean_dec(v___x_2056_);
v___x_2072_ = lean_box(0);
v_isShared_2073_ = v_isSharedCheck_2077_;
goto v_resetjp_2071_;
}
v_resetjp_2071_:
{
lean_object* v___x_2075_; 
if (v_isShared_2073_ == 0)
{
v___x_2075_ = v___x_2072_;
goto v_reusejp_2074_;
}
else
{
lean_object* v_reuseFailAlloc_2076_; 
v_reuseFailAlloc_2076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2076_, 0, v_a_2070_);
v___x_2075_ = v_reuseFailAlloc_2076_;
goto v_reusejp_2074_;
}
v_reusejp_2074_:
{
return v___x_2075_;
}
}
}
}
v___jp_2078_:
{
if (v___y_2080_ == 0)
{
lean_dec_ref(v___y_2079_);
v___y_2051_ = v_a_2047_;
v___y_2052_ = v_a_2048_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2081_; 
lean_dec(v_decl_2046_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v___y_2079_);
return v___x_2081_;
}
}
v___jp_2082_:
{
uint8_t v___x_2084_; 
v___x_2084_ = l_Lean_Exception_isInterrupt(v_a_2083_);
if (v___x_2084_ == 0)
{
uint8_t v___x_2085_; 
lean_inc_ref(v_a_2083_);
v___x_2085_ = l_Lean_Exception_isRuntime(v_a_2083_);
v___y_2079_ = v_a_2083_;
v___y_2080_ = v___x_2085_;
goto v___jp_2078_;
}
else
{
v___y_2079_ = v_a_2083_;
v___y_2080_ = v___x_2084_;
goto v___jp_2078_;
}
}
v___jp_2086_:
{
if (v___y_2088_ == 0)
{
lean_dec_ref(v___y_2087_);
v___y_2051_ = v_a_2047_;
v___y_2052_ = v_a_2048_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2089_; 
lean_dec(v_decl_2046_);
v___x_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2089_, 0, v___y_2087_);
return v___x_2089_;
}
}
v___jp_2090_:
{
uint8_t v___x_2092_; 
v___x_2092_ = l_Lean_Exception_isInterrupt(v_a_2091_);
if (v___x_2092_ == 0)
{
uint8_t v___x_2093_; 
lean_inc_ref(v_a_2091_);
v___x_2093_ = l_Lean_Exception_isRuntime(v_a_2091_);
v___y_2087_ = v_a_2091_;
v___y_2088_ = v___x_2093_;
goto v___jp_2086_;
}
else
{
v___y_2087_ = v_a_2091_;
v___y_2088_ = v___x_2092_;
goto v___jp_2086_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2046_ = stack[0].m_obj;
lean_object* v_a_2047_ = stack[1].m_obj;
lean_object* v_a_2048_ = stack[2].m_obj;
lean_object* v_res_2142_;
v_res_2142_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2046_, v_a_2047_, v_a_2048_);
stack->m_obj
 = v_res_2142_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_, lean_object* v_a_2146_){
_start:
{
lean_object* v_res_2147_; 
v_res_2147_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2143_, v_a_2144_, v_a_2145_);
lean_dec(v_a_2145_);
lean_dec_ref(v_a_2144_);
return v_res_2147_;
}
}
lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2148_, lean_object* v_x_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2149_, v___y_2150_, v___y_2151_);
return v___x_2153_;
}
}
LEAN_EXPORT void l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2149_ = stack[1].m_obj;
lean_object* v___y_2150_ = stack[2].m_obj;
lean_object* v___y_2151_ = stack[3].m_obj;
lean_object* v_res_2154_;
v_res_2154_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_box(0), v_x_2149_, v___y_2150_, v___y_2151_);
stack->m_obj
 = v_res_2154_;
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2155_, lean_object* v_x_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_){
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2155_, v_x_2156_, v___y_2157_, v___y_2158_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
return v_res_2160_;
}
}
lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2161_, lean_object* v_as_x27_2162_, lean_object* v_b_2163_, lean_object* v_a_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v___x_2168_; 
v___x_2168_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2162_, v_b_2163_, v___y_2165_, v___y_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_2161_ = stack[0].m_obj;
lean_object* v_as_x27_2162_ = stack[1].m_obj;
lean_object* v_b_2163_ = stack[2].m_obj;
lean_object* v___y_2165_ = stack[4].m_obj;
lean_object* v___y_2166_ = stack[5].m_obj;
lean_object* v_res_2169_;
v_res_2169_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2161_, v_as_x27_2162_, v_b_2163_, lean_box(0), v___y_2165_, v___y_2166_);
stack->m_obj
 = v_res_2169_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2170_, lean_object* v_as_x27_2171_, lean_object* v_b_2172_, lean_object* v_a_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2170_, v_as_x27_2171_, v_b_2172_, v_a_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v_as_x27_2171_);
lean_dec(v_as_2170_);
return v_res_2177_;
}
}
lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2182_;
}
}
LEAN_EXPORT void l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2179_ = stack[1].m_obj;
lean_object* v___y_2180_ = stack[2].m_obj;
lean_object* v_res_2183_;
v_res_2183_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_box(0), v___y_2179_, v___y_2180_);
stack->m_obj
 = v_res_2183_;
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2184_, v___y_2185_, v___y_2186_);
lean_dec(v___y_2186_);
lean_dec_ref(v___y_2185_);
return v_res_2188_;
}
}
lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2189_, lean_object* v_ex_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2190_, v___y_2191_, v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT void l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_ex_2190_ = stack[1].m_obj;
lean_object* v___y_2191_ = stack[2].m_obj;
lean_object* v___y_2192_ = stack[3].m_obj;
lean_object* v_res_2195_;
v_res_2195_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_box(0), v_ex_2190_, v___y_2191_, v___y_2192_);
stack->m_obj
 = v_res_2195_;
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2196_, lean_object* v_ex_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2196_, v_ex_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
return v_res_2201_;
}
}
lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2202_, lean_object* v_msg_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2203_, v___y_2204_, v___y_2205_);
return v___x_2207_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2203_ = stack[1].m_obj;
lean_object* v___y_2204_ = stack[2].m_obj;
lean_object* v___y_2205_ = stack[3].m_obj;
lean_object* v_res_2208_;
v_res_2208_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_box(0), v_msg_2203_, v___y_2204_, v___y_2205_);
stack->m_obj
 = v_res_2208_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2209_, lean_object* v_msg_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2209_, v_msg_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
return v_res_2214_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_unsigned_to_nat(32u);
v___x_2216_ = lean_mk_empty_array_with_capacity(v___x_2215_);
v___x_2217_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
return v___x_2217_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2218_ = ((size_t)5ULL);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = lean_unsigned_to_nat(32u);
v___x_2221_ = lean_mk_empty_array_with_capacity(v___x_2220_);
v___x_2222_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2223_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2221_);
lean_ctor_set(v___x_2223_, 2, v___x_2219_);
lean_ctor_set(v___x_2223_, 3, v___x_2219_);
lean_ctor_set_usize(v___x_2223_, 4, v___x_2218_);
return v___x_2223_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2224_){
_start:
{
lean_object* v___x_2226_; lean_object* v_traceState_2227_; lean_object* v_traces_2228_; lean_object* v___x_2229_; lean_object* v_traceState_2230_; lean_object* v_env_2231_; lean_object* v_nextMacroScope_2232_; lean_object* v_ngen_2233_; lean_object* v_auxDeclNGen_2234_; lean_object* v_cache_2235_; lean_object* v_recordedDeps_2236_; lean_object* v_messages_2237_; lean_object* v_infoState_2238_; lean_object* v_snapshotTasks_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2258_; 
v___x_2226_ = lean_st_ref_get(v___y_2224_);
v_traceState_2227_ = lean_ctor_get(v___x_2226_, 4);
lean_inc_ref(v_traceState_2227_);
lean_dec(v___x_2226_);
v_traces_2228_ = lean_ctor_get(v_traceState_2227_, 0);
lean_inc_ref(v_traces_2228_);
lean_dec_ref(v_traceState_2227_);
v___x_2229_ = lean_st_ref_take(v___y_2224_);
v_traceState_2230_ = lean_ctor_get(v___x_2229_, 4);
v_env_2231_ = lean_ctor_get(v___x_2229_, 0);
v_nextMacroScope_2232_ = lean_ctor_get(v___x_2229_, 1);
v_ngen_2233_ = lean_ctor_get(v___x_2229_, 2);
v_auxDeclNGen_2234_ = lean_ctor_get(v___x_2229_, 3);
v_cache_2235_ = lean_ctor_get(v___x_2229_, 5);
v_recordedDeps_2236_ = lean_ctor_get(v___x_2229_, 6);
v_messages_2237_ = lean_ctor_get(v___x_2229_, 7);
v_infoState_2238_ = lean_ctor_get(v___x_2229_, 8);
v_snapshotTasks_2239_ = lean_ctor_get(v___x_2229_, 9);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2241_ = v___x_2229_;
v_isShared_2242_ = v_isSharedCheck_2258_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_snapshotTasks_2239_);
lean_inc(v_infoState_2238_);
lean_inc(v_messages_2237_);
lean_inc(v_recordedDeps_2236_);
lean_inc(v_cache_2235_);
lean_inc(v_traceState_2230_);
lean_inc(v_auxDeclNGen_2234_);
lean_inc(v_ngen_2233_);
lean_inc(v_nextMacroScope_2232_);
lean_inc(v_env_2231_);
lean_dec(v___x_2229_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2258_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
uint64_t v_tid_2243_; lean_object* v___x_2245_; uint8_t v_isShared_2246_; uint8_t v_isSharedCheck_2256_; 
v_tid_2243_ = lean_ctor_get_uint64(v_traceState_2230_, sizeof(void*)*1);
v_isSharedCheck_2256_ = !lean_is_exclusive(v_traceState_2230_);
if (v_isSharedCheck_2256_ == 0)
{
lean_object* v_unused_2257_; 
v_unused_2257_ = lean_ctor_get(v_traceState_2230_, 0);
lean_dec(v_unused_2257_);
v___x_2245_ = v_traceState_2230_;
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
else
{
lean_dec(v_traceState_2230_);
v___x_2245_ = lean_box(0);
v_isShared_2246_ = v_isSharedCheck_2256_;
goto v_resetjp_2244_;
}
v_resetjp_2244_:
{
lean_object* v___x_2247_; lean_object* v___x_2249_; 
v___x_2247_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2246_ == 0)
{
lean_ctor_set(v___x_2245_, 0, v___x_2247_);
v___x_2249_ = v___x_2245_;
goto v_reusejp_2248_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2247_);
lean_ctor_set_uint64(v_reuseFailAlloc_2255_, sizeof(void*)*1, v_tid_2243_);
v___x_2249_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2248_;
}
v_reusejp_2248_:
{
lean_object* v___x_2251_; 
if (v_isShared_2242_ == 0)
{
lean_ctor_set(v___x_2241_, 4, v___x_2249_);
v___x_2251_ = v___x_2241_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_env_2231_);
lean_ctor_set(v_reuseFailAlloc_2254_, 1, v_nextMacroScope_2232_);
lean_ctor_set(v_reuseFailAlloc_2254_, 2, v_ngen_2233_);
lean_ctor_set(v_reuseFailAlloc_2254_, 3, v_auxDeclNGen_2234_);
lean_ctor_set(v_reuseFailAlloc_2254_, 4, v___x_2249_);
lean_ctor_set(v_reuseFailAlloc_2254_, 5, v_cache_2235_);
lean_ctor_set(v_reuseFailAlloc_2254_, 6, v_recordedDeps_2236_);
lean_ctor_set(v_reuseFailAlloc_2254_, 7, v_messages_2237_);
lean_ctor_set(v_reuseFailAlloc_2254_, 8, v_infoState_2238_);
lean_ctor_set(v_reuseFailAlloc_2254_, 9, v_snapshotTasks_2239_);
v___x_2251_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2252_ = lean_st_ref_put(v___y_2224_, v___x_2251_);
v___x_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2253_, 0, v_traces_2228_);
return v___x_2253_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2224_ = stack[0].m_obj;
lean_object* v_res_2259_;
v_res_2259_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2224_);
stack->m_obj
 = v_res_2259_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2260_);
lean_dec(v___y_2260_);
return v_res_2262_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v___x_2266_; 
v___x_2266_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2264_);
return v___x_2266_;
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2263_ = stack[0].m_obj;
lean_object* v___y_2264_ = stack[1].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2263_, v___y_2264_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2268_, v___y_2269_);
lean_dec(v___y_2269_);
lean_dec_ref(v___y_2268_);
return v_res_2271_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2272_, lean_object* v_opts_2273_, lean_object* v_act_2274_, lean_object* v_decl_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; 
lean_inc(v___y_2277_);
lean_inc_ref(v___y_2276_);
v___x_2279_ = lean_apply_2(v_act_2274_, v___y_2276_, v___y_2277_);
v___x_2280_ = l_Lean_profileitIOUnsafe___redArg(v_category_2272_, v_opts_2273_, v___x_2279_, v_decl_2275_);
return v___x_2280_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_2272_ = stack[0].m_obj;
lean_object* v_opts_2273_ = stack[1].m_obj;
lean_object* v_act_2274_ = stack[2].m_obj;
lean_object* v_decl_2275_ = stack[3].m_obj;
lean_object* v___y_2276_ = stack[4].m_obj;
lean_object* v___y_2277_ = stack[5].m_obj;
lean_object* v_res_2281_;
v_res_2281_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2272_, v_opts_2273_, v_act_2274_, v_decl_2275_, v___y_2276_, v___y_2277_);
stack->m_obj
 = v_res_2281_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2282_, lean_object* v_opts_2283_, lean_object* v_act_2284_, lean_object* v_decl_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_){
_start:
{
lean_object* v_res_2289_; 
v_res_2289_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2282_, v_opts_2283_, v_act_2284_, v_decl_2285_, v___y_2286_, v___y_2287_);
lean_dec(v___y_2287_);
lean_dec_ref(v___y_2286_);
lean_dec_ref(v_opts_2283_);
lean_dec_ref(v_category_2282_);
return v_res_2289_;
}
}
lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2290_, lean_object* v_category_2291_, lean_object* v_opts_2292_, lean_object* v_act_2293_, lean_object* v_decl_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v___x_2298_; 
v___x_2298_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2291_, v_opts_2292_, v_act_2293_, v_decl_2294_, v___y_2295_, v___y_2296_);
return v___x_2298_;
}
}
LEAN_EXPORT void l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_category_2291_ = stack[1].m_obj;
lean_object* v_opts_2292_ = stack[2].m_obj;
lean_object* v_act_2293_ = stack[3].m_obj;
lean_object* v_decl_2294_ = stack[4].m_obj;
lean_object* v___y_2295_ = stack[5].m_obj;
lean_object* v___y_2296_ = stack[6].m_obj;
lean_object* v_res_2299_;
v_res_2299_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_box(0), v_category_2291_, v_opts_2292_, v_act_2293_, v_decl_2294_, v___y_2295_, v___y_2296_);
stack->m_obj
 = v_res_2299_;
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2300_, lean_object* v_category_2301_, lean_object* v_opts_2302_, lean_object* v_act_2303_, lean_object* v_decl_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_){
_start:
{
lean_object* v_res_2308_; 
v_res_2308_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2300_, v_category_2301_, v_opts_2302_, v_act_2303_, v_decl_2304_, v___y_2305_, v___y_2306_);
lean_dec(v___y_2306_);
lean_dec_ref(v___y_2305_);
lean_dec_ref(v_opts_2302_);
lean_dec_ref(v_category_2301_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2309_, lean_object* v_a_2310_){
_start:
{
if (lean_obj_tag(v_a_2309_) == 0)
{
lean_object* v___x_2311_; 
v___x_2311_ = l_List_reverse___redArg(v_a_2310_);
return v___x_2311_;
}
else
{
lean_object* v_head_2312_; lean_object* v_tail_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2322_; 
v_head_2312_ = lean_ctor_get(v_a_2309_, 0);
v_tail_2313_ = lean_ctor_get(v_a_2309_, 1);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2309_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2315_ = v_a_2309_;
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_tail_2313_);
lean_inc(v_head_2312_);
lean_dec(v_a_2309_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2322_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2319_; 
v___x_2317_ = l_Lean_MessageData_ofName(v_head_2312_);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 1, v_a_2310_);
lean_ctor_set(v___x_2315_, 0, v___x_2317_);
v___x_2319_ = v___x_2315_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_a_2310_);
v___x_2319_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
v_a_2309_ = v_tail_2313_;
v_a_2310_ = v___x_2319_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2325_ = l_Lean_stringToMessageData(v___x_2324_);
return v___x_2325_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2326_, lean_object* v_x_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2331_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2332_ = l_Lean_Declaration_getTopLevelNames(v_decl_2326_);
v___x_2333_ = lean_box(0);
v___x_2334_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2332_, v___x_2333_);
v___x_2335_ = l_Lean_MessageData_ofList(v___x_2334_);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2331_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2326_ = stack[0].m_obj;
lean_object* v_x_2327_ = stack[1].m_obj;
lean_object* v___y_2328_ = stack[2].m_obj;
lean_object* v___y_2329_ = stack[3].m_obj;
lean_object* v_res_2338_;
v_res_2338_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2326_, v_x_2327_, v___y_2328_, v___y_2329_);
stack->m_obj
 = v_res_2338_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2339_, lean_object* v_x_2340_, lean_object* v___y_2341_, lean_object* v___y_2342_, lean_object* v___y_2343_){
_start:
{
lean_object* v_res_2344_; 
v_res_2344_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2339_, v_x_2340_, v___y_2341_, v___y_2342_);
lean_dec(v___y_2342_);
lean_dec_ref(v___y_2341_);
lean_dec_ref(v_x_2340_);
return v_res_2344_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2345_, size_t v_i_2346_, lean_object* v_bs_2347_){
_start:
{
uint8_t v___x_2348_; 
v___x_2348_ = lean_usize_dec_lt(v_i_2346_, v_sz_2345_);
if (v___x_2348_ == 0)
{
return v_bs_2347_;
}
else
{
lean_object* v_v_2349_; lean_object* v_msg_2350_; lean_object* v___x_2351_; lean_object* v_bs_x27_2352_; size_t v___x_2353_; size_t v___x_2354_; lean_object* v___x_2355_; 
v_v_2349_ = lean_array_uget_borrowed(v_bs_2347_, v_i_2346_);
v_msg_2350_ = lean_ctor_get(v_v_2349_, 1);
lean_inc_ref(v_msg_2350_);
v___x_2351_ = lean_unsigned_to_nat(0u);
v_bs_x27_2352_ = lean_array_uset(v_bs_2347_, v_i_2346_, v___x_2351_);
v___x_2353_ = ((size_t)1ULL);
v___x_2354_ = lean_usize_add(v_i_2346_, v___x_2353_);
v___x_2355_ = lean_array_uset(v_bs_x27_2352_, v_i_2346_, v_msg_2350_);
v_i_2346_ = v___x_2354_;
v_bs_2347_ = v___x_2355_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2345_ = stack[0].m_num;
size_t v_i_2346_ = stack[1].m_num;
lean_object* v_bs_2347_ = stack[2].m_obj;
lean_object* v_res_2357_;
v_res_2357_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2345_, v_i_2346_, v_bs_2347_);
stack->m_obj
 = v_res_2357_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2358_, lean_object* v_i_2359_, lean_object* v_bs_2360_){
_start:
{
size_t v_sz_boxed_2361_; size_t v_i_boxed_2362_; lean_object* v_res_2363_; 
v_sz_boxed_2361_ = lean_unbox_usize(v_sz_2358_);
lean_dec(v_sz_2358_);
v_i_boxed_2362_ = lean_unbox_usize(v_i_2359_);
lean_dec(v_i_2359_);
v_res_2363_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2361_, v_i_boxed_2362_, v_bs_2360_);
return v_res_2363_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2364_, lean_object* v_data_2365_, lean_object* v_ref_2366_, lean_object* v_msg_2367_, lean_object* v___y_2368_, lean_object* v___y_2369_){
_start:
{
lean_object* v_toCold_2371_; lean_object* v_currRecDepth_2372_; lean_object* v_ref_2373_; uint16_t v_optionFlags_2374_; uint8_t v_suppressElabErrors_2375_; uint8_t v_isRecordingDeps_2376_; lean_object* v_ref_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v_traceState_2380_; lean_object* v_traces_2381_; lean_object* v___x_2382_; size_t v_sz_2383_; size_t v___x_2384_; lean_object* v___x_2385_; lean_object* v_msg_2386_; lean_object* v___x_2387_; lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2426_; 
v_toCold_2371_ = lean_ctor_get(v___y_2368_, 0);
v_currRecDepth_2372_ = lean_ctor_get(v___y_2368_, 1);
v_ref_2373_ = lean_ctor_get(v___y_2368_, 2);
v_optionFlags_2374_ = lean_ctor_get_uint16(v___y_2368_, sizeof(void*)*3);
v_suppressElabErrors_2375_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2376_ = lean_ctor_get_uint8(v___y_2368_, sizeof(void*)*3 + 3);
v_ref_2377_ = l_Lean_replaceRef(v_ref_2366_, v_ref_2373_);
lean_inc(v_currRecDepth_2372_);
lean_inc_ref(v_toCold_2371_);
v___x_2378_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2378_, 0, v_toCold_2371_);
lean_ctor_set(v___x_2378_, 1, v_currRecDepth_2372_);
lean_ctor_set(v___x_2378_, 2, v_ref_2377_);
lean_ctor_set_uint16(v___x_2378_, sizeof(void*)*3, v_optionFlags_2374_);
lean_ctor_set_uint8(v___x_2378_, sizeof(void*)*3 + 2, v_suppressElabErrors_2375_);
lean_ctor_set_uint8(v___x_2378_, sizeof(void*)*3 + 3, v_isRecordingDeps_2376_);
v___x_2379_ = lean_st_ref_get(v___y_2369_);
v_traceState_2380_ = lean_ctor_get(v___x_2379_, 4);
lean_inc_ref(v_traceState_2380_);
lean_dec(v___x_2379_);
v_traces_2381_ = lean_ctor_get(v_traceState_2380_, 0);
lean_inc_ref(v_traces_2381_);
lean_dec_ref(v_traceState_2380_);
v___x_2382_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2381_);
lean_dec_ref(v_traces_2381_);
v_sz_2383_ = lean_array_size(v___x_2382_);
v___x_2384_ = ((size_t)0ULL);
v___x_2385_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2383_, v___x_2384_, v___x_2382_);
v_msg_2386_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2386_, 0, v_data_2365_);
lean_ctor_set(v_msg_2386_, 1, v_msg_2367_);
lean_ctor_set(v_msg_2386_, 2, v___x_2385_);
v___x_2387_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2386_, v___x_2378_, v___y_2369_);
lean_dec_ref_known(v___x_2378_, 3);
v_a_2388_ = lean_ctor_get(v___x_2387_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2387_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2390_ = v___x_2387_;
v_isShared_2391_ = v_isSharedCheck_2426_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2387_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2426_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2392_; lean_object* v_traceState_2393_; lean_object* v_env_2394_; lean_object* v_nextMacroScope_2395_; lean_object* v_ngen_2396_; lean_object* v_auxDeclNGen_2397_; lean_object* v_cache_2398_; lean_object* v_recordedDeps_2399_; lean_object* v_messages_2400_; lean_object* v_infoState_2401_; lean_object* v_snapshotTasks_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2425_; 
v___x_2392_ = lean_st_ref_take(v___y_2369_);
v_traceState_2393_ = lean_ctor_get(v___x_2392_, 4);
v_env_2394_ = lean_ctor_get(v___x_2392_, 0);
v_nextMacroScope_2395_ = lean_ctor_get(v___x_2392_, 1);
v_ngen_2396_ = lean_ctor_get(v___x_2392_, 2);
v_auxDeclNGen_2397_ = lean_ctor_get(v___x_2392_, 3);
v_cache_2398_ = lean_ctor_get(v___x_2392_, 5);
v_recordedDeps_2399_ = lean_ctor_get(v___x_2392_, 6);
v_messages_2400_ = lean_ctor_get(v___x_2392_, 7);
v_infoState_2401_ = lean_ctor_get(v___x_2392_, 8);
v_snapshotTasks_2402_ = lean_ctor_get(v___x_2392_, 9);
v_isSharedCheck_2425_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2404_ = v___x_2392_;
v_isShared_2405_ = v_isSharedCheck_2425_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_snapshotTasks_2402_);
lean_inc(v_infoState_2401_);
lean_inc(v_messages_2400_);
lean_inc(v_recordedDeps_2399_);
lean_inc(v_cache_2398_);
lean_inc(v_traceState_2393_);
lean_inc(v_auxDeclNGen_2397_);
lean_inc(v_ngen_2396_);
lean_inc(v_nextMacroScope_2395_);
lean_inc(v_env_2394_);
lean_dec(v___x_2392_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2425_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
uint64_t v_tid_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2423_; 
v_tid_2406_ = lean_ctor_get_uint64(v_traceState_2393_, sizeof(void*)*1);
v_isSharedCheck_2423_ = !lean_is_exclusive(v_traceState_2393_);
if (v_isSharedCheck_2423_ == 0)
{
lean_object* v_unused_2424_; 
v_unused_2424_ = lean_ctor_get(v_traceState_2393_, 0);
lean_dec(v_unused_2424_);
v___x_2408_ = v_traceState_2393_;
v_isShared_2409_ = v_isSharedCheck_2423_;
goto v_resetjp_2407_;
}
else
{
lean_dec(v_traceState_2393_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2423_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2414_; 
v___x_2410_ = lean_box(0);
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v_ref_2366_);
lean_ctor_set(v___x_2411_, 1, v_a_2388_);
v___x_2412_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2364_, v___x_2411_);
if (v_isShared_2409_ == 0)
{
lean_ctor_set(v___x_2408_, 0, v___x_2412_);
v___x_2414_ = v___x_2408_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v___x_2412_);
lean_ctor_set_uint64(v_reuseFailAlloc_2422_, sizeof(void*)*1, v_tid_2406_);
v___x_2414_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2416_; 
if (v_isShared_2405_ == 0)
{
lean_ctor_set(v___x_2404_, 4, v___x_2414_);
v___x_2416_ = v___x_2404_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2421_; 
v_reuseFailAlloc_2421_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2421_, 0, v_env_2394_);
lean_ctor_set(v_reuseFailAlloc_2421_, 1, v_nextMacroScope_2395_);
lean_ctor_set(v_reuseFailAlloc_2421_, 2, v_ngen_2396_);
lean_ctor_set(v_reuseFailAlloc_2421_, 3, v_auxDeclNGen_2397_);
lean_ctor_set(v_reuseFailAlloc_2421_, 4, v___x_2414_);
lean_ctor_set(v_reuseFailAlloc_2421_, 5, v_cache_2398_);
lean_ctor_set(v_reuseFailAlloc_2421_, 6, v_recordedDeps_2399_);
lean_ctor_set(v_reuseFailAlloc_2421_, 7, v_messages_2400_);
lean_ctor_set(v_reuseFailAlloc_2421_, 8, v_infoState_2401_);
lean_ctor_set(v_reuseFailAlloc_2421_, 9, v_snapshotTasks_2402_);
v___x_2416_ = v_reuseFailAlloc_2421_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2417_ = lean_st_ref_put(v___y_2369_, v___x_2416_);
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2410_);
v___x_2419_ = v___x_2390_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2410_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_oldTraces_2364_ = stack[0].m_obj;
lean_object* v_data_2365_ = stack[1].m_obj;
lean_object* v_ref_2366_ = stack[2].m_obj;
lean_object* v_msg_2367_ = stack[3].m_obj;
lean_object* v___y_2368_ = stack[4].m_obj;
lean_object* v___y_2369_ = stack[5].m_obj;
lean_object* v_res_2427_;
v_res_2427_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2364_, v_data_2365_, v_ref_2366_, v_msg_2367_, v___y_2368_, v___y_2369_);
stack->m_obj
 = v_res_2427_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2428_, lean_object* v_data_2429_, lean_object* v_ref_2430_, lean_object* v_msg_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2428_, v_data_2429_, v_ref_2430_, v_msg_2431_, v___y_2432_, v___y_2433_);
lean_dec(v___y_2433_);
lean_dec_ref(v___y_2432_);
return v_res_2435_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2436_){
_start:
{
if (lean_obj_tag(v_x_2436_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
v_a_2438_ = lean_ctor_get(v_x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v_x_2436_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v_x_2436_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set_tag(v___x_2440_, 1);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
v_a_2446_ = lean_ctor_get(v_x_2436_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_x_2436_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v_x_2436_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v_x_2436_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set_tag(v___x_2448_, 0);
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2436_ = stack[0].m_obj;
lean_object* v_res_2454_;
v_res_2454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2436_);
stack->m_obj
 = v_res_2454_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2455_, lean_object* v___y_2456_){
_start:
{
lean_object* v_res_2457_; 
v_res_2457_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2455_);
return v_res_2457_;
}
}
uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2458_){
_start:
{
if (lean_obj_tag(v_e_2458_) == 0)
{
uint8_t v___x_2459_; 
v___x_2459_ = 2;
return v___x_2459_;
}
else
{
uint8_t v___x_2460_; 
v___x_2460_ = 0;
return v___x_2460_;
}
}
}
LEAN_EXPORT void l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_2458_ = stack[0].m_obj;
uint8_t v_res_2461_;
v_res_2461_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2458_);
stack->m_num = v_res_2461_;
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2462_){
_start:
{
uint8_t v_res_2463_; lean_object* v_r_2464_; 
v_res_2463_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2462_);
lean_dec_ref(v_e_2462_);
v_r_2464_ = lean_box(v_res_2463_);
return v_r_2464_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2465_; double v___x_2466_; 
v___x_2465_ = lean_unsigned_to_nat(0u);
v___x_2466_ = lean_float_of_nat(v___x_2465_);
return v___x_2466_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___x_2468_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2469_ = l_Lean_stringToMessageData(v___x_2468_);
return v___x_2469_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2470_; double v___x_2471_; 
v___x_2470_ = lean_unsigned_to_nat(1000u);
v___x_2471_ = lean_float_of_nat(v___x_2470_);
return v___x_2471_;
}
}
lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2472_, uint8_t v_collapsed_2473_, lean_object* v_tag_2474_, lean_object* v_opts_2475_, uint8_t v_clsEnabled_2476_, lean_object* v_oldTraces_2477_, lean_object* v_msg_2478_, lean_object* v_resStartStop_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_){
_start:
{
lean_object* v_fst_2483_; lean_object* v_snd_2484_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v_data_2488_; lean_object* v_fst_2491_; lean_object* v_snd_2492_; lean_object* v___x_2493_; uint8_t v___x_2494_; lean_object* v___y_2496_; lean_object* v_a_2497_; uint8_t v___y_2512_; double v___y_2544_; 
v_fst_2483_ = lean_ctor_get(v_resStartStop_2479_, 0);
lean_inc(v_fst_2483_);
v_snd_2484_ = lean_ctor_get(v_resStartStop_2479_, 1);
lean_inc(v_snd_2484_);
lean_dec_ref(v_resStartStop_2479_);
v_fst_2491_ = lean_ctor_get(v_snd_2484_, 0);
lean_inc(v_fst_2491_);
v_snd_2492_ = lean_ctor_get(v_snd_2484_, 1);
lean_inc(v_snd_2492_);
lean_dec(v_snd_2484_);
v___x_2493_ = l_Lean_trace_profiler;
v___x_2494_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2475_, v___x_2493_);
if (v___x_2494_ == 0)
{
v___y_2512_ = v___x_2494_;
goto v___jp_2511_;
}
else
{
lean_object* v___x_2549_; uint8_t v___x_2550_; 
v___x_2549_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2550_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2475_, v___x_2549_);
if (v___x_2550_ == 0)
{
lean_object* v___x_2551_; lean_object* v___x_2552_; double v___x_2553_; double v___x_2554_; double v___x_2555_; 
v___x_2551_ = l_Lean_trace_profiler_threshold;
v___x_2552_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2475_, v___x_2551_);
v___x_2553_ = lean_float_of_nat(v___x_2552_);
v___x_2554_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2555_ = lean_float_div(v___x_2553_, v___x_2554_);
v___y_2544_ = v___x_2555_;
goto v___jp_2543_;
}
else
{
lean_object* v___x_2556_; lean_object* v___x_2557_; double v___x_2558_; 
v___x_2556_ = l_Lean_trace_profiler_threshold;
v___x_2557_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2475_, v___x_2556_);
v___x_2558_ = lean_float_of_nat(v___x_2557_);
v___y_2544_ = v___x_2558_;
goto v___jp_2543_;
}
}
v___jp_2485_:
{
lean_object* v___x_2489_; 
lean_inc(v___y_2487_);
v___x_2489_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2477_, v_data_2488_, v___y_2487_, v___y_2486_, v___y_2480_, v___y_2481_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v___x_2490_; 
lean_dec_ref_known(v___x_2489_, 1);
v___x_2490_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2483_);
return v___x_2490_;
}
else
{
lean_dec(v_fst_2483_);
return v___x_2489_;
}
}
v___jp_2495_:
{
uint8_t v_result_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; double v___x_2501_; lean_object* v_data_2502_; 
v_result_2498_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2483_);
v___x_2499_ = lean_box(v_result_2498_);
v___x_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2499_);
v___x_2501_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2474_);
lean_inc_ref(v___x_2500_);
lean_inc(v_cls_2472_);
v_data_2502_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2502_, 0, v_cls_2472_);
lean_ctor_set(v_data_2502_, 1, v___x_2500_);
lean_ctor_set(v_data_2502_, 2, v_tag_2474_);
lean_ctor_set_float(v_data_2502_, sizeof(void*)*3, v___x_2501_);
lean_ctor_set_float(v_data_2502_, sizeof(void*)*3 + 8, v___x_2501_);
lean_ctor_set_uint8(v_data_2502_, sizeof(void*)*3 + 16, v_collapsed_2473_);
if (v___x_2494_ == 0)
{
lean_dec_ref_known(v___x_2500_, 1);
lean_dec(v_snd_2492_);
lean_dec(v_fst_2491_);
lean_dec_ref(v_tag_2474_);
lean_dec(v_cls_2472_);
v___y_2486_ = v_a_2497_;
v___y_2487_ = v___y_2496_;
v_data_2488_ = v_data_2502_;
goto v___jp_2485_;
}
else
{
lean_object* v_data_2503_; double v___x_2504_; double v___x_2505_; 
lean_dec_ref_known(v_data_2502_, 3);
v_data_2503_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2503_, 0, v_cls_2472_);
lean_ctor_set(v_data_2503_, 1, v___x_2500_);
lean_ctor_set(v_data_2503_, 2, v_tag_2474_);
v___x_2504_ = lean_unbox_float(v_fst_2491_);
lean_dec(v_fst_2491_);
lean_ctor_set_float(v_data_2503_, sizeof(void*)*3, v___x_2504_);
v___x_2505_ = lean_unbox_float(v_snd_2492_);
lean_dec(v_snd_2492_);
lean_ctor_set_float(v_data_2503_, sizeof(void*)*3 + 8, v___x_2505_);
lean_ctor_set_uint8(v_data_2503_, sizeof(void*)*3 + 16, v_collapsed_2473_);
v___y_2486_ = v_a_2497_;
v___y_2487_ = v___y_2496_;
v_data_2488_ = v_data_2503_;
goto v___jp_2485_;
}
}
v___jp_2506_:
{
lean_object* v_ref_2507_; lean_object* v___x_2508_; 
v_ref_2507_ = lean_ctor_get(v___y_2480_, 2);
lean_inc(v___y_2481_);
lean_inc_ref(v___y_2480_);
lean_inc(v_fst_2483_);
v___x_2508_ = lean_apply_4(v_msg_2478_, v_fst_2483_, v___y_2480_, v___y_2481_, lean_box(0));
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref_known(v___x_2508_, 1);
v___y_2496_ = v_ref_2507_;
v_a_2497_ = v_a_2509_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2510_; 
lean_dec_ref_known(v___x_2508_, 1);
v___x_2510_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2496_ = v_ref_2507_;
v_a_2497_ = v___x_2510_;
goto v___jp_2495_;
}
}
v___jp_2511_:
{
if (v_clsEnabled_2476_ == 0)
{
if (v___y_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v_traceState_2514_; lean_object* v_env_2515_; lean_object* v_nextMacroScope_2516_; lean_object* v_ngen_2517_; lean_object* v_auxDeclNGen_2518_; lean_object* v_cache_2519_; lean_object* v_recordedDeps_2520_; lean_object* v_messages_2521_; lean_object* v_infoState_2522_; lean_object* v_snapshotTasks_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_snd_2492_);
lean_dec(v_fst_2491_);
lean_dec_ref(v_msg_2478_);
lean_dec_ref(v_tag_2474_);
lean_dec(v_cls_2472_);
v___x_2513_ = lean_st_ref_take(v___y_2481_);
v_traceState_2514_ = lean_ctor_get(v___x_2513_, 4);
v_env_2515_ = lean_ctor_get(v___x_2513_, 0);
v_nextMacroScope_2516_ = lean_ctor_get(v___x_2513_, 1);
v_ngen_2517_ = lean_ctor_get(v___x_2513_, 2);
v_auxDeclNGen_2518_ = lean_ctor_get(v___x_2513_, 3);
v_cache_2519_ = lean_ctor_get(v___x_2513_, 5);
v_recordedDeps_2520_ = lean_ctor_get(v___x_2513_, 6);
v_messages_2521_ = lean_ctor_get(v___x_2513_, 7);
v_infoState_2522_ = lean_ctor_get(v___x_2513_, 8);
v_snapshotTasks_2523_ = lean_ctor_get(v___x_2513_, 9);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2525_ = v___x_2513_;
v_isShared_2526_ = v_isSharedCheck_2542_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_snapshotTasks_2523_);
lean_inc(v_infoState_2522_);
lean_inc(v_messages_2521_);
lean_inc(v_recordedDeps_2520_);
lean_inc(v_cache_2519_);
lean_inc(v_traceState_2514_);
lean_inc(v_auxDeclNGen_2518_);
lean_inc(v_ngen_2517_);
lean_inc(v_nextMacroScope_2516_);
lean_inc(v_env_2515_);
lean_dec(v___x_2513_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2542_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
uint64_t v_tid_2527_; lean_object* v_traces_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2541_; 
v_tid_2527_ = lean_ctor_get_uint64(v_traceState_2514_, sizeof(void*)*1);
v_traces_2528_ = lean_ctor_get(v_traceState_2514_, 0);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_traceState_2514_);
if (v_isSharedCheck_2541_ == 0)
{
v___x_2530_ = v_traceState_2514_;
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_traces_2528_);
lean_dec(v_traceState_2514_);
v___x_2530_ = lean_box(0);
v_isShared_2531_ = v_isSharedCheck_2541_;
goto v_resetjp_2529_;
}
v_resetjp_2529_:
{
lean_object* v___x_2532_; lean_object* v___x_2534_; 
v___x_2532_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2477_, v_traces_2528_);
lean_dec_ref(v_traces_2528_);
if (v_isShared_2531_ == 0)
{
lean_ctor_set(v___x_2530_, 0, v___x_2532_);
v___x_2534_ = v___x_2530_;
goto v_reusejp_2533_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v___x_2532_);
lean_ctor_set_uint64(v_reuseFailAlloc_2540_, sizeof(void*)*1, v_tid_2527_);
v___x_2534_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2533_;
}
v_reusejp_2533_:
{
lean_object* v___x_2536_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 4, v___x_2534_);
v___x_2536_ = v___x_2525_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v_env_2515_);
lean_ctor_set(v_reuseFailAlloc_2539_, 1, v_nextMacroScope_2516_);
lean_ctor_set(v_reuseFailAlloc_2539_, 2, v_ngen_2517_);
lean_ctor_set(v_reuseFailAlloc_2539_, 3, v_auxDeclNGen_2518_);
lean_ctor_set(v_reuseFailAlloc_2539_, 4, v___x_2534_);
lean_ctor_set(v_reuseFailAlloc_2539_, 5, v_cache_2519_);
lean_ctor_set(v_reuseFailAlloc_2539_, 6, v_recordedDeps_2520_);
lean_ctor_set(v_reuseFailAlloc_2539_, 7, v_messages_2521_);
lean_ctor_set(v_reuseFailAlloc_2539_, 8, v_infoState_2522_);
lean_ctor_set(v_reuseFailAlloc_2539_, 9, v_snapshotTasks_2523_);
v___x_2536_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = lean_st_ref_put(v___y_2481_, v___x_2536_);
v___x_2538_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2483_);
return v___x_2538_;
}
}
}
}
}
else
{
goto v___jp_2506_;
}
}
else
{
goto v___jp_2506_;
}
}
v___jp_2543_:
{
double v___x_2545_; double v___x_2546_; double v___x_2547_; uint8_t v___x_2548_; 
v___x_2545_ = lean_unbox_float(v_snd_2492_);
v___x_2546_ = lean_unbox_float(v_fst_2491_);
v___x_2547_ = lean_float_sub(v___x_2545_, v___x_2546_);
v___x_2548_ = lean_float_decLt(v___y_2544_, v___x_2547_);
v___y_2512_ = v___x_2548_;
goto v___jp_2511_;
}
}
}
LEAN_EXPORT void l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2472_ = stack[0].m_obj;
uint8_t v_collapsed_2473_ = stack[1].m_num;
lean_object* v_tag_2474_ = stack[2].m_obj;
lean_object* v_opts_2475_ = stack[3].m_obj;
uint8_t v_clsEnabled_2476_ = stack[4].m_num;
lean_object* v_oldTraces_2477_ = stack[5].m_obj;
lean_object* v_msg_2478_ = stack[6].m_obj;
lean_object* v_resStartStop_2479_ = stack[7].m_obj;
lean_object* v___y_2480_ = stack[8].m_obj;
lean_object* v___y_2481_ = stack[9].m_obj;
lean_object* v_res_2559_;
v_res_2559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2472_, v_collapsed_2473_, v_tag_2474_, v_opts_2475_, v_clsEnabled_2476_, v_oldTraces_2477_, v_msg_2478_, v_resStartStop_2479_, v___y_2480_, v___y_2481_);
stack->m_obj
 = v_res_2559_;
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2560_, lean_object* v_collapsed_2561_, lean_object* v_tag_2562_, lean_object* v_opts_2563_, lean_object* v_clsEnabled_2564_, lean_object* v_oldTraces_2565_, lean_object* v_msg_2566_, lean_object* v_resStartStop_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
uint8_t v_collapsed_boxed_2571_; uint8_t v_clsEnabled_boxed_2572_; lean_object* v_res_2573_; 
v_collapsed_boxed_2571_ = lean_unbox(v_collapsed_2561_);
v_clsEnabled_boxed_2572_ = lean_unbox(v_clsEnabled_2564_);
v_res_2573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2560_, v_collapsed_boxed_2571_, v_tag_2562_, v_opts_2563_, v_clsEnabled_boxed_2572_, v_oldTraces_2565_, v_msg_2566_, v_resStartStop_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec_ref(v_opts_2563_);
return v_res_2573_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2576_; double v___x_2577_; 
v___x_2576_ = lean_unsigned_to_nat(1000000000u);
v___x_2577_ = lean_float_of_nat(v___x_2576_);
return v___x_2577_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2578_, lean_object* v___x_2579_, uint8_t v___x_2580_, lean_object* v___x_2581_, lean_object* v___f_2582_, lean_object* v___y_2583_, lean_object* v___y_2584_){
_start:
{
lean_object* v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___y_2607_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v_toCold_2622_; lean_object* v_options_2623_; uint8_t v_hasTrace_2624_; 
v_toCold_2622_ = lean_ctor_get(v___y_2583_, 0);
v_options_2623_ = lean_ctor_get(v_toCold_2622_, 2);
v_hasTrace_2624_ = lean_ctor_get_uint8(v_options_2623_, sizeof(void*)*1);
if (v_hasTrace_2624_ == 0)
{
lean_object* v_cancelTk_x3f_2625_; lean_object* v___x_2626_; 
lean_dec_ref(v___f_2582_);
lean_dec_ref(v___x_2581_);
lean_dec(v___x_2579_);
v_cancelTk_x3f_2625_ = lean_ctor_get(v_toCold_2622_, 10);
lean_inc(v_decl_2578_);
v___x_2626_ = l_Lean_warnIfUsesSorry(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; lean_object* v_env_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec_ref_known(v___x_2626_, 1);
v___x_2627_ = lean_st_ref_get(v___y_2584_);
v_env_2628_ = lean_ctor_get(v___x_2627_, 0);
lean_inc_ref(v_env_2628_);
lean_dec(v___x_2627_);
v___x_2629_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2583_);
v___x_2630_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2628_, v___x_2629_, v_decl_2578_, v_cancelTk_x3f_2625_);
lean_dec_ref(v___x_2629_);
v___x_2631_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2630_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_object* v_a_2632_; lean_object* v___x_2633_; 
lean_dec(v_decl_2578_);
v_a_2632_ = lean_ctor_get(v___x_2631_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___x_2631_, 1);
v___x_2633_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2632_, v___y_2584_);
return v___x_2633_;
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
v_a_2634_ = lean_ctor_get(v___x_2631_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2631_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2631_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2631_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
lean_inc(v_a_2634_);
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
v___y_2618_ = v___x_2639_;
v_a_2619_ = v_a_2634_;
goto v___jp_2617_;
}
}
}
}
else
{
lean_dec(v_decl_2578_);
return v___x_2626_;
}
}
else
{
lean_object* v_cancelTk_x3f_2642_; lean_object* v_inheritedTraceOptions_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; lean_object* v___y_2648_; lean_object* v___y_2649_; lean_object* v_a_2650_; lean_object* v___y_2663_; lean_object* v___y_2664_; lean_object* v_a_2665_; lean_object* v___y_2668_; lean_object* v___y_2669_; lean_object* v_a_2670_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2679_; lean_object* v___y_2680_; lean_object* v___y_2681_; uint8_t v___y_2682_; lean_object* v___y_2685_; lean_object* v___y_2686_; lean_object* v_a_2687_; lean_object* v___y_2691_; lean_object* v___y_2692_; lean_object* v_a_2693_; lean_object* v___y_2703_; lean_object* v___y_2704_; lean_object* v_a_2705_; lean_object* v___y_2708_; lean_object* v___y_2709_; lean_object* v_a_2710_; lean_object* v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; uint8_t v___y_2722_; lean_object* v___y_2725_; lean_object* v___y_2726_; lean_object* v_a_2727_; 
v_cancelTk_x3f_2642_ = lean_ctor_get(v_toCold_2622_, 10);
v_inheritedTraceOptions_2643_ = lean_ctor_get(v_toCold_2622_, 11);
v___x_2644_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2579_);
v___x_2645_ = l_Lean_Name_append(v___x_2644_, v___x_2579_);
v___x_2646_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2643_, v_options_2623_, v___x_2645_);
lean_dec(v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = l_Lean_trace_profiler;
v___x_2758_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2623_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_object* v___x_2759_; 
lean_dec_ref(v___f_2582_);
lean_dec_ref(v___x_2581_);
lean_dec(v___x_2579_);
lean_inc(v_decl_2578_);
v___x_2759_ = l_Lean_warnIfUsesSorry(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2759_) == 0)
{
lean_object* v___x_2760_; lean_object* v_env_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
lean_dec_ref_known(v___x_2759_, 1);
v___x_2760_ = lean_st_ref_get(v___y_2584_);
v_env_2761_ = lean_ctor_get(v___x_2760_, 0);
lean_inc_ref(v_env_2761_);
lean_dec(v___x_2760_);
v___x_2762_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2583_);
v___x_2763_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2761_, v___x_2762_, v_decl_2578_, v_cancelTk_x3f_2642_);
lean_dec_ref(v___x_2762_);
v___x_2764_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2763_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2764_) == 0)
{
lean_object* v_a_2765_; lean_object* v___x_2766_; 
lean_dec(v_decl_2578_);
v_a_2765_ = lean_ctor_get(v___x_2764_, 0);
lean_inc(v_a_2765_);
lean_dec_ref_known(v___x_2764_, 1);
v___x_2766_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2765_, v___y_2584_);
return v___x_2766_;
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
v_a_2767_ = lean_ctor_get(v___x_2764_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2764_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2764_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
lean_inc(v_a_2767_);
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
v___y_2600_ = v___x_2772_;
v_a_2601_ = v_a_2767_;
goto v___jp_2599_;
}
}
}
}
else
{
lean_dec(v_decl_2578_);
return v___x_2759_;
}
}
else
{
goto v___jp_2730_;
}
}
else
{
goto v___jp_2730_;
}
v___jp_2647_:
{
lean_object* v___x_2651_; double v___x_2652_; double v___x_2653_; double v___x_2654_; double v___x_2655_; double v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2651_ = lean_io_mono_nanos_now();
v___x_2652_ = lean_float_of_nat(v___y_2649_);
v___x_2653_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2654_ = lean_float_div(v___x_2652_, v___x_2653_);
v___x_2655_ = lean_float_of_nat(v___x_2651_);
v___x_2656_ = lean_float_div(v___x_2655_, v___x_2653_);
v___x_2657_ = lean_box_float(v___x_2654_);
v___x_2658_ = lean_box_float(v___x_2656_);
v___x_2659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2659_, 0, v___x_2657_);
lean_ctor_set(v___x_2659_, 1, v___x_2658_);
v___x_2660_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2660_, 0, v_a_2650_);
lean_ctor_set(v___x_2660_, 1, v___x_2659_);
v___x_2661_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2579_, v___x_2580_, v___x_2581_, v_options_2623_, v___x_2646_, v___y_2648_, v___f_2582_, v___x_2660_, v___y_2583_, v___y_2584_);
return v___x_2661_;
}
v___jp_2662_:
{
lean_object* v___x_2666_; 
v___x_2666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2666_, 0, v_a_2665_);
v___y_2648_ = v___y_2663_;
v___y_2649_ = v___y_2664_;
v_a_2650_ = v___x_2666_;
goto v___jp_2647_;
}
v___jp_2667_:
{
lean_object* v___x_2671_; 
v___x_2671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2671_, 0, v_a_2670_);
v___y_2648_ = v___y_2668_;
v___y_2649_ = v___y_2669_;
v_a_2650_ = v___x_2671_;
goto v___jp_2647_;
}
v___jp_2672_:
{
if (lean_obj_tag(v___y_2675_) == 0)
{
lean_object* v_a_2676_; 
v_a_2676_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___y_2675_, 1);
v___y_2668_ = v___y_2673_;
v___y_2669_ = v___y_2674_;
v_a_2670_ = v_a_2676_;
goto v___jp_2667_;
}
else
{
lean_object* v_a_2677_; 
v_a_2677_ = lean_ctor_get(v___y_2675_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___y_2675_, 1);
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v_a_2665_ = v_a_2677_;
goto v___jp_2662_;
}
}
v___jp_2678_:
{
if (v___y_2682_ == 0)
{
lean_object* v___x_2683_; 
v___x_2683_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2683_) == 0)
{
lean_dec_ref_known(v___x_2683_, 1);
v___y_2663_ = v___y_2679_;
v___y_2664_ = v___y_2681_;
v_a_2665_ = v___y_2680_;
goto v___jp_2662_;
}
else
{
lean_dec_ref(v___y_2680_);
v___y_2673_ = v___y_2679_;
v___y_2674_ = v___y_2681_;
v___y_2675_ = v___x_2683_;
goto v___jp_2672_;
}
}
else
{
lean_dec(v_decl_2578_);
v___y_2663_ = v___y_2679_;
v___y_2664_ = v___y_2681_;
v_a_2665_ = v___y_2680_;
goto v___jp_2662_;
}
}
v___jp_2684_:
{
uint8_t v___x_2688_; 
v___x_2688_ = l_Lean_Exception_isInterrupt(v_a_2687_);
if (v___x_2688_ == 0)
{
uint8_t v___x_2689_; 
lean_inc_ref(v_a_2687_);
v___x_2689_ = l_Lean_Exception_isRuntime(v_a_2687_);
v___y_2679_ = v___y_2685_;
v___y_2680_ = v_a_2687_;
v___y_2681_ = v___y_2686_;
v___y_2682_ = v___x_2689_;
goto v___jp_2678_;
}
else
{
v___y_2679_ = v___y_2685_;
v___y_2680_ = v_a_2687_;
v___y_2681_ = v___y_2686_;
v___y_2682_ = v___x_2688_;
goto v___jp_2678_;
}
}
v___jp_2690_:
{
lean_object* v___x_2694_; double v___x_2695_; double v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2694_ = lean_io_get_num_heartbeats();
v___x_2695_ = lean_float_of_nat(v___y_2692_);
v___x_2696_ = lean_float_of_nat(v___x_2694_);
v___x_2697_ = lean_box_float(v___x_2695_);
v___x_2698_ = lean_box_float(v___x_2696_);
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2697_);
lean_ctor_set(v___x_2699_, 1, v___x_2698_);
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v_a_2693_);
lean_ctor_set(v___x_2700_, 1, v___x_2699_);
v___x_2701_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2579_, v___x_2580_, v___x_2581_, v_options_2623_, v___x_2646_, v___y_2691_, v___f_2582_, v___x_2700_, v___y_2583_, v___y_2584_);
return v___x_2701_;
}
v___jp_2702_:
{
lean_object* v___x_2706_; 
v___x_2706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2706_, 0, v_a_2705_);
v___y_2691_ = v___y_2703_;
v___y_2692_ = v___y_2704_;
v_a_2693_ = v___x_2706_;
goto v___jp_2690_;
}
v___jp_2707_:
{
lean_object* v___x_2711_; 
v___x_2711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2711_, 0, v_a_2710_);
v___y_2691_ = v___y_2708_;
v___y_2692_ = v___y_2709_;
v_a_2693_ = v___x_2711_;
goto v___jp_2690_;
}
v___jp_2712_:
{
if (lean_obj_tag(v___y_2715_) == 0)
{
lean_object* v_a_2716_; 
v_a_2716_ = lean_ctor_get(v___y_2715_, 0);
lean_inc(v_a_2716_);
lean_dec_ref_known(v___y_2715_, 1);
v___y_2708_ = v___y_2713_;
v___y_2709_ = v___y_2714_;
v_a_2710_ = v_a_2716_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2717_; 
v_a_2717_ = lean_ctor_get(v___y_2715_, 0);
lean_inc(v_a_2717_);
lean_dec_ref_known(v___y_2715_, 1);
v___y_2703_ = v___y_2713_;
v___y_2704_ = v___y_2714_;
v_a_2705_ = v_a_2717_;
goto v___jp_2702_;
}
}
v___jp_2718_:
{
if (v___y_2722_ == 0)
{
lean_object* v___x_2723_; 
v___x_2723_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_dec_ref_known(v___x_2723_, 1);
v___y_2703_ = v___y_2720_;
v___y_2704_ = v___y_2721_;
v_a_2705_ = v___y_2719_;
goto v___jp_2702_;
}
else
{
lean_dec_ref(v___y_2719_);
v___y_2713_ = v___y_2720_;
v___y_2714_ = v___y_2721_;
v___y_2715_ = v___x_2723_;
goto v___jp_2712_;
}
}
else
{
lean_dec(v_decl_2578_);
v___y_2703_ = v___y_2720_;
v___y_2704_ = v___y_2721_;
v_a_2705_ = v___y_2719_;
goto v___jp_2702_;
}
}
v___jp_2724_:
{
uint8_t v___x_2728_; 
v___x_2728_ = l_Lean_Exception_isInterrupt(v_a_2727_);
if (v___x_2728_ == 0)
{
uint8_t v___x_2729_; 
lean_inc_ref(v_a_2727_);
v___x_2729_ = l_Lean_Exception_isRuntime(v_a_2727_);
v___y_2719_ = v_a_2727_;
v___y_2720_ = v___y_2725_;
v___y_2721_ = v___y_2726_;
v___y_2722_ = v___x_2729_;
goto v___jp_2718_;
}
else
{
v___y_2719_ = v_a_2727_;
v___y_2720_ = v___y_2725_;
v___y_2721_ = v___y_2726_;
v___y_2722_ = v___x_2728_;
goto v___jp_2718_;
}
}
v___jp_2730_:
{
lean_object* v___x_2731_; lean_object* v_a_2732_; lean_object* v___x_2733_; uint8_t v___x_2734_; 
v___x_2731_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2584_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref(v___x_2731_);
v___x_2733_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2734_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2623_, v___x_2733_);
if (v___x_2734_ == 0)
{
lean_object* v___x_2735_; lean_object* v___x_2736_; 
v___x_2735_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2578_);
v___x_2736_ = l_Lean_warnIfUsesSorry(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v___x_2737_; lean_object* v_env_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; 
lean_dec_ref_known(v___x_2736_, 1);
v___x_2737_ = lean_st_ref_get(v___y_2584_);
v_env_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_ref(v_env_2738_);
lean_dec(v___x_2737_);
v___x_2739_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2583_);
v___x_2740_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2738_, v___x_2739_, v_decl_2578_, v_cancelTk_x3f_2642_);
lean_dec_ref(v___x_2739_);
v___x_2741_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2740_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v___x_2743_; lean_object* v_a_2744_; 
lean_dec(v_decl_2578_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2741_, 1);
v___x_2743_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2742_, v___y_2584_);
v_a_2744_ = lean_ctor_get(v___x_2743_, 0);
lean_inc(v_a_2744_);
lean_dec_ref(v___x_2743_);
v___y_2668_ = v_a_2732_;
v___y_2669_ = v___x_2735_;
v_a_2670_ = v_a_2744_;
goto v___jp_2667_;
}
else
{
lean_object* v_a_2745_; 
v_a_2745_ = lean_ctor_get(v___x_2741_, 0);
lean_inc(v_a_2745_);
lean_dec_ref_known(v___x_2741_, 1);
v___y_2685_ = v_a_2732_;
v___y_2686_ = v___x_2735_;
v_a_2687_ = v_a_2745_;
goto v___jp_2684_;
}
}
else
{
lean_dec(v_decl_2578_);
v___y_2673_ = v_a_2732_;
v___y_2674_ = v___x_2735_;
v___y_2675_ = v___x_2736_;
goto v___jp_2672_;
}
}
else
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2578_);
v___x_2747_ = l_Lean_warnIfUsesSorry(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v___x_2748_; lean_object* v_env_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; 
lean_dec_ref_known(v___x_2747_, 1);
v___x_2748_ = lean_st_ref_get(v___y_2584_);
v_env_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc_ref(v_env_2749_);
lean_dec(v___x_2748_);
v___x_2750_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2583_);
v___x_2751_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2749_, v___x_2750_, v_decl_2578_, v_cancelTk_x3f_2642_);
lean_dec_ref(v___x_2750_);
v___x_2752_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2751_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v_a_2753_; lean_object* v___x_2754_; lean_object* v_a_2755_; 
lean_dec(v_decl_2578_);
v_a_2753_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2753_);
lean_dec_ref_known(v___x_2752_, 1);
v___x_2754_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2753_, v___y_2584_);
v_a_2755_ = lean_ctor_get(v___x_2754_, 0);
lean_inc(v_a_2755_);
lean_dec_ref(v___x_2754_);
v___y_2708_ = v_a_2732_;
v___y_2709_ = v___x_2746_;
v_a_2710_ = v_a_2755_;
goto v___jp_2707_;
}
else
{
lean_object* v_a_2756_; 
v_a_2756_ = lean_ctor_get(v___x_2752_, 0);
lean_inc(v_a_2756_);
lean_dec_ref_known(v___x_2752_, 1);
v___y_2725_ = v_a_2732_;
v___y_2726_ = v___x_2746_;
v_a_2727_ = v_a_2756_;
goto v___jp_2724_;
}
}
else
{
lean_dec(v_decl_2578_);
v___y_2713_ = v_a_2732_;
v___y_2714_ = v___x_2746_;
v___y_2715_ = v___x_2747_;
goto v___jp_2712_;
}
}
}
}
v___jp_2586_:
{
if (v___y_2589_ == 0)
{
lean_object* v___x_2590_; 
lean_dec_ref(v___y_2587_);
v___x_2590_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v___x_2590_, 0);
lean_dec(v_unused_2598_);
v___x_2592_ = v___x_2590_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_dec(v___x_2590_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
lean_ctor_set_tag(v___x_2592_, 1);
lean_ctor_set(v___x_2592_, 0, v___y_2588_);
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v___y_2588_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
else
{
lean_dec_ref(v___y_2588_);
return v___x_2590_;
}
}
else
{
lean_dec_ref(v___y_2588_);
lean_dec(v_decl_2578_);
return v___y_2587_;
}
}
v___jp_2599_:
{
uint8_t v___x_2602_; 
v___x_2602_ = l_Lean_Exception_isInterrupt(v_a_2601_);
if (v___x_2602_ == 0)
{
uint8_t v___x_2603_; 
lean_inc_ref(v_a_2601_);
v___x_2603_ = l_Lean_Exception_isRuntime(v_a_2601_);
v___y_2587_ = v___y_2600_;
v___y_2588_ = v_a_2601_;
v___y_2589_ = v___x_2603_;
goto v___jp_2586_;
}
else
{
v___y_2587_ = v___y_2600_;
v___y_2588_ = v_a_2601_;
v___y_2589_ = v___x_2602_;
goto v___jp_2586_;
}
}
v___jp_2604_:
{
if (v___y_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_dec_ref(v___y_2606_);
v___x_2608_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2578_, v___y_2583_, v___y_2584_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2615_; 
v_isSharedCheck_2615_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; 
v_unused_2616_ = lean_ctor_get(v___x_2608_, 0);
lean_dec(v_unused_2616_);
v___x_2610_ = v___x_2608_;
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
else
{
lean_dec(v___x_2608_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2615_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v___x_2613_; 
if (v_isShared_2611_ == 0)
{
lean_ctor_set_tag(v___x_2610_, 1);
lean_ctor_set(v___x_2610_, 0, v___y_2605_);
v___x_2613_ = v___x_2610_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v___y_2605_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
else
{
lean_dec_ref(v___y_2605_);
return v___x_2608_;
}
}
else
{
lean_dec_ref(v___y_2605_);
lean_dec(v_decl_2578_);
return v___y_2606_;
}
}
v___jp_2617_:
{
uint8_t v___x_2620_; 
v___x_2620_ = l_Lean_Exception_isInterrupt(v_a_2619_);
if (v___x_2620_ == 0)
{
uint8_t v___x_2621_; 
lean_inc_ref(v_a_2619_);
v___x_2621_ = l_Lean_Exception_isRuntime(v_a_2619_);
v___y_2605_ = v_a_2619_;
v___y_2606_ = v___y_2618_;
v___y_2607_ = v___x_2621_;
goto v___jp_2604_;
}
else
{
v___y_2605_ = v_a_2619_;
v___y_2606_ = v___y_2618_;
v___y_2607_ = v___x_2620_;
goto v___jp_2604_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2578_ = stack[0].m_obj;
lean_object* v___x_2579_ = stack[1].m_obj;
uint8_t v___x_2580_ = stack[2].m_num;
lean_object* v___x_2581_ = stack[3].m_obj;
lean_object* v___f_2582_ = stack[4].m_obj;
lean_object* v___y_2583_ = stack[5].m_obj;
lean_object* v___y_2584_ = stack[6].m_obj;
lean_object* v_res_2775_;
v_res_2775_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2578_, v___x_2579_, v___x_2580_, v___x_2581_, v___f_2582_, v___y_2583_, v___y_2584_);
stack->m_obj
 = v_res_2775_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2776_, lean_object* v___x_2777_, lean_object* v___x_2778_, lean_object* v___x_2779_, lean_object* v___f_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_){
_start:
{
uint8_t v___x_8176__boxed_2784_; lean_object* v_res_2785_; 
v___x_8176__boxed_2784_ = lean_unbox(v___x_2778_);
v_res_2785_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2776_, v___x_2777_, v___x_8176__boxed_2784_, v___x_2779_, v___f_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2785_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_){
_start:
{
lean_object* v___f_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___f_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; 
lean_inc(v_decl_2790_);
v___f_2794_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2794_, 0, v_decl_2790_);
v___x_2795_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2791_);
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
lean_closure_set(v___f_2801_, 4, v___f_2794_);
v___x_2802_ = lean_box(0);
v___x_2803_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2796_, v___x_2795_, v___f_2801_, v___x_2802_, v_a_2791_, v_a_2792_);
lean_dec_ref(v___x_2795_);
return v___x_2803_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2790_ = stack[0].m_obj;
lean_object* v_a_2791_ = stack[1].m_obj;
lean_object* v_a_2792_ = stack[2].m_obj;
lean_object* v_res_2804_;
v_res_2804_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2790_, v_a_2791_, v_a_2792_);
stack->m_obj
 = v_res_2804_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2805_, v_a_2806_, v_a_2807_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2809_;
}
}
lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; 
v___x_2815_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2811_);
return v___x_2815_;
}
}
LEAN_EXPORT void l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2811_ = stack[1].m_obj;
lean_object* v___y_2812_ = stack[2].m_obj;
lean_object* v___y_2813_ = stack[3].m_obj;
lean_object* v_res_2816_;
v_res_2816_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_box(0), v_x_2811_, v___y_2812_, v___y_2813_);
stack->m_obj
 = v_res_2816_;
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2817_, lean_object* v_x_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2817_, v_x_2818_, v___y_2819_, v___y_2820_);
lean_dec(v___y_2820_);
lean_dec_ref(v___y_2819_);
return v_res_2822_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2823_, lean_object* v_a_2824_, lean_object* v_ref_2825_, lean_object* v_a_x3f_2826_){
_start:
{
lean_object* v___x_2828_; lean_object* v_env_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_st_ref_get(v___y_2823_);
v_env_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc_ref(v_env_2829_);
lean_dec(v___x_2828_);
v___x_2830_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2824_, v_env_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_dec(v_ref_2825_);
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2830_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2830_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
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
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2850_; 
v_a_2839_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2841_ = v___x_2830_;
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2830_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2850_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2848_; 
v___x_2843_ = lean_io_error_to_string(v_a_2839_);
v___x_2844_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2843_);
v___x_2845_ = l_Lean_MessageData_ofFormat(v___x_2844_);
v___x_2846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2846_, 0, v_ref_2825_);
lean_ctor_set(v___x_2846_, 1, v___x_2845_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2846_);
v___x_2848_ = v___x_2841_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v___x_2846_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2823_ = stack[0].m_obj;
lean_object* v_a_2824_ = stack[1].m_obj;
lean_object* v_ref_2825_ = stack[2].m_obj;
lean_object* v_a_x3f_2826_ = stack[3].m_obj;
lean_object* v_res_2851_;
v_res_2851_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2823_, v_a_2824_, v_ref_2825_, v_a_x3f_2826_);
stack->m_obj
 = v_res_2851_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2852_, lean_object* v_a_2853_, lean_object* v_ref_2854_, lean_object* v_a_x3f_2855_, lean_object* v___y_2856_){
_start:
{
lean_object* v_res_2857_; 
v_res_2857_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2852_, v_a_2853_, v_ref_2854_, v_a_x3f_2855_);
lean_dec(v_a_x3f_2855_);
lean_dec(v___y_2852_);
return v_res_2857_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2858_, lean_object* v___y_2859_, lean_object* v_a_2860_, lean_object* v_a_x3f_2861_){
_start:
{
lean_object* v___x_2863_; lean_object* v_env_2864_; lean_object* v_ref_2865_; lean_object* v___x_2866_; 
v___x_2863_ = lean_st_ref_get(v___y_2858_);
v_env_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc_ref(v_env_2864_);
lean_dec(v___x_2863_);
v_ref_2865_ = lean_ctor_get(v___y_2859_, 2);
v___x_2866_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2860_, v_env_2864_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2866_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2866_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
else
{
lean_object* v_a_2875_; lean_object* v___x_2877_; uint8_t v_isShared_2878_; uint8_t v_isSharedCheck_2886_; 
v_a_2875_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2877_ = v___x_2866_;
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
else
{
lean_inc(v_a_2875_);
lean_dec(v___x_2866_);
v___x_2877_ = lean_box(0);
v_isShared_2878_ = v_isSharedCheck_2886_;
goto v_resetjp_2876_;
}
v_resetjp_2876_:
{
lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2884_; 
v___x_2879_ = lean_io_error_to_string(v_a_2875_);
v___x_2880_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2880_, 0, v___x_2879_);
v___x_2881_ = l_Lean_MessageData_ofFormat(v___x_2880_);
lean_inc(v_ref_2865_);
v___x_2882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2882_, 0, v_ref_2865_);
lean_ctor_set(v___x_2882_, 1, v___x_2881_);
if (v_isShared_2878_ == 0)
{
lean_ctor_set(v___x_2877_, 0, v___x_2882_);
v___x_2884_ = v___x_2877_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v___y_2858_ = stack[0].m_obj;
lean_object* v___y_2859_ = stack[1].m_obj;
lean_object* v_a_2860_ = stack[2].m_obj;
lean_object* v_a_x3f_2861_ = stack[3].m_obj;
lean_object* v_res_2887_;
v_res_2887_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2858_, v___y_2859_, v_a_2860_, v_a_x3f_2861_);
stack->m_obj
 = v_res_2887_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v_a_2890_, lean_object* v_a_x3f_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2888_, v___y_2889_, v_a_2890_, v_a_x3f_2891_);
lean_dec(v_a_x3f_2891_);
lean_dec_ref(v___y_2889_);
lean_dec(v___y_2888_);
return v_res_2893_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2894_, lean_object* v_asyncEnv_2895_, lean_object* v_decl_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v___x_2901_; lean_object* v_r_2902_; 
v___x_2901_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2895_, v___y_2899_);
lean_dec_ref(v___x_2901_);
v_r_2902_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2896_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v_r_2902_) == 0)
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2919_; 
v_a_2903_ = lean_ctor_get(v_r_2902_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v_r_2902_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2905_ = v_r_2902_;
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v_r_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2919_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
lean_inc(v_a_2903_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 1);
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; 
v___x_2909_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2899_, v___y_2898_, v_a_2894_, v___x_2908_);
lean_dec_ref(v___x_2908_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2916_ == 0)
{
lean_object* v_unused_2917_; 
v_unused_2917_ = lean_ctor_get(v___x_2909_, 0);
lean_dec(v_unused_2917_);
v___x_2911_ = v___x_2909_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_dec(v___x_2909_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
lean_ctor_set(v___x_2911_, 0, v_a_2903_);
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2903_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
else
{
lean_dec(v_a_2903_);
return v___x_2909_;
}
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2921_; lean_object* v___x_2922_; 
v_a_2920_ = lean_ctor_get(v_r_2902_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v_r_2902_, 1);
v___x_2921_ = lean_box(0);
v___x_2922_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2899_, v___y_2898_, v_a_2894_, v___x_2921_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; 
v_unused_2930_ = lean_ctor_get(v___x_2922_, 0);
lean_dec(v_unused_2930_);
v___x_2924_ = v___x_2922_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_dec(v___x_2922_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
lean_ctor_set_tag(v___x_2924_, 1);
lean_ctor_set(v___x_2924_, 0, v_a_2920_);
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2920_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
else
{
lean_dec(v_a_2920_);
return v___x_2922_;
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2894_ = stack[0].m_obj;
lean_object* v_asyncEnv_2895_ = stack[1].m_obj;
lean_object* v_decl_2896_ = stack[2].m_obj;
lean_object* v_x_2897_ = stack[3].m_obj;
lean_object* v___y_2898_ = stack[4].m_obj;
lean_object* v___y_2899_ = stack[5].m_obj;
lean_object* v_res_2931_;
v_res_2931_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2894_, v_asyncEnv_2895_, v_decl_2896_, v_x_2897_, v___y_2898_, v___y_2899_);
stack->m_obj
 = v_res_2931_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2932_, lean_object* v_asyncEnv_2933_, lean_object* v_decl_2934_, lean_object* v_x_2935_, lean_object* v___y_2936_, lean_object* v___y_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_res_2939_; 
v_res_2939_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2932_, v_asyncEnv_2933_, v_decl_2934_, v_x_2935_, v___y_2936_, v___y_2937_);
lean_dec(v___y_2937_);
lean_dec_ref(v___y_2936_);
lean_dec_ref(v_x_2935_);
return v_res_2939_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2943_, lean_object* v_x_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2948_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2949_ = l_Lean_Declaration_getNames(v_decl_2943_);
v___x_2950_ = lean_box(0);
v___x_2951_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2949_, v___x_2950_);
v___x_2952_ = l_Lean_MessageData_ofList(v___x_2951_);
v___x_2953_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2953_, 0, v___x_2948_);
lean_ctor_set(v___x_2953_, 1, v___x_2952_);
v___x_2954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_2943_ = stack[0].m_obj;
lean_object* v_x_2944_ = stack[1].m_obj;
lean_object* v___y_2945_ = stack[2].m_obj;
lean_object* v___y_2946_ = stack[3].m_obj;
lean_object* v_res_2955_;
v_res_2955_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2943_, v_x_2944_, v___y_2945_, v___y_2946_);
stack->m_obj
 = v_res_2955_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2956_, v_x_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec_ref(v_x_2957_);
return v_res_2961_;
}
}
lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2964_, lean_object* v_msg_2965_, lean_object* v___y_2966_, lean_object* v___y_2967_){
_start:
{
lean_object* v_ref_2969_; lean_object* v___x_2970_; lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3016_; 
v_ref_2969_ = lean_ctor_get(v___y_2966_, 2);
v___x_2970_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2965_, v___y_2966_, v___y_2967_);
v_a_2971_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2973_ = v___x_2970_;
v_isShared_2974_ = v_isSharedCheck_3016_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3016_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2975_; lean_object* v_traceState_2976_; lean_object* v_env_2977_; lean_object* v_nextMacroScope_2978_; lean_object* v_ngen_2979_; lean_object* v_auxDeclNGen_2980_; lean_object* v_cache_2981_; lean_object* v_recordedDeps_2982_; lean_object* v_messages_2983_; lean_object* v_infoState_2984_; lean_object* v_snapshotTasks_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3015_; 
v___x_2975_ = lean_st_ref_take(v___y_2967_);
v_traceState_2976_ = lean_ctor_get(v___x_2975_, 4);
v_env_2977_ = lean_ctor_get(v___x_2975_, 0);
v_nextMacroScope_2978_ = lean_ctor_get(v___x_2975_, 1);
v_ngen_2979_ = lean_ctor_get(v___x_2975_, 2);
v_auxDeclNGen_2980_ = lean_ctor_get(v___x_2975_, 3);
v_cache_2981_ = lean_ctor_get(v___x_2975_, 5);
v_recordedDeps_2982_ = lean_ctor_get(v___x_2975_, 6);
v_messages_2983_ = lean_ctor_get(v___x_2975_, 7);
v_infoState_2984_ = lean_ctor_get(v___x_2975_, 8);
v_snapshotTasks_2985_ = lean_ctor_get(v___x_2975_, 9);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2975_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2987_ = v___x_2975_;
v_isShared_2988_ = v_isSharedCheck_3015_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_snapshotTasks_2985_);
lean_inc(v_infoState_2984_);
lean_inc(v_messages_2983_);
lean_inc(v_recordedDeps_2982_);
lean_inc(v_cache_2981_);
lean_inc(v_traceState_2976_);
lean_inc(v_auxDeclNGen_2980_);
lean_inc(v_ngen_2979_);
lean_inc(v_nextMacroScope_2978_);
lean_inc(v_env_2977_);
lean_dec(v___x_2975_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3015_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint64_t v_tid_2989_; lean_object* v_traces_2990_; lean_object* v___x_2992_; uint8_t v_isShared_2993_; uint8_t v_isSharedCheck_3014_; 
v_tid_2989_ = lean_ctor_get_uint64(v_traceState_2976_, sizeof(void*)*1);
v_traces_2990_ = lean_ctor_get(v_traceState_2976_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v_traceState_2976_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_2992_ = v_traceState_2976_;
v_isShared_2993_ = v_isSharedCheck_3014_;
goto v_resetjp_2991_;
}
else
{
lean_inc(v_traces_2990_);
lean_dec(v_traceState_2976_);
v___x_2992_ = lean_box(0);
v_isShared_2993_ = v_isSharedCheck_3014_;
goto v_resetjp_2991_;
}
v_resetjp_2991_:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; double v___x_2996_; uint8_t v___x_2997_; lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v___x_2994_ = lean_box(0);
v___x_2995_ = lean_box(0);
v___x_2996_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2997_ = 0;
v___x_2998_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2999_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2999_, 0, v_cls_2964_);
lean_ctor_set(v___x_2999_, 1, v___x_2995_);
lean_ctor_set(v___x_2999_, 2, v___x_2998_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3, v___x_2996_);
lean_ctor_set_float(v___x_2999_, sizeof(void*)*3 + 8, v___x_2996_);
lean_ctor_set_uint8(v___x_2999_, sizeof(void*)*3 + 16, v___x_2997_);
v___x_3000_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_3001_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3001_, 0, v___x_2999_);
lean_ctor_set(v___x_3001_, 1, v_a_2971_);
lean_ctor_set(v___x_3001_, 2, v___x_3000_);
lean_inc(v_ref_2969_);
v___x_3002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3002_, 0, v_ref_2969_);
lean_ctor_set(v___x_3002_, 1, v___x_3001_);
v___x_3003_ = l_Lean_PersistentArray_push___redArg(v_traces_2990_, v___x_3002_);
if (v_isShared_2993_ == 0)
{
lean_ctor_set(v___x_2992_, 0, v___x_3003_);
v___x_3005_ = v___x_2992_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v___x_3003_);
lean_ctor_set_uint64(v_reuseFailAlloc_3013_, sizeof(void*)*1, v_tid_2989_);
v___x_3005_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3007_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 4, v___x_3005_);
v___x_3007_ = v___x_2987_;
goto v_reusejp_3006_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_env_2977_);
lean_ctor_set(v_reuseFailAlloc_3012_, 1, v_nextMacroScope_2978_);
lean_ctor_set(v_reuseFailAlloc_3012_, 2, v_ngen_2979_);
lean_ctor_set(v_reuseFailAlloc_3012_, 3, v_auxDeclNGen_2980_);
lean_ctor_set(v_reuseFailAlloc_3012_, 4, v___x_3005_);
lean_ctor_set(v_reuseFailAlloc_3012_, 5, v_cache_2981_);
lean_ctor_set(v_reuseFailAlloc_3012_, 6, v_recordedDeps_2982_);
lean_ctor_set(v_reuseFailAlloc_3012_, 7, v_messages_2983_);
lean_ctor_set(v_reuseFailAlloc_3012_, 8, v_infoState_2984_);
lean_ctor_set(v_reuseFailAlloc_3012_, 9, v_snapshotTasks_2985_);
v___x_3007_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3006_;
}
v_reusejp_3006_:
{
lean_object* v___x_3008_; lean_object* v___x_3010_; 
v___x_3008_ = lean_st_ref_put(v___y_2967_, v___x_3007_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2994_);
v___x_3010_ = v___x_2973_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v___x_2994_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_2964_ = stack[0].m_obj;
lean_object* v_msg_2965_ = stack[1].m_obj;
lean_object* v___y_2966_ = stack[2].m_obj;
lean_object* v___y_2967_ = stack[3].m_obj;
lean_object* v_res_3017_;
v_res_3017_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2964_, v_msg_2965_, v___y_2966_, v___y_2967_);
stack->m_obj
 = v_res_3017_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_3018_, lean_object* v_msg_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_, lean_object* v___y_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3018_, v_msg_3019_, v___y_3020_, v___y_3021_);
lean_dec(v___y_3021_);
lean_dec_ref(v___y_3020_);
return v_res_3023_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3025_; lean_object* v___x_3026_; 
v___x_3025_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3026_ = l_Lean_stringToMessageData(v___x_3025_);
return v___x_3026_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_3027_, lean_object* v_cls_3028_, lean_object* v_x_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_toCold_3033_; lean_object* v_options_3034_; uint8_t v_hasTrace_3035_; 
v_toCold_3033_ = lean_ctor_get(v___y_3030_, 0);
v_options_3034_ = lean_ctor_get(v_toCold_3033_, 2);
v_hasTrace_3035_ = lean_ctor_get_uint8(v_options_3034_, sizeof(void*)*1);
if (v_hasTrace_3035_ == 0)
{
lean_object* v___x_3036_; 
lean_dec(v_cls_3028_);
v___x_3036_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3027_, v___y_3030_, v___y_3031_);
return v___x_3036_;
}
else
{
lean_object* v_inheritedTraceOptions_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v___x_3040_; 
v_inheritedTraceOptions_3037_ = lean_ctor_get(v_toCold_3033_, 11);
v___x_3038_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3028_);
v___x_3039_ = l_Lean_Name_append(v___x_3038_, v_cls_3028_);
v___x_3040_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3037_, v_options_3034_, v___x_3039_);
lean_dec(v___x_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; 
lean_dec(v_cls_3028_);
v___x_3041_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3027_, v___y_3030_, v___y_3031_);
return v___x_3041_;
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3043_; 
v___x_3042_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3043_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3028_, v___x_3042_, v___y_3030_, v___y_3031_);
if (lean_obj_tag(v___x_3043_) == 0)
{
lean_object* v___x_3044_; 
lean_dec_ref_known(v___x_3043_, 1);
v___x_3044_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3027_, v___y_3030_, v___y_3031_);
return v___x_3044_;
}
else
{
lean_dec(v_decl_3027_);
return v___x_3043_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3027_ = stack[0].m_obj;
lean_object* v_cls_3028_ = stack[1].m_obj;
lean_object* v_x_3029_ = stack[2].m_obj;
lean_object* v___y_3030_ = stack[3].m_obj;
lean_object* v___y_3031_ = stack[4].m_obj;
lean_object* v_res_3045_;
v_res_3045_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3027_, v_cls_3028_, v_x_3029_, v___y_3030_, v___y_3031_);
stack->m_obj
 = v_res_3045_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_3046_, lean_object* v_cls_3047_, lean_object* v_x_3048_, lean_object* v___y_3049_, lean_object* v___y_3050_, lean_object* v___y_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3046_, v_cls_3047_, v_x_3048_, v___y_3049_, v___y_3050_);
lean_dec(v___y_3050_);
lean_dec_ref(v___y_3049_);
lean_dec(v_x_3048_);
return v_res_3052_;
}
}
lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3056_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3054_);
v___x_3057_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3056_, v_opt_3053_);
lean_dec_ref(v___x_3056_);
v___x_3058_ = lean_box(v___x_3057_);
v___x_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
return v___x_3059_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_3053_ = stack[0].m_obj;
lean_object* v___y_3054_ = stack[1].m_obj;
lean_object* v_res_3060_;
v_res_3060_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_3053_, v___y_3054_);
stack->m_obj
 = v_res_3060_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_3061_, v___y_3062_);
lean_dec_ref(v___y_3062_);
lean_dec_ref(v_opt_3061_);
return v_res_3064_;
}
}
uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_3065_){
_start:
{
if (lean_obj_tag(v_x_3065_) == 0)
{
uint8_t v___x_3066_; 
v___x_3066_ = 1;
return v___x_3066_;
}
else
{
lean_object* v_head_3067_; lean_object* v_tail_3068_; uint8_t v___x_3069_; 
v_head_3067_ = lean_ctor_get(v_x_3065_, 0);
v_tail_3068_ = lean_ctor_get(v_x_3065_, 1);
v___x_3069_ = l_Lean_isPrivateName(v_head_3067_);
if (v___x_3069_ == 0)
{
return v___x_3069_;
}
else
{
v_x_3065_ = v_tail_3068_;
goto _start;
}
}
}
}
LEAN_EXPORT void l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3065_ = stack[0].m_obj;
uint8_t v_res_3071_;
v_res_3071_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_3065_);
stack->m_num = v_res_3071_;
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_3072_){
_start:
{
uint8_t v_res_3073_; lean_object* v_r_3074_; 
v_res_3073_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_3072_);
lean_dec(v_x_3072_);
v_r_3074_ = lean_box(v_res_3073_);
return v_r_3074_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_3081_ = l_Lean_stringToMessageData(v___x_3080_);
return v___x_3081_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_3084_ = l_Lean_stringToMessageData(v___x_3083_);
return v___x_3084_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3086_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_3087_ = l_Lean_stringToMessageData(v___x_3086_);
return v___x_3087_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_3088_, uint8_t v_hasTrace_3089_, uint8_t v___x_3090_, lean_object* v___x_3091_, uint8_t v___x_3092_, lean_object* v_cls_3093_, lean_object* v___x_3094_, lean_object* v_____x_3095_, lean_object* v_exportedInfo_x3f_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v___y_3101_; lean_object* v___y_3102_; lean_object* v_a_3103_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v_a_3116_; lean_object* v___y_3127_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v_snd_3199_; lean_object* v_fst_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3341_; 
v_snd_3199_ = lean_ctor_get(v_____x_3095_, 1);
v_fst_3200_ = lean_ctor_get(v_____x_3095_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_____x_3095_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3202_ = v_____x_3095_;
v_isShared_3203_ = v_isSharedCheck_3341_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_snd_3199_);
lean_inc(v_fst_3200_);
lean_dec(v_____x_3095_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3341_;
goto v_resetjp_3201_;
}
v___jp_3100_:
{
lean_object* v___x_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
v___x_3104_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3101_, v___y_3102_);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3111_ == 0)
{
lean_object* v_unused_3112_; 
v_unused_3112_ = lean_ctor_get(v___x_3104_, 0);
lean_dec(v_unused_3112_);
v___x_3106_ = v___x_3104_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_dec(v___x_3104_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
lean_ctor_set_tag(v___x_3106_, 1);
lean_ctor_set(v___x_3106_, 0, v_a_3103_);
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3103_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
v___jp_3113_:
{
lean_object* v___x_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3124_; 
v___x_3117_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3114_, v___y_3115_);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v___x_3117_, 0);
lean_dec(v_unused_3125_);
v___x_3119_ = v___x_3117_;
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
else
{
lean_dec(v___x_3117_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3124_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
lean_object* v___x_3122_; 
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v_a_3116_);
v___x_3122_ = v___x_3119_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3116_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
v___jp_3126_:
{
lean_object* v___x_3138_; 
lean_inc_ref(v___y_3128_);
v___x_3138_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3136_, v___y_3128_, v___y_3132_, v___y_3137_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v___x_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3185_; 
lean_dec_ref_known(v___x_3138_, 1);
lean_dec(v___y_3129_);
lean_inc_ref(v___y_3130_);
v___x_3139_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3130_, v___y_3134_);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3185_ == 0)
{
lean_object* v_unused_3186_; 
v_unused_3186_ = lean_ctor_get(v___x_3139_, 0);
lean_dec(v_unused_3186_);
v___x_3141_ = v___x_3139_;
v_isShared_3142_ = v_isSharedCheck_3185_;
goto v_resetjp_3140_;
}
else
{
lean_dec(v___x_3139_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3185_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; uint8_t v___x_3145_; 
v___x_3143_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3135_);
v___x_3144_ = l_Lean_Elab_async;
v___x_3145_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3143_, v___x_3144_);
lean_dec_ref(v___x_3143_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v_r_3147_; 
lean_del_object(v___x_3141_);
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3127_);
v___x_3146_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3128_, v___y_3134_);
lean_dec_ref(v___x_3146_);
v_r_3147_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3088_, v___y_3135_, v___y_3134_);
if (lean_obj_tag(v_r_3147_) == 0)
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3157_; 
v_a_3148_ = lean_ctor_get(v_r_3147_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v_r_3147_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3150_ = v_r_3147_;
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v_r_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3157_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
lean_inc(v_a_3148_);
if (v_isShared_3151_ == 0)
{
lean_ctor_set_tag(v___x_3150_, 1);
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
lean_object* v___x_3154_; 
v___x_3154_ = lean_apply_2(v___y_3131_, v___x_3153_, lean_box(0));
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_dec_ref_known(v___x_3154_, 1);
v___y_3114_ = v___y_3130_;
v___y_3115_ = v___y_3134_;
v_a_3116_ = v_a_3148_;
goto v___jp_3113_;
}
else
{
lean_object* v_a_3155_; 
lean_dec(v_a_3148_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
v___y_3101_ = v___y_3130_;
v___y_3102_ = v___y_3134_;
v_a_3103_ = v_a_3155_;
goto v___jp_3100_;
}
}
}
}
else
{
lean_object* v_a_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; 
v_a_3158_ = lean_ctor_get(v_r_3147_, 0);
lean_inc(v_a_3158_);
lean_dec_ref_known(v_r_3147_, 1);
v___x_3159_ = lean_box(0);
v___x_3160_ = lean_apply_2(v___y_3131_, v___x_3159_, lean_box(0));
if (lean_obj_tag(v___x_3160_) == 0)
{
lean_dec_ref_known(v___x_3160_, 1);
v___y_3101_ = v___y_3130_;
v___y_3102_ = v___y_3134_;
v_a_3103_ = v_a_3158_;
goto v___jp_3100_;
}
else
{
lean_object* v_a_3161_; 
lean_dec(v_a_3158_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref_known(v___x_3160_, 1);
v___y_3101_ = v___y_3130_;
v___y_3102_ = v___y_3134_;
v_a_3103_ = v_a_3161_;
goto v___jp_3100_;
}
}
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3164_; 
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3128_);
lean_dec(v_decl_3088_);
v___x_3162_ = l_IO_CancelToken_new();
if (v_isShared_3142_ == 0)
{
lean_ctor_set_tag(v___x_3141_, 1);
lean_ctor_set(v___x_3141_, 0, v___x_3162_);
v___x_3164_ = v___x_3141_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v___x_3162_);
v___x_3164_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; 
v___x_3165_ = lean_unsigned_to_nat(0u);
v___x_3166_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3167_ = l_Lean_Name_toString(v___x_3166_, v_hasTrace_3089_);
lean_inc_ref(v___x_3164_);
v___x_3168_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3133_, v___x_3164_, v___x_3167_, v___y_3135_, v___y_3134_);
if (lean_obj_tag(v___x_3168_) == 0)
{
lean_object* v_a_3169_; lean_object* v_checked_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v_a_3169_ = lean_ctor_get(v___x_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref_known(v___x_3168_, 1);
v_checked_3170_ = lean_ctor_get(v___y_3127_, 2);
lean_inc_ref(v_checked_3170_);
lean_dec_ref(v___y_3127_);
v___x_3171_ = lean_io_map_task(v_a_3169_, v_checked_3170_, v___x_3165_, v___x_3090_);
v___x_3172_ = lean_box(0);
v___x_3173_ = lean_box(2);
v___x_3174_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3172_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
lean_ctor_set(v___x_3174_, 2, v___x_3164_);
lean_ctor_set(v___x_3174_, 3, v___x_3171_);
v___x_3175_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3174_, v___y_3134_);
return v___x_3175_;
}
else
{
lean_object* v_a_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3183_; 
lean_dec_ref(v___x_3164_);
lean_dec_ref(v___y_3127_);
v_a_3176_ = lean_ctor_get(v___x_3168_, 0);
v_isSharedCheck_3183_ = !lean_is_exclusive(v___x_3168_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3178_ = v___x_3168_;
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_a_3176_);
lean_dec(v___x_3168_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3183_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3181_; 
if (v_isShared_3179_ == 0)
{
v___x_3181_ = v___x_3178_;
goto v_reusejp_3180_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v_a_3176_);
v___x_3181_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3180_;
}
v_reusejp_3180_:
{
return v___x_3181_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3187_; lean_object* v___x_3189_; uint8_t v_isShared_3190_; uint8_t v_isSharedCheck_3198_; 
lean_dec_ref(v___y_3133_);
lean_dec_ref(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v_decl_3088_);
v_a_3187_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3189_ = v___x_3138_;
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
else
{
lean_inc(v_a_3187_);
lean_dec(v___x_3138_);
v___x_3189_ = lean_box(0);
v_isShared_3190_ = v_isSharedCheck_3198_;
goto v_resetjp_3188_;
}
v_resetjp_3188_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v___x_3196_; 
v___x_3191_ = lean_io_error_to_string(v_a_3187_);
v___x_3192_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
v___x_3193_ = l_Lean_MessageData_ofFormat(v___x_3192_);
v___x_3194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3194_, 0, v___y_3129_);
lean_ctor_set(v___x_3194_, 1, v___x_3193_);
if (v_isShared_3190_ == 0)
{
lean_ctor_set(v___x_3189_, 0, v___x_3194_);
v___x_3196_ = v___x_3189_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v___x_3194_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
}
v_resetjp_3201_:
{
lean_object* v_fst_3204_; lean_object* v_snd_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3340_; 
v_fst_3204_ = lean_ctor_get(v_snd_3199_, 0);
v_snd_3205_ = lean_ctor_get(v_snd_3199_, 1);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_snd_3199_);
if (v_isSharedCheck_3340_ == 0)
{
v___x_3207_ = v_snd_3199_;
v_isShared_3208_ = v_isSharedCheck_3340_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_snd_3205_);
lean_inc(v_fst_3204_);
lean_dec(v_snd_3199_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3340_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v_exportedInfo_x3f_3239_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3259_; uint8_t v___y_3260_; lean_object* v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3284_; uint8_t v___y_3285_; lean_object* v___y_3286_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___x_3330_; lean_object* v_env_3331_; uint8_t v___x_3332_; 
v___x_3330_ = lean_st_ref_get(v___y_3098_);
v_env_3331_ = lean_ctor_get(v___x_3330_, 0);
lean_inc_ref(v_env_3331_);
lean_dec(v___x_3330_);
v___x_3332_ = l_Lean_Environment_containsOnBranch(v_env_3331_, v_fst_3200_);
lean_dec_ref(v_env_3331_);
if (v___x_3332_ == 0)
{
lean_del_object(v___x_3202_);
v___y_3295_ = v___y_3097_;
v___y_3296_ = v___y_3098_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3333_; lean_object* v_env_3334_; lean_object* v___x_3335_; lean_object* v___x_3337_; 
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_dec(v_exportedInfo_x3f_3096_);
lean_dec(v___x_3094_);
lean_dec(v_cls_3093_);
lean_dec_ref(v___x_3091_);
lean_dec(v_decl_3088_);
v___x_3333_ = lean_st_ref_get(v___y_3098_);
v_env_3334_ = lean_ctor_get(v___x_3333_, 0);
lean_inc_ref(v_env_3334_);
lean_dec(v___x_3333_);
v___x_3335_ = lean_elab_environment_to_kernel_env(v_env_3334_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set_tag(v___x_3202_, 1);
lean_ctor_set(v___x_3202_, 1, v_fst_3200_);
lean_ctor_set(v___x_3202_, 0, v___x_3335_);
v___x_3337_ = v___x_3202_;
goto v_reusejp_3336_;
}
else
{
lean_object* v_reuseFailAlloc_3339_; 
v_reuseFailAlloc_3339_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3339_, 0, v___x_3335_);
lean_ctor_set(v_reuseFailAlloc_3339_, 1, v_fst_3200_);
v___x_3337_ = v_reuseFailAlloc_3339_;
goto v_reusejp_3336_;
}
v_reusejp_3336_:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3337_, v___y_3097_, v___y_3098_);
return v___x_3338_;
}
}
v___jp_3209_:
{
lean_object* v_ref_3215_; uint8_t v___x_3216_; lean_object* v___x_3217_; 
v_ref_3215_ = lean_ctor_get(v___y_3212_, 2);
v___x_3216_ = lean_unbox(v_snd_3205_);
lean_dec(v_snd_3205_);
lean_inc_ref(v___y_3213_);
v___x_3217_ = l_Lean_Environment_addConstAsync(v___y_3213_, v_fst_3200_, v___x_3216_, v___y_3214_, v___x_3090_, v_hasTrace_3089_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v_mainEnv_3219_; lean_object* v_asyncEnv_3220_; lean_object* v___f_3221_; lean_object* v___f_3222_; lean_object* v___x_3223_; 
lean_del_object(v___x_3207_);
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_n(v_a_3218_, 3);
lean_dec_ref_known(v___x_3217_, 1);
v_mainEnv_3219_ = lean_ctor_get(v_a_3218_, 0);
lean_inc_ref(v_mainEnv_3219_);
v_asyncEnv_3220_ = lean_ctor_get(v_a_3218_, 1);
lean_inc_ref_n(v_asyncEnv_3220_, 2);
lean_inc(v_ref_3215_);
lean_inc(v___y_3211_);
v___f_3221_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3221_, 0, v___y_3211_);
lean_closure_set(v___f_3221_, 1, v_a_3218_);
lean_closure_set(v___f_3221_, 2, v_ref_3215_);
lean_inc(v_decl_3088_);
v___f_3222_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3222_, 0, v_a_3218_);
lean_closure_set(v___f_3222_, 1, v_asyncEnv_3220_);
lean_closure_set(v___f_3222_, 2, v_decl_3088_);
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_fst_3204_);
if (lean_obj_tag(v___y_3210_) == 0)
{
lean_inc_ref(v___x_3223_);
lean_inc(v_ref_3215_);
v___y_3127_ = v___y_3213_;
v___y_3128_ = v_asyncEnv_3220_;
v___y_3129_ = v_ref_3215_;
v___y_3130_ = v_mainEnv_3219_;
v___y_3131_ = v___f_3221_;
v___y_3132_ = v___x_3223_;
v___y_3133_ = v___f_3222_;
v___y_3134_ = v___y_3211_;
v___y_3135_ = v___y_3212_;
v___y_3136_ = v_a_3218_;
v___y_3137_ = v___x_3223_;
goto v___jp_3126_;
}
else
{
lean_inc(v_ref_3215_);
v___y_3127_ = v___y_3213_;
v___y_3128_ = v_asyncEnv_3220_;
v___y_3129_ = v_ref_3215_;
v___y_3130_ = v_mainEnv_3219_;
v___y_3131_ = v___f_3221_;
v___y_3132_ = v___x_3223_;
v___y_3133_ = v___f_3222_;
v___y_3134_ = v___y_3211_;
v___y_3135_ = v___y_3212_;
v___y_3136_ = v_a_3218_;
v___y_3137_ = v___y_3210_;
goto v___jp_3126_;
}
}
else
{
lean_object* v_a_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3237_; 
lean_dec_ref(v___y_3213_);
lean_dec(v___y_3210_);
lean_dec(v_fst_3204_);
lean_dec(v_decl_3088_);
v_a_3224_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3226_ = v___x_3217_;
v_isShared_3227_ = v_isSharedCheck_3237_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_a_3224_);
lean_dec(v___x_3217_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3237_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3232_; 
v___x_3228_ = lean_io_error_to_string(v_a_3224_);
v___x_3229_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
v___x_3230_ = l_Lean_MessageData_ofFormat(v___x_3229_);
lean_inc(v_ref_3215_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 1, v___x_3230_);
lean_ctor_set(v___x_3207_, 0, v_ref_3215_);
v___x_3232_ = v___x_3207_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_ref_3215_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3230_);
v___x_3232_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
lean_object* v___x_3234_; 
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v___x_3232_);
v___x_3234_ = v___x_3226_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3232_);
v___x_3234_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
return v___x_3234_;
}
}
}
}
}
v___jp_3238_:
{
lean_object* v___x_3242_; 
v___x_3242_ = lean_st_ref_get(v___y_3241_);
if (lean_obj_tag(v_exportedInfo_x3f_3239_) == 0)
{
lean_object* v_env_3243_; lean_object* v___x_3244_; 
v_env_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_env_3243_);
lean_dec(v___x_3242_);
v___x_3244_ = lean_box(0);
v___y_3210_ = v_exportedInfo_x3f_3239_;
v___y_3211_ = v___y_3241_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v_env_3243_;
v___y_3214_ = v___x_3244_;
goto v___jp_3209_;
}
else
{
lean_object* v_env_3245_; lean_object* v_val_3246_; uint8_t v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; 
v_env_3245_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_env_3245_);
lean_dec(v___x_3242_);
v_val_3246_ = lean_ctor_get(v_exportedInfo_x3f_3239_, 0);
v___x_3247_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3246_);
v___x_3248_ = lean_box(v___x_3247_);
v___x_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3248_);
v___y_3210_ = v_exportedInfo_x3f_3239_;
v___y_3211_ = v___y_3241_;
v___y_3212_ = v___y_3240_;
v___y_3213_ = v_env_3245_;
v___y_3214_ = v___x_3249_;
goto v___jp_3209_;
}
}
v___jp_3250_:
{
lean_object* v___x_3253_; 
lean_inc(v_fst_3204_);
v___x_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3253_, 0, v_fst_3204_);
v_exportedInfo_x3f_3239_ = v___x_3253_;
v___y_3240_ = v___y_3251_;
v___y_3241_ = v___y_3252_;
goto v___jp_3238_;
}
v___jp_3254_:
{
lean_object* v___x_3257_; 
lean_inc(v_fst_3204_);
v___x_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3257_, 0, v_fst_3204_);
v_exportedInfo_x3f_3239_ = v___x_3257_;
v___y_3240_ = v___y_3255_;
v___y_3241_ = v___y_3256_;
goto v___jp_3238_;
}
v___jp_3258_:
{
lean_object* v___x_3263_; lean_object* v_env_3264_; lean_object* v_nextMacroScope_3265_; lean_object* v_ngen_3266_; lean_object* v_auxDeclNGen_3267_; lean_object* v_traceState_3268_; lean_object* v_recordedDeps_3269_; lean_object* v_messages_3270_; lean_object* v_infoState_3271_; lean_object* v_snapshotTasks_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3281_; 
v___x_3263_ = lean_st_ref_take(v___y_3262_);
v_env_3264_ = lean_ctor_get(v___x_3263_, 0);
v_nextMacroScope_3265_ = lean_ctor_get(v___x_3263_, 1);
v_ngen_3266_ = lean_ctor_get(v___x_3263_, 2);
v_auxDeclNGen_3267_ = lean_ctor_get(v___x_3263_, 3);
v_traceState_3268_ = lean_ctor_get(v___x_3263_, 4);
v_recordedDeps_3269_ = lean_ctor_get(v___x_3263_, 6);
v_messages_3270_ = lean_ctor_get(v___x_3263_, 7);
v_infoState_3271_ = lean_ctor_get(v___x_3263_, 8);
v_snapshotTasks_3272_ = lean_ctor_get(v___x_3263_, 9);
v_isSharedCheck_3281_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v___x_3263_, 5);
lean_dec(v_unused_3282_);
v___x_3274_ = v___x_3263_;
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_snapshotTasks_3272_);
lean_inc(v_infoState_3271_);
lean_inc(v_messages_3270_);
lean_inc(v_recordedDeps_3269_);
lean_inc(v_traceState_3268_);
lean_inc(v_auxDeclNGen_3267_);
lean_inc(v_ngen_3266_);
lean_inc(v_nextMacroScope_3265_);
lean_inc(v_env_3264_);
lean_dec(v___x_3263_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3281_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
lean_inc(v_snd_3205_);
lean_inc(v_fst_3200_);
lean_inc_ref(v___y_3261_);
v___x_3276_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_3261_, v_env_3264_, v_fst_3200_, v_snd_3205_, v___y_3260_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 5, v___x_3091_);
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3276_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_nextMacroScope_3265_);
lean_ctor_set(v_reuseFailAlloc_3280_, 2, v_ngen_3266_);
lean_ctor_set(v_reuseFailAlloc_3280_, 3, v_auxDeclNGen_3267_);
lean_ctor_set(v_reuseFailAlloc_3280_, 4, v_traceState_3268_);
lean_ctor_set(v_reuseFailAlloc_3280_, 5, v___x_3091_);
lean_ctor_set(v_reuseFailAlloc_3280_, 6, v_recordedDeps_3269_);
lean_ctor_set(v_reuseFailAlloc_3280_, 7, v_messages_3270_);
lean_ctor_set(v_reuseFailAlloc_3280_, 8, v_infoState_3271_);
lean_ctor_set(v_reuseFailAlloc_3280_, 9, v_snapshotTasks_3272_);
v___x_3278_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_st_ref_put(v___y_3262_, v___x_3278_);
v_exportedInfo_x3f_3239_ = v_exportedInfo_x3f_3096_;
v___y_3240_ = v___y_3259_;
v___y_3241_ = v___y_3262_;
goto v___jp_3238_;
}
}
}
v___jp_3283_:
{
lean_object* v___x_3287_; lean_object* v_env_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; uint8_t v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; 
v___x_3287_ = lean_st_ref_get(v___y_3286_);
v_env_3288_ = lean_ctor_get(v___x_3287_, 0);
lean_inc_ref(v_env_3288_);
lean_dec(v___x_3287_);
v___x_3289_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3290_ = lean_box(1);
v___x_3291_ = 0;
v___x_3292_ = lean_box(v___x_3092_);
lean_inc(v_fst_3200_);
v___x_3293_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3292_, v___x_3289_, v_env_3288_, v_fst_3200_, v___x_3290_, v___x_3291_);
if (lean_obj_tag(v___x_3293_) == 0)
{
v___y_3259_ = v___y_3284_;
v___y_3260_ = v___y_3285_;
v___y_3261_ = v___x_3289_;
v___y_3262_ = v___y_3286_;
goto v___jp_3258_;
}
else
{
lean_dec_ref_known(v___x_3293_, 1);
if (v___y_3285_ == 0)
{
lean_dec_ref(v___x_3091_);
v_exportedInfo_x3f_3239_ = v_exportedInfo_x3f_3096_;
v___y_3240_ = v___y_3284_;
v___y_3241_ = v___y_3286_;
goto v___jp_3238_;
}
else
{
v___y_3259_ = v___y_3284_;
v___y_3260_ = v___y_3285_;
v___y_3261_ = v___x_3289_;
v___y_3262_ = v___y_3286_;
goto v___jp_3258_;
}
}
}
v___jp_3294_:
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
lean_inc(v_decl_3088_);
v___x_3297_ = l_Lean_Declaration_getTopLevelNames(v_decl_3088_);
v___x_3298_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3297_);
lean_dec(v___x_3297_);
if (v___x_3298_ == 0)
{
lean_dec(v___x_3094_);
if (lean_obj_tag(v_exportedInfo_x3f_3096_) == 0)
{
if (v___x_3298_ == 0)
{
lean_object* v_toCold_3299_; lean_object* v_options_3300_; uint8_t v_hasTrace_3301_; 
lean_dec_ref(v___x_3091_);
v_toCold_3299_ = lean_ctor_get(v___y_3295_, 0);
v_options_3300_ = lean_ctor_get(v_toCold_3299_, 2);
v_hasTrace_3301_ = lean_ctor_get_uint8(v_options_3300_, sizeof(void*)*1);
if (v_hasTrace_3301_ == 0)
{
lean_dec(v_cls_3093_);
v___y_3255_ = v___y_3295_;
v___y_3256_ = v___y_3296_;
goto v___jp_3254_;
}
else
{
lean_object* v_inheritedTraceOptions_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; uint8_t v___x_3305_; 
v_inheritedTraceOptions_3302_ = lean_ctor_get(v_toCold_3299_, 11);
v___x_3303_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3093_);
v___x_3304_ = l_Lean_Name_append(v___x_3303_, v_cls_3093_);
v___x_3305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3302_, v_options_3300_, v___x_3304_);
lean_dec(v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec(v_cls_3093_);
v___y_3255_ = v___y_3295_;
v___y_3256_ = v___y_3296_;
goto v___jp_3254_;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; 
v___x_3306_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3307_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3093_, v___x_3306_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3307_) == 0)
{
lean_dec_ref_known(v___x_3307_, 1);
v___y_3255_ = v___y_3295_;
v___y_3256_ = v___y_3296_;
goto v___jp_3254_;
}
else
{
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_dec(v_fst_3200_);
lean_dec(v_decl_3088_);
return v___x_3307_;
}
}
}
}
else
{
lean_dec(v_cls_3093_);
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___x_3298_;
v___y_3286_ = v___y_3296_;
goto v___jp_3283_;
}
}
else
{
lean_dec(v_cls_3093_);
v___y_3284_ = v___y_3295_;
v___y_3285_ = v___x_3298_;
v___y_3286_ = v___y_3296_;
goto v___jp_3283_;
}
}
else
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v_a_3310_; uint8_t v___x_3311_; 
lean_dec(v_exportedInfo_x3f_3096_);
lean_dec_ref(v___x_3091_);
v___x_3308_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3309_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3308_, v___y_3295_);
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = lean_unbox(v_a_3310_);
lean_dec(v_a_3310_);
if (v___x_3311_ == 0)
{
lean_object* v_toCold_3312_; lean_object* v_options_3313_; uint8_t v_hasTrace_3314_; 
v_toCold_3312_ = lean_ctor_get(v___y_3295_, 0);
v_options_3313_ = lean_ctor_get(v_toCold_3312_, 2);
v_hasTrace_3314_ = lean_ctor_get_uint8(v_options_3313_, sizeof(void*)*1);
if (v_hasTrace_3314_ == 0)
{
lean_dec(v_cls_3093_);
v_exportedInfo_x3f_3239_ = v___x_3094_;
v___y_3240_ = v___y_3295_;
v___y_3241_ = v___y_3296_;
goto v___jp_3238_;
}
else
{
lean_object* v_inheritedTraceOptions_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; uint8_t v___x_3318_; 
v_inheritedTraceOptions_3315_ = lean_ctor_get(v_toCold_3312_, 11);
v___x_3316_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3093_);
v___x_3317_ = l_Lean_Name_append(v___x_3316_, v_cls_3093_);
v___x_3318_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3315_, v_options_3313_, v___x_3317_);
lean_dec(v___x_3317_);
if (v___x_3318_ == 0)
{
lean_dec(v_cls_3093_);
v_exportedInfo_x3f_3239_ = v___x_3094_;
v___y_3240_ = v___y_3295_;
v___y_3241_ = v___y_3296_;
goto v___jp_3238_;
}
else
{
lean_object* v___x_3319_; lean_object* v___x_3320_; 
v___x_3319_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3320_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3093_, v___x_3319_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3320_) == 0)
{
lean_dec_ref_known(v___x_3320_, 1);
v_exportedInfo_x3f_3239_ = v___x_3094_;
v___y_3240_ = v___y_3295_;
v___y_3241_ = v___y_3296_;
goto v___jp_3238_;
}
else
{
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_dec(v_fst_3200_);
lean_dec(v___x_3094_);
lean_dec(v_decl_3088_);
return v___x_3320_;
}
}
}
}
else
{
lean_object* v_toCold_3321_; lean_object* v_options_3322_; uint8_t v_hasTrace_3323_; 
lean_dec(v___x_3094_);
v_toCold_3321_ = lean_ctor_get(v___y_3295_, 0);
v_options_3322_ = lean_ctor_get(v_toCold_3321_, 2);
v_hasTrace_3323_ = lean_ctor_get_uint8(v_options_3322_, sizeof(void*)*1);
if (v_hasTrace_3323_ == 0)
{
lean_dec(v_cls_3093_);
v___y_3251_ = v___y_3295_;
v___y_3252_ = v___y_3296_;
goto v___jp_3250_;
}
else
{
lean_object* v_inheritedTraceOptions_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; uint8_t v___x_3327_; 
v_inheritedTraceOptions_3324_ = lean_ctor_get(v_toCold_3321_, 11);
v___x_3325_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3093_);
v___x_3326_ = l_Lean_Name_append(v___x_3325_, v_cls_3093_);
v___x_3327_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3324_, v_options_3322_, v___x_3326_);
lean_dec(v___x_3326_);
if (v___x_3327_ == 0)
{
lean_dec(v_cls_3093_);
v___y_3251_ = v___y_3295_;
v___y_3252_ = v___y_3296_;
goto v___jp_3250_;
}
else
{
lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3329_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3093_, v___x_3328_, v___y_3295_, v___y_3296_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_dec_ref_known(v___x_3329_, 1);
v___y_3251_ = v___y_3295_;
v___y_3252_ = v___y_3296_;
goto v___jp_3250_;
}
else
{
lean_del_object(v___x_3207_);
lean_dec(v_snd_3205_);
lean_dec(v_fst_3204_);
lean_dec(v_fst_3200_);
lean_dec(v_decl_3088_);
return v___x_3329_;
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
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3088_ = stack[0].m_obj;
uint8_t v_hasTrace_3089_ = stack[1].m_num;
uint8_t v___x_3090_ = stack[2].m_num;
lean_object* v___x_3091_ = stack[3].m_obj;
uint8_t v___x_3092_ = stack[4].m_num;
lean_object* v_cls_3093_ = stack[5].m_obj;
lean_object* v___x_3094_ = stack[6].m_obj;
lean_object* v_____x_3095_ = stack[7].m_obj;
lean_object* v_exportedInfo_x3f_3096_ = stack[8].m_obj;
lean_object* v___y_3097_ = stack[9].m_obj;
lean_object* v___y_3098_ = stack[10].m_obj;
lean_object* v_res_3342_;
v_res_3342_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3088_, v_hasTrace_3089_, v___x_3090_, v___x_3091_, v___x_3092_, v_cls_3093_, v___x_3094_, v_____x_3095_, v_exportedInfo_x3f_3096_, v___y_3097_, v___y_3098_);
stack->m_obj
 = v_res_3342_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3343_, lean_object* v_hasTrace_3344_, lean_object* v___x_3345_, lean_object* v___x_3346_, lean_object* v___x_3347_, lean_object* v_cls_3348_, lean_object* v___x_3349_, lean_object* v_____x_3350_, lean_object* v_exportedInfo_x3f_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_, lean_object* v___y_3354_){
_start:
{
uint8_t v_hasTrace_boxed_3355_; uint8_t v___x_54341__boxed_3356_; uint8_t v___x_54343__boxed_3357_; lean_object* v_res_3358_; 
v_hasTrace_boxed_3355_ = lean_unbox(v_hasTrace_3344_);
v___x_54341__boxed_3356_ = lean_unbox(v___x_3345_);
v___x_54343__boxed_3357_ = lean_unbox(v___x_3347_);
v_res_3358_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3343_, v_hasTrace_boxed_3355_, v___x_54341__boxed_3356_, v___x_3346_, v___x_54343__boxed_3357_, v_cls_3348_, v___x_3349_, v_____x_3350_, v_exportedInfo_x3f_3351_, v___y_3352_, v___y_3353_);
lean_dec(v___y_3353_);
lean_dec_ref(v___y_3352_);
return v_res_3358_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3360_; lean_object* v___x_3361_; 
v___x_3360_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3361_ = l_Lean_stringToMessageData(v___x_3360_);
return v___x_3361_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3364_ = l_Lean_stringToMessageData(v___x_3363_);
return v___x_3364_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3365_, uint8_t v___x_3366_, lean_object* v_cls_3367_, lean_object* v___x_3368_, uint8_t v_forceExpose_3369_, lean_object* v_defn_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
lean_object* v_exportedInfo_x3f_3375_; lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; uint8_t v___y_3390_; uint8_t v___y_3395_; lean_object* v___x_3400_; lean_object* v_env_3401_; lean_object* v___x_3402_; uint8_t v___y_3404_; lean_object* v_env_3420_; 
v___x_3400_ = lean_st_ref_get(v___y_3372_);
v_env_3401_ = lean_ctor_get(v___x_3400_, 0);
lean_inc_ref(v_env_3401_);
lean_dec(v___x_3400_);
v___x_3402_ = lean_st_ref_get(v___y_3372_);
v_env_3420_ = lean_ctor_get(v___x_3402_, 0);
lean_inc_ref(v_env_3420_);
lean_dec(v___x_3402_);
if (v_forceExpose_3369_ == 0)
{
goto v___jp_3421_;
}
else
{
if (v___x_3366_ == 0)
{
lean_dec_ref(v_env_3420_);
lean_dec_ref(v_env_3401_);
lean_dec(v_cls_3367_);
v_exportedInfo_x3f_3375_ = v___x_3368_;
v___y_3376_ = v___y_3371_;
v___y_3377_ = v___y_3372_;
goto v___jp_3374_;
}
else
{
goto v___jp_3421_;
}
}
v___jp_3374_:
{
lean_object* v_toConstantVal_3378_; lean_object* v_name_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___x_3384_; lean_object* v___x_3385_; 
v_toConstantVal_3378_ = lean_ctor_get(v_defn_3370_, 0);
v_name_3379_ = lean_ctor_get(v_toConstantVal_3378_, 0);
lean_inc(v_name_3379_);
v___x_3380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3380_, 0, v_defn_3370_);
v___x_3381_ = 0;
v___x_3382_ = lean_box(v___x_3381_);
v___x_3383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3380_);
lean_ctor_set(v___x_3383_, 1, v___x_3382_);
v___x_3384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3384_, 0, v_name_3379_);
lean_ctor_set(v___x_3384_, 1, v___x_3383_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
v___x_3385_ = lean_apply_5(v___f_3365_, v___x_3384_, v_exportedInfo_x3f_3375_, v___y_3376_, v___y_3377_, lean_box(0));
return v___x_3385_;
}
v___jp_3386_:
{
lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3391_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3391_, 0, v___y_3389_);
lean_ctor_set_uint8(v___x_3391_, sizeof(void*)*1, v___y_3390_);
v___x_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
v___x_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
v_exportedInfo_x3f_3375_ = v___x_3393_;
v___y_3376_ = v___y_3387_;
v___y_3377_ = v___y_3388_;
goto v___jp_3374_;
}
v___jp_3394_:
{
lean_object* v_toConstantVal_3396_; uint8_t v_safety_3397_; uint8_t v___x_3398_; uint8_t v___x_3399_; 
v_toConstantVal_3396_ = lean_ctor_get(v_defn_3370_, 0);
v_safety_3397_ = lean_ctor_get_uint8(v_defn_3370_, sizeof(void*)*4);
v___x_3398_ = 1;
v___x_3399_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3397_, v___x_3398_);
if (v___x_3399_ == 0)
{
lean_inc_ref(v_toConstantVal_3396_);
v___y_3387_ = v___y_3371_;
v___y_3388_ = v___y_3372_;
v___y_3389_ = v_toConstantVal_3396_;
v___y_3390_ = v___y_3395_;
goto v___jp_3386_;
}
else
{
lean_inc_ref(v_toConstantVal_3396_);
v___y_3387_ = v___y_3371_;
v___y_3388_ = v___y_3372_;
v___y_3389_ = v_toConstantVal_3396_;
v___y_3390_ = v___x_3366_;
goto v___jp_3386_;
}
}
v___jp_3403_:
{
lean_object* v_toCold_3405_; lean_object* v_options_3406_; uint8_t v_hasTrace_3407_; 
v_toCold_3405_ = lean_ctor_get(v___y_3371_, 0);
v_options_3406_ = lean_ctor_get(v_toCold_3405_, 2);
v_hasTrace_3407_ = lean_ctor_get_uint8(v_options_3406_, sizeof(void*)*1);
if (v_hasTrace_3407_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3395_ = v___y_3404_;
goto v___jp_3394_;
}
else
{
lean_object* v_inheritedTraceOptions_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; uint8_t v___x_3411_; 
v_inheritedTraceOptions_3408_ = lean_ctor_get(v_toCold_3405_, 11);
v___x_3409_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3367_);
v___x_3410_ = l_Lean_Name_append(v___x_3409_, v_cls_3367_);
v___x_3411_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3408_, v_options_3406_, v___x_3410_);
lean_dec(v___x_3410_);
if (v___x_3411_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3395_ = v___y_3404_;
goto v___jp_3394_;
}
else
{
lean_object* v_toConstantVal_3412_; lean_object* v_name_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; 
v_toConstantVal_3412_ = lean_ctor_get(v_defn_3370_, 0);
v_name_3413_ = lean_ctor_get(v_toConstantVal_3412_, 0);
v___x_3414_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3413_);
v___x_3415_ = l_Lean_MessageData_ofName(v_name_3413_);
v___x_3416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3414_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3418_, 0, v___x_3416_);
lean_ctor_set(v___x_3418_, 1, v___x_3417_);
v___x_3419_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3367_, v___x_3418_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3419_) == 0)
{
lean_dec_ref_known(v___x_3419_, 1);
v___y_3395_ = v___y_3404_;
goto v___jp_3394_;
}
else
{
lean_dec_ref(v_defn_3370_);
lean_dec_ref(v___f_3365_);
return v___x_3419_;
}
}
}
}
v___jp_3421_:
{
lean_object* v___x_3422_; uint8_t v_isModule_3423_; 
v___x_3422_ = l_Lean_Environment_header(v_env_3401_);
lean_dec_ref(v_env_3401_);
v_isModule_3423_ = lean_ctor_get_uint8(v___x_3422_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3422_);
if (v_isModule_3423_ == 0)
{
lean_dec_ref(v_env_3420_);
lean_dec(v_cls_3367_);
v_exportedInfo_x3f_3375_ = v___x_3368_;
v___y_3376_ = v___y_3371_;
v___y_3377_ = v___y_3372_;
goto v___jp_3374_;
}
else
{
uint8_t v_isExporting_3424_; 
v_isExporting_3424_ = lean_ctor_get_uint8(v_env_3420_, sizeof(void*)*13);
lean_dec_ref(v_env_3420_);
if (v_isExporting_3424_ == 0)
{
lean_dec(v___x_3368_);
v___y_3404_ = v_isModule_3423_;
goto v___jp_3403_;
}
else
{
if (v___x_3366_ == 0)
{
lean_dec(v_cls_3367_);
v_exportedInfo_x3f_3375_ = v___x_3368_;
v___y_3376_ = v___y_3371_;
v___y_3377_ = v___y_3372_;
goto v___jp_3374_;
}
else
{
lean_dec(v___x_3368_);
v___y_3404_ = v___x_3366_;
goto v___jp_3403_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3365_ = stack[0].m_obj;
uint8_t v___x_3366_ = stack[1].m_num;
lean_object* v_cls_3367_ = stack[2].m_obj;
lean_object* v___x_3368_ = stack[3].m_obj;
uint8_t v_forceExpose_3369_ = stack[4].m_num;
lean_object* v_defn_3370_ = stack[5].m_obj;
lean_object* v___y_3371_ = stack[6].m_obj;
lean_object* v___y_3372_ = stack[7].m_obj;
lean_object* v_res_3425_;
v_res_3425_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3365_, v___x_3366_, v_cls_3367_, v___x_3368_, v_forceExpose_3369_, v_defn_3370_, v___y_3371_, v___y_3372_);
stack->m_obj
 = v_res_3425_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3426_, lean_object* v___x_3427_, lean_object* v_cls_3428_, lean_object* v___x_3429_, lean_object* v_forceExpose_3430_, lean_object* v_defn_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
uint8_t v___x_55080__boxed_3435_; uint8_t v_forceExpose_boxed_3436_; lean_object* v_res_3437_; 
v___x_55080__boxed_3435_ = lean_unbox(v___x_3427_);
v_forceExpose_boxed_3436_ = lean_unbox(v_forceExpose_3430_);
v_res_3437_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3426_, v___x_55080__boxed_3435_, v_cls_3428_, v___x_3429_, v_forceExpose_boxed_3436_, v_defn_3431_, v___y_3432_, v___y_3433_);
lean_dec(v___y_3433_);
lean_dec_ref(v___y_3432_);
return v_res_3437_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3438_, lean_object* v___f_3439_, lean_object* v_____r_3440_, lean_object* v_exportedInfo_x3f_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_toConstantVal_3445_; lean_object* v_name_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_toConstantVal_3445_ = lean_ctor_get(v_val_3438_, 0);
v_name_3446_ = lean_ctor_get(v_toConstantVal_3445_, 0);
lean_inc(v_name_3446_);
v___x_3447_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3447_, 0, v_val_3438_);
v___x_3448_ = 1;
v___x_3449_ = lean_box(v___x_3448_);
v___x_3450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3450_, 0, v___x_3447_);
lean_ctor_set(v___x_3450_, 1, v___x_3449_);
v___x_3451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3451_, 0, v_name_3446_);
lean_ctor_set(v___x_3451_, 1, v___x_3450_);
lean_inc(v___y_3443_);
lean_inc_ref(v___y_3442_);
v___x_3452_ = lean_apply_5(v___f_3439_, v___x_3451_, v_exportedInfo_x3f_3441_, v___y_3442_, v___y_3443_, lean_box(0));
return v___x_3452_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3438_ = stack[0].m_obj;
lean_object* v___f_3439_ = stack[1].m_obj;
lean_object* v_____r_3440_ = stack[2].m_obj;
lean_object* v_exportedInfo_x3f_3441_ = stack[3].m_obj;
lean_object* v___y_3442_ = stack[4].m_obj;
lean_object* v___y_3443_ = stack[5].m_obj;
lean_object* v_res_3453_;
v_res_3453_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3438_, v___f_3439_, v_____r_3440_, v_exportedInfo_x3f_3441_, v___y_3442_, v___y_3443_);
stack->m_obj
 = v_res_3453_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3454_, lean_object* v___f_3455_, lean_object* v_____r_3456_, lean_object* v_exportedInfo_x3f_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_, lean_object* v___y_3460_){
_start:
{
lean_object* v_res_3461_; 
v_res_3461_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3454_, v___f_3455_, v_____r_3456_, v_exportedInfo_x3f_3457_, v___y_3458_, v___y_3459_);
lean_dec(v___y_3459_);
lean_dec_ref(v___y_3458_);
return v_res_3461_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3462_, uint8_t v___x_3463_, lean_object* v___f_3464_, lean_object* v_____r_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_){
_start:
{
lean_object* v_toConstantVal_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v_toConstantVal_3469_ = lean_ctor_get(v_val_3462_, 0);
lean_inc_ref(v_toConstantVal_3469_);
v___x_3470_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3470_, 0, v_toConstantVal_3469_);
lean_ctor_set_uint8(v___x_3470_, sizeof(void*)*1, v___x_3463_);
v___x_3471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3471_, 0, v___x_3470_);
v___x_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3472_, 0, v___x_3471_);
v___x_3473_ = lean_box(0);
lean_inc(v___y_3467_);
lean_inc_ref(v___y_3466_);
v___x_3474_ = lean_apply_5(v___f_3464_, v___x_3473_, v___x_3472_, v___y_3466_, v___y_3467_, lean_box(0));
return v___x_3474_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3462_ = stack[0].m_obj;
uint8_t v___x_3463_ = stack[1].m_num;
lean_object* v___f_3464_ = stack[2].m_obj;
lean_object* v_____r_3465_ = stack[3].m_obj;
lean_object* v___y_3466_ = stack[4].m_obj;
lean_object* v___y_3467_ = stack[5].m_obj;
lean_object* v_res_3475_;
v_res_3475_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3462_, v___x_3463_, v___f_3464_, v_____r_3465_, v___y_3466_, v___y_3467_);
stack->m_obj
 = v_res_3475_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3476_, lean_object* v___x_3477_, lean_object* v___f_3478_, lean_object* v_____r_3479_, lean_object* v___y_3480_, lean_object* v___y_3481_, lean_object* v___y_3482_){
_start:
{
uint8_t v___x_55285__boxed_3483_; lean_object* v_res_3484_; 
v___x_55285__boxed_3483_ = lean_unbox(v___x_3477_);
v_res_3484_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3476_, v___x_55285__boxed_3483_, v___f_3478_, v_____r_3479_, v___y_3480_, v___y_3481_);
lean_dec(v___y_3481_);
lean_dec_ref(v___y_3480_);
lean_dec_ref(v_val_3476_);
return v_res_3484_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3485_, lean_object* v___f_3486_, lean_object* v_____r_3487_, lean_object* v_exportedInfo_x3f_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v_toConstantVal_3492_; lean_object* v_name_3493_; lean_object* v___x_3494_; uint8_t v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; 
v_toConstantVal_3492_ = lean_ctor_get(v_val_3485_, 0);
v_name_3493_ = lean_ctor_get(v_toConstantVal_3492_, 0);
lean_inc(v_name_3493_);
v___x_3494_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3494_, 0, v_val_3485_);
v___x_3495_ = 3;
v___x_3496_ = lean_box(v___x_3495_);
v___x_3497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3494_);
lean_ctor_set(v___x_3497_, 1, v___x_3496_);
v___x_3498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3498_, 0, v_name_3493_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
lean_inc(v___y_3490_);
lean_inc_ref(v___y_3489_);
v___x_3499_ = lean_apply_5(v___f_3486_, v___x_3498_, v_exportedInfo_x3f_3488_, v___y_3489_, v___y_3490_, lean_box(0));
return v___x_3499_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3485_ = stack[0].m_obj;
lean_object* v___f_3486_ = stack[1].m_obj;
lean_object* v_____r_3487_ = stack[2].m_obj;
lean_object* v_exportedInfo_x3f_3488_ = stack[3].m_obj;
lean_object* v___y_3489_ = stack[4].m_obj;
lean_object* v___y_3490_ = stack[5].m_obj;
lean_object* v_res_3500_;
v_res_3500_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3485_, v___f_3486_, v_____r_3487_, v_exportedInfo_x3f_3488_, v___y_3489_, v___y_3490_);
stack->m_obj
 = v_res_3500_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3501_, lean_object* v___f_3502_, lean_object* v_____r_3503_, lean_object* v_exportedInfo_x3f_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_, lean_object* v___y_3507_){
_start:
{
lean_object* v_res_3508_; 
v_res_3508_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3501_, v___f_3502_, v_____r_3503_, v_exportedInfo_x3f_3504_, v___y_3505_, v___y_3506_);
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
return v_res_3508_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3509_, lean_object* v___f_3510_, lean_object* v_____r_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v_toConstantVal_3515_; uint8_t v_isUnsafe_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; 
v_toConstantVal_3515_ = lean_ctor_get(v_val_3509_, 0);
v_isUnsafe_3516_ = lean_ctor_get_uint8(v_val_3509_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3515_);
v___x_3517_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3517_, 0, v_toConstantVal_3515_);
lean_ctor_set_uint8(v___x_3517_, sizeof(void*)*1, v_isUnsafe_3516_);
v___x_3518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3519_, 0, v___x_3518_);
v___x_3520_ = lean_box(0);
lean_inc(v___y_3513_);
lean_inc_ref(v___y_3512_);
v___x_3521_ = lean_apply_5(v___f_3510_, v___x_3520_, v___x_3519_, v___y_3512_, v___y_3513_, lean_box(0));
return v___x_3521_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3509_ = stack[0].m_obj;
lean_object* v___f_3510_ = stack[1].m_obj;
lean_object* v_____r_3511_ = stack[2].m_obj;
lean_object* v___y_3512_ = stack[3].m_obj;
lean_object* v___y_3513_ = stack[4].m_obj;
lean_object* v_res_3522_;
v_res_3522_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3509_, v___f_3510_, v_____r_3511_, v___y_3512_, v___y_3513_);
stack->m_obj
 = v_res_3522_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3523_, lean_object* v___f_3524_, lean_object* v_____r_3525_, lean_object* v___y_3526_, lean_object* v___y_3527_, lean_object* v___y_3528_){
_start:
{
lean_object* v_res_3529_; 
v_res_3529_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3523_, v___f_3524_, v_____r_3525_, v___y_3526_, v___y_3527_);
lean_dec(v___y_3527_);
lean_dec_ref(v___y_3526_);
lean_dec_ref(v_val_3523_);
return v_res_3529_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3530_, uint8_t v___x_3531_, lean_object* v___x_3532_, lean_object* v_cls_3533_, uint8_t v___x_3534_, lean_object* v___x_3535_, lean_object* v_____x_3536_, lean_object* v_exportedInfo_x3f_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_){
_start:
{
lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v_a_3544_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v_a_3557_; lean_object* v___y_3568_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3574_; uint8_t v___y_3575_; lean_object* v___y_3576_; lean_object* v___y_3577_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v_snd_3641_; lean_object* v_fst_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3785_; 
v_snd_3641_ = lean_ctor_get(v_____x_3536_, 1);
v_fst_3642_ = lean_ctor_get(v_____x_3536_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_____x_3536_);
if (v_isSharedCheck_3785_ == 0)
{
v___x_3644_ = v_____x_3536_;
v_isShared_3645_ = v_isSharedCheck_3785_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_snd_3641_);
lean_inc(v_fst_3642_);
lean_dec(v_____x_3536_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3785_;
goto v_resetjp_3643_;
}
v___jp_3541_:
{
lean_object* v___x_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
v___x_3545_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3542_, v___y_3543_);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3552_ == 0)
{
lean_object* v_unused_3553_; 
v_unused_3553_ = lean_ctor_get(v___x_3545_, 0);
lean_dec(v_unused_3553_);
v___x_3547_ = v___x_3545_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_dec(v___x_3545_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 1);
lean_ctor_set(v___x_3547_, 0, v_a_3544_);
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3544_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
v___jp_3554_:
{
lean_object* v___x_3558_; lean_object* v___x_3560_; uint8_t v_isShared_3561_; uint8_t v_isSharedCheck_3565_; 
v___x_3558_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3555_, v___y_3556_);
v_isSharedCheck_3565_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3565_ == 0)
{
lean_object* v_unused_3566_; 
v_unused_3566_ = lean_ctor_get(v___x_3558_, 0);
lean_dec(v_unused_3566_);
v___x_3560_ = v___x_3558_;
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
else
{
lean_dec(v___x_3558_);
v___x_3560_ = lean_box(0);
v_isShared_3561_ = v_isSharedCheck_3565_;
goto v_resetjp_3559_;
}
v_resetjp_3559_:
{
lean_object* v___x_3563_; 
if (v_isShared_3561_ == 0)
{
lean_ctor_set(v___x_3560_, 0, v_a_3557_);
v___x_3563_ = v___x_3560_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v_a_3557_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
return v___x_3563_;
}
}
}
v___jp_3567_:
{
lean_object* v___x_3580_; 
lean_inc_ref(v___y_3574_);
v___x_3580_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3569_, v___y_3574_, v___y_3573_, v___y_3579_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v___x_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3627_; 
lean_dec_ref_known(v___x_3580_, 1);
lean_dec(v___y_3577_);
lean_inc_ref(v___y_3570_);
v___x_3581_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3570_, v___y_3572_);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3581_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v___x_3581_, 0);
lean_dec(v_unused_3628_);
v___x_3583_ = v___x_3581_;
v_isShared_3584_ = v_isSharedCheck_3627_;
goto v_resetjp_3582_;
}
else
{
lean_dec(v___x_3581_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3627_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3585_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3578_);
v___x_3586_ = l_Lean_Elab_async;
v___x_3587_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3585_, v___x_3586_);
lean_dec_ref(v___x_3585_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v_r_3589_; 
lean_del_object(v___x_3583_);
lean_dec_ref(v___y_3576_);
lean_dec_ref(v___y_3571_);
v___x_3588_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3574_, v___y_3572_);
lean_dec_ref(v___x_3588_);
v_r_3589_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3530_, v___y_3578_, v___y_3572_);
if (lean_obj_tag(v_r_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3599_; 
v_a_3590_ = lean_ctor_get(v_r_3589_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_r_3589_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3592_ = v_r_3589_;
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v_r_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3599_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3595_; 
lean_inc(v_a_3590_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set_tag(v___x_3592_, 1);
v___x_3595_ = v___x_3592_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3590_);
v___x_3595_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_apply_2(v___y_3568_, v___x_3595_, lean_box(0));
if (lean_obj_tag(v___x_3596_) == 0)
{
lean_dec_ref_known(v___x_3596_, 1);
v___y_3555_ = v___y_3570_;
v___y_3556_ = v___y_3572_;
v_a_3557_ = v_a_3590_;
goto v___jp_3554_;
}
else
{
lean_object* v_a_3597_; 
lean_dec(v_a_3590_);
v_a_3597_ = lean_ctor_get(v___x_3596_, 0);
lean_inc(v_a_3597_);
lean_dec_ref_known(v___x_3596_, 1);
v___y_3542_ = v___y_3570_;
v___y_3543_ = v___y_3572_;
v_a_3544_ = v_a_3597_;
goto v___jp_3541_;
}
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; 
v_a_3600_ = lean_ctor_get(v_r_3589_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v_r_3589_, 1);
v___x_3601_ = lean_box(0);
v___x_3602_ = lean_apply_2(v___y_3568_, v___x_3601_, lean_box(0));
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_dec_ref_known(v___x_3602_, 1);
v___y_3542_ = v___y_3570_;
v___y_3543_ = v___y_3572_;
v_a_3544_ = v_a_3600_;
goto v___jp_3541_;
}
else
{
lean_object* v_a_3603_; 
lean_dec(v_a_3600_);
v_a_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc(v_a_3603_);
lean_dec_ref_known(v___x_3602_, 1);
v___y_3542_ = v___y_3570_;
v___y_3543_ = v___y_3572_;
v_a_3544_ = v_a_3603_;
goto v___jp_3541_;
}
}
}
else
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
lean_dec_ref(v___y_3574_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3568_);
lean_dec(v_decl_3530_);
v___x_3604_ = l_IO_CancelToken_new();
if (v_isShared_3584_ == 0)
{
lean_ctor_set_tag(v___x_3583_, 1);
lean_ctor_set(v___x_3583_, 0, v___x_3604_);
v___x_3606_ = v___x_3583_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3609_ = l_Lean_Name_toString(v___x_3608_, v___x_3531_);
lean_inc_ref(v___x_3606_);
v___x_3610_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3576_, v___x_3606_, v___x_3609_, v___y_3578_, v___y_3572_);
if (lean_obj_tag(v___x_3610_) == 0)
{
lean_object* v_a_3611_; lean_object* v_checked_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc(v_a_3611_);
lean_dec_ref_known(v___x_3610_, 1);
v_checked_3612_ = lean_ctor_get(v___y_3571_, 2);
lean_inc_ref(v_checked_3612_);
lean_dec_ref(v___y_3571_);
v___x_3613_ = lean_io_map_task(v_a_3611_, v_checked_3612_, v___x_3607_, v___y_3575_);
v___x_3614_ = lean_box(0);
v___x_3615_ = lean_box(2);
v___x_3616_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
lean_ctor_set(v___x_3616_, 2, v___x_3606_);
lean_ctor_set(v___x_3616_, 3, v___x_3613_);
v___x_3617_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3616_, v___y_3572_);
return v___x_3617_;
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_dec_ref(v___x_3606_);
lean_dec_ref(v___y_3571_);
v_a_3618_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3610_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3610_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3629_; lean_object* v___x_3631_; uint8_t v_isShared_3632_; uint8_t v_isSharedCheck_3640_; 
lean_dec_ref(v___y_3576_);
lean_dec_ref(v___y_3574_);
lean_dec_ref(v___y_3571_);
lean_dec_ref(v___y_3570_);
lean_dec_ref(v___y_3568_);
lean_dec(v_decl_3530_);
v_a_3629_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3631_ = v___x_3580_;
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
else
{
lean_inc(v_a_3629_);
lean_dec(v___x_3580_);
v___x_3631_ = lean_box(0);
v_isShared_3632_ = v_isSharedCheck_3640_;
goto v_resetjp_3630_;
}
v_resetjp_3630_:
{
lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3638_; 
v___x_3633_ = lean_io_error_to_string(v_a_3629_);
v___x_3634_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3634_, 0, v___x_3633_);
v___x_3635_ = l_Lean_MessageData_ofFormat(v___x_3634_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___y_3577_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
if (v_isShared_3632_ == 0)
{
lean_ctor_set(v___x_3631_, 0, v___x_3636_);
v___x_3638_ = v___x_3631_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v___x_3636_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
v_resetjp_3643_:
{
lean_object* v_fst_3646_; lean_object* v_snd_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3784_; 
v_fst_3646_ = lean_ctor_get(v_snd_3641_, 0);
v_snd_3647_ = lean_ctor_get(v_snd_3641_, 1);
v_isSharedCheck_3784_ = !lean_is_exclusive(v_snd_3641_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3649_ = v_snd_3641_;
v_isShared_3650_ = v_isSharedCheck_3784_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_snd_3647_);
lean_inc(v_fst_3646_);
lean_dec(v_snd_3641_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3784_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___y_3652_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; lean_object* v___y_3656_; lean_object* v_exportedInfo_x3f_3682_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3694_; lean_object* v___y_3695_; lean_object* v___y_3698_; lean_object* v___y_3699_; uint8_t v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; uint8_t v___y_3727_; lean_object* v___y_3728_; lean_object* v___y_3729_; uint8_t v___y_3730_; lean_object* v___y_3748_; lean_object* v___y_3749_; lean_object* v___x_3774_; lean_object* v_env_3775_; uint8_t v___x_3776_; 
v___x_3774_ = lean_st_ref_get(v___y_3539_);
v_env_3775_ = lean_ctor_get(v___x_3774_, 0);
lean_inc_ref(v_env_3775_);
lean_dec(v___x_3774_);
v___x_3776_ = l_Lean_Environment_containsOnBranch(v_env_3775_, v_fst_3642_);
lean_dec_ref(v_env_3775_);
if (v___x_3776_ == 0)
{
lean_del_object(v___x_3644_);
v___y_3748_ = v___y_3538_;
v___y_3749_ = v___y_3539_;
goto v___jp_3747_;
}
else
{
lean_object* v___x_3777_; lean_object* v_env_3778_; lean_object* v___x_3779_; lean_object* v___x_3781_; 
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_exportedInfo_x3f_3537_);
lean_dec(v___x_3535_);
lean_dec(v_cls_3533_);
lean_dec_ref(v___x_3532_);
lean_dec(v_decl_3530_);
v___x_3777_ = lean_st_ref_get(v___y_3539_);
v_env_3778_ = lean_ctor_get(v___x_3777_, 0);
lean_inc_ref(v_env_3778_);
lean_dec(v___x_3777_);
v___x_3779_ = lean_elab_environment_to_kernel_env(v_env_3778_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 1);
lean_ctor_set(v___x_3644_, 1, v_fst_3642_);
lean_ctor_set(v___x_3644_, 0, v___x_3779_);
v___x_3781_ = v___x_3644_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v___x_3779_);
lean_ctor_set(v_reuseFailAlloc_3783_, 1, v_fst_3642_);
v___x_3781_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3781_, v___y_3538_, v___y_3539_);
return v___x_3782_;
}
}
v___jp_3651_:
{
lean_object* v_ref_3657_; uint8_t v___x_3658_; uint8_t v___x_3659_; lean_object* v___x_3660_; 
v_ref_3657_ = lean_ctor_get(v___y_3653_, 2);
v___x_3658_ = 0;
v___x_3659_ = lean_unbox(v_snd_3647_);
lean_dec(v_snd_3647_);
lean_inc_ref(v___y_3655_);
v___x_3660_ = l_Lean_Environment_addConstAsync(v___y_3655_, v_fst_3642_, v___x_3659_, v___y_3656_, v___x_3658_, v___x_3531_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v_mainEnv_3662_; lean_object* v_asyncEnv_3663_; lean_object* v___f_3664_; lean_object* v___f_3665_; lean_object* v___x_3666_; 
lean_del_object(v___x_3649_);
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc_n(v_a_3661_, 3);
lean_dec_ref_known(v___x_3660_, 1);
v_mainEnv_3662_ = lean_ctor_get(v_a_3661_, 0);
lean_inc_ref(v_mainEnv_3662_);
v_asyncEnv_3663_ = lean_ctor_get(v_a_3661_, 1);
lean_inc_ref_n(v_asyncEnv_3663_, 2);
lean_inc(v_ref_3657_);
lean_inc(v___y_3654_);
v___f_3664_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3664_, 0, v___y_3654_);
lean_closure_set(v___f_3664_, 1, v_a_3661_);
lean_closure_set(v___f_3664_, 2, v_ref_3657_);
lean_inc(v_decl_3530_);
v___f_3665_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3665_, 0, v_a_3661_);
lean_closure_set(v___f_3665_, 1, v_asyncEnv_3663_);
lean_closure_set(v___f_3665_, 2, v_decl_3530_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v_fst_3646_);
if (lean_obj_tag(v___y_3652_) == 0)
{
lean_inc(v_ref_3657_);
lean_inc_ref(v___x_3666_);
v___y_3568_ = v___f_3664_;
v___y_3569_ = v_a_3661_;
v___y_3570_ = v_mainEnv_3662_;
v___y_3571_ = v___y_3655_;
v___y_3572_ = v___y_3654_;
v___y_3573_ = v___x_3666_;
v___y_3574_ = v_asyncEnv_3663_;
v___y_3575_ = v___x_3658_;
v___y_3576_ = v___f_3665_;
v___y_3577_ = v_ref_3657_;
v___y_3578_ = v___y_3653_;
v___y_3579_ = v___x_3666_;
goto v___jp_3567_;
}
else
{
lean_inc(v_ref_3657_);
v___y_3568_ = v___f_3664_;
v___y_3569_ = v_a_3661_;
v___y_3570_ = v_mainEnv_3662_;
v___y_3571_ = v___y_3655_;
v___y_3572_ = v___y_3654_;
v___y_3573_ = v___x_3666_;
v___y_3574_ = v_asyncEnv_3663_;
v___y_3575_ = v___x_3658_;
v___y_3576_ = v___f_3665_;
v___y_3577_ = v_ref_3657_;
v___y_3578_ = v___y_3653_;
v___y_3579_ = v___y_3652_;
goto v___jp_3567_;
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3680_; 
lean_dec_ref(v___y_3655_);
lean_dec(v___y_3652_);
lean_dec(v_fst_3646_);
lean_dec(v_decl_3530_);
v_a_3667_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3669_ = v___x_3660_;
v_isShared_3670_ = v_isSharedCheck_3680_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3660_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3680_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3675_; 
v___x_3671_ = lean_io_error_to_string(v_a_3667_);
v___x_3672_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3672_, 0, v___x_3671_);
v___x_3673_ = l_Lean_MessageData_ofFormat(v___x_3672_);
lean_inc(v_ref_3657_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 1, v___x_3673_);
lean_ctor_set(v___x_3649_, 0, v_ref_3657_);
v___x_3675_ = v___x_3649_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_ref_3657_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___x_3675_);
v___x_3677_ = v___x_3669_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3675_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
v___jp_3681_:
{
lean_object* v___x_3685_; 
v___x_3685_ = lean_st_ref_get(v___y_3684_);
if (lean_obj_tag(v_exportedInfo_x3f_3682_) == 0)
{
lean_object* v_env_3686_; lean_object* v___x_3687_; 
v_env_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc_ref(v_env_3686_);
lean_dec(v___x_3685_);
v___x_3687_ = lean_box(0);
v___y_3652_ = v_exportedInfo_x3f_3682_;
v___y_3653_ = v___y_3683_;
v___y_3654_ = v___y_3684_;
v___y_3655_ = v_env_3686_;
v___y_3656_ = v___x_3687_;
goto v___jp_3651_;
}
else
{
lean_object* v_env_3688_; lean_object* v_val_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v_env_3688_ = lean_ctor_get(v___x_3685_, 0);
lean_inc_ref(v_env_3688_);
lean_dec(v___x_3685_);
v_val_3689_ = lean_ctor_get(v_exportedInfo_x3f_3682_, 0);
v___x_3690_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3689_);
v___x_3691_ = lean_box(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
v___y_3652_ = v_exportedInfo_x3f_3682_;
v___y_3653_ = v___y_3683_;
v___y_3654_ = v___y_3684_;
v___y_3655_ = v_env_3688_;
v___y_3656_ = v___x_3692_;
goto v___jp_3651_;
}
}
v___jp_3693_:
{
lean_object* v___x_3696_; 
lean_inc(v_fst_3646_);
v___x_3696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3696_, 0, v_fst_3646_);
v_exportedInfo_x3f_3682_ = v___x_3696_;
v___y_3683_ = v___y_3694_;
v___y_3684_ = v___y_3695_;
goto v___jp_3681_;
}
v___jp_3697_:
{
lean_object* v___x_3700_; 
lean_inc(v_fst_3646_);
v___x_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3700_, 0, v_fst_3646_);
v_exportedInfo_x3f_3682_ = v___x_3700_;
v___y_3683_ = v___y_3698_;
v___y_3684_ = v___y_3699_;
goto v___jp_3681_;
}
v___jp_3701_:
{
lean_object* v___x_3706_; lean_object* v_env_3707_; lean_object* v_nextMacroScope_3708_; lean_object* v_ngen_3709_; lean_object* v_auxDeclNGen_3710_; lean_object* v_traceState_3711_; lean_object* v_recordedDeps_3712_; lean_object* v_messages_3713_; lean_object* v_infoState_3714_; lean_object* v_snapshotTasks_3715_; lean_object* v___x_3717_; uint8_t v_isShared_3718_; uint8_t v_isSharedCheck_3724_; 
v___x_3706_ = lean_st_ref_take(v___y_3705_);
v_env_3707_ = lean_ctor_get(v___x_3706_, 0);
v_nextMacroScope_3708_ = lean_ctor_get(v___x_3706_, 1);
v_ngen_3709_ = lean_ctor_get(v___x_3706_, 2);
v_auxDeclNGen_3710_ = lean_ctor_get(v___x_3706_, 3);
v_traceState_3711_ = lean_ctor_get(v___x_3706_, 4);
v_recordedDeps_3712_ = lean_ctor_get(v___x_3706_, 6);
v_messages_3713_ = lean_ctor_get(v___x_3706_, 7);
v_infoState_3714_ = lean_ctor_get(v___x_3706_, 8);
v_snapshotTasks_3715_ = lean_ctor_get(v___x_3706_, 9);
v_isSharedCheck_3724_ = !lean_is_exclusive(v___x_3706_);
if (v_isSharedCheck_3724_ == 0)
{
lean_object* v_unused_3725_; 
v_unused_3725_ = lean_ctor_get(v___x_3706_, 5);
lean_dec(v_unused_3725_);
v___x_3717_ = v___x_3706_;
v_isShared_3718_ = v_isSharedCheck_3724_;
goto v_resetjp_3716_;
}
else
{
lean_inc(v_snapshotTasks_3715_);
lean_inc(v_infoState_3714_);
lean_inc(v_messages_3713_);
lean_inc(v_recordedDeps_3712_);
lean_inc(v_traceState_3711_);
lean_inc(v_auxDeclNGen_3710_);
lean_inc(v_ngen_3709_);
lean_inc(v_nextMacroScope_3708_);
lean_inc(v_env_3707_);
lean_dec(v___x_3706_);
v___x_3717_ = lean_box(0);
v_isShared_3718_ = v_isSharedCheck_3724_;
goto v_resetjp_3716_;
}
v_resetjp_3716_:
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_inc(v_snd_3647_);
lean_inc(v_fst_3642_);
lean_inc_ref(v___y_3703_);
v___x_3719_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_3703_, v_env_3707_, v_fst_3642_, v_snd_3647_, v___y_3702_);
if (v_isShared_3718_ == 0)
{
lean_ctor_set(v___x_3717_, 5, v___x_3532_);
lean_ctor_set(v___x_3717_, 0, v___x_3719_);
v___x_3721_ = v___x_3717_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3723_; 
v_reuseFailAlloc_3723_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3723_, 0, v___x_3719_);
lean_ctor_set(v_reuseFailAlloc_3723_, 1, v_nextMacroScope_3708_);
lean_ctor_set(v_reuseFailAlloc_3723_, 2, v_ngen_3709_);
lean_ctor_set(v_reuseFailAlloc_3723_, 3, v_auxDeclNGen_3710_);
lean_ctor_set(v_reuseFailAlloc_3723_, 4, v_traceState_3711_);
lean_ctor_set(v_reuseFailAlloc_3723_, 5, v___x_3532_);
lean_ctor_set(v_reuseFailAlloc_3723_, 6, v_recordedDeps_3712_);
lean_ctor_set(v_reuseFailAlloc_3723_, 7, v_messages_3713_);
lean_ctor_set(v_reuseFailAlloc_3723_, 8, v_infoState_3714_);
lean_ctor_set(v_reuseFailAlloc_3723_, 9, v_snapshotTasks_3715_);
v___x_3721_ = v_reuseFailAlloc_3723_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3722_; 
v___x_3722_ = lean_st_ref_put(v___y_3705_, v___x_3721_);
v_exportedInfo_x3f_3682_ = v_exportedInfo_x3f_3537_;
v___y_3683_ = v___y_3704_;
v___y_3684_ = v___y_3705_;
goto v___jp_3681_;
}
}
}
v___jp_3726_:
{
if (v___y_3730_ == 0)
{
lean_object* v_toCold_3731_; lean_object* v_options_3732_; uint8_t v_hasTrace_3733_; 
lean_dec(v_exportedInfo_x3f_3537_);
lean_dec_ref(v___x_3532_);
v_toCold_3731_ = lean_ctor_get(v___y_3728_, 0);
v_options_3732_ = lean_ctor_get(v_toCold_3731_, 2);
v_hasTrace_3733_ = lean_ctor_get_uint8(v_options_3732_, sizeof(void*)*1);
if (v_hasTrace_3733_ == 0)
{
lean_dec(v_cls_3533_);
v___y_3698_ = v___y_3728_;
v___y_3699_ = v___y_3729_;
goto v___jp_3697_;
}
else
{
lean_object* v_inheritedTraceOptions_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; uint8_t v___x_3737_; 
v_inheritedTraceOptions_3734_ = lean_ctor_get(v_toCold_3731_, 11);
v___x_3735_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3533_);
v___x_3736_ = l_Lean_Name_append(v___x_3735_, v_cls_3533_);
v___x_3737_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3734_, v_options_3732_, v___x_3736_);
lean_dec(v___x_3736_);
if (v___x_3737_ == 0)
{
lean_dec(v_cls_3533_);
v___y_3698_ = v___y_3728_;
v___y_3699_ = v___y_3729_;
goto v___jp_3697_;
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; 
v___x_3738_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3739_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3533_, v___x_3738_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_dec_ref_known(v___x_3739_, 1);
v___y_3698_ = v___y_3728_;
v___y_3699_ = v___y_3729_;
goto v___jp_3697_;
}
else
{
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_dec(v_decl_3530_);
return v___x_3739_;
}
}
}
}
else
{
lean_object* v___x_3740_; lean_object* v_env_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; uint8_t v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; 
lean_dec(v_cls_3533_);
v___x_3740_ = lean_st_ref_get(v___y_3729_);
v_env_3741_ = lean_ctor_get(v___x_3740_, 0);
lean_inc_ref(v_env_3741_);
lean_dec(v___x_3740_);
v___x_3742_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3743_ = lean_box(1);
v___x_3744_ = 0;
v___x_3745_ = lean_box(v___x_3534_);
lean_inc(v_fst_3642_);
v___x_3746_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_3745_, v___x_3742_, v_env_3741_, v_fst_3642_, v___x_3743_, v___x_3744_);
if (lean_obj_tag(v___x_3746_) == 0)
{
v___y_3702_ = v___y_3727_;
v___y_3703_ = v___x_3742_;
v___y_3704_ = v___y_3728_;
v___y_3705_ = v___y_3729_;
goto v___jp_3701_;
}
else
{
lean_dec_ref_known(v___x_3746_, 1);
if (v___y_3727_ == 0)
{
lean_dec_ref(v___x_3532_);
v_exportedInfo_x3f_3682_ = v_exportedInfo_x3f_3537_;
v___y_3683_ = v___y_3728_;
v___y_3684_ = v___y_3729_;
goto v___jp_3681_;
}
else
{
v___y_3702_ = v___y_3727_;
v___y_3703_ = v___x_3742_;
v___y_3704_ = v___y_3728_;
v___y_3705_ = v___y_3729_;
goto v___jp_3701_;
}
}
}
}
v___jp_3747_:
{
lean_object* v___x_3750_; uint8_t v___x_3751_; 
lean_inc(v_decl_3530_);
v___x_3750_ = l_Lean_Declaration_getTopLevelNames(v_decl_3530_);
v___x_3751_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3750_);
lean_dec(v___x_3750_);
if (v___x_3751_ == 0)
{
lean_dec(v___x_3535_);
if (lean_obj_tag(v_exportedInfo_x3f_3537_) == 0)
{
v___y_3727_ = v___x_3751_;
v___y_3728_ = v___y_3748_;
v___y_3729_ = v___y_3749_;
v___y_3730_ = v___x_3751_;
goto v___jp_3726_;
}
else
{
v___y_3727_ = v___x_3751_;
v___y_3728_ = v___y_3748_;
v___y_3729_ = v___y_3749_;
v___y_3730_ = v___x_3531_;
goto v___jp_3726_;
}
}
else
{
lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v_a_3754_; uint8_t v___x_3755_; 
lean_dec(v_exportedInfo_x3f_3537_);
lean_dec_ref(v___x_3532_);
v___x_3752_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3753_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3752_, v___y_3748_);
v_a_3754_ = lean_ctor_get(v___x_3753_, 0);
lean_inc(v_a_3754_);
lean_dec_ref(v___x_3753_);
v___x_3755_ = lean_unbox(v_a_3754_);
lean_dec(v_a_3754_);
if (v___x_3755_ == 0)
{
lean_object* v_toCold_3756_; lean_object* v_options_3757_; uint8_t v_hasTrace_3758_; 
v_toCold_3756_ = lean_ctor_get(v___y_3748_, 0);
v_options_3757_ = lean_ctor_get(v_toCold_3756_, 2);
v_hasTrace_3758_ = lean_ctor_get_uint8(v_options_3757_, sizeof(void*)*1);
if (v_hasTrace_3758_ == 0)
{
lean_dec(v_cls_3533_);
v_exportedInfo_x3f_3682_ = v___x_3535_;
v___y_3683_ = v___y_3748_;
v___y_3684_ = v___y_3749_;
goto v___jp_3681_;
}
else
{
lean_object* v_inheritedTraceOptions_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; 
v_inheritedTraceOptions_3759_ = lean_ctor_get(v_toCold_3756_, 11);
v___x_3760_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3533_);
v___x_3761_ = l_Lean_Name_append(v___x_3760_, v_cls_3533_);
v___x_3762_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3759_, v_options_3757_, v___x_3761_);
lean_dec(v___x_3761_);
if (v___x_3762_ == 0)
{
lean_dec(v_cls_3533_);
v_exportedInfo_x3f_3682_ = v___x_3535_;
v___y_3683_ = v___y_3748_;
v___y_3684_ = v___y_3749_;
goto v___jp_3681_;
}
else
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
v___x_3763_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3764_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3533_, v___x_3763_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_dec_ref_known(v___x_3764_, 1);
v_exportedInfo_x3f_3682_ = v___x_3535_;
v___y_3683_ = v___y_3748_;
v___y_3684_ = v___y_3749_;
goto v___jp_3681_;
}
else
{
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_dec(v___x_3535_);
lean_dec(v_decl_3530_);
return v___x_3764_;
}
}
}
}
else
{
lean_object* v_toCold_3765_; lean_object* v_options_3766_; uint8_t v_hasTrace_3767_; 
lean_dec(v___x_3535_);
v_toCold_3765_ = lean_ctor_get(v___y_3748_, 0);
v_options_3766_ = lean_ctor_get(v_toCold_3765_, 2);
v_hasTrace_3767_ = lean_ctor_get_uint8(v_options_3766_, sizeof(void*)*1);
if (v_hasTrace_3767_ == 0)
{
lean_dec(v_cls_3533_);
v___y_3694_ = v___y_3748_;
v___y_3695_ = v___y_3749_;
goto v___jp_3693_;
}
else
{
lean_object* v_inheritedTraceOptions_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; uint8_t v___x_3771_; 
v_inheritedTraceOptions_3768_ = lean_ctor_get(v_toCold_3765_, 11);
v___x_3769_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3533_);
v___x_3770_ = l_Lean_Name_append(v___x_3769_, v_cls_3533_);
v___x_3771_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3768_, v_options_3766_, v___x_3770_);
lean_dec(v___x_3770_);
if (v___x_3771_ == 0)
{
lean_dec(v_cls_3533_);
v___y_3694_ = v___y_3748_;
v___y_3695_ = v___y_3749_;
goto v___jp_3693_;
}
else
{
lean_object* v___x_3772_; lean_object* v___x_3773_; 
v___x_3772_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3773_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3533_, v___x_3772_, v___y_3748_, v___y_3749_);
if (lean_obj_tag(v___x_3773_) == 0)
{
lean_dec_ref_known(v___x_3773_, 1);
v___y_3694_ = v___y_3748_;
v___y_3695_ = v___y_3749_;
goto v___jp_3693_;
}
else
{
lean_del_object(v___x_3649_);
lean_dec(v_snd_3647_);
lean_dec(v_fst_3646_);
lean_dec(v_fst_3642_);
lean_dec(v_decl_3530_);
return v___x_3773_;
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
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3530_ = stack[0].m_obj;
uint8_t v___x_3531_ = stack[1].m_num;
lean_object* v___x_3532_ = stack[2].m_obj;
lean_object* v_cls_3533_ = stack[3].m_obj;
uint8_t v___x_3534_ = stack[4].m_num;
lean_object* v___x_3535_ = stack[5].m_obj;
lean_object* v_____x_3536_ = stack[6].m_obj;
lean_object* v_exportedInfo_x3f_3537_ = stack[7].m_obj;
lean_object* v___y_3538_ = stack[8].m_obj;
lean_object* v___y_3539_ = stack[9].m_obj;
lean_object* v_res_3786_;
v_res_3786_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3530_, v___x_3531_, v___x_3532_, v_cls_3533_, v___x_3534_, v___x_3535_, v_____x_3536_, v_exportedInfo_x3f_3537_, v___y_3538_, v___y_3539_);
stack->m_obj
 = v_res_3786_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3787_, lean_object* v___x_3788_, lean_object* v___x_3789_, lean_object* v_cls_3790_, lean_object* v___x_3791_, lean_object* v___x_3792_, lean_object* v_____x_3793_, lean_object* v_exportedInfo_x3f_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_){
_start:
{
uint8_t v___x_55470__boxed_3798_; uint8_t v___x_55473__boxed_3799_; lean_object* v_res_3800_; 
v___x_55470__boxed_3798_ = lean_unbox(v___x_3788_);
v___x_55473__boxed_3799_ = lean_unbox(v___x_3791_);
v_res_3800_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3787_, v___x_55470__boxed_3798_, v___x_3789_, v_cls_3790_, v___x_55473__boxed_3799_, v___x_3792_, v_____x_3793_, v_exportedInfo_x3f_3794_, v___y_3795_, v___y_3796_);
lean_dec(v___y_3796_);
lean_dec_ref(v___y_3795_);
return v_res_3800_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3801_, uint8_t v_forceExpose_3802_, uint8_t v___x_3803_, lean_object* v___x_3804_, lean_object* v_cls_3805_, lean_object* v_defn_3806_, lean_object* v___y_3807_, lean_object* v___y_3808_){
_start:
{
lean_object* v_exportedInfo_x3f_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; uint8_t v___y_3826_; lean_object* v___x_3830_; lean_object* v_env_3831_; lean_object* v___x_3832_; 
v___x_3830_ = lean_st_ref_get(v___y_3808_);
v_env_3831_ = lean_ctor_get(v___x_3830_, 0);
lean_inc_ref(v_env_3831_);
lean_dec(v___x_3830_);
v___x_3832_ = lean_st_ref_get(v___y_3808_);
if (v_forceExpose_3802_ == 0)
{
if (v___x_3803_ == 0)
{
lean_dec(v___x_3832_);
lean_dec_ref(v_env_3831_);
lean_dec(v_cls_3805_);
v_exportedInfo_x3f_3811_ = v___x_3804_;
v___y_3812_ = v___y_3807_;
v___y_3813_ = v___y_3808_;
goto v___jp_3810_;
}
else
{
lean_object* v_env_3833_; lean_object* v___x_3834_; uint8_t v_isModule_3835_; 
v_env_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc_ref(v_env_3833_);
lean_dec(v___x_3832_);
v___x_3834_ = l_Lean_Environment_header(v_env_3831_);
lean_dec_ref(v_env_3831_);
v_isModule_3835_ = lean_ctor_get_uint8(v___x_3834_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_3834_);
if (v_isModule_3835_ == 0)
{
lean_dec_ref(v_env_3833_);
lean_dec(v_cls_3805_);
v_exportedInfo_x3f_3811_ = v___x_3804_;
v___y_3812_ = v___y_3807_;
v___y_3813_ = v___y_3808_;
goto v___jp_3810_;
}
else
{
uint8_t v_isExporting_3836_; lean_object* v___y_3838_; lean_object* v___y_3839_; 
v_isExporting_3836_ = lean_ctor_get_uint8(v_env_3833_, sizeof(void*)*13);
lean_dec_ref(v_env_3833_);
if (v_isExporting_3836_ == 0)
{
lean_object* v_toCold_3844_; lean_object* v_options_3845_; uint8_t v_hasTrace_3846_; 
lean_dec(v___x_3804_);
v_toCold_3844_ = lean_ctor_get(v___y_3807_, 0);
v_options_3845_ = lean_ctor_get(v_toCold_3844_, 2);
v_hasTrace_3846_ = lean_ctor_get_uint8(v_options_3845_, sizeof(void*)*1);
if (v_hasTrace_3846_ == 0)
{
lean_dec(v_cls_3805_);
v___y_3838_ = v___y_3807_;
v___y_3839_ = v___y_3808_;
goto v___jp_3837_;
}
else
{
lean_object* v_inheritedTraceOptions_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; uint8_t v___x_3850_; 
v_inheritedTraceOptions_3847_ = lean_ctor_get(v_toCold_3844_, 11);
v___x_3848_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3805_);
v___x_3849_ = l_Lean_Name_append(v___x_3848_, v_cls_3805_);
v___x_3850_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3847_, v_options_3845_, v___x_3849_);
lean_dec(v___x_3849_);
if (v___x_3850_ == 0)
{
lean_dec(v_cls_3805_);
v___y_3838_ = v___y_3807_;
v___y_3839_ = v___y_3808_;
goto v___jp_3837_;
}
else
{
lean_object* v_toConstantVal_3851_; lean_object* v_name_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; 
v_toConstantVal_3851_ = lean_ctor_get(v_defn_3806_, 0);
v_name_3852_ = lean_ctor_get(v_toConstantVal_3851_, 0);
v___x_3853_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3852_);
v___x_3854_ = l_Lean_MessageData_ofName(v_name_3852_);
v___x_3855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
v___x_3856_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3857_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3857_, 0, v___x_3855_);
lean_ctor_set(v___x_3857_, 1, v___x_3856_);
v___x_3858_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3805_, v___x_3857_, v___y_3807_, v___y_3808_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_dec_ref_known(v___x_3858_, 1);
v___y_3838_ = v___y_3807_;
v___y_3839_ = v___y_3808_;
goto v___jp_3837_;
}
else
{
lean_dec_ref(v_defn_3806_);
lean_dec_ref(v___f_3801_);
return v___x_3858_;
}
}
}
}
else
{
lean_dec(v_cls_3805_);
v_exportedInfo_x3f_3811_ = v___x_3804_;
v___y_3812_ = v___y_3807_;
v___y_3813_ = v___y_3808_;
goto v___jp_3810_;
}
v___jp_3837_:
{
lean_object* v_toConstantVal_3840_; uint8_t v_safety_3841_; uint8_t v___x_3842_; uint8_t v___x_3843_; 
v_toConstantVal_3840_ = lean_ctor_get(v_defn_3806_, 0);
v_safety_3841_ = lean_ctor_get_uint8(v_defn_3806_, sizeof(void*)*4);
v___x_3842_ = 1;
v___x_3843_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3841_, v___x_3842_);
if (v___x_3843_ == 0)
{
lean_inc_ref(v_toConstantVal_3840_);
v___y_3823_ = v___y_3839_;
v___y_3824_ = v_toConstantVal_3840_;
v___y_3825_ = v___y_3838_;
v___y_3826_ = v_isModule_3835_;
goto v___jp_3822_;
}
else
{
lean_inc_ref(v_toConstantVal_3840_);
v___y_3823_ = v___y_3839_;
v___y_3824_ = v_toConstantVal_3840_;
v___y_3825_ = v___y_3838_;
v___y_3826_ = v_isExporting_3836_;
goto v___jp_3822_;
}
}
}
}
}
else
{
lean_dec(v___x_3832_);
lean_dec_ref(v_env_3831_);
lean_dec(v_cls_3805_);
v_exportedInfo_x3f_3811_ = v___x_3804_;
v___y_3812_ = v___y_3807_;
v___y_3813_ = v___y_3808_;
goto v___jp_3810_;
}
v___jp_3810_:
{
lean_object* v_toConstantVal_3814_; lean_object* v_name_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v_toConstantVal_3814_ = lean_ctor_get(v_defn_3806_, 0);
v_name_3815_ = lean_ctor_get(v_toConstantVal_3814_, 0);
lean_inc(v_name_3815_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_defn_3806_);
v___x_3817_ = 0;
v___x_3818_ = lean_box(v___x_3817_);
v___x_3819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3819_, 0, v___x_3816_);
lean_ctor_set(v___x_3819_, 1, v___x_3818_);
v___x_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3820_, 0, v_name_3815_);
lean_ctor_set(v___x_3820_, 1, v___x_3819_);
lean_inc(v___y_3813_);
lean_inc_ref(v___y_3812_);
v___x_3821_ = lean_apply_5(v___f_3801_, v___x_3820_, v_exportedInfo_x3f_3811_, v___y_3812_, v___y_3813_, lean_box(0));
return v___x_3821_;
}
v___jp_3822_:
{
lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v___x_3827_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3827_, 0, v___y_3824_);
lean_ctor_set_uint8(v___x_3827_, sizeof(void*)*1, v___y_3826_);
v___x_3828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
v___x_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3828_);
v_exportedInfo_x3f_3811_ = v___x_3829_;
v___y_3812_ = v___y_3825_;
v___y_3813_ = v___y_3823_;
goto v___jp_3810_;
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___f_3801_ = stack[0].m_obj;
uint8_t v_forceExpose_3802_ = stack[1].m_num;
uint8_t v___x_3803_ = stack[2].m_num;
lean_object* v___x_3804_ = stack[3].m_obj;
lean_object* v_cls_3805_ = stack[4].m_obj;
lean_object* v_defn_3806_ = stack[5].m_obj;
lean_object* v___y_3807_ = stack[6].m_obj;
lean_object* v___y_3808_ = stack[7].m_obj;
lean_object* v_res_3859_;
v_res_3859_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3801_, v_forceExpose_3802_, v___x_3803_, v___x_3804_, v_cls_3805_, v_defn_3806_, v___y_3807_, v___y_3808_);
stack->m_obj
 = v_res_3859_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3860_, lean_object* v_forceExpose_3861_, lean_object* v___x_3862_, lean_object* v___x_3863_, lean_object* v_cls_3864_, lean_object* v_defn_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
uint8_t v_forceExpose_boxed_3869_; uint8_t v___x_56202__boxed_3870_; lean_object* v_res_3871_; 
v_forceExpose_boxed_3869_ = lean_unbox(v_forceExpose_3861_);
v___x_56202__boxed_3870_ = lean_unbox(v___x_3862_);
v_res_3871_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3860_, v_forceExpose_boxed_3869_, v___x_56202__boxed_3870_, v___x_3863_, v_cls_3864_, v_defn_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
return v_res_3871_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3872_, lean_object* v___f_3873_, lean_object* v_____r_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v_toConstantVal_3878_; uint8_t v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v_toConstantVal_3878_ = lean_ctor_get(v_val_3872_, 0);
v___x_3879_ = 0;
lean_inc_ref(v_toConstantVal_3878_);
v___x_3880_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3880_, 0, v_toConstantVal_3878_);
lean_ctor_set_uint8(v___x_3880_, sizeof(void*)*1, v___x_3879_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
v___x_3882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
v___x_3883_ = lean_box(0);
lean_inc(v___y_3876_);
lean_inc_ref(v___y_3875_);
v___x_3884_ = lean_apply_5(v___f_3873_, v___x_3883_, v___x_3882_, v___y_3875_, v___y_3876_, lean_box(0));
return v___x_3884_;
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_3872_ = stack[0].m_obj;
lean_object* v___f_3873_ = stack[1].m_obj;
lean_object* v_____r_3874_ = stack[2].m_obj;
lean_object* v___y_3875_ = stack[3].m_obj;
lean_object* v___y_3876_ = stack[4].m_obj;
lean_object* v_res_3885_;
v_res_3885_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3872_, v___f_3873_, v_____r_3874_, v___y_3875_, v___y_3876_);
stack->m_obj
 = v_res_3885_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3886_, lean_object* v___f_3887_, lean_object* v_____r_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v_res_3892_; 
v_res_3892_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3886_, v___f_3887_, v_____r_3888_, v___y_3889_, v___y_3890_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v_val_3886_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3893_, lean_object* v_x_3894_){
_start:
{
if (lean_obj_tag(v_x_3894_) == 0)
{
return v_x_3893_;
}
else
{
lean_object* v_head_3895_; lean_object* v_tail_3896_; lean_object* v___x_3897_; 
v_head_3895_ = lean_ctor_get(v_x_3894_, 0);
lean_inc(v_head_3895_);
v_tail_3896_ = lean_ctor_get(v_x_3894_, 1);
lean_inc(v_tail_3896_);
lean_dec_ref_known(v_x_3894_, 2);
v___x_3897_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3893_, v_head_3895_);
v_x_3893_ = v___x_3897_;
v_x_3894_ = v_tail_3896_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v_cls_3899_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3900_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3901_ = l_Lean_Name_append(v___x_3900_, v_cls_3899_);
return v___x_3901_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3904_ = l_Lean_stringToMessageData(v___x_3903_);
return v___x_3904_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3907_ = l_Lean_stringToMessageData(v___x_3906_);
return v___x_3907_;
}
}
lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3908_, uint8_t v_forceExpose_3909_, lean_object* v_a_3910_, lean_object* v_a_3911_){
_start:
{
lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v_a_3916_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v_a_3929_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v_a_3942_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v_a_3955_; lean_object* v_toCold_3965_; lean_object* v_options_3966_; lean_object* v_inheritedTraceOptions_3967_; uint8_t v_hasTrace_3968_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v___y_3974_; uint8_t v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_4044_; uint8_t v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; lean_object* v___y_4050_; lean_object* v___y_4051_; uint8_t v___y_4074_; lean_object* v___y_4075_; lean_object* v___y_4076_; lean_object* v_exportedInfo_x3f_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; uint8_t v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; lean_object* v___y_4100_; uint8_t v___x_4102_; lean_object* v_cls_4103_; lean_object* v___y_4105_; lean_object* v_options_4106_; lean_object* v_inheritedTraceOptions_4107_; lean_object* v___y_4108_; 
v_toCold_3965_ = lean_ctor_get(v_a_3910_, 0);
v_options_3966_ = lean_ctor_get(v_toCold_3965_, 2);
v_inheritedTraceOptions_3967_ = lean_ctor_get(v_toCold_3965_, 11);
v_hasTrace_3968_ = lean_ctor_get_uint8(v_options_3966_, sizeof(void*)*1);
v___x_4102_ = 0;
v_cls_4103_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3968_ == 0)
{
lean_object* v___x_4115_; lean_object* v_env_4116_; lean_object* v_nextMacroScope_4117_; lean_object* v_ngen_4118_; lean_object* v_auxDeclNGen_4119_; lean_object* v_traceState_4120_; lean_object* v_recordedDeps_4121_; lean_object* v_messages_4122_; lean_object* v_infoState_4123_; lean_object* v_snapshotTasks_4124_; lean_object* v___x_4126_; uint8_t v_isShared_4127_; uint8_t v_isSharedCheck_4342_; 
v___x_4115_ = lean_st_ref_take(v_a_3911_);
v_env_4116_ = lean_ctor_get(v___x_4115_, 0);
v_nextMacroScope_4117_ = lean_ctor_get(v___x_4115_, 1);
v_ngen_4118_ = lean_ctor_get(v___x_4115_, 2);
v_auxDeclNGen_4119_ = lean_ctor_get(v___x_4115_, 3);
v_traceState_4120_ = lean_ctor_get(v___x_4115_, 4);
v_recordedDeps_4121_ = lean_ctor_get(v___x_4115_, 6);
v_messages_4122_ = lean_ctor_get(v___x_4115_, 7);
v_infoState_4123_ = lean_ctor_get(v___x_4115_, 8);
v_snapshotTasks_4124_ = lean_ctor_get(v___x_4115_, 9);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4342_ == 0)
{
lean_object* v_unused_4343_; 
v_unused_4343_ = lean_ctor_get(v___x_4115_, 5);
lean_dec(v_unused_4343_);
v___x_4126_ = v___x_4115_;
v_isShared_4127_ = v_isSharedCheck_4342_;
goto v_resetjp_4125_;
}
else
{
lean_inc(v_snapshotTasks_4124_);
lean_inc(v_infoState_4123_);
lean_inc(v_messages_4122_);
lean_inc(v_recordedDeps_4121_);
lean_inc(v_traceState_4120_);
lean_inc(v_auxDeclNGen_4119_);
lean_inc(v_ngen_4118_);
lean_inc(v_nextMacroScope_4117_);
lean_inc(v_env_4116_);
lean_dec(v___x_4115_);
v___x_4126_ = lean_box(0);
v_isShared_4127_ = v_isSharedCheck_4342_;
goto v_resetjp_4125_;
}
v_resetjp_4125_:
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___y_4132_; uint8_t v___y_4133_; uint8_t v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; lean_object* v___y_4162_; uint8_t v___y_4163_; uint8_t v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___x_4177_; 
lean_inc(v_decl_3908_);
v___x_4128_ = l_Lean_Declaration_getNames(v_decl_3908_);
v___x_4129_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4116_, v___x_4128_);
v___x_4130_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4127_ == 0)
{
lean_ctor_set(v___x_4126_, 5, v___x_4130_);
lean_ctor_set(v___x_4126_, 0, v___x_4129_);
v___x_4177_ = v___x_4126_;
goto v_reusejp_4176_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v___x_4129_);
lean_ctor_set(v_reuseFailAlloc_4341_, 1, v_nextMacroScope_4117_);
lean_ctor_set(v_reuseFailAlloc_4341_, 2, v_ngen_4118_);
lean_ctor_set(v_reuseFailAlloc_4341_, 3, v_auxDeclNGen_4119_);
lean_ctor_set(v_reuseFailAlloc_4341_, 4, v_traceState_4120_);
lean_ctor_set(v_reuseFailAlloc_4341_, 5, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4341_, 6, v_recordedDeps_4121_);
lean_ctor_set(v_reuseFailAlloc_4341_, 7, v_messages_4122_);
lean_ctor_set(v_reuseFailAlloc_4341_, 8, v_infoState_4123_);
lean_ctor_set(v_reuseFailAlloc_4341_, 9, v_snapshotTasks_4124_);
v___x_4177_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4176_;
}
v___jp_4131_:
{
lean_object* v___x_4140_; lean_object* v_env_4141_; lean_object* v_nextMacroScope_4142_; lean_object* v_ngen_4143_; lean_object* v_auxDeclNGen_4144_; lean_object* v_traceState_4145_; lean_object* v_recordedDeps_4146_; lean_object* v_messages_4147_; lean_object* v_infoState_4148_; lean_object* v_snapshotTasks_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4159_; 
v___x_4140_ = lean_st_ref_take(v___y_4132_);
v_env_4141_ = lean_ctor_get(v___x_4140_, 0);
v_nextMacroScope_4142_ = lean_ctor_get(v___x_4140_, 1);
v_ngen_4143_ = lean_ctor_get(v___x_4140_, 2);
v_auxDeclNGen_4144_ = lean_ctor_get(v___x_4140_, 3);
v_traceState_4145_ = lean_ctor_get(v___x_4140_, 4);
v_recordedDeps_4146_ = lean_ctor_get(v___x_4140_, 6);
v_messages_4147_ = lean_ctor_get(v___x_4140_, 7);
v_infoState_4148_ = lean_ctor_get(v___x_4140_, 8);
v_snapshotTasks_4149_ = lean_ctor_get(v___x_4140_, 9);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4159_ == 0)
{
lean_object* v_unused_4160_; 
v_unused_4160_ = lean_ctor_get(v___x_4140_, 5);
lean_dec(v_unused_4160_);
v___x_4151_ = v___x_4140_;
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_snapshotTasks_4149_);
lean_inc(v_infoState_4148_);
lean_inc(v_messages_4147_);
lean_inc(v_recordedDeps_4146_);
lean_inc(v_traceState_4145_);
lean_inc(v_auxDeclNGen_4144_);
lean_inc(v_ngen_4143_);
lean_inc(v_nextMacroScope_4142_);
lean_inc(v_env_4141_);
lean_dec(v___x_4140_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4159_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4156_; 
v___x_4153_ = lean_box(v___y_4134_);
lean_inc(v___y_4135_);
lean_inc_ref(v___y_4136_);
v___x_4154_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_4136_, v_env_4141_, v___y_4135_, v___x_4153_, v___y_4133_);
if (v_isShared_4152_ == 0)
{
lean_ctor_set(v___x_4151_, 5, v___x_4130_);
lean_ctor_set(v___x_4151_, 0, v___x_4154_);
v___x_4156_ = v___x_4151_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4154_);
lean_ctor_set(v_reuseFailAlloc_4158_, 1, v_nextMacroScope_4142_);
lean_ctor_set(v_reuseFailAlloc_4158_, 2, v_ngen_4143_);
lean_ctor_set(v_reuseFailAlloc_4158_, 3, v_auxDeclNGen_4144_);
lean_ctor_set(v_reuseFailAlloc_4158_, 4, v_traceState_4145_);
lean_ctor_set(v_reuseFailAlloc_4158_, 5, v___x_4130_);
lean_ctor_set(v_reuseFailAlloc_4158_, 6, v_recordedDeps_4146_);
lean_ctor_set(v_reuseFailAlloc_4158_, 7, v_messages_4147_);
lean_ctor_set(v_reuseFailAlloc_4158_, 8, v_infoState_4148_);
lean_ctor_set(v_reuseFailAlloc_4158_, 9, v_snapshotTasks_4149_);
v___x_4156_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
lean_object* v___x_4157_; 
v___x_4157_ = lean_st_ref_put(v___y_4132_, v___x_4156_);
v___y_4074_ = v___y_4134_;
v___y_4075_ = v___y_4135_;
v___y_4076_ = v___y_4137_;
v_exportedInfo_x3f_4077_ = v___y_4139_;
v___y_4078_ = v___y_4138_;
v___y_4079_ = v___y_4132_;
goto v___jp_4073_;
}
}
}
v___jp_4161_:
{
lean_object* v___x_4169_; lean_object* v_env_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; uint8_t v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4169_ = lean_st_ref_get(v___y_4162_);
v_env_4170_ = lean_ctor_get(v___x_4169_, 0);
lean_inc_ref(v_env_4170_);
lean_dec(v___x_4169_);
v___x_4171_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4172_ = lean_box(1);
v___x_4173_ = 0;
v___x_4174_ = lean_box(v___x_4102_);
lean_inc(v___y_4165_);
v___x_4175_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4174_, v___x_4171_, v_env_4170_, v___y_4165_, v___x_4172_, v___x_4173_);
if (lean_obj_tag(v___x_4175_) == 0)
{
v___y_4132_ = v___y_4162_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4163_;
v___y_4135_ = v___y_4165_;
v___y_4136_ = v___x_4171_;
v___y_4137_ = v___y_4166_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4167_;
goto v___jp_4131_;
}
else
{
lean_dec_ref_known(v___x_4175_, 1);
if (v___y_4164_ == 0)
{
v___y_4074_ = v___y_4163_;
v___y_4075_ = v___y_4165_;
v___y_4076_ = v___y_4166_;
v_exportedInfo_x3f_4077_ = v___y_4167_;
v___y_4078_ = v___y_4168_;
v___y_4079_ = v___y_4162_;
goto v___jp_4073_;
}
else
{
v___y_4132_ = v___y_4162_;
v___y_4133_ = v___y_4164_;
v___y_4134_ = v___y_4163_;
v___y_4135_ = v___y_4165_;
v___y_4136_ = v___x_4171_;
v___y_4137_ = v___y_4166_;
v___y_4138_ = v___y_4168_;
v___y_4139_ = v___y_4167_;
goto v___jp_4131_;
}
}
}
v_reusejp_4176_:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; uint8_t v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v_fst_4218_; lean_object* v_fst_4219_; uint8_t v_snd_4220_; lean_object* v_exportedInfo_x3f_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4233_; lean_object* v_exportedInfo_x3f_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; uint8_t v___y_4245_; uint8_t v___y_4250_; lean_object* v___y_4251_; lean_object* v_toConstantVal_4252_; uint8_t v_safety_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; uint8_t v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v_defn_4266_; lean_object* v___y_4267_; lean_object* v___y_4268_; 
v___x_4178_ = lean_st_ref_put(v_a_3911_, v___x_4177_);
v___x_4179_ = lean_box(0);
switch(lean_obj_tag(v_decl_3908_))
{
case 2:
{
lean_object* v_val_4291_; lean_object* v_exportedInfo_x3f_4293_; lean_object* v___y_4294_; lean_object* v___y_4295_; lean_object* v___x_4300_; 
v_val_4291_ = lean_ctor_get(v_decl_3908_, 0);
v___x_4300_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4301_; lean_object* v___x_4302_; uint8_t v_isModule_4303_; 
v_env_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc_ref(v_env_4301_);
lean_dec(v___x_4300_);
v___x_4302_ = l_Lean_Environment_header(v_env_4301_);
lean_dec_ref(v_env_4301_);
v_isModule_4303_ = lean_ctor_get_uint8(v___x_4302_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4302_);
if (v_isModule_4303_ == 0)
{
v_exportedInfo_x3f_4293_ = v___x_4179_;
v___y_4294_ = v_a_3910_;
v___y_4295_ = v_a_3911_;
goto v___jp_4292_;
}
else
{
lean_object* v_toConstantVal_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v_toConstantVal_4304_ = lean_ctor_get(v_val_4291_, 0);
lean_inc_ref(v_toConstantVal_4304_);
v___x_4305_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4305_, 0, v_toConstantVal_4304_);
lean_ctor_set_uint8(v___x_4305_, sizeof(void*)*1, v_hasTrace_3968_);
v___x_4306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
v___x_4307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
v_exportedInfo_x3f_4293_ = v___x_4307_;
v___y_4294_ = v_a_3910_;
v___y_4295_ = v_a_3911_;
goto v___jp_4292_;
}
}
else
{
lean_dec(v___x_4300_);
v_exportedInfo_x3f_4293_ = v___x_4179_;
v___y_4294_ = v_a_3910_;
v___y_4295_ = v_a_3911_;
goto v___jp_4292_;
}
v___jp_4292_:
{
lean_object* v_toConstantVal_4296_; lean_object* v_name_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_toConstantVal_4296_ = lean_ctor_get(v_val_4291_, 0);
v_name_4297_ = lean_ctor_get(v_toConstantVal_4296_, 0);
lean_inc_ref(v_val_4291_);
v___x_4298_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4298_, 0, v_val_4291_);
v___x_4299_ = 1;
lean_inc(v_name_4297_);
v_fst_4218_ = v_name_4297_;
v_fst_4219_ = v___x_4298_;
v_snd_4220_ = v___x_4299_;
v_exportedInfo_x3f_4221_ = v_exportedInfo_x3f_4293_;
v___y_4222_ = v___y_4294_;
v___y_4223_ = v___y_4295_;
goto v___jp_4217_;
}
}
case 1:
{
lean_object* v_val_4308_; 
v_val_4308_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref(v_val_4308_);
v_defn_4266_ = v_val_4308_;
v___y_4267_ = v_a_3910_;
v___y_4268_ = v_a_3911_;
goto v___jp_4265_;
}
case 5:
{
lean_object* v_defns_4309_; 
v_defns_4309_ = lean_ctor_get(v_decl_3908_, 0);
if (lean_obj_tag(v_defns_4309_) == 1)
{
lean_object* v_tail_4310_; 
v_tail_4310_ = lean_ctor_get(v_defns_4309_, 1);
if (lean_obj_tag(v_tail_4310_) == 0)
{
lean_object* v_head_4311_; 
v_head_4311_ = lean_ctor_get(v_defns_4309_, 0);
lean_inc(v_head_4311_);
v_defn_4266_ = v_head_4311_;
v___y_4267_ = v_a_3910_;
v___y_4268_ = v_a_3911_;
goto v___jp_4265_;
}
else
{
lean_object* v___x_4312_; 
v___x_4312_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v_a_3910_, v_a_3911_);
return v___x_4312_;
}
}
else
{
lean_object* v___x_4313_; 
v___x_4313_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v_a_3910_, v_a_3911_);
return v___x_4313_;
}
}
case 3:
{
lean_object* v_val_4314_; lean_object* v_exportedInfo_x3f_4316_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___x_4323_; lean_object* v_env_4324_; lean_object* v___x_4325_; 
v_val_4314_ = lean_ctor_get(v_decl_3908_, 0);
v___x_4323_ = lean_st_ref_get(v_a_3911_);
v_env_4324_ = lean_ctor_get(v___x_4323_, 0);
lean_inc_ref(v_env_4324_);
lean_dec(v___x_4323_);
v___x_4325_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4326_; lean_object* v___x_4327_; uint8_t v_isModule_4328_; 
v_env_4326_ = lean_ctor_get(v___x_4325_, 0);
lean_inc_ref(v_env_4326_);
lean_dec(v___x_4325_);
v___x_4327_ = l_Lean_Environment_header(v_env_4324_);
lean_dec_ref(v_env_4324_);
v_isModule_4328_ = lean_ctor_get_uint8(v___x_4327_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4327_);
if (v_isModule_4328_ == 0)
{
lean_dec_ref(v_env_4326_);
v_exportedInfo_x3f_4316_ = v___x_4179_;
v___y_4317_ = v_a_3910_;
v___y_4318_ = v_a_3911_;
goto v___jp_4315_;
}
else
{
uint8_t v_isExporting_4329_; 
v_isExporting_4329_ = lean_ctor_get_uint8(v_env_4326_, sizeof(void*)*13);
lean_dec_ref(v_env_4326_);
if (v_isExporting_4329_ == 0)
{
lean_object* v_toConstantVal_4330_; uint8_t v_isUnsafe_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; 
v_toConstantVal_4330_ = lean_ctor_get(v_val_4314_, 0);
v_isUnsafe_4331_ = lean_ctor_get_uint8(v_val_4314_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4330_);
v___x_4332_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4332_, 0, v_toConstantVal_4330_);
lean_ctor_set_uint8(v___x_4332_, sizeof(void*)*1, v_isUnsafe_4331_);
v___x_4333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4333_, 0, v___x_4332_);
v___x_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4333_);
v_exportedInfo_x3f_4316_ = v___x_4334_;
v___y_4317_ = v_a_3910_;
v___y_4318_ = v_a_3911_;
goto v___jp_4315_;
}
else
{
v_exportedInfo_x3f_4316_ = v___x_4179_;
v___y_4317_ = v_a_3910_;
v___y_4318_ = v_a_3911_;
goto v___jp_4315_;
}
}
}
else
{
lean_dec(v___x_4325_);
lean_dec_ref(v_env_4324_);
v_exportedInfo_x3f_4316_ = v___x_4179_;
v___y_4317_ = v_a_3910_;
v___y_4318_ = v_a_3911_;
goto v___jp_4315_;
}
v___jp_4315_:
{
lean_object* v_toConstantVal_4319_; lean_object* v_name_4320_; lean_object* v___x_4321_; uint8_t v___x_4322_; 
v_toConstantVal_4319_ = lean_ctor_get(v_val_4314_, 0);
v_name_4320_ = lean_ctor_get(v_toConstantVal_4319_, 0);
lean_inc_ref(v_val_4314_);
v___x_4321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4321_, 0, v_val_4314_);
v___x_4322_ = 3;
lean_inc(v_name_4320_);
v_fst_4218_ = v_name_4320_;
v_fst_4219_ = v___x_4321_;
v_snd_4220_ = v___x_4322_;
v_exportedInfo_x3f_4221_ = v_exportedInfo_x3f_4316_;
v___y_4222_ = v___y_4317_;
v___y_4223_ = v___y_4318_;
goto v___jp_4217_;
}
}
case 0:
{
lean_object* v_val_4335_; lean_object* v_toConstantVal_4336_; lean_object* v_name_4337_; lean_object* v___x_4338_; uint8_t v___x_4339_; 
v_val_4335_ = lean_ctor_get(v_decl_3908_, 0);
v_toConstantVal_4336_ = lean_ctor_get(v_val_4335_, 0);
v_name_4337_ = lean_ctor_get(v_toConstantVal_4336_, 0);
lean_inc_ref(v_val_4335_);
v___x_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4338_, 0, v_val_4335_);
v___x_4339_ = 2;
lean_inc(v_name_4337_);
v_fst_4218_ = v_name_4337_;
v_fst_4219_ = v___x_4338_;
v_snd_4220_ = v___x_4339_;
v_exportedInfo_x3f_4221_ = v___x_4179_;
v___y_4222_ = v_a_3910_;
v___y_4223_ = v_a_3911_;
goto v___jp_4217_;
}
default: 
{
lean_object* v___x_4340_; 
v___x_4340_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v_a_3910_, v_a_3911_);
return v___x_4340_;
}
}
v___jp_4180_:
{
lean_object* v___x_4187_; uint8_t v___x_4188_; 
lean_inc(v_decl_3908_);
v___x_4187_ = l_Lean_Declaration_getTopLevelNames(v_decl_3908_);
v___x_4188_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4187_);
lean_dec(v___x_4187_);
if (v___x_4188_ == 0)
{
if (lean_obj_tag(v___y_4184_) == 0)
{
if (v___x_4188_ == 0)
{
lean_object* v_toCold_4189_; lean_object* v_options_4190_; uint8_t v_hasTrace_4191_; 
v_toCold_4189_ = lean_ctor_get(v___y_4185_, 0);
v_options_4190_ = lean_ctor_get(v_toCold_4189_, 2);
v_hasTrace_4191_ = lean_ctor_get_uint8(v_options_4190_, sizeof(void*)*1);
if (v_hasTrace_4191_ == 0)
{
v___y_4089_ = v___y_4181_;
v___y_4090_ = v___y_4182_;
v___y_4091_ = v___y_4183_;
v___y_4092_ = v___y_4185_;
v___y_4093_ = v___y_4186_;
goto v___jp_4088_;
}
else
{
lean_object* v_inheritedTraceOptions_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v_inheritedTraceOptions_4192_ = lean_ctor_get(v_toCold_4189_, 11);
v___x_4193_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4192_, v_options_4190_, v___x_4193_);
if (v___x_4194_ == 0)
{
v___y_4089_ = v___y_4181_;
v___y_4090_ = v___y_4182_;
v___y_4091_ = v___y_4183_;
v___y_4092_ = v___y_4185_;
v___y_4093_ = v___y_4186_;
goto v___jp_4088_;
}
else
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4196_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4195_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_dec_ref_known(v___x_4196_, 1);
v___y_4089_ = v___y_4181_;
v___y_4090_ = v___y_4182_;
v___y_4091_ = v___y_4183_;
v___y_4092_ = v___y_4185_;
v___y_4093_ = v___y_4186_;
goto v___jp_4088_;
}
else
{
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec(v_decl_3908_);
return v___x_4196_;
}
}
}
}
else
{
v___y_4162_ = v___y_4186_;
v___y_4163_ = v___y_4181_;
v___y_4164_ = v___x_4188_;
v___y_4165_ = v___y_4182_;
v___y_4166_ = v___y_4183_;
v___y_4167_ = v___y_4184_;
v___y_4168_ = v___y_4185_;
goto v___jp_4161_;
}
}
else
{
v___y_4162_ = v___y_4186_;
v___y_4163_ = v___y_4181_;
v___y_4164_ = v___x_4188_;
v___y_4165_ = v___y_4182_;
v___y_4166_ = v___y_4183_;
v___y_4167_ = v___y_4184_;
v___y_4168_ = v___y_4185_;
goto v___jp_4161_;
}
}
else
{
lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v_a_4199_; uint8_t v___x_4200_; 
lean_dec(v___y_4184_);
v___x_4197_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4198_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4197_, v___y_4185_);
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref(v___x_4198_);
v___x_4200_ = lean_unbox(v_a_4199_);
lean_dec(v_a_4199_);
if (v___x_4200_ == 0)
{
lean_object* v_toCold_4201_; lean_object* v_options_4202_; uint8_t v_hasTrace_4203_; 
v_toCold_4201_ = lean_ctor_get(v___y_4185_, 0);
v_options_4202_ = lean_ctor_get(v_toCold_4201_, 2);
v_hasTrace_4203_ = lean_ctor_get_uint8(v_options_4202_, sizeof(void*)*1);
if (v_hasTrace_4203_ == 0)
{
v___y_4074_ = v___y_4181_;
v___y_4075_ = v___y_4182_;
v___y_4076_ = v___y_4183_;
v_exportedInfo_x3f_4077_ = v___x_4179_;
v___y_4078_ = v___y_4185_;
v___y_4079_ = v___y_4186_;
goto v___jp_4073_;
}
else
{
lean_object* v_inheritedTraceOptions_4204_; lean_object* v___x_4205_; uint8_t v___x_4206_; 
v_inheritedTraceOptions_4204_ = lean_ctor_get(v_toCold_4201_, 11);
v___x_4205_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4204_, v_options_4202_, v___x_4205_);
if (v___x_4206_ == 0)
{
v___y_4074_ = v___y_4181_;
v___y_4075_ = v___y_4182_;
v___y_4076_ = v___y_4183_;
v_exportedInfo_x3f_4077_ = v___x_4179_;
v___y_4078_ = v___y_4185_;
v___y_4079_ = v___y_4186_;
goto v___jp_4073_;
}
else
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4208_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4207_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_dec_ref_known(v___x_4208_, 1);
v___y_4074_ = v___y_4181_;
v___y_4075_ = v___y_4182_;
v___y_4076_ = v___y_4183_;
v_exportedInfo_x3f_4077_ = v___x_4179_;
v___y_4078_ = v___y_4185_;
v___y_4079_ = v___y_4186_;
goto v___jp_4073_;
}
else
{
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec(v_decl_3908_);
return v___x_4208_;
}
}
}
}
else
{
lean_object* v_toCold_4209_; lean_object* v_options_4210_; uint8_t v_hasTrace_4211_; 
v_toCold_4209_ = lean_ctor_get(v___y_4185_, 0);
v_options_4210_ = lean_ctor_get(v_toCold_4209_, 2);
v_hasTrace_4211_ = lean_ctor_get_uint8(v_options_4210_, sizeof(void*)*1);
if (v_hasTrace_4211_ == 0)
{
v___y_4096_ = v___y_4181_;
v___y_4097_ = v___y_4182_;
v___y_4098_ = v___y_4183_;
v___y_4099_ = v___y_4185_;
v___y_4100_ = v___y_4186_;
goto v___jp_4095_;
}
else
{
lean_object* v_inheritedTraceOptions_4212_; lean_object* v___x_4213_; uint8_t v___x_4214_; 
v_inheritedTraceOptions_4212_ = lean_ctor_get(v_toCold_4209_, 11);
v___x_4213_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4214_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4212_, v_options_4210_, v___x_4213_);
if (v___x_4214_ == 0)
{
v___y_4096_ = v___y_4181_;
v___y_4097_ = v___y_4182_;
v___y_4098_ = v___y_4183_;
v___y_4099_ = v___y_4185_;
v___y_4100_ = v___y_4186_;
goto v___jp_4095_;
}
else
{
lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4215_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4216_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4215_, v___y_4185_, v___y_4186_);
if (lean_obj_tag(v___x_4216_) == 0)
{
lean_dec_ref_known(v___x_4216_, 1);
v___y_4096_ = v___y_4181_;
v___y_4097_ = v___y_4182_;
v___y_4098_ = v___y_4183_;
v___y_4099_ = v___y_4185_;
v___y_4100_ = v___y_4186_;
goto v___jp_4095_;
}
else
{
lean_dec_ref(v___y_4183_);
lean_dec(v___y_4182_);
lean_dec(v_decl_3908_);
return v___x_4216_;
}
}
}
}
}
}
v___jp_4217_:
{
lean_object* v___x_4224_; lean_object* v_env_4225_; uint8_t v___x_4226_; 
v___x_4224_ = lean_st_ref_get(v___y_4223_);
v_env_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc_ref(v_env_4225_);
lean_dec(v___x_4224_);
v___x_4226_ = l_Lean_Environment_containsOnBranch(v_env_4225_, v_fst_4218_);
lean_dec_ref(v_env_4225_);
if (v___x_4226_ == 0)
{
v___y_4181_ = v_snd_4220_;
v___y_4182_ = v_fst_4218_;
v___y_4183_ = v_fst_4219_;
v___y_4184_ = v_exportedInfo_x3f_4221_;
v___y_4185_ = v___y_4222_;
v___y_4186_ = v___y_4223_;
goto v___jp_4180_;
}
else
{
lean_object* v___x_4227_; lean_object* v_env_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; 
lean_dec(v_exportedInfo_x3f_4221_);
lean_dec_ref(v_fst_4219_);
lean_dec(v_decl_3908_);
v___x_4227_ = lean_st_ref_get(v___y_4223_);
v_env_4228_ = lean_ctor_get(v___x_4227_, 0);
lean_inc_ref(v_env_4228_);
lean_dec(v___x_4227_);
v___x_4229_ = lean_elab_environment_to_kernel_env(v_env_4228_);
v___x_4230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4229_);
lean_ctor_set(v___x_4230_, 1, v_fst_4218_);
v___x_4231_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4230_, v___y_4222_, v___y_4223_);
return v___x_4231_;
}
}
v___jp_4232_:
{
lean_object* v_toConstantVal_4237_; lean_object* v_name_4238_; lean_object* v___x_4239_; 
v_toConstantVal_4237_ = lean_ctor_get(v___y_4233_, 0);
v_name_4238_ = lean_ctor_get(v_toConstantVal_4237_, 0);
lean_inc(v_name_4238_);
v___x_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4239_, 0, v___y_4233_);
v_fst_4218_ = v_name_4238_;
v_fst_4219_ = v___x_4239_;
v_snd_4220_ = v___x_4102_;
v_exportedInfo_x3f_4221_ = v_exportedInfo_x3f_4234_;
v___y_4222_ = v___y_4235_;
v___y_4223_ = v___y_4236_;
goto v___jp_4217_;
}
v___jp_4240_:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; 
v___x_4246_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4246_, 0, v___y_4242_);
lean_ctor_set_uint8(v___x_4246_, sizeof(void*)*1, v___y_4245_);
v___x_4247_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
v___x_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
v___y_4233_ = v___y_4243_;
v_exportedInfo_x3f_4234_ = v___x_4248_;
v___y_4235_ = v___y_4244_;
v___y_4236_ = v___y_4241_;
goto v___jp_4232_;
}
v___jp_4249_:
{
uint8_t v___x_4256_; uint8_t v___x_4257_; 
v___x_4256_ = 1;
v___x_4257_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4253_, v___x_4256_);
if (v___x_4257_ == 0)
{
v___y_4241_ = v___y_4255_;
v___y_4242_ = v_toConstantVal_4252_;
v___y_4243_ = v___y_4251_;
v___y_4244_ = v___y_4254_;
v___y_4245_ = v___y_4250_;
goto v___jp_4240_;
}
else
{
v___y_4241_ = v___y_4255_;
v___y_4242_ = v_toConstantVal_4252_;
v___y_4243_ = v___y_4251_;
v___y_4244_ = v___y_4254_;
v___y_4245_ = v_hasTrace_3968_;
goto v___jp_4240_;
}
}
v___jp_4258_:
{
lean_object* v_toConstantVal_4263_; uint8_t v_safety_4264_; 
v_toConstantVal_4263_ = lean_ctor_get(v___y_4260_, 0);
lean_inc_ref(v_toConstantVal_4263_);
v_safety_4264_ = lean_ctor_get_uint8(v___y_4260_, sizeof(void*)*4);
v___y_4250_ = v___y_4259_;
v___y_4251_ = v___y_4260_;
v_toConstantVal_4252_ = v_toConstantVal_4263_;
v_safety_4253_ = v_safety_4264_;
v___y_4254_ = v___y_4261_;
v___y_4255_ = v___y_4262_;
goto v___jp_4249_;
}
v___jp_4265_:
{
lean_object* v___x_4269_; lean_object* v_env_4270_; lean_object* v___x_4271_; 
v___x_4269_ = lean_st_ref_get(v___y_4268_);
v_env_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc_ref(v_env_4270_);
lean_dec(v___x_4269_);
v___x_4271_ = lean_st_ref_get(v___y_4268_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4272_; lean_object* v___x_4273_; uint8_t v_isModule_4274_; 
v_env_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc_ref(v_env_4272_);
lean_dec(v___x_4271_);
v___x_4273_ = l_Lean_Environment_header(v_env_4270_);
lean_dec_ref(v_env_4270_);
v_isModule_4274_ = lean_ctor_get_uint8(v___x_4273_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4273_);
if (v_isModule_4274_ == 0)
{
lean_dec_ref(v_env_4272_);
v___y_4233_ = v_defn_4266_;
v_exportedInfo_x3f_4234_ = v___x_4179_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4268_;
goto v___jp_4232_;
}
else
{
uint8_t v_isExporting_4275_; 
v_isExporting_4275_ = lean_ctor_get_uint8(v_env_4272_, sizeof(void*)*13);
lean_dec_ref(v_env_4272_);
if (v_isExporting_4275_ == 0)
{
lean_object* v_toCold_4276_; lean_object* v_options_4277_; uint8_t v_hasTrace_4278_; 
v_toCold_4276_ = lean_ctor_get(v___y_4267_, 0);
v_options_4277_ = lean_ctor_get(v_toCold_4276_, 2);
v_hasTrace_4278_ = lean_ctor_get_uint8(v_options_4277_, sizeof(void*)*1);
if (v_hasTrace_4278_ == 0)
{
v___y_4259_ = v_isModule_4274_;
v___y_4260_ = v_defn_4266_;
v___y_4261_ = v___y_4267_;
v___y_4262_ = v___y_4268_;
goto v___jp_4258_;
}
else
{
lean_object* v_inheritedTraceOptions_4279_; lean_object* v___x_4280_; uint8_t v___x_4281_; 
v_inheritedTraceOptions_4279_ = lean_ctor_get(v_toCold_4276_, 11);
v___x_4280_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4281_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4279_, v_options_4277_, v___x_4280_);
if (v___x_4281_ == 0)
{
v___y_4259_ = v_isModule_4274_;
v___y_4260_ = v_defn_4266_;
v___y_4261_ = v___y_4267_;
v___y_4262_ = v___y_4268_;
goto v___jp_4258_;
}
else
{
lean_object* v_toConstantVal_4282_; uint8_t v_safety_4283_; lean_object* v_name_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v_toConstantVal_4282_ = lean_ctor_get(v_defn_4266_, 0);
lean_inc_ref(v_toConstantVal_4282_);
v_safety_4283_ = lean_ctor_get_uint8(v_defn_4266_, sizeof(void*)*4);
v_name_4284_ = lean_ctor_get(v_toConstantVal_4282_, 0);
v___x_4285_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4284_);
v___x_4286_ = l_Lean_MessageData_ofName(v_name_4284_);
v___x_4287_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4287_, 0, v___x_4285_);
lean_ctor_set(v___x_4287_, 1, v___x_4286_);
v___x_4288_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4289_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4287_);
lean_ctor_set(v___x_4289_, 1, v___x_4288_);
v___x_4290_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4289_, v___y_4267_, v___y_4268_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_dec_ref_known(v___x_4290_, 1);
v___y_4250_ = v_isModule_4274_;
v___y_4251_ = v_defn_4266_;
v_toConstantVal_4252_ = v_toConstantVal_4282_;
v_safety_4253_ = v_safety_4283_;
v___y_4254_ = v___y_4267_;
v___y_4255_ = v___y_4268_;
goto v___jp_4249_;
}
else
{
lean_dec_ref(v_toConstantVal_4282_);
lean_dec_ref(v_defn_4266_);
lean_dec(v_decl_3908_);
return v___x_4290_;
}
}
}
}
else
{
v___y_4233_ = v_defn_4266_;
v_exportedInfo_x3f_4234_ = v___x_4179_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4268_;
goto v___jp_4232_;
}
}
}
else
{
lean_dec(v___x_4271_);
lean_dec_ref(v_env_4270_);
v___y_4233_ = v_defn_4266_;
v_exportedInfo_x3f_4234_ = v___x_4179_;
v___y_4235_ = v___y_4267_;
v___y_4236_ = v___y_4268_;
goto v___jp_4232_;
}
}
}
}
}
else
{
lean_object* v___f_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; uint8_t v___x_4347_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v_a_4351_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4384_; lean_object* v___y_4385_; lean_object* v___y_4386_; lean_object* v___y_4387_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4413_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; lean_object* v___y_4433_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; uint8_t v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4450_; lean_object* v___y_4451_; lean_object* v_a_4452_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4482_; lean_object* v___y_4483_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; 
lean_inc(v_decl_3908_);
v___f_4344_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4344_, 0, v_decl_3908_);
v___x_4345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4346_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4347_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3967_, v_options_3966_, v___x_4346_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4653_; uint8_t v___x_4654_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4664_; lean_object* v___y_4665_; lean_object* v___y_4666_; uint8_t v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4732_; lean_object* v___y_4733_; lean_object* v___y_4734_; lean_object* v___y_4735_; lean_object* v___y_4736_; lean_object* v___y_4758_; uint8_t v___y_4759_; lean_object* v___y_4760_; lean_object* v_exportedInfo_x3f_4761_; lean_object* v___y_4762_; lean_object* v___y_4763_; lean_object* v___y_4773_; uint8_t v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v___y_4777_; lean_object* v___y_4780_; uint8_t v___y_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4784_; 
v___x_4653_ = l_Lean_trace_profiler;
v___x_4654_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3966_, v___x_4653_);
if (v___x_4654_ == 0)
{
lean_object* v___x_4786_; lean_object* v_env_4787_; lean_object* v_nextMacroScope_4788_; lean_object* v_ngen_4789_; lean_object* v_auxDeclNGen_4790_; lean_object* v_traceState_4791_; lean_object* v_recordedDeps_4792_; lean_object* v_messages_4793_; lean_object* v_infoState_4794_; lean_object* v_snapshotTasks_4795_; lean_object* v___x_4797_; uint8_t v_isShared_4798_; uint8_t v_isSharedCheck_5043_; 
lean_dec_ref(v___f_4344_);
v___x_4786_ = lean_st_ref_take(v_a_3911_);
v_env_4787_ = lean_ctor_get(v___x_4786_, 0);
v_nextMacroScope_4788_ = lean_ctor_get(v___x_4786_, 1);
v_ngen_4789_ = lean_ctor_get(v___x_4786_, 2);
v_auxDeclNGen_4790_ = lean_ctor_get(v___x_4786_, 3);
v_traceState_4791_ = lean_ctor_get(v___x_4786_, 4);
v_recordedDeps_4792_ = lean_ctor_get(v___x_4786_, 6);
v_messages_4793_ = lean_ctor_get(v___x_4786_, 7);
v_infoState_4794_ = lean_ctor_get(v___x_4786_, 8);
v_snapshotTasks_4795_ = lean_ctor_get(v___x_4786_, 9);
v_isSharedCheck_5043_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_5043_ == 0)
{
lean_object* v_unused_5044_; 
v_unused_5044_ = lean_ctor_get(v___x_4786_, 5);
lean_dec(v_unused_5044_);
v___x_4797_ = v___x_4786_;
v_isShared_4798_ = v_isSharedCheck_5043_;
goto v_resetjp_4796_;
}
else
{
lean_inc(v_snapshotTasks_4795_);
lean_inc(v_infoState_4794_);
lean_inc(v_messages_4793_);
lean_inc(v_recordedDeps_4792_);
lean_inc(v_traceState_4791_);
lean_inc(v_auxDeclNGen_4790_);
lean_inc(v_ngen_4789_);
lean_inc(v_nextMacroScope_4788_);
lean_inc(v_env_4787_);
lean_dec(v___x_4786_);
v___x_4797_ = lean_box(0);
v_isShared_4798_ = v_isSharedCheck_5043_;
goto v_resetjp_4796_;
}
v_resetjp_4796_:
{
lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; uint8_t v___y_4803_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___y_4806_; lean_object* v___y_4807_; uint8_t v___y_4808_; lean_object* v___y_4809_; lean_object* v___y_4810_; uint8_t v___y_4833_; lean_object* v___y_4834_; lean_object* v___y_4835_; lean_object* v___y_4836_; uint8_t v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___x_4848_; 
lean_inc(v_decl_3908_);
v___x_4799_ = l_Lean_Declaration_getNames(v_decl_3908_);
v___x_4800_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4787_, v___x_4799_);
v___x_4801_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4798_ == 0)
{
lean_ctor_set(v___x_4797_, 5, v___x_4801_);
lean_ctor_set(v___x_4797_, 0, v___x_4800_);
v___x_4848_ = v___x_4797_;
goto v_reusejp_4847_;
}
else
{
lean_object* v_reuseFailAlloc_5042_; 
v_reuseFailAlloc_5042_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5042_, 0, v___x_4800_);
lean_ctor_set(v_reuseFailAlloc_5042_, 1, v_nextMacroScope_4788_);
lean_ctor_set(v_reuseFailAlloc_5042_, 2, v_ngen_4789_);
lean_ctor_set(v_reuseFailAlloc_5042_, 3, v_auxDeclNGen_4790_);
lean_ctor_set(v_reuseFailAlloc_5042_, 4, v_traceState_4791_);
lean_ctor_set(v_reuseFailAlloc_5042_, 5, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_5042_, 6, v_recordedDeps_4792_);
lean_ctor_set(v_reuseFailAlloc_5042_, 7, v_messages_4793_);
lean_ctor_set(v_reuseFailAlloc_5042_, 8, v_infoState_4794_);
lean_ctor_set(v_reuseFailAlloc_5042_, 9, v_snapshotTasks_4795_);
v___x_4848_ = v_reuseFailAlloc_5042_;
goto v_reusejp_4847_;
}
v___jp_4802_:
{
lean_object* v___x_4811_; lean_object* v_env_4812_; lean_object* v_nextMacroScope_4813_; lean_object* v_ngen_4814_; lean_object* v_auxDeclNGen_4815_; lean_object* v_traceState_4816_; lean_object* v_recordedDeps_4817_; lean_object* v_messages_4818_; lean_object* v_infoState_4819_; lean_object* v_snapshotTasks_4820_; lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4830_; 
v___x_4811_ = lean_st_ref_take(v___y_4805_);
v_env_4812_ = lean_ctor_get(v___x_4811_, 0);
v_nextMacroScope_4813_ = lean_ctor_get(v___x_4811_, 1);
v_ngen_4814_ = lean_ctor_get(v___x_4811_, 2);
v_auxDeclNGen_4815_ = lean_ctor_get(v___x_4811_, 3);
v_traceState_4816_ = lean_ctor_get(v___x_4811_, 4);
v_recordedDeps_4817_ = lean_ctor_get(v___x_4811_, 6);
v_messages_4818_ = lean_ctor_get(v___x_4811_, 7);
v_infoState_4819_ = lean_ctor_get(v___x_4811_, 8);
v_snapshotTasks_4820_ = lean_ctor_get(v___x_4811_, 9);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4830_ == 0)
{
lean_object* v_unused_4831_; 
v_unused_4831_ = lean_ctor_get(v___x_4811_, 5);
lean_dec(v_unused_4831_);
v___x_4822_ = v___x_4811_;
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
else
{
lean_inc(v_snapshotTasks_4820_);
lean_inc(v_infoState_4819_);
lean_inc(v_messages_4818_);
lean_inc(v_recordedDeps_4817_);
lean_inc(v_traceState_4816_);
lean_inc(v_auxDeclNGen_4815_);
lean_inc(v_ngen_4814_);
lean_inc(v_nextMacroScope_4813_);
lean_inc(v_env_4812_);
lean_dec(v___x_4811_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4830_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4824_; lean_object* v___x_4825_; lean_object* v___x_4827_; 
v___x_4824_ = lean_box(v___y_4808_);
lean_inc(v___y_4806_);
lean_inc_ref(v___y_4807_);
v___x_4825_ = l_Lean_MapDeclarationExtension_insert___redArg(v___y_4807_, v_env_4812_, v___y_4806_, v___x_4824_, v___y_4803_);
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 5, v___x_4801_);
lean_ctor_set(v___x_4822_, 0, v___x_4825_);
v___x_4827_ = v___x_4822_;
goto v_reusejp_4826_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v___x_4825_);
lean_ctor_set(v_reuseFailAlloc_4829_, 1, v_nextMacroScope_4813_);
lean_ctor_set(v_reuseFailAlloc_4829_, 2, v_ngen_4814_);
lean_ctor_set(v_reuseFailAlloc_4829_, 3, v_auxDeclNGen_4815_);
lean_ctor_set(v_reuseFailAlloc_4829_, 4, v_traceState_4816_);
lean_ctor_set(v_reuseFailAlloc_4829_, 5, v___x_4801_);
lean_ctor_set(v_reuseFailAlloc_4829_, 6, v_recordedDeps_4817_);
lean_ctor_set(v_reuseFailAlloc_4829_, 7, v_messages_4818_);
lean_ctor_set(v_reuseFailAlloc_4829_, 8, v_infoState_4819_);
lean_ctor_set(v_reuseFailAlloc_4829_, 9, v_snapshotTasks_4820_);
v___x_4827_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4826_;
}
v_reusejp_4826_:
{
lean_object* v___x_4828_; 
v___x_4828_ = lean_st_ref_put(v___y_4805_, v___x_4827_);
v___y_4758_ = v___y_4806_;
v___y_4759_ = v___y_4808_;
v___y_4760_ = v___y_4809_;
v_exportedInfo_x3f_4761_ = v___y_4804_;
v___y_4762_ = v___y_4810_;
v___y_4763_ = v___y_4805_;
goto v___jp_4757_;
}
}
}
v___jp_4832_:
{
lean_object* v___x_4840_; lean_object* v_env_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; uint8_t v___x_4844_; lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4840_ = lean_st_ref_get(v___y_4835_);
v_env_4841_ = lean_ctor_get(v___x_4840_, 0);
lean_inc_ref(v_env_4841_);
lean_dec(v___x_4840_);
v___x_4842_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4843_ = lean_box(1);
v___x_4844_ = 0;
v___x_4845_ = lean_box(v___x_4102_);
lean_inc(v___y_4836_);
v___x_4846_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_4845_, v___x_4842_, v_env_4841_, v___y_4836_, v___x_4843_, v___x_4844_);
if (lean_obj_tag(v___x_4846_) == 0)
{
v___y_4803_ = v___y_4833_;
v___y_4804_ = v___y_4834_;
v___y_4805_ = v___y_4835_;
v___y_4806_ = v___y_4836_;
v___y_4807_ = v___x_4842_;
v___y_4808_ = v___y_4837_;
v___y_4809_ = v___y_4839_;
v___y_4810_ = v___y_4838_;
goto v___jp_4802_;
}
else
{
lean_dec_ref_known(v___x_4846_, 1);
if (v___y_4833_ == 0)
{
v___y_4758_ = v___y_4836_;
v___y_4759_ = v___y_4837_;
v___y_4760_ = v___y_4839_;
v_exportedInfo_x3f_4761_ = v___y_4834_;
v___y_4762_ = v___y_4838_;
v___y_4763_ = v___y_4835_;
goto v___jp_4757_;
}
else
{
v___y_4803_ = v___y_4833_;
v___y_4804_ = v___y_4834_;
v___y_4805_ = v___y_4835_;
v___y_4806_ = v___y_4836_;
v___y_4807_ = v___x_4842_;
v___y_4808_ = v___y_4837_;
v___y_4809_ = v___y_4839_;
v___y_4810_ = v___y_4838_;
goto v___jp_4802_;
}
}
}
v_reusejp_4847_:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; lean_object* v___y_4852_; lean_object* v___y_4853_; uint8_t v___y_4854_; lean_object* v___y_4855_; lean_object* v___y_4856_; lean_object* v___y_4857_; lean_object* v_fst_4886_; lean_object* v_fst_4887_; uint8_t v_snd_4888_; lean_object* v_exportedInfo_x3f_4889_; lean_object* v___y_4890_; lean_object* v___y_4891_; lean_object* v___y_4901_; lean_object* v_exportedInfo_x3f_4902_; lean_object* v___y_4903_; lean_object* v___y_4904_; lean_object* v___y_4909_; lean_object* v___y_4910_; lean_object* v___y_4911_; lean_object* v___y_4912_; uint8_t v___y_4913_; lean_object* v___y_4918_; lean_object* v_toConstantVal_4919_; uint8_t v_safety_4920_; uint8_t v___y_4921_; lean_object* v___y_4922_; lean_object* v___y_4923_; lean_object* v___y_4927_; uint8_t v___y_4928_; lean_object* v___y_4929_; lean_object* v___y_4930_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; uint8_t v___y_4937_; lean_object* v___y_4953_; lean_object* v___y_4954_; lean_object* v___y_4955_; lean_object* v___y_4956_; lean_object* v___y_4957_; lean_object* v_defn_4962_; lean_object* v___y_4963_; lean_object* v___y_4964_; 
v___x_4849_ = lean_st_ref_put(v_a_3911_, v___x_4848_);
v___x_4850_ = lean_box(0);
switch(lean_obj_tag(v_decl_3908_))
{
case 2:
{
lean_object* v_val_4970_; lean_object* v_exportedInfo_x3f_4972_; lean_object* v___y_4973_; lean_object* v___y_4974_; lean_object* v___y_4980_; lean_object* v___y_4981_; lean_object* v___x_4986_; lean_object* v_env_4987_; 
v_val_4970_ = lean_ctor_get(v_decl_3908_, 0);
v___x_4986_ = lean_st_ref_get(v_a_3911_);
v_env_4987_ = lean_ctor_get(v___x_4986_, 0);
lean_inc_ref(v_env_4987_);
lean_dec(v___x_4986_);
if (v_forceExpose_3909_ == 0)
{
goto v___jp_4988_;
}
else
{
if (v___x_4654_ == 0)
{
lean_dec_ref(v_env_4987_);
v_exportedInfo_x3f_4972_ = v___x_4850_;
v___y_4973_ = v_a_3910_;
v___y_4974_ = v_a_3911_;
goto v___jp_4971_;
}
else
{
goto v___jp_4988_;
}
}
v___jp_4971_:
{
lean_object* v_toConstantVal_4975_; lean_object* v_name_4976_; lean_object* v___x_4977_; uint8_t v___x_4978_; 
v_toConstantVal_4975_ = lean_ctor_get(v_val_4970_, 0);
v_name_4976_ = lean_ctor_get(v_toConstantVal_4975_, 0);
lean_inc_ref(v_val_4970_);
v___x_4977_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4977_, 0, v_val_4970_);
v___x_4978_ = 1;
lean_inc(v_name_4976_);
v_fst_4886_ = v_name_4976_;
v_fst_4887_ = v___x_4977_;
v_snd_4888_ = v___x_4978_;
v_exportedInfo_x3f_4889_ = v_exportedInfo_x3f_4972_;
v___y_4890_ = v___y_4973_;
v___y_4891_ = v___y_4974_;
goto v___jp_4885_;
}
v___jp_4979_:
{
lean_object* v_toConstantVal_4982_; lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v_toConstantVal_4982_ = lean_ctor_get(v_val_4970_, 0);
lean_inc_ref(v_toConstantVal_4982_);
v___x_4983_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4983_, 0, v_toConstantVal_4982_);
lean_ctor_set_uint8(v___x_4983_, sizeof(void*)*1, v___x_4654_);
v___x_4984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4984_, 0, v___x_4983_);
v___x_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
v_exportedInfo_x3f_4972_ = v___x_4985_;
v___y_4973_ = v___y_4980_;
v___y_4974_ = v___y_4981_;
goto v___jp_4971_;
}
v___jp_4988_:
{
lean_object* v___x_4989_; uint8_t v_isModule_4990_; 
v___x_4989_ = l_Lean_Environment_header(v_env_4987_);
lean_dec_ref(v_env_4987_);
v_isModule_4990_ = lean_ctor_get_uint8(v___x_4989_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4989_);
if (v_isModule_4990_ == 0)
{
v_exportedInfo_x3f_4972_ = v___x_4850_;
v___y_4973_ = v_a_3910_;
v___y_4974_ = v_a_3911_;
goto v___jp_4971_;
}
else
{
if (v___x_4347_ == 0)
{
v___y_4980_ = v_a_3910_;
v___y_4981_ = v_a_3911_;
goto v___jp_4979_;
}
else
{
lean_object* v_toConstantVal_4991_; lean_object* v_name_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; 
v_toConstantVal_4991_ = lean_ctor_get(v_val_4970_, 0);
v_name_4992_ = lean_ctor_get(v_toConstantVal_4991_, 0);
v___x_4993_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4992_);
v___x_4994_ = l_Lean_MessageData_ofName(v_name_4992_);
v___x_4995_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4995_, 0, v___x_4993_);
lean_ctor_set(v___x_4995_, 1, v___x_4994_);
v___x_4996_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4997_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4995_);
lean_ctor_set(v___x_4997_, 1, v___x_4996_);
v___x_4998_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4997_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_4998_) == 0)
{
lean_dec_ref_known(v___x_4998_, 1);
v___y_4980_ = v_a_3910_;
v___y_4981_ = v_a_3911_;
goto v___jp_4979_;
}
else
{
lean_dec_ref_known(v_decl_3908_, 1);
return v___x_4998_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4999_; 
v_val_4999_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref(v_val_4999_);
v_defn_4962_ = v_val_4999_;
v___y_4963_ = v_a_3910_;
v___y_4964_ = v_a_3911_;
goto v___jp_4961_;
}
case 5:
{
lean_object* v_defns_5000_; 
v_defns_5000_ = lean_ctor_get(v_decl_3908_, 0);
if (lean_obj_tag(v_defns_5000_) == 1)
{
lean_object* v_tail_5001_; 
v_tail_5001_ = lean_ctor_get(v_defns_5000_, 1);
if (lean_obj_tag(v_tail_5001_) == 0)
{
lean_object* v_head_5002_; 
v_head_5002_ = lean_ctor_get(v_defns_5000_, 0);
lean_inc(v_head_5002_);
v_defn_4962_ = v_head_5002_;
v___y_4963_ = v_a_3910_;
v___y_4964_ = v_a_3911_;
goto v___jp_4961_;
}
else
{
v___y_4105_ = v_a_3910_;
v_options_4106_ = v_options_3966_;
v_inheritedTraceOptions_4107_ = v_inheritedTraceOptions_3967_;
v___y_4108_ = v_a_3911_;
goto v___jp_4104_;
}
}
else
{
v___y_4105_ = v_a_3910_;
v_options_4106_ = v_options_3966_;
v_inheritedTraceOptions_4107_ = v_inheritedTraceOptions_3967_;
v___y_4108_ = v_a_3911_;
goto v___jp_4104_;
}
}
case 3:
{
lean_object* v_val_5003_; lean_object* v_exportedInfo_x3f_5005_; lean_object* v___y_5006_; lean_object* v___y_5007_; lean_object* v___y_5013_; lean_object* v___y_5014_; lean_object* v___x_5020_; lean_object* v_env_5021_; lean_object* v___x_5022_; lean_object* v_env_5032_; 
v_val_5003_ = lean_ctor_get(v_decl_3908_, 0);
v___x_5020_ = lean_st_ref_get(v_a_3911_);
v_env_5021_ = lean_ctor_get(v___x_5020_, 0);
lean_inc_ref(v_env_5021_);
lean_dec(v___x_5020_);
v___x_5022_ = lean_st_ref_get(v_a_3911_);
v_env_5032_ = lean_ctor_get(v___x_5022_, 0);
lean_inc_ref(v_env_5032_);
lean_dec(v___x_5022_);
if (v_forceExpose_3909_ == 0)
{
goto v___jp_5033_;
}
else
{
if (v___x_4654_ == 0)
{
lean_dec_ref(v_env_5032_);
lean_dec_ref(v_env_5021_);
v_exportedInfo_x3f_5005_ = v___x_4850_;
v___y_5006_ = v_a_3910_;
v___y_5007_ = v_a_3911_;
goto v___jp_5004_;
}
else
{
goto v___jp_5033_;
}
}
v___jp_5004_:
{
lean_object* v_toConstantVal_5008_; lean_object* v_name_5009_; lean_object* v___x_5010_; uint8_t v___x_5011_; 
v_toConstantVal_5008_ = lean_ctor_get(v_val_5003_, 0);
v_name_5009_ = lean_ctor_get(v_toConstantVal_5008_, 0);
lean_inc_ref(v_val_5003_);
v___x_5010_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5010_, 0, v_val_5003_);
v___x_5011_ = 3;
lean_inc(v_name_5009_);
v_fst_4886_ = v_name_5009_;
v_fst_4887_ = v___x_5010_;
v_snd_4888_ = v___x_5011_;
v_exportedInfo_x3f_4889_ = v_exportedInfo_x3f_5005_;
v___y_4890_ = v___y_5006_;
v___y_4891_ = v___y_5007_;
goto v___jp_4885_;
}
v___jp_5012_:
{
lean_object* v_toConstantVal_5015_; uint8_t v_isUnsafe_5016_; lean_object* v___x_5017_; lean_object* v___x_5018_; lean_object* v___x_5019_; 
v_toConstantVal_5015_ = lean_ctor_get(v_val_5003_, 0);
v_isUnsafe_5016_ = lean_ctor_get_uint8(v_val_5003_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_5015_);
v___x_5017_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_5017_, 0, v_toConstantVal_5015_);
lean_ctor_set_uint8(v___x_5017_, sizeof(void*)*1, v_isUnsafe_5016_);
v___x_5018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5018_, 0, v___x_5017_);
v___x_5019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5019_, 0, v___x_5018_);
v_exportedInfo_x3f_5005_ = v___x_5019_;
v___y_5006_ = v___y_5013_;
v___y_5007_ = v___y_5014_;
goto v___jp_5004_;
}
v___jp_5023_:
{
if (v___x_4347_ == 0)
{
v___y_5013_ = v_a_3910_;
v___y_5014_ = v_a_3911_;
goto v___jp_5012_;
}
else
{
lean_object* v_toConstantVal_5024_; lean_object* v_name_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; lean_object* v___x_5028_; lean_object* v___x_5029_; lean_object* v___x_5030_; lean_object* v___x_5031_; 
v_toConstantVal_5024_ = lean_ctor_get(v_val_5003_, 0);
v_name_5025_ = lean_ctor_get(v_toConstantVal_5024_, 0);
v___x_5026_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_5025_);
v___x_5027_ = l_Lean_MessageData_ofName(v_name_5025_);
v___x_5028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5028_, 0, v___x_5026_);
lean_ctor_set(v___x_5028_, 1, v___x_5027_);
v___x_5029_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_5030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5030_, 0, v___x_5028_);
lean_ctor_set(v___x_5030_, 1, v___x_5029_);
v___x_5031_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_5030_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_5031_) == 0)
{
lean_dec_ref_known(v___x_5031_, 1);
v___y_5013_ = v_a_3910_;
v___y_5014_ = v_a_3911_;
goto v___jp_5012_;
}
else
{
lean_dec_ref_known(v_decl_3908_, 1);
return v___x_5031_;
}
}
}
v___jp_5033_:
{
lean_object* v___x_5034_; uint8_t v_isModule_5035_; 
v___x_5034_ = l_Lean_Environment_header(v_env_5021_);
lean_dec_ref(v_env_5021_);
v_isModule_5035_ = lean_ctor_get_uint8(v___x_5034_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_5034_);
if (v_isModule_5035_ == 0)
{
lean_dec_ref(v_env_5032_);
v_exportedInfo_x3f_5005_ = v___x_4850_;
v___y_5006_ = v_a_3910_;
v___y_5007_ = v_a_3911_;
goto v___jp_5004_;
}
else
{
uint8_t v_isExporting_5036_; 
v_isExporting_5036_ = lean_ctor_get_uint8(v_env_5032_, sizeof(void*)*13);
lean_dec_ref(v_env_5032_);
if (v_isExporting_5036_ == 0)
{
goto v___jp_5023_;
}
else
{
if (v___x_4654_ == 0)
{
v_exportedInfo_x3f_5005_ = v___x_4850_;
v___y_5006_ = v_a_3910_;
v___y_5007_ = v_a_3911_;
goto v___jp_5004_;
}
else
{
goto v___jp_5023_;
}
}
}
}
}
case 0:
{
lean_object* v_val_5037_; lean_object* v_toConstantVal_5038_; lean_object* v_name_5039_; lean_object* v___x_5040_; uint8_t v___x_5041_; 
v_val_5037_ = lean_ctor_get(v_decl_3908_, 0);
v_toConstantVal_5038_ = lean_ctor_get(v_val_5037_, 0);
v_name_5039_ = lean_ctor_get(v_toConstantVal_5038_, 0);
lean_inc_ref(v_val_5037_);
v___x_5040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5040_, 0, v_val_5037_);
v___x_5041_ = 2;
lean_inc(v_name_5039_);
v_fst_4886_ = v_name_5039_;
v_fst_4887_ = v___x_5040_;
v_snd_4888_ = v___x_5041_;
v_exportedInfo_x3f_4889_ = v___x_4850_;
v___y_4890_ = v_a_3910_;
v___y_4891_ = v_a_3911_;
goto v___jp_4885_;
}
default: 
{
v___y_4105_ = v_a_3910_;
v_options_4106_ = v_options_3966_;
v_inheritedTraceOptions_4107_ = v_inheritedTraceOptions_3967_;
v___y_4108_ = v_a_3911_;
goto v___jp_4104_;
}
}
v___jp_4851_:
{
lean_object* v___x_4858_; uint8_t v___x_4859_; 
lean_inc(v_decl_3908_);
v___x_4858_ = l_Lean_Declaration_getTopLevelNames(v_decl_3908_);
v___x_4859_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4858_);
lean_dec(v___x_4858_);
if (v___x_4859_ == 0)
{
if (lean_obj_tag(v___y_4852_) == 0)
{
if (v___x_4859_ == 0)
{
lean_object* v_toCold_4860_; lean_object* v_options_4861_; uint8_t v_hasTrace_4862_; 
v_toCold_4860_ = lean_ctor_get(v___y_4856_, 0);
v_options_4861_ = lean_ctor_get(v_toCold_4860_, 2);
v_hasTrace_4862_ = lean_ctor_get_uint8(v_options_4861_, sizeof(void*)*1);
if (v_hasTrace_4862_ == 0)
{
v___y_4773_ = v___y_4853_;
v___y_4774_ = v___y_4854_;
v___y_4775_ = v___y_4855_;
v___y_4776_ = v___y_4856_;
v___y_4777_ = v___y_4857_;
goto v___jp_4772_;
}
else
{
lean_object* v_inheritedTraceOptions_4863_; uint8_t v___x_4864_; 
v_inheritedTraceOptions_4863_ = lean_ctor_get(v_toCold_4860_, 11);
v___x_4864_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4863_, v_options_4861_, v___x_4346_);
if (v___x_4864_ == 0)
{
v___y_4773_ = v___y_4853_;
v___y_4774_ = v___y_4854_;
v___y_4775_ = v___y_4855_;
v___y_4776_ = v___y_4856_;
v___y_4777_ = v___y_4857_;
goto v___jp_4772_;
}
else
{
lean_object* v___x_4865_; lean_object* v___x_4866_; 
v___x_4865_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4866_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4865_, v___y_4856_, v___y_4857_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_dec_ref_known(v___x_4866_, 1);
v___y_4773_ = v___y_4853_;
v___y_4774_ = v___y_4854_;
v___y_4775_ = v___y_4855_;
v___y_4776_ = v___y_4856_;
v___y_4777_ = v___y_4857_;
goto v___jp_4772_;
}
else
{
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4853_);
lean_dec(v_decl_3908_);
return v___x_4866_;
}
}
}
}
else
{
v___y_4833_ = v___x_4859_;
v___y_4834_ = v___y_4852_;
v___y_4835_ = v___y_4857_;
v___y_4836_ = v___y_4853_;
v___y_4837_ = v___y_4854_;
v___y_4838_ = v___y_4856_;
v___y_4839_ = v___y_4855_;
goto v___jp_4832_;
}
}
else
{
v___y_4833_ = v___x_4859_;
v___y_4834_ = v___y_4852_;
v___y_4835_ = v___y_4857_;
v___y_4836_ = v___y_4853_;
v___y_4837_ = v___y_4854_;
v___y_4838_ = v___y_4856_;
v___y_4839_ = v___y_4855_;
goto v___jp_4832_;
}
}
else
{
lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v_a_4869_; uint8_t v___x_4870_; 
lean_dec(v___y_4852_);
v___x_4867_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4868_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4867_, v___y_4856_);
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
lean_inc(v_a_4869_);
lean_dec_ref(v___x_4868_);
v___x_4870_ = lean_unbox(v_a_4869_);
lean_dec(v_a_4869_);
if (v___x_4870_ == 0)
{
lean_object* v_toCold_4871_; lean_object* v_options_4872_; uint8_t v_hasTrace_4873_; 
v_toCold_4871_ = lean_ctor_get(v___y_4856_, 0);
v_options_4872_ = lean_ctor_get(v_toCold_4871_, 2);
v_hasTrace_4873_ = lean_ctor_get_uint8(v_options_4872_, sizeof(void*)*1);
if (v_hasTrace_4873_ == 0)
{
v___y_4758_ = v___y_4853_;
v___y_4759_ = v___y_4854_;
v___y_4760_ = v___y_4855_;
v_exportedInfo_x3f_4761_ = v___x_4850_;
v___y_4762_ = v___y_4856_;
v___y_4763_ = v___y_4857_;
goto v___jp_4757_;
}
else
{
lean_object* v_inheritedTraceOptions_4874_; uint8_t v___x_4875_; 
v_inheritedTraceOptions_4874_ = lean_ctor_get(v_toCold_4871_, 11);
v___x_4875_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4874_, v_options_4872_, v___x_4346_);
if (v___x_4875_ == 0)
{
v___y_4758_ = v___y_4853_;
v___y_4759_ = v___y_4854_;
v___y_4760_ = v___y_4855_;
v_exportedInfo_x3f_4761_ = v___x_4850_;
v___y_4762_ = v___y_4856_;
v___y_4763_ = v___y_4857_;
goto v___jp_4757_;
}
else
{
lean_object* v___x_4876_; lean_object* v___x_4877_; 
v___x_4876_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4877_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4876_, v___y_4856_, v___y_4857_);
if (lean_obj_tag(v___x_4877_) == 0)
{
lean_dec_ref_known(v___x_4877_, 1);
v___y_4758_ = v___y_4853_;
v___y_4759_ = v___y_4854_;
v___y_4760_ = v___y_4855_;
v_exportedInfo_x3f_4761_ = v___x_4850_;
v___y_4762_ = v___y_4856_;
v___y_4763_ = v___y_4857_;
goto v___jp_4757_;
}
else
{
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4853_);
lean_dec(v_decl_3908_);
return v___x_4877_;
}
}
}
}
else
{
lean_object* v_toCold_4878_; lean_object* v_options_4879_; uint8_t v_hasTrace_4880_; 
v_toCold_4878_ = lean_ctor_get(v___y_4856_, 0);
v_options_4879_ = lean_ctor_get(v_toCold_4878_, 2);
v_hasTrace_4880_ = lean_ctor_get_uint8(v_options_4879_, sizeof(void*)*1);
if (v_hasTrace_4880_ == 0)
{
v___y_4780_ = v___y_4853_;
v___y_4781_ = v___y_4854_;
v___y_4782_ = v___y_4855_;
v___y_4783_ = v___y_4856_;
v___y_4784_ = v___y_4857_;
goto v___jp_4779_;
}
else
{
lean_object* v_inheritedTraceOptions_4881_; uint8_t v___x_4882_; 
v_inheritedTraceOptions_4881_ = lean_ctor_get(v_toCold_4878_, 11);
v___x_4882_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4881_, v_options_4879_, v___x_4346_);
if (v___x_4882_ == 0)
{
v___y_4780_ = v___y_4853_;
v___y_4781_ = v___y_4854_;
v___y_4782_ = v___y_4855_;
v___y_4783_ = v___y_4856_;
v___y_4784_ = v___y_4857_;
goto v___jp_4779_;
}
else
{
lean_object* v___x_4883_; lean_object* v___x_4884_; 
v___x_4883_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4884_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4883_, v___y_4856_, v___y_4857_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_dec_ref_known(v___x_4884_, 1);
v___y_4780_ = v___y_4853_;
v___y_4781_ = v___y_4854_;
v___y_4782_ = v___y_4855_;
v___y_4783_ = v___y_4856_;
v___y_4784_ = v___y_4857_;
goto v___jp_4779_;
}
else
{
lean_dec_ref(v___y_4855_);
lean_dec(v___y_4853_);
lean_dec(v_decl_3908_);
return v___x_4884_;
}
}
}
}
}
}
v___jp_4885_:
{
lean_object* v___x_4892_; lean_object* v_env_4893_; uint8_t v___x_4894_; 
v___x_4892_ = lean_st_ref_get(v___y_4891_);
v_env_4893_ = lean_ctor_get(v___x_4892_, 0);
lean_inc_ref(v_env_4893_);
lean_dec(v___x_4892_);
v___x_4894_ = l_Lean_Environment_containsOnBranch(v_env_4893_, v_fst_4886_);
lean_dec_ref(v_env_4893_);
if (v___x_4894_ == 0)
{
v___y_4852_ = v_exportedInfo_x3f_4889_;
v___y_4853_ = v_fst_4886_;
v___y_4854_ = v_snd_4888_;
v___y_4855_ = v_fst_4887_;
v___y_4856_ = v___y_4890_;
v___y_4857_ = v___y_4891_;
goto v___jp_4851_;
}
else
{
lean_object* v___x_4895_; lean_object* v_env_4896_; lean_object* v___x_4897_; lean_object* v___x_4898_; lean_object* v___x_4899_; 
lean_dec(v_exportedInfo_x3f_4889_);
lean_dec_ref(v_fst_4887_);
lean_dec(v_decl_3908_);
v___x_4895_ = lean_st_ref_get(v___y_4891_);
v_env_4896_ = lean_ctor_get(v___x_4895_, 0);
lean_inc_ref(v_env_4896_);
lean_dec(v___x_4895_);
v___x_4897_ = lean_elab_environment_to_kernel_env(v_env_4896_);
v___x_4898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4898_, 0, v___x_4897_);
lean_ctor_set(v___x_4898_, 1, v_fst_4886_);
v___x_4899_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4898_, v___y_4890_, v___y_4891_);
return v___x_4899_;
}
}
v___jp_4900_:
{
lean_object* v_toConstantVal_4905_; lean_object* v_name_4906_; lean_object* v___x_4907_; 
v_toConstantVal_4905_ = lean_ctor_get(v___y_4901_, 0);
v_name_4906_ = lean_ctor_get(v_toConstantVal_4905_, 0);
lean_inc(v_name_4906_);
v___x_4907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4907_, 0, v___y_4901_);
v_fst_4886_ = v_name_4906_;
v_fst_4887_ = v___x_4907_;
v_snd_4888_ = v___x_4102_;
v_exportedInfo_x3f_4889_ = v_exportedInfo_x3f_4902_;
v___y_4890_ = v___y_4903_;
v___y_4891_ = v___y_4904_;
goto v___jp_4885_;
}
v___jp_4908_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; 
v___x_4914_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4914_, 0, v___y_4909_);
lean_ctor_set_uint8(v___x_4914_, sizeof(void*)*1, v___y_4913_);
v___x_4915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4915_, 0, v___x_4914_);
v___x_4916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4916_, 0, v___x_4915_);
v___y_4901_ = v___y_4910_;
v_exportedInfo_x3f_4902_ = v___x_4916_;
v___y_4903_ = v___y_4912_;
v___y_4904_ = v___y_4911_;
goto v___jp_4900_;
}
v___jp_4917_:
{
uint8_t v___x_4924_; uint8_t v___x_4925_; 
v___x_4924_ = 1;
v___x_4925_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4920_, v___x_4924_);
if (v___x_4925_ == 0)
{
v___y_4909_ = v_toConstantVal_4919_;
v___y_4910_ = v___y_4918_;
v___y_4911_ = v___y_4923_;
v___y_4912_ = v___y_4922_;
v___y_4913_ = v___y_4921_;
goto v___jp_4908_;
}
else
{
v___y_4909_ = v_toConstantVal_4919_;
v___y_4910_ = v___y_4918_;
v___y_4911_ = v___y_4923_;
v___y_4912_ = v___y_4922_;
v___y_4913_ = v___x_4654_;
goto v___jp_4908_;
}
}
v___jp_4926_:
{
lean_object* v_toConstantVal_4931_; uint8_t v_safety_4932_; 
v_toConstantVal_4931_ = lean_ctor_get(v___y_4927_, 0);
lean_inc_ref(v_toConstantVal_4931_);
v_safety_4932_ = lean_ctor_get_uint8(v___y_4927_, sizeof(void*)*4);
v___y_4918_ = v___y_4927_;
v_toConstantVal_4919_ = v_toConstantVal_4931_;
v_safety_4920_ = v_safety_4932_;
v___y_4921_ = v___y_4928_;
v___y_4922_ = v___y_4929_;
v___y_4923_ = v___y_4930_;
goto v___jp_4917_;
}
v___jp_4933_:
{
lean_object* v_toCold_4938_; lean_object* v_options_4939_; uint8_t v_hasTrace_4940_; 
v_toCold_4938_ = lean_ctor_get(v___y_4935_, 0);
v_options_4939_ = lean_ctor_get(v_toCold_4938_, 2);
v_hasTrace_4940_ = lean_ctor_get_uint8(v_options_4939_, sizeof(void*)*1);
if (v_hasTrace_4940_ == 0)
{
v___y_4927_ = v___y_4934_;
v___y_4928_ = v___y_4937_;
v___y_4929_ = v___y_4935_;
v___y_4930_ = v___y_4936_;
goto v___jp_4926_;
}
else
{
lean_object* v_inheritedTraceOptions_4941_; uint8_t v___x_4942_; 
v_inheritedTraceOptions_4941_ = lean_ctor_get(v_toCold_4938_, 11);
v___x_4942_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4941_, v_options_4939_, v___x_4346_);
if (v___x_4942_ == 0)
{
v___y_4927_ = v___y_4934_;
v___y_4928_ = v___y_4937_;
v___y_4929_ = v___y_4935_;
v___y_4930_ = v___y_4936_;
goto v___jp_4926_;
}
else
{
lean_object* v_toConstantVal_4943_; uint8_t v_safety_4944_; lean_object* v_name_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4951_; 
v_toConstantVal_4943_ = lean_ctor_get(v___y_4934_, 0);
lean_inc_ref(v_toConstantVal_4943_);
v_safety_4944_ = lean_ctor_get_uint8(v___y_4934_, sizeof(void*)*4);
v_name_4945_ = lean_ctor_get(v_toConstantVal_4943_, 0);
v___x_4946_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4945_);
v___x_4947_ = l_Lean_MessageData_ofName(v_name_4945_);
v___x_4948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4948_, 0, v___x_4946_);
lean_ctor_set(v___x_4948_, 1, v___x_4947_);
v___x_4949_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4950_, 0, v___x_4948_);
lean_ctor_set(v___x_4950_, 1, v___x_4949_);
v___x_4951_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4950_, v___y_4935_, v___y_4936_);
if (lean_obj_tag(v___x_4951_) == 0)
{
lean_dec_ref_known(v___x_4951_, 1);
v___y_4918_ = v___y_4934_;
v_toConstantVal_4919_ = v_toConstantVal_4943_;
v_safety_4920_ = v_safety_4944_;
v___y_4921_ = v___y_4937_;
v___y_4922_ = v___y_4935_;
v___y_4923_ = v___y_4936_;
goto v___jp_4917_;
}
else
{
lean_dec_ref(v_toConstantVal_4943_);
lean_dec_ref(v___y_4934_);
lean_dec(v_decl_3908_);
return v___x_4951_;
}
}
}
}
v___jp_4952_:
{
lean_object* v___x_4958_; uint8_t v_isModule_4959_; 
v___x_4958_ = l_Lean_Environment_header(v___y_4955_);
lean_dec_ref(v___y_4955_);
v_isModule_4959_ = lean_ctor_get_uint8(v___x_4958_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4958_);
if (v_isModule_4959_ == 0)
{
lean_dec_ref(v___y_4956_);
v___y_4901_ = v___y_4953_;
v_exportedInfo_x3f_4902_ = v___x_4850_;
v___y_4903_ = v___y_4954_;
v___y_4904_ = v___y_4957_;
goto v___jp_4900_;
}
else
{
uint8_t v_isExporting_4960_; 
v_isExporting_4960_ = lean_ctor_get_uint8(v___y_4956_, sizeof(void*)*13);
lean_dec_ref(v___y_4956_);
if (v_isExporting_4960_ == 0)
{
v___y_4934_ = v___y_4953_;
v___y_4935_ = v___y_4954_;
v___y_4936_ = v___y_4957_;
v___y_4937_ = v_isModule_4959_;
goto v___jp_4933_;
}
else
{
if (v___x_4654_ == 0)
{
v___y_4901_ = v___y_4953_;
v_exportedInfo_x3f_4902_ = v___x_4850_;
v___y_4903_ = v___y_4954_;
v___y_4904_ = v___y_4957_;
goto v___jp_4900_;
}
else
{
v___y_4934_ = v___y_4953_;
v___y_4935_ = v___y_4954_;
v___y_4936_ = v___y_4957_;
v___y_4937_ = v___x_4654_;
goto v___jp_4933_;
}
}
}
}
v___jp_4961_:
{
lean_object* v___x_4965_; lean_object* v_env_4966_; lean_object* v___x_4967_; 
v___x_4965_ = lean_st_ref_get(v___y_4964_);
v_env_4966_ = lean_ctor_get(v___x_4965_, 0);
lean_inc_ref(v_env_4966_);
lean_dec(v___x_4965_);
v___x_4967_ = lean_st_ref_get(v___y_4964_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4968_; 
v_env_4968_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_env_4968_);
lean_dec(v___x_4967_);
v___y_4953_ = v_defn_4962_;
v___y_4954_ = v___y_4963_;
v___y_4955_ = v_env_4966_;
v___y_4956_ = v_env_4968_;
v___y_4957_ = v___y_4964_;
goto v___jp_4952_;
}
else
{
if (v___x_4654_ == 0)
{
lean_dec(v___x_4967_);
lean_dec_ref(v_env_4966_);
v___y_4901_ = v_defn_4962_;
v_exportedInfo_x3f_4902_ = v___x_4850_;
v___y_4903_ = v___y_4963_;
v___y_4904_ = v___y_4964_;
goto v___jp_4900_;
}
else
{
lean_object* v_env_4969_; 
v_env_4969_ = lean_ctor_get(v___x_4967_, 0);
lean_inc_ref(v_env_4969_);
lean_dec(v___x_4967_);
v___y_4953_ = v_defn_4962_;
v___y_4954_ = v___y_4963_;
v___y_4955_ = v_env_4966_;
v___y_4956_ = v_env_4969_;
v___y_4957_ = v___y_4964_;
goto v___jp_4952_;
}
}
}
}
}
}
else
{
goto v___jp_4495_;
}
v___jp_4655_:
{
lean_object* v___x_4667_; 
lean_inc_ref(v___y_4658_);
v___x_4667_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4663_, v___y_4658_, v___y_4665_, v___y_4666_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v___x_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4714_; 
lean_dec_ref_known(v___x_4667_, 1);
lean_dec(v___y_4656_);
lean_inc_ref(v___y_4661_);
v___x_4668_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4661_, v___y_4657_);
v_isSharedCheck_4714_ = !lean_is_exclusive(v___x_4668_);
if (v_isSharedCheck_4714_ == 0)
{
lean_object* v_unused_4715_; 
v_unused_4715_ = lean_ctor_get(v___x_4668_, 0);
lean_dec(v_unused_4715_);
v___x_4670_ = v___x_4668_;
v_isShared_4671_ = v_isSharedCheck_4714_;
goto v_resetjp_4669_;
}
else
{
lean_dec(v___x_4668_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4714_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
lean_object* v___x_4672_; lean_object* v___x_4673_; uint8_t v___x_4674_; 
v___x_4672_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4664_);
v___x_4673_ = l_Lean_Elab_async;
v___x_4674_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4672_, v___x_4673_);
lean_dec_ref(v___x_4672_);
if (v___x_4674_ == 0)
{
lean_object* v___x_4675_; lean_object* v_r_4676_; 
lean_del_object(v___x_4670_);
lean_dec_ref(v___y_4662_);
lean_dec_ref(v___y_4659_);
v___x_4675_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4658_, v___y_4657_);
lean_dec_ref(v___x_4675_);
v_r_4676_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v___y_4664_, v___y_4657_);
if (lean_obj_tag(v_r_4676_) == 0)
{
lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4686_; 
v_a_4677_ = lean_ctor_get(v_r_4676_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_r_4676_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4679_ = v_r_4676_;
v_isShared_4680_ = v_isSharedCheck_4686_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v_r_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4686_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4682_; 
lean_inc(v_a_4677_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set_tag(v___x_4679_, 1);
v___x_4682_ = v___x_4679_;
goto v_reusejp_4681_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4677_);
v___x_4682_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4681_;
}
v_reusejp_4681_:
{
lean_object* v___x_4683_; 
v___x_4683_ = lean_apply_2(v___y_4660_, v___x_4682_, lean_box(0));
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_dec_ref_known(v___x_4683_, 1);
v___y_3940_ = v___y_4657_;
v___y_3941_ = v___y_4661_;
v_a_3942_ = v_a_4677_;
goto v___jp_3939_;
}
else
{
lean_object* v_a_4684_; 
lean_dec(v_a_4677_);
v_a_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc(v_a_4684_);
lean_dec_ref_known(v___x_4683_, 1);
v___y_3953_ = v___y_4657_;
v___y_3954_ = v___y_4661_;
v_a_3955_ = v_a_4684_;
goto v___jp_3952_;
}
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; 
v_a_4687_ = lean_ctor_get(v_r_4676_, 0);
lean_inc(v_a_4687_);
lean_dec_ref_known(v_r_4676_, 1);
v___x_4688_ = lean_box(0);
v___x_4689_ = lean_apply_2(v___y_4660_, v___x_4688_, lean_box(0));
if (lean_obj_tag(v___x_4689_) == 0)
{
lean_dec_ref_known(v___x_4689_, 1);
v___y_3953_ = v___y_4657_;
v___y_3954_ = v___y_4661_;
v_a_3955_ = v_a_4687_;
goto v___jp_3952_;
}
else
{
lean_object* v_a_4690_; 
lean_dec(v_a_4687_);
v_a_4690_ = lean_ctor_get(v___x_4689_, 0);
lean_inc(v_a_4690_);
lean_dec_ref_known(v___x_4689_, 1);
v___y_3953_ = v___y_4657_;
v___y_3954_ = v___y_4661_;
v_a_3955_ = v_a_4690_;
goto v___jp_3952_;
}
}
}
else
{
lean_object* v___x_4691_; lean_object* v___x_4693_; 
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec_ref(v___y_4658_);
lean_dec(v_decl_3908_);
v___x_4691_ = l_IO_CancelToken_new();
if (v_isShared_4671_ == 0)
{
lean_ctor_set_tag(v___x_4670_, 1);
lean_ctor_set(v___x_4670_, 0, v___x_4691_);
v___x_4693_ = v___x_4670_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4713_; 
v_reuseFailAlloc_4713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4713_, 0, v___x_4691_);
v___x_4693_ = v_reuseFailAlloc_4713_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v___x_4694_ = lean_unsigned_to_nat(0u);
v___x_4695_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4696_ = l_Lean_Name_toString(v___x_4695_, v_hasTrace_3968_);
lean_inc_ref(v___x_4693_);
v___x_4697_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4659_, v___x_4693_, v___x_4696_, v___y_4664_, v___y_4657_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v_checked_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v___x_4704_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref_known(v___x_4697_, 1);
v_checked_4699_ = lean_ctor_get(v___y_4662_, 2);
lean_inc_ref(v_checked_4699_);
lean_dec_ref(v___y_4662_);
v___x_4700_ = lean_io_map_task(v_a_4698_, v_checked_4699_, v___x_4694_, v___x_4654_);
v___x_4701_ = lean_box(0);
v___x_4702_ = lean_box(2);
v___x_4703_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4703_, 0, v___x_4701_);
lean_ctor_set(v___x_4703_, 1, v___x_4702_);
lean_ctor_set(v___x_4703_, 2, v___x_4693_);
lean_ctor_set(v___x_4703_, 3, v___x_4700_);
v___x_4704_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4703_, v___y_4657_);
return v___x_4704_;
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec_ref(v___x_4693_);
lean_dec_ref(v___y_4662_);
v_a_4705_ = lean_ctor_get(v___x_4697_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4697_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4697_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4697_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4716_; lean_object* v___x_4718_; uint8_t v_isShared_4719_; uint8_t v_isSharedCheck_4727_; 
lean_dec_ref(v___y_4662_);
lean_dec_ref(v___y_4661_);
lean_dec_ref(v___y_4660_);
lean_dec_ref(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v_decl_3908_);
v_a_4716_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4718_ = v___x_4667_;
v_isShared_4719_ = v_isSharedCheck_4727_;
goto v_resetjp_4717_;
}
else
{
lean_inc(v_a_4716_);
lean_dec(v___x_4667_);
v___x_4718_ = lean_box(0);
v_isShared_4719_ = v_isSharedCheck_4727_;
goto v_resetjp_4717_;
}
v_resetjp_4717_:
{
lean_object* v___x_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4725_; 
v___x_4720_ = lean_io_error_to_string(v_a_4716_);
v___x_4721_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4721_, 0, v___x_4720_);
v___x_4722_ = l_Lean_MessageData_ofFormat(v___x_4721_);
v___x_4723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4723_, 0, v___y_4656_);
lean_ctor_set(v___x_4723_, 1, v___x_4722_);
if (v_isShared_4719_ == 0)
{
lean_ctor_set(v___x_4718_, 0, v___x_4723_);
v___x_4725_ = v___x_4718_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v___x_4723_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
}
v___jp_4728_:
{
lean_object* v_ref_4737_; lean_object* v___x_4738_; 
v_ref_4737_ = lean_ctor_get(v___y_4733_, 2);
lean_inc_ref(v___y_4735_);
v___x_4738_ = l_Lean_Environment_addConstAsync(v___y_4735_, v___y_4732_, v___y_4729_, v___y_4736_, v___x_4654_, v_hasTrace_3968_);
if (lean_obj_tag(v___x_4738_) == 0)
{
lean_object* v_a_4739_; lean_object* v_mainEnv_4740_; lean_object* v_asyncEnv_4741_; lean_object* v___f_4742_; lean_object* v___f_4743_; lean_object* v___x_4744_; 
v_a_4739_ = lean_ctor_get(v___x_4738_, 0);
lean_inc_n(v_a_4739_, 3);
lean_dec_ref_known(v___x_4738_, 1);
v_mainEnv_4740_ = lean_ctor_get(v_a_4739_, 0);
lean_inc_ref(v_mainEnv_4740_);
v_asyncEnv_4741_ = lean_ctor_get(v_a_4739_, 1);
lean_inc_ref_n(v_asyncEnv_4741_, 2);
lean_inc(v_ref_4737_);
lean_inc(v___y_4730_);
v___f_4742_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4742_, 0, v___y_4730_);
lean_closure_set(v___f_4742_, 1, v_a_4739_);
lean_closure_set(v___f_4742_, 2, v_ref_4737_);
lean_inc(v_decl_3908_);
v___f_4743_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4743_, 0, v_a_4739_);
lean_closure_set(v___f_4743_, 1, v_asyncEnv_4741_);
lean_closure_set(v___f_4743_, 2, v_decl_3908_);
v___x_4744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4744_, 0, v___y_4731_);
if (lean_obj_tag(v___y_4734_) == 0)
{
lean_inc_ref(v___x_4744_);
lean_inc(v_ref_4737_);
v___y_4656_ = v_ref_4737_;
v___y_4657_ = v___y_4730_;
v___y_4658_ = v_asyncEnv_4741_;
v___y_4659_ = v___f_4743_;
v___y_4660_ = v___f_4742_;
v___y_4661_ = v_mainEnv_4740_;
v___y_4662_ = v___y_4735_;
v___y_4663_ = v_a_4739_;
v___y_4664_ = v___y_4733_;
v___y_4665_ = v___x_4744_;
v___y_4666_ = v___x_4744_;
goto v___jp_4655_;
}
else
{
lean_inc(v_ref_4737_);
v___y_4656_ = v_ref_4737_;
v___y_4657_ = v___y_4730_;
v___y_4658_ = v_asyncEnv_4741_;
v___y_4659_ = v___f_4743_;
v___y_4660_ = v___f_4742_;
v___y_4661_ = v_mainEnv_4740_;
v___y_4662_ = v___y_4735_;
v___y_4663_ = v_a_4739_;
v___y_4664_ = v___y_4733_;
v___y_4665_ = v___x_4744_;
v___y_4666_ = v___y_4734_;
goto v___jp_4655_;
}
}
else
{
lean_object* v_a_4745_; lean_object* v___x_4747_; uint8_t v_isShared_4748_; uint8_t v_isSharedCheck_4756_; 
lean_dec_ref(v___y_4735_);
lean_dec(v___y_4734_);
lean_dec_ref(v___y_4731_);
lean_dec(v_decl_3908_);
v_a_4745_ = lean_ctor_get(v___x_4738_, 0);
v_isSharedCheck_4756_ = !lean_is_exclusive(v___x_4738_);
if (v_isSharedCheck_4756_ == 0)
{
v___x_4747_ = v___x_4738_;
v_isShared_4748_ = v_isSharedCheck_4756_;
goto v_resetjp_4746_;
}
else
{
lean_inc(v_a_4745_);
lean_dec(v___x_4738_);
v___x_4747_ = lean_box(0);
v_isShared_4748_ = v_isSharedCheck_4756_;
goto v_resetjp_4746_;
}
v_resetjp_4746_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
v___x_4749_ = lean_io_error_to_string(v_a_4745_);
v___x_4750_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
v___x_4751_ = l_Lean_MessageData_ofFormat(v___x_4750_);
lean_inc(v_ref_4737_);
v___x_4752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4752_, 0, v_ref_4737_);
lean_ctor_set(v___x_4752_, 1, v___x_4751_);
if (v_isShared_4748_ == 0)
{
lean_ctor_set(v___x_4747_, 0, v___x_4752_);
v___x_4754_ = v___x_4747_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4755_; 
v_reuseFailAlloc_4755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4755_, 0, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4755_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
return v___x_4754_;
}
}
}
}
v___jp_4757_:
{
lean_object* v___x_4764_; 
v___x_4764_ = lean_st_ref_get(v___y_4763_);
if (lean_obj_tag(v_exportedInfo_x3f_4761_) == 0)
{
lean_object* v_env_4765_; lean_object* v___x_4766_; 
v_env_4765_ = lean_ctor_get(v___x_4764_, 0);
lean_inc_ref(v_env_4765_);
lean_dec(v___x_4764_);
v___x_4766_ = lean_box(0);
v___y_4729_ = v___y_4759_;
v___y_4730_ = v___y_4763_;
v___y_4731_ = v___y_4760_;
v___y_4732_ = v___y_4758_;
v___y_4733_ = v___y_4762_;
v___y_4734_ = v_exportedInfo_x3f_4761_;
v___y_4735_ = v_env_4765_;
v___y_4736_ = v___x_4766_;
goto v___jp_4728_;
}
else
{
lean_object* v_env_4767_; lean_object* v_val_4768_; uint8_t v___x_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; 
v_env_4767_ = lean_ctor_get(v___x_4764_, 0);
lean_inc_ref(v_env_4767_);
lean_dec(v___x_4764_);
v_val_4768_ = lean_ctor_get(v_exportedInfo_x3f_4761_, 0);
v___x_4769_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4768_);
v___x_4770_ = lean_box(v___x_4769_);
v___x_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
v___y_4729_ = v___y_4759_;
v___y_4730_ = v___y_4763_;
v___y_4731_ = v___y_4760_;
v___y_4732_ = v___y_4758_;
v___y_4733_ = v___y_4762_;
v___y_4734_ = v_exportedInfo_x3f_4761_;
v___y_4735_ = v_env_4767_;
v___y_4736_ = v___x_4771_;
goto v___jp_4728_;
}
}
v___jp_4772_:
{
lean_object* v___x_4778_; 
lean_inc_ref(v___y_4775_);
v___x_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___y_4775_);
v___y_4758_ = v___y_4773_;
v___y_4759_ = v___y_4774_;
v___y_4760_ = v___y_4775_;
v_exportedInfo_x3f_4761_ = v___x_4778_;
v___y_4762_ = v___y_4776_;
v___y_4763_ = v___y_4777_;
goto v___jp_4757_;
}
v___jp_4779_:
{
lean_object* v___x_4785_; 
lean_inc_ref(v___y_4782_);
v___x_4785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___y_4782_);
v___y_4758_ = v___y_4780_;
v___y_4759_ = v___y_4781_;
v___y_4760_ = v___y_4782_;
v_exportedInfo_x3f_4761_ = v___x_4785_;
v___y_4762_ = v___y_4783_;
v___y_4763_ = v___y_4784_;
goto v___jp_4757_;
}
}
else
{
goto v___jp_4495_;
}
v___jp_4348_:
{
lean_object* v___x_4352_; double v___x_4353_; double v___x_4354_; double v___x_4355_; double v___x_4356_; double v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; 
v___x_4352_ = lean_io_mono_nanos_now();
v___x_4353_ = lean_float_of_nat(v___y_4349_);
v___x_4354_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4355_ = lean_float_div(v___x_4353_, v___x_4354_);
v___x_4356_ = lean_float_of_nat(v___x_4352_);
v___x_4357_ = lean_float_div(v___x_4356_, v___x_4354_);
v___x_4358_ = lean_box_float(v___x_4355_);
v___x_4359_ = lean_box_float(v___x_4357_);
v___x_4360_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4361_, 0, v_a_4351_);
lean_ctor_set(v___x_4361_, 1, v___x_4360_);
v___x_4362_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4103_, v_hasTrace_3968_, v___x_4345_, v_options_3966_, v___x_4347_, v___y_4350_, v___f_4344_, v___x_4361_, v_a_3910_, v_a_3911_);
return v___x_4362_;
}
v___jp_4363_:
{
if (lean_obj_tag(v___y_4366_) == 0)
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
v_a_4367_ = lean_ctor_get(v___y_4366_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___y_4366_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___y_4366_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___y_4366_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
lean_ctor_set_tag(v___x_4369_, 1);
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
v___y_4349_ = v___y_4364_;
v___y_4350_ = v___y_4365_;
v_a_4351_ = v___x_4372_;
goto v___jp_4348_;
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
v_a_4375_ = lean_ctor_get(v___y_4366_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___y_4366_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___y_4366_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___y_4366_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 0);
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
v___y_4349_ = v___y_4364_;
v___y_4350_ = v___y_4365_;
v_a_4351_ = v___x_4380_;
goto v___jp_4348_;
}
}
}
}
v___jp_4383_:
{
lean_object* v___x_4388_; lean_object* v___x_4389_; 
v___x_4388_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4389_ = lean_apply_5(v___y_4387_, v___x_4388_, v___y_4385_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4384_;
v___y_4365_ = v___y_4386_;
v___y_4366_ = v___x_4389_;
goto v___jp_4363_;
}
v___jp_4390_:
{
lean_object* v___x_4398_; uint8_t v_isModule_4399_; 
v___x_4398_ = l_Lean_Environment_header(v___y_4397_);
lean_dec_ref(v___y_4397_);
v_isModule_4399_ = lean_ctor_get_uint8(v___x_4398_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4398_);
if (v_isModule_4399_ == 0)
{
lean_dec_ref(v___y_4396_);
lean_dec_ref(v___y_4395_);
v___y_4384_ = v___y_4391_;
v___y_4385_ = v___y_4392_;
v___y_4386_ = v___y_4394_;
v___y_4387_ = v___y_4393_;
goto v___jp_4383_;
}
else
{
lean_dec_ref(v___y_4393_);
lean_dec(v___y_4392_);
if (v___x_4347_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
lean_dec_ref(v___y_4395_);
v___x_4400_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4401_ = lean_apply_4(v___y_4396_, v___x_4400_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___x_4401_;
goto v___jp_4363_;
}
else
{
lean_object* v_toConstantVal_4402_; lean_object* v_name_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_toConstantVal_4402_ = lean_ctor_get(v___y_4395_, 0);
lean_inc_ref(v_toConstantVal_4402_);
lean_dec_ref(v___y_4395_);
v_name_4403_ = lean_ctor_get(v_toConstantVal_4402_, 0);
lean_inc(v_name_4403_);
lean_dec_ref(v_toConstantVal_4402_);
v___x_4404_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4405_ = l_Lean_MessageData_ofName(v_name_4403_);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4408_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4411_ = lean_apply_4(v___y_4396_, v_a_4410_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___x_4411_;
goto v___jp_4363_;
}
else
{
lean_dec_ref(v___y_4396_);
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4394_;
v___y_4366_ = v___x_4409_;
goto v___jp_4363_;
}
}
}
}
v___jp_4412_:
{
if (v___x_4347_ == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4418_; 
lean_dec_ref(v___y_4413_);
v___x_4417_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4418_ = lean_apply_4(v___y_4415_, v___x_4417_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4414_;
v___y_4365_ = v___y_4416_;
v___y_4366_ = v___x_4418_;
goto v___jp_4363_;
}
else
{
lean_object* v_toConstantVal_4419_; lean_object* v_name_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; lean_object* v___x_4426_; 
v_toConstantVal_4419_ = lean_ctor_get(v___y_4413_, 0);
lean_inc_ref(v_toConstantVal_4419_);
lean_dec_ref(v___y_4413_);
v_name_4420_ = lean_ctor_get(v_toConstantVal_4419_, 0);
lean_inc(v_name_4420_);
lean_dec_ref(v_toConstantVal_4419_);
v___x_4421_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4422_ = l_Lean_MessageData_ofName(v_name_4420_);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4425_, 0, v___x_4423_);
lean_ctor_set(v___x_4425_, 1, v___x_4424_);
v___x_4426_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4425_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_4426_) == 0)
{
lean_object* v_a_4427_; lean_object* v___x_4428_; 
v_a_4427_ = lean_ctor_get(v___x_4426_, 0);
lean_inc(v_a_4427_);
lean_dec_ref_known(v___x_4426_, 1);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4428_ = lean_apply_4(v___y_4415_, v_a_4427_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4414_;
v___y_4365_ = v___y_4416_;
v___y_4366_ = v___x_4428_;
goto v___jp_4363_;
}
else
{
lean_dec_ref(v___y_4415_);
v___y_4364_ = v___y_4414_;
v___y_4365_ = v___y_4416_;
v___y_4366_ = v___x_4426_;
goto v___jp_4363_;
}
}
}
v___jp_4429_:
{
lean_object* v___x_4434_; lean_object* v___x_4435_; 
v___x_4434_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4435_ = lean_apply_5(v___y_4432_, v___x_4434_, v___y_4431_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4364_ = v___y_4430_;
v___y_4365_ = v___y_4433_;
v___y_4366_ = v___x_4435_;
goto v___jp_4363_;
}
v___jp_4436_:
{
lean_object* v___x_4446_; uint8_t v_isModule_4447_; 
v___x_4446_ = l_Lean_Environment_header(v___y_4445_);
lean_dec_ref(v___y_4445_);
v_isModule_4447_ = lean_ctor_get_uint8(v___x_4446_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4446_);
if (v_isModule_4447_ == 0)
{
lean_dec_ref(v___y_4444_);
lean_dec_ref(v___y_4441_);
lean_dec_ref(v___y_4437_);
v___y_4430_ = v___y_4438_;
v___y_4431_ = v___y_4439_;
v___y_4432_ = v___y_4442_;
v___y_4433_ = v___y_4443_;
goto v___jp_4429_;
}
else
{
uint8_t v_isExporting_4448_; 
v_isExporting_4448_ = lean_ctor_get_uint8(v___y_4444_, sizeof(void*)*13);
lean_dec_ref(v___y_4444_);
if (v_isExporting_4448_ == 0)
{
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4439_);
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4438_;
v___y_4415_ = v___y_4441_;
v___y_4416_ = v___y_4443_;
goto v___jp_4412_;
}
else
{
if (v___y_4440_ == 0)
{
lean_dec_ref(v___y_4441_);
lean_dec_ref(v___y_4437_);
v___y_4430_ = v___y_4438_;
v___y_4431_ = v___y_4439_;
v___y_4432_ = v___y_4442_;
v___y_4433_ = v___y_4443_;
goto v___jp_4429_;
}
else
{
lean_dec_ref(v___y_4442_);
lean_dec(v___y_4439_);
v___y_4413_ = v___y_4437_;
v___y_4414_ = v___y_4438_;
v___y_4415_ = v___y_4441_;
v___y_4416_ = v___y_4443_;
goto v___jp_4412_;
}
}
}
}
v___jp_4449_:
{
lean_object* v___x_4453_; double v___x_4454_; double v___x_4455_; lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4453_ = lean_io_get_num_heartbeats();
v___x_4454_ = lean_float_of_nat(v___y_4450_);
v___x_4455_ = lean_float_of_nat(v___x_4453_);
v___x_4456_ = lean_box_float(v___x_4454_);
v___x_4457_ = lean_box_float(v___x_4455_);
v___x_4458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4456_);
lean_ctor_set(v___x_4458_, 1, v___x_4457_);
v___x_4459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4459_, 0, v_a_4452_);
lean_ctor_set(v___x_4459_, 1, v___x_4458_);
v___x_4460_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_4103_, v_hasTrace_3968_, v___x_4345_, v_options_3966_, v___x_4347_, v___y_4451_, v___f_4344_, v___x_4459_, v_a_3910_, v_a_3911_);
return v___x_4460_;
}
v___jp_4461_:
{
if (lean_obj_tag(v___y_4464_) == 0)
{
lean_object* v_a_4465_; lean_object* v___x_4467_; uint8_t v_isShared_4468_; uint8_t v_isSharedCheck_4472_; 
v_a_4465_ = lean_ctor_get(v___y_4464_, 0);
v_isSharedCheck_4472_ = !lean_is_exclusive(v___y_4464_);
if (v_isSharedCheck_4472_ == 0)
{
v___x_4467_ = v___y_4464_;
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
else
{
lean_inc(v_a_4465_);
lean_dec(v___y_4464_);
v___x_4467_ = lean_box(0);
v_isShared_4468_ = v_isSharedCheck_4472_;
goto v_resetjp_4466_;
}
v_resetjp_4466_:
{
lean_object* v___x_4470_; 
if (v_isShared_4468_ == 0)
{
lean_ctor_set_tag(v___x_4467_, 1);
v___x_4470_ = v___x_4467_;
goto v_reusejp_4469_;
}
else
{
lean_object* v_reuseFailAlloc_4471_; 
v_reuseFailAlloc_4471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4471_, 0, v_a_4465_);
v___x_4470_ = v_reuseFailAlloc_4471_;
goto v_reusejp_4469_;
}
v_reusejp_4469_:
{
v___y_4450_ = v___y_4462_;
v___y_4451_ = v___y_4463_;
v_a_4452_ = v___x_4470_;
goto v___jp_4449_;
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4480_; 
v_a_4473_ = lean_ctor_get(v___y_4464_, 0);
v_isSharedCheck_4480_ = !lean_is_exclusive(v___y_4464_);
if (v_isSharedCheck_4480_ == 0)
{
v___x_4475_ = v___y_4464_;
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___y_4464_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4480_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
if (v_isShared_4476_ == 0)
{
lean_ctor_set_tag(v___x_4475_, 0);
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4479_; 
v_reuseFailAlloc_4479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4479_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4479_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
v___y_4450_ = v___y_4462_;
v___y_4451_ = v___y_4463_;
v_a_4452_ = v___x_4478_;
goto v___jp_4449_;
}
}
}
}
v___jp_4481_:
{
lean_object* v___x_4486_; lean_object* v___x_4487_; 
v___x_4486_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4487_ = lean_apply_5(v___y_4482_, v___x_4486_, v___y_4485_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4462_ = v___y_4483_;
v___y_4463_ = v___y_4484_;
v___y_4464_ = v___x_4487_;
goto v___jp_4461_;
}
v___jp_4488_:
{
lean_object* v___x_4493_; lean_object* v___x_4494_; 
v___x_4493_ = lean_box(0);
lean_inc(v_a_3911_);
lean_inc_ref(v_a_3910_);
v___x_4494_ = lean_apply_5(v___y_4491_, v___x_4493_, v___y_4492_, v_a_3910_, v_a_3911_, lean_box(0));
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___x_4494_;
goto v___jp_4461_;
}
v___jp_4495_:
{
lean_object* v___x_4496_; lean_object* v_a_4497_; lean_object* v___x_4499_; uint8_t v_isShared_4500_; uint8_t v_isSharedCheck_4652_; 
v___x_4496_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3911_);
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4652_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4652_ == 0)
{
v___x_4499_ = v___x_4496_;
v_isShared_4500_ = v_isSharedCheck_4652_;
goto v_resetjp_4498_;
}
else
{
lean_inc(v_a_4497_);
lean_dec(v___x_4496_);
v___x_4499_ = lean_box(0);
v_isShared_4500_ = v_isSharedCheck_4652_;
goto v_resetjp_4498_;
}
v_resetjp_4498_:
{
lean_object* v___x_4501_; uint8_t v___x_4502_; 
v___x_4501_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4502_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3966_, v___x_4501_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; lean_object* v___x_4504_; lean_object* v_env_4505_; lean_object* v_nextMacroScope_4506_; lean_object* v_ngen_4507_; lean_object* v_auxDeclNGen_4508_; lean_object* v_traceState_4509_; lean_object* v_recordedDeps_4510_; lean_object* v_messages_4511_; lean_object* v_infoState_4512_; lean_object* v_snapshotTasks_4513_; lean_object* v___x_4515_; uint8_t v_isShared_4516_; uint8_t v_isSharedCheck_4564_; 
v___x_4503_ = lean_io_mono_nanos_now();
v___x_4504_ = lean_st_ref_take(v_a_3911_);
v_env_4505_ = lean_ctor_get(v___x_4504_, 0);
v_nextMacroScope_4506_ = lean_ctor_get(v___x_4504_, 1);
v_ngen_4507_ = lean_ctor_get(v___x_4504_, 2);
v_auxDeclNGen_4508_ = lean_ctor_get(v___x_4504_, 3);
v_traceState_4509_ = lean_ctor_get(v___x_4504_, 4);
v_recordedDeps_4510_ = lean_ctor_get(v___x_4504_, 6);
v_messages_4511_ = lean_ctor_get(v___x_4504_, 7);
v_infoState_4512_ = lean_ctor_get(v___x_4504_, 8);
v_snapshotTasks_4513_ = lean_ctor_get(v___x_4504_, 9);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4504_);
if (v_isSharedCheck_4564_ == 0)
{
lean_object* v_unused_4565_; 
v_unused_4565_ = lean_ctor_get(v___x_4504_, 5);
lean_dec(v_unused_4565_);
v___x_4515_ = v___x_4504_;
v_isShared_4516_ = v_isSharedCheck_4564_;
goto v_resetjp_4514_;
}
else
{
lean_inc(v_snapshotTasks_4513_);
lean_inc(v_infoState_4512_);
lean_inc(v_messages_4511_);
lean_inc(v_recordedDeps_4510_);
lean_inc(v_traceState_4509_);
lean_inc(v_auxDeclNGen_4508_);
lean_inc(v_ngen_4507_);
lean_inc(v_nextMacroScope_4506_);
lean_inc(v_env_4505_);
lean_dec(v___x_4504_);
v___x_4515_ = lean_box(0);
v_isShared_4516_ = v_isSharedCheck_4564_;
goto v_resetjp_4514_;
}
v_resetjp_4514_:
{
lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4521_; 
lean_inc(v_decl_3908_);
v___x_4517_ = l_Lean_Declaration_getNames(v_decl_3908_);
v___x_4518_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4505_, v___x_4517_);
v___x_4519_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4516_ == 0)
{
lean_ctor_set(v___x_4515_, 5, v___x_4519_);
lean_ctor_set(v___x_4515_, 0, v___x_4518_);
v___x_4521_ = v___x_4515_;
goto v_reusejp_4520_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4518_);
lean_ctor_set(v_reuseFailAlloc_4563_, 1, v_nextMacroScope_4506_);
lean_ctor_set(v_reuseFailAlloc_4563_, 2, v_ngen_4507_);
lean_ctor_set(v_reuseFailAlloc_4563_, 3, v_auxDeclNGen_4508_);
lean_ctor_set(v_reuseFailAlloc_4563_, 4, v_traceState_4509_);
lean_ctor_set(v_reuseFailAlloc_4563_, 5, v___x_4519_);
lean_ctor_set(v_reuseFailAlloc_4563_, 6, v_recordedDeps_4510_);
lean_ctor_set(v_reuseFailAlloc_4563_, 7, v_messages_4511_);
lean_ctor_set(v_reuseFailAlloc_4563_, 8, v_infoState_4512_);
lean_ctor_set(v_reuseFailAlloc_4563_, 9, v_snapshotTasks_4513_);
v___x_4521_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4520_;
}
v_reusejp_4520_:
{
lean_object* v___x_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___f_4527_; 
v___x_4522_ = lean_st_ref_put(v_a_3911_, v___x_4521_);
v___x_4523_ = lean_box(0);
v___x_4524_ = lean_box(v_hasTrace_3968_);
v___x_4525_ = lean_box(v___x_4502_);
v___x_4526_ = lean_box(v___x_4102_);
lean_inc(v_decl_3908_);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 12, 7);
lean_closure_set(v___f_4527_, 0, v_decl_3908_);
lean_closure_set(v___f_4527_, 1, v___x_4524_);
lean_closure_set(v___f_4527_, 2, v___x_4525_);
lean_closure_set(v___f_4527_, 3, v___x_4519_);
lean_closure_set(v___f_4527_, 4, v___x_4526_);
lean_closure_set(v___f_4527_, 5, v_cls_4103_);
lean_closure_set(v___f_4527_, 6, v___x_4523_);
switch(lean_obj_tag(v_decl_3908_))
{
case 2:
{
lean_object* v_val_4528_; lean_object* v___f_4529_; lean_object* v___x_4530_; lean_object* v___f_4531_; lean_object* v___x_4532_; 
lean_del_object(v___x_4499_);
v_val_4528_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref_n(v_val_4528_, 3);
lean_dec_ref_known(v_decl_3908_, 1);
v___f_4529_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4529_, 0, v_val_4528_);
lean_closure_set(v___f_4529_, 1, v___f_4527_);
v___x_4530_ = lean_box(v___x_4502_);
lean_inc_ref(v___f_4529_);
v___f_4531_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4531_, 0, v_val_4528_);
lean_closure_set(v___f_4531_, 1, v___x_4530_);
lean_closure_set(v___f_4531_, 2, v___f_4529_);
v___x_4532_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4533_; 
v_env_4533_ = lean_ctor_get(v___x_4532_, 0);
lean_inc_ref(v_env_4533_);
lean_dec(v___x_4532_);
v___y_4391_ = v___x_4503_;
v___y_4392_ = v___x_4523_;
v___y_4393_ = v___f_4529_;
v___y_4394_ = v_a_4497_;
v___y_4395_ = v_val_4528_;
v___y_4396_ = v___f_4531_;
v___y_4397_ = v_env_4533_;
goto v___jp_4390_;
}
else
{
if (v___x_4502_ == 0)
{
lean_dec(v___x_4532_);
lean_dec_ref(v___f_4531_);
lean_dec_ref(v_val_4528_);
v___y_4384_ = v___x_4503_;
v___y_4385_ = v___x_4523_;
v___y_4386_ = v_a_4497_;
v___y_4387_ = v___f_4529_;
goto v___jp_4383_;
}
else
{
lean_object* v_env_4534_; 
v_env_4534_ = lean_ctor_get(v___x_4532_, 0);
lean_inc_ref(v_env_4534_);
lean_dec(v___x_4532_);
v___y_4391_ = v___x_4503_;
v___y_4392_ = v___x_4523_;
v___y_4393_ = v___f_4529_;
v___y_4394_ = v_a_4497_;
v___y_4395_ = v_val_4528_;
v___y_4396_ = v___f_4531_;
v___y_4397_ = v_env_4534_;
goto v___jp_4390_;
}
}
}
case 1:
{
lean_object* v_val_4535_; lean_object* v___x_4536_; 
lean_del_object(v___x_4499_);
v_val_4535_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref(v_val_4535_);
lean_dec_ref_known(v_decl_3908_, 1);
v___x_4536_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4527_, v___x_4502_, v_cls_4103_, v___x_4523_, v_forceExpose_3909_, v_val_4535_, v_a_3910_, v_a_3911_);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4536_;
goto v___jp_4363_;
}
case 5:
{
lean_object* v_defns_4537_; 
lean_del_object(v___x_4499_);
v_defns_4537_ = lean_ctor_get(v_decl_3908_, 0);
if (lean_obj_tag(v_defns_4537_) == 1)
{
lean_object* v_tail_4538_; 
v_tail_4538_ = lean_ctor_get(v_defns_4537_, 1);
if (lean_obj_tag(v_tail_4538_) == 0)
{
lean_object* v_head_4539_; lean_object* v___x_4540_; 
lean_inc_ref(v_defns_4537_);
lean_dec_ref_known(v_decl_3908_, 1);
v_head_4539_ = lean_ctor_get(v_defns_4537_, 0);
lean_inc(v_head_4539_);
lean_dec_ref_known(v_defns_4537_, 2);
v___x_4540_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4527_, v___x_4502_, v_cls_4103_, v___x_4523_, v_forceExpose_3909_, v_head_4539_, v_a_3910_, v_a_3911_);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4540_;
goto v___jp_4363_;
}
else
{
lean_object* v___x_4541_; 
lean_dec_ref(v___f_4527_);
lean_inc_ref(v_decl_3908_);
v___x_4541_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec_ref_known(v_decl_3908_, 1);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4541_;
goto v___jp_4363_;
}
}
else
{
lean_object* v___x_4542_; 
lean_dec_ref(v___f_4527_);
lean_inc_ref(v_decl_3908_);
v___x_4542_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec_ref_known(v_decl_3908_, 1);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4542_;
goto v___jp_4363_;
}
}
case 3:
{
lean_object* v_val_4543_; lean_object* v___f_4544_; lean_object* v___f_4545_; lean_object* v___x_4546_; lean_object* v_env_4547_; lean_object* v___x_4548_; 
lean_del_object(v___x_4499_);
v_val_4543_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref_n(v_val_4543_, 3);
lean_dec_ref_known(v_decl_3908_, 1);
v___f_4544_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4544_, 0, v_val_4543_);
lean_closure_set(v___f_4544_, 1, v___f_4527_);
lean_inc_ref(v___f_4544_);
v___f_4545_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4545_, 0, v_val_4543_);
lean_closure_set(v___f_4545_, 1, v___f_4544_);
v___x_4546_ = lean_st_ref_get(v_a_3911_);
v_env_4547_ = lean_ctor_get(v___x_4546_, 0);
lean_inc_ref(v_env_4547_);
lean_dec(v___x_4546_);
v___x_4548_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
lean_object* v_env_4549_; 
v_env_4549_ = lean_ctor_get(v___x_4548_, 0);
lean_inc_ref(v_env_4549_);
lean_dec(v___x_4548_);
v___y_4437_ = v_val_4543_;
v___y_4438_ = v___x_4503_;
v___y_4439_ = v___x_4523_;
v___y_4440_ = v___x_4502_;
v___y_4441_ = v___f_4545_;
v___y_4442_ = v___f_4544_;
v___y_4443_ = v_a_4497_;
v___y_4444_ = v_env_4549_;
v___y_4445_ = v_env_4547_;
goto v___jp_4436_;
}
else
{
if (v___x_4502_ == 0)
{
lean_dec(v___x_4548_);
lean_dec_ref(v_env_4547_);
lean_dec_ref(v___f_4545_);
lean_dec_ref(v_val_4543_);
v___y_4430_ = v___x_4503_;
v___y_4431_ = v___x_4523_;
v___y_4432_ = v___f_4544_;
v___y_4433_ = v_a_4497_;
goto v___jp_4429_;
}
else
{
lean_object* v_env_4550_; 
v_env_4550_ = lean_ctor_get(v___x_4548_, 0);
lean_inc_ref(v_env_4550_);
lean_dec(v___x_4548_);
v___y_4437_ = v_val_4543_;
v___y_4438_ = v___x_4503_;
v___y_4439_ = v___x_4523_;
v___y_4440_ = v___x_4502_;
v___y_4441_ = v___f_4545_;
v___y_4442_ = v___f_4544_;
v___y_4443_ = v_a_4497_;
v___y_4444_ = v_env_4550_;
v___y_4445_ = v_env_4547_;
goto v___jp_4436_;
}
}
}
case 0:
{
lean_object* v_val_4551_; lean_object* v_toConstantVal_4552_; lean_object* v_name_4553_; lean_object* v___x_4555_; 
lean_dec_ref(v___f_4527_);
v_val_4551_ = lean_ctor_get(v_decl_3908_, 0);
v_toConstantVal_4552_ = lean_ctor_get(v_val_4551_, 0);
v_name_4553_ = lean_ctor_get(v_toConstantVal_4552_, 0);
lean_inc_ref(v_val_4551_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v_val_4551_);
v___x_4555_ = v___x_4499_;
goto v_reusejp_4554_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_val_4551_);
v___x_4555_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4554_;
}
v_reusejp_4554_:
{
uint8_t v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; 
v___x_4556_ = 2;
v___x_4557_ = lean_box(v___x_4556_);
v___x_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4555_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
lean_inc(v_name_4553_);
v___x_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4559_, 0, v_name_4553_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
v___x_4560_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3908_, v_hasTrace_3968_, v___x_4502_, v___x_4519_, v___x_4102_, v_cls_4103_, v___x_4523_, v___x_4559_, v___x_4523_, v_a_3910_, v_a_3911_);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4560_;
goto v___jp_4363_;
}
}
default: 
{
lean_object* v___x_4562_; 
lean_dec_ref(v___f_4527_);
lean_del_object(v___x_4499_);
lean_inc(v_decl_3908_);
v___x_4562_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec(v_decl_3908_);
v___y_4364_ = v___x_4503_;
v___y_4365_ = v_a_4497_;
v___y_4366_ = v___x_4562_;
goto v___jp_4363_;
}
}
}
}
}
else
{
lean_object* v___x_4566_; lean_object* v___x_4567_; lean_object* v_env_4568_; lean_object* v_nextMacroScope_4569_; lean_object* v_ngen_4570_; lean_object* v_auxDeclNGen_4571_; lean_object* v_traceState_4572_; lean_object* v_recordedDeps_4573_; lean_object* v_messages_4574_; lean_object* v_infoState_4575_; lean_object* v_snapshotTasks_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4650_; 
v___x_4566_ = lean_io_get_num_heartbeats();
v___x_4567_ = lean_st_ref_take(v_a_3911_);
v_env_4568_ = lean_ctor_get(v___x_4567_, 0);
v_nextMacroScope_4569_ = lean_ctor_get(v___x_4567_, 1);
v_ngen_4570_ = lean_ctor_get(v___x_4567_, 2);
v_auxDeclNGen_4571_ = lean_ctor_get(v___x_4567_, 3);
v_traceState_4572_ = lean_ctor_get(v___x_4567_, 4);
v_recordedDeps_4573_ = lean_ctor_get(v___x_4567_, 6);
v_messages_4574_ = lean_ctor_get(v___x_4567_, 7);
v_infoState_4575_ = lean_ctor_get(v___x_4567_, 8);
v_snapshotTasks_4576_ = lean_ctor_get(v___x_4567_, 9);
v_isSharedCheck_4650_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4650_ == 0)
{
lean_object* v_unused_4651_; 
v_unused_4651_ = lean_ctor_get(v___x_4567_, 5);
lean_dec(v_unused_4651_);
v___x_4578_ = v___x_4567_;
v_isShared_4579_ = v_isSharedCheck_4650_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_snapshotTasks_4576_);
lean_inc(v_infoState_4575_);
lean_inc(v_messages_4574_);
lean_inc(v_recordedDeps_4573_);
lean_inc(v_traceState_4572_);
lean_inc(v_auxDeclNGen_4571_);
lean_inc(v_ngen_4570_);
lean_inc(v_nextMacroScope_4569_);
lean_inc(v_env_4568_);
lean_dec(v___x_4567_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4650_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
lean_inc(v_decl_3908_);
v___x_4580_ = l_Lean_Declaration_getNames(v_decl_3908_);
v___x_4581_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4568_, v___x_4580_);
v___x_4582_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 5, v___x_4582_);
lean_ctor_set(v___x_4578_, 0, v___x_4581_);
v___x_4584_ = v___x_4578_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4649_; 
v_reuseFailAlloc_4649_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4649_, 0, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4649_, 1, v_nextMacroScope_4569_);
lean_ctor_set(v_reuseFailAlloc_4649_, 2, v_ngen_4570_);
lean_ctor_set(v_reuseFailAlloc_4649_, 3, v_auxDeclNGen_4571_);
lean_ctor_set(v_reuseFailAlloc_4649_, 4, v_traceState_4572_);
lean_ctor_set(v_reuseFailAlloc_4649_, 5, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4649_, 6, v_recordedDeps_4573_);
lean_ctor_set(v_reuseFailAlloc_4649_, 7, v_messages_4574_);
lean_ctor_set(v_reuseFailAlloc_4649_, 8, v_infoState_4575_);
lean_ctor_set(v_reuseFailAlloc_4649_, 9, v_snapshotTasks_4576_);
v___x_4584_ = v_reuseFailAlloc_4649_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___f_4589_; 
v___x_4585_ = lean_st_ref_put(v_a_3911_, v___x_4584_);
v___x_4586_ = lean_box(0);
v___x_4587_ = lean_box(v___x_4502_);
v___x_4588_ = lean_box(v___x_4102_);
lean_inc(v_decl_3908_);
v___f_4589_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 11, 6);
lean_closure_set(v___f_4589_, 0, v_decl_3908_);
lean_closure_set(v___f_4589_, 1, v___x_4587_);
lean_closure_set(v___f_4589_, 2, v___x_4582_);
lean_closure_set(v___f_4589_, 3, v_cls_4103_);
lean_closure_set(v___f_4589_, 4, v___x_4588_);
lean_closure_set(v___f_4589_, 5, v___x_4586_);
switch(lean_obj_tag(v_decl_3908_))
{
case 2:
{
lean_object* v_val_4590_; lean_object* v___f_4591_; lean_object* v___x_4592_; 
lean_del_object(v___x_4499_);
v_val_4590_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref_n(v_val_4590_, 2);
lean_dec_ref_known(v_decl_3908_, 1);
v___f_4591_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4591_, 0, v_val_4590_);
lean_closure_set(v___f_4591_, 1, v___f_4589_);
v___x_4592_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
if (v___x_4502_ == 0)
{
lean_dec(v___x_4592_);
lean_dec_ref(v_val_4590_);
v___y_4482_ = v___f_4591_;
v___y_4483_ = v___x_4566_;
v___y_4484_ = v_a_4497_;
v___y_4485_ = v___x_4586_;
goto v___jp_4481_;
}
else
{
lean_object* v_env_4593_; lean_object* v___x_4594_; uint8_t v_isModule_4595_; 
v_env_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc_ref(v_env_4593_);
lean_dec(v___x_4592_);
v___x_4594_ = l_Lean_Environment_header(v_env_4593_);
lean_dec_ref(v_env_4593_);
v_isModule_4595_ = lean_ctor_get_uint8(v___x_4594_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4594_);
if (v_isModule_4595_ == 0)
{
lean_dec_ref(v_val_4590_);
v___y_4482_ = v___f_4591_;
v___y_4483_ = v___x_4566_;
v___y_4484_ = v_a_4497_;
v___y_4485_ = v___x_4586_;
goto v___jp_4481_;
}
else
{
if (v___x_4347_ == 0)
{
lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4596_ = lean_box(0);
v___x_4597_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4590_, v___f_4591_, v___x_4596_, v_a_3910_, v_a_3911_);
lean_dec_ref(v_val_4590_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4597_;
goto v___jp_4461_;
}
else
{
lean_object* v_toConstantVal_4598_; lean_object* v_name_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; 
v_toConstantVal_4598_ = lean_ctor_get(v_val_4590_, 0);
v_name_4599_ = lean_ctor_get(v_toConstantVal_4598_, 0);
v___x_4600_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4599_);
v___x_4601_ = l_Lean_MessageData_ofName(v_name_4599_);
v___x_4602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4602_, 0, v___x_4600_);
lean_ctor_set(v___x_4602_, 1, v___x_4601_);
v___x_4603_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4604_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4604_, 0, v___x_4602_);
lean_ctor_set(v___x_4604_, 1, v___x_4603_);
v___x_4605_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4604_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_4605_) == 0)
{
lean_object* v_a_4606_; lean_object* v___x_4607_; 
v_a_4606_ = lean_ctor_get(v___x_4605_, 0);
lean_inc(v_a_4606_);
lean_dec_ref_known(v___x_4605_, 1);
v___x_4607_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4590_, v___f_4591_, v_a_4606_, v_a_3910_, v_a_3911_);
lean_dec_ref(v_val_4590_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4607_;
goto v___jp_4461_;
}
else
{
lean_dec_ref(v___f_4591_);
lean_dec_ref(v_val_4590_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4605_;
goto v___jp_4461_;
}
}
}
}
}
else
{
lean_dec(v___x_4592_);
lean_dec_ref(v_val_4590_);
v___y_4482_ = v___f_4591_;
v___y_4483_ = v___x_4566_;
v___y_4484_ = v_a_4497_;
v___y_4485_ = v___x_4586_;
goto v___jp_4481_;
}
}
case 1:
{
lean_object* v_val_4608_; lean_object* v___x_4609_; 
lean_del_object(v___x_4499_);
v_val_4608_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref(v_val_4608_);
lean_dec_ref_known(v_decl_3908_, 1);
v___x_4609_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4589_, v_forceExpose_3909_, v___x_4502_, v___x_4586_, v_cls_4103_, v_val_4608_, v_a_3910_, v_a_3911_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4609_;
goto v___jp_4461_;
}
case 5:
{
lean_object* v_defns_4610_; 
lean_del_object(v___x_4499_);
v_defns_4610_ = lean_ctor_get(v_decl_3908_, 0);
if (lean_obj_tag(v_defns_4610_) == 1)
{
lean_object* v_tail_4611_; 
v_tail_4611_ = lean_ctor_get(v_defns_4610_, 1);
if (lean_obj_tag(v_tail_4611_) == 0)
{
lean_object* v_head_4612_; lean_object* v___x_4613_; 
lean_inc_ref(v_defns_4610_);
lean_dec_ref_known(v_decl_3908_, 1);
v_head_4612_ = lean_ctor_get(v_defns_4610_, 0);
lean_inc(v_head_4612_);
lean_dec_ref_known(v_defns_4610_, 2);
v___x_4613_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4589_, v_forceExpose_3909_, v___x_4502_, v___x_4586_, v_cls_4103_, v_head_4612_, v_a_3910_, v_a_3911_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4613_;
goto v___jp_4461_;
}
else
{
lean_object* v___x_4614_; 
lean_dec_ref(v___f_4589_);
lean_inc_ref(v_decl_3908_);
v___x_4614_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec_ref_known(v_decl_3908_, 1);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4614_;
goto v___jp_4461_;
}
}
else
{
lean_object* v___x_4615_; 
lean_dec_ref(v___f_4589_);
lean_inc_ref(v_decl_3908_);
v___x_4615_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec_ref_known(v_decl_3908_, 1);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4615_;
goto v___jp_4461_;
}
}
case 3:
{
lean_object* v_val_4616_; lean_object* v___f_4617_; lean_object* v___x_4618_; lean_object* v_env_4619_; lean_object* v___x_4620_; 
lean_del_object(v___x_4499_);
v_val_4616_ = lean_ctor_get(v_decl_3908_, 0);
lean_inc_ref_n(v_val_4616_, 2);
lean_dec_ref_known(v_decl_3908_, 1);
v___f_4617_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4617_, 0, v_val_4616_);
lean_closure_set(v___f_4617_, 1, v___f_4589_);
v___x_4618_ = lean_st_ref_get(v_a_3911_);
v_env_4619_ = lean_ctor_get(v___x_4618_, 0);
lean_inc_ref(v_env_4619_);
lean_dec(v___x_4618_);
v___x_4620_ = lean_st_ref_get(v_a_3911_);
if (v_forceExpose_3909_ == 0)
{
if (v___x_4502_ == 0)
{
lean_dec(v___x_4620_);
lean_dec_ref(v_env_4619_);
lean_dec_ref(v_val_4616_);
v___y_4489_ = v___x_4566_;
v___y_4490_ = v_a_4497_;
v___y_4491_ = v___f_4617_;
v___y_4492_ = v___x_4586_;
goto v___jp_4488_;
}
else
{
lean_object* v_env_4621_; lean_object* v___x_4622_; uint8_t v_isModule_4623_; 
v_env_4621_ = lean_ctor_get(v___x_4620_, 0);
lean_inc_ref(v_env_4621_);
lean_dec(v___x_4620_);
v___x_4622_ = l_Lean_Environment_header(v_env_4619_);
lean_dec_ref(v_env_4619_);
v_isModule_4623_ = lean_ctor_get_uint8(v___x_4622_, sizeof(void*)*8 + 4);
lean_dec_ref(v___x_4622_);
if (v_isModule_4623_ == 0)
{
lean_dec_ref(v_env_4621_);
lean_dec_ref(v_val_4616_);
v___y_4489_ = v___x_4566_;
v___y_4490_ = v_a_4497_;
v___y_4491_ = v___f_4617_;
v___y_4492_ = v___x_4586_;
goto v___jp_4488_;
}
else
{
uint8_t v_isExporting_4624_; 
v_isExporting_4624_ = lean_ctor_get_uint8(v_env_4621_, sizeof(void*)*13);
lean_dec_ref(v_env_4621_);
if (v_isExporting_4624_ == 0)
{
if (v___x_4347_ == 0)
{
lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4625_ = lean_box(0);
v___x_4626_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4616_, v___f_4617_, v___x_4625_, v_a_3910_, v_a_3911_);
lean_dec_ref(v_val_4616_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4626_;
goto v___jp_4461_;
}
else
{
lean_object* v_toConstantVal_4627_; lean_object* v_name_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4631_; lean_object* v___x_4632_; lean_object* v___x_4633_; lean_object* v___x_4634_; 
v_toConstantVal_4627_ = lean_ctor_get(v_val_4616_, 0);
v_name_4628_ = lean_ctor_get(v_toConstantVal_4627_, 0);
v___x_4629_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4628_);
v___x_4630_ = l_Lean_MessageData_ofName(v_name_4628_);
v___x_4631_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4631_, 0, v___x_4629_);
lean_ctor_set(v___x_4631_, 1, v___x_4630_);
v___x_4632_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4633_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4633_, 0, v___x_4631_);
lean_ctor_set(v___x_4633_, 1, v___x_4632_);
v___x_4634_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4633_, v_a_3910_, v_a_3911_);
if (lean_obj_tag(v___x_4634_) == 0)
{
lean_object* v_a_4635_; lean_object* v___x_4636_; 
v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
lean_inc(v_a_4635_);
lean_dec_ref_known(v___x_4634_, 1);
v___x_4636_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4616_, v___f_4617_, v_a_4635_, v_a_3910_, v_a_3911_);
lean_dec_ref(v_val_4616_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4636_;
goto v___jp_4461_;
}
else
{
lean_dec_ref(v___f_4617_);
lean_dec_ref(v_val_4616_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4634_;
goto v___jp_4461_;
}
}
}
else
{
lean_dec_ref(v_val_4616_);
v___y_4489_ = v___x_4566_;
v___y_4490_ = v_a_4497_;
v___y_4491_ = v___f_4617_;
v___y_4492_ = v___x_4586_;
goto v___jp_4488_;
}
}
}
}
else
{
lean_dec(v___x_4620_);
lean_dec_ref(v_env_4619_);
lean_dec_ref(v_val_4616_);
v___y_4489_ = v___x_4566_;
v___y_4490_ = v_a_4497_;
v___y_4491_ = v___f_4617_;
v___y_4492_ = v___x_4586_;
goto v___jp_4488_;
}
}
case 0:
{
lean_object* v_val_4637_; lean_object* v_toConstantVal_4638_; lean_object* v_name_4639_; lean_object* v___x_4641_; 
lean_dec_ref(v___f_4589_);
v_val_4637_ = lean_ctor_get(v_decl_3908_, 0);
v_toConstantVal_4638_ = lean_ctor_get(v_val_4637_, 0);
v_name_4639_ = lean_ctor_get(v_toConstantVal_4638_, 0);
lean_inc_ref(v_val_4637_);
if (v_isShared_4500_ == 0)
{
lean_ctor_set(v___x_4499_, 0, v_val_4637_);
v___x_4641_ = v___x_4499_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v_val_4637_);
v___x_4641_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
uint8_t v___x_4642_; lean_object* v___x_4643_; lean_object* v___x_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; 
v___x_4642_ = 2;
v___x_4643_ = lean_box(v___x_4642_);
v___x_4644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4644_, 0, v___x_4641_);
lean_ctor_set(v___x_4644_, 1, v___x_4643_);
lean_inc(v_name_4639_);
v___x_4645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4645_, 0, v_name_4639_);
lean_ctor_set(v___x_4645_, 1, v___x_4644_);
v___x_4646_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3908_, v___x_4502_, v___x_4582_, v_cls_4103_, v___x_4102_, v___x_4586_, v___x_4645_, v___x_4586_, v_a_3910_, v_a_3911_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4646_;
goto v___jp_4461_;
}
}
default: 
{
lean_object* v___x_4648_; 
lean_dec_ref(v___f_4589_);
lean_del_object(v___x_4499_);
lean_inc(v_decl_3908_);
v___x_4648_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3908_, v_cls_4103_, v_decl_3908_, v_a_3910_, v_a_3911_);
lean_dec(v_decl_3908_);
v___y_4462_ = v___x_4566_;
v___y_4463_ = v_a_4497_;
v___y_4464_ = v___x_4648_;
goto v___jp_4461_;
}
}
}
}
}
}
}
}
v___jp_3913_:
{
lean_object* v___x_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
v___x_3917_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3914_, v___y_3915_);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v___x_3917_, 0);
lean_dec(v_unused_3925_);
v___x_3919_ = v___x_3917_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_dec(v___x_3917_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v_a_3916_);
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3916_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
v___jp_3926_:
{
lean_object* v___x_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
v___x_3930_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3927_, v___y_3928_);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3930_);
if (v_isSharedCheck_3937_ == 0)
{
lean_object* v_unused_3938_; 
v_unused_3938_ = lean_ctor_get(v___x_3930_, 0);
lean_dec(v_unused_3938_);
v___x_3932_ = v___x_3930_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_dec(v___x_3930_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
lean_ctor_set_tag(v___x_3932_, 1);
lean_ctor_set(v___x_3932_, 0, v_a_3929_);
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3929_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
v___jp_3939_:
{
lean_object* v___x_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3950_; 
v___x_3943_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3941_, v___y_3940_);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v___x_3943_, 0);
lean_dec(v_unused_3951_);
v___x_3945_ = v___x_3943_;
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
else
{
lean_dec(v___x_3943_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3950_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
lean_object* v___x_3948_; 
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v_a_3942_);
v___x_3948_ = v___x_3945_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3942_);
v___x_3948_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
return v___x_3948_;
}
}
}
v___jp_3952_:
{
lean_object* v___x_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_3963_; 
v___x_3956_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3954_, v___y_3953_);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v___x_3956_, 0);
lean_dec(v_unused_3964_);
v___x_3958_ = v___x_3956_;
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
else
{
lean_dec(v___x_3956_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_3963_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3961_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set_tag(v___x_3958_, 1);
lean_ctor_set(v___x_3958_, 0, v_a_3955_);
v___x_3961_ = v___x_3958_;
goto v_reusejp_3960_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v_a_3955_);
v___x_3961_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3960_;
}
v_reusejp_3960_:
{
return v___x_3961_;
}
}
}
v___jp_3969_:
{
lean_object* v___x_3982_; 
lean_inc_ref(v___y_3978_);
v___x_3982_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3973_, v___y_3978_, v___y_3976_, v___y_3981_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v___x_3983_; lean_object* v___x_3985_; uint8_t v_isShared_3986_; uint8_t v_isSharedCheck_4029_; 
lean_dec_ref_known(v___x_3982_, 1);
lean_dec(v___y_3977_);
lean_inc_ref(v___y_3970_);
v___x_3983_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3970_, v___y_3979_);
v_isSharedCheck_4029_ = !lean_is_exclusive(v___x_3983_);
if (v_isSharedCheck_4029_ == 0)
{
lean_object* v_unused_4030_; 
v_unused_4030_ = lean_ctor_get(v___x_3983_, 0);
lean_dec(v_unused_4030_);
v___x_3985_ = v___x_3983_;
v_isShared_3986_ = v_isSharedCheck_4029_;
goto v_resetjp_3984_;
}
else
{
lean_dec(v___x_3983_);
v___x_3985_ = lean_box(0);
v_isShared_3986_ = v_isSharedCheck_4029_;
goto v_resetjp_3984_;
}
v_resetjp_3984_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___x_3989_; 
v___x_3987_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3972_);
v___x_3988_ = l_Lean_Elab_async;
v___x_3989_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3987_, v___x_3988_);
lean_dec_ref(v___x_3987_);
if (v___x_3989_ == 0)
{
lean_object* v___x_3990_; lean_object* v_r_3991_; 
lean_del_object(v___x_3985_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v___y_3971_);
v___x_3990_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3978_, v___y_3979_);
lean_dec_ref(v___x_3990_);
v_r_3991_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v___y_3972_, v___y_3979_);
if (lean_obj_tag(v_r_3991_) == 0)
{
lean_object* v_a_3992_; lean_object* v___x_3994_; uint8_t v_isShared_3995_; uint8_t v_isSharedCheck_4001_; 
v_a_3992_ = lean_ctor_get(v_r_3991_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_r_3991_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3994_ = v_r_3991_;
v_isShared_3995_ = v_isSharedCheck_4001_;
goto v_resetjp_3993_;
}
else
{
lean_inc(v_a_3992_);
lean_dec(v_r_3991_);
v___x_3994_ = lean_box(0);
v_isShared_3995_ = v_isSharedCheck_4001_;
goto v_resetjp_3993_;
}
v_resetjp_3993_:
{
lean_object* v___x_3997_; 
lean_inc(v_a_3992_);
if (v_isShared_3995_ == 0)
{
lean_ctor_set_tag(v___x_3994_, 1);
v___x_3997_ = v___x_3994_;
goto v_reusejp_3996_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3992_);
v___x_3997_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3996_;
}
v_reusejp_3996_:
{
lean_object* v___x_3998_; 
v___x_3998_ = lean_apply_2(v___y_3980_, v___x_3997_, lean_box(0));
if (lean_obj_tag(v___x_3998_) == 0)
{
lean_dec_ref_known(v___x_3998_, 1);
v___y_3914_ = v___y_3970_;
v___y_3915_ = v___y_3979_;
v_a_3916_ = v_a_3992_;
goto v___jp_3913_;
}
else
{
lean_object* v_a_3999_; 
lean_dec(v_a_3992_);
v_a_3999_ = lean_ctor_get(v___x_3998_, 0);
lean_inc(v_a_3999_);
lean_dec_ref_known(v___x_3998_, 1);
v___y_3927_ = v___y_3970_;
v___y_3928_ = v___y_3979_;
v_a_3929_ = v_a_3999_;
goto v___jp_3926_;
}
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v_a_4002_ = lean_ctor_get(v_r_3991_, 0);
lean_inc(v_a_4002_);
lean_dec_ref_known(v_r_3991_, 1);
v___x_4003_ = lean_box(0);
v___x_4004_ = lean_apply_2(v___y_3980_, v___x_4003_, lean_box(0));
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_dec_ref_known(v___x_4004_, 1);
v___y_3927_ = v___y_3970_;
v___y_3928_ = v___y_3979_;
v_a_3929_ = v_a_4002_;
goto v___jp_3926_;
}
else
{
lean_object* v_a_4005_; 
lean_dec(v_a_4002_);
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
v___y_3927_ = v___y_3970_;
v___y_3928_ = v___y_3979_;
v_a_3929_ = v_a_4005_;
goto v___jp_3926_;
}
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4008_; 
lean_dec_ref(v___y_3980_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3970_);
lean_dec(v_decl_3908_);
v___x_4006_ = l_IO_CancelToken_new();
if (v_isShared_3986_ == 0)
{
lean_ctor_set_tag(v___x_3985_, 1);
lean_ctor_set(v___x_3985_, 0, v___x_4006_);
v___x_4008_ = v___x_3985_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4028_; 
v_reuseFailAlloc_4028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4028_, 0, v___x_4006_);
v___x_4008_ = v_reuseFailAlloc_4028_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; lean_object* v___x_4012_; 
v___x_4009_ = lean_unsigned_to_nat(0u);
v___x_4010_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4011_ = l_Lean_Name_toString(v___x_4010_, v___y_3975_);
lean_inc_ref(v___x_4008_);
v___x_4012_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3971_, v___x_4008_, v___x_4011_, v___y_3972_, v___y_3979_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_checked_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
lean_dec_ref_known(v___x_4012_, 1);
v_checked_4014_ = lean_ctor_get(v___y_3974_, 2);
lean_inc_ref(v_checked_4014_);
lean_dec_ref(v___y_3974_);
v___x_4015_ = lean_io_map_task(v_a_4013_, v_checked_4014_, v___x_4009_, v_hasTrace_3968_);
v___x_4016_ = lean_box(0);
v___x_4017_ = lean_box(2);
v___x_4018_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4018_, 0, v___x_4016_);
lean_ctor_set(v___x_4018_, 1, v___x_4017_);
lean_ctor_set(v___x_4018_, 2, v___x_4008_);
lean_ctor_set(v___x_4018_, 3, v___x_4015_);
v___x_4019_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4018_, v___y_3979_);
return v___x_4019_;
}
else
{
lean_object* v_a_4020_; lean_object* v___x_4022_; uint8_t v_isShared_4023_; uint8_t v_isSharedCheck_4027_; 
lean_dec_ref(v___x_4008_);
lean_dec_ref(v___y_3974_);
v_a_4020_ = lean_ctor_get(v___x_4012_, 0);
v_isSharedCheck_4027_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4027_ == 0)
{
v___x_4022_ = v___x_4012_;
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
else
{
lean_inc(v_a_4020_);
lean_dec(v___x_4012_);
v___x_4022_ = lean_box(0);
v_isShared_4023_ = v_isSharedCheck_4027_;
goto v_resetjp_4021_;
}
v_resetjp_4021_:
{
lean_object* v___x_4025_; 
if (v_isShared_4023_ == 0)
{
v___x_4025_ = v___x_4022_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4020_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4042_; 
lean_dec_ref(v___y_3980_);
lean_dec_ref(v___y_3978_);
lean_dec_ref(v___y_3974_);
lean_dec_ref(v___y_3971_);
lean_dec_ref(v___y_3970_);
lean_dec(v_decl_3908_);
v_a_4031_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_4042_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_4042_ == 0)
{
v___x_4033_ = v___x_3982_;
v_isShared_4034_ = v_isSharedCheck_4042_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_3982_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4042_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
lean_object* v___x_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; lean_object* v___x_4040_; 
v___x_4035_ = lean_io_error_to_string(v_a_4031_);
v___x_4036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4036_, 0, v___x_4035_);
v___x_4037_ = l_Lean_MessageData_ofFormat(v___x_4036_);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___y_3977_);
lean_ctor_set(v___x_4038_, 1, v___x_4037_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set(v___x_4033_, 0, v___x_4038_);
v___x_4040_ = v___x_4033_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v___x_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
}
}
v___jp_4043_:
{
lean_object* v_ref_4052_; uint8_t v___x_4053_; lean_object* v___x_4054_; 
v_ref_4052_ = lean_ctor_get(v___y_4046_, 2);
v___x_4053_ = 1;
lean_inc_ref(v___y_4050_);
v___x_4054_ = l_Lean_Environment_addConstAsync(v___y_4050_, v___y_4044_, v___y_4045_, v___y_4051_, v_hasTrace_3968_, v___x_4053_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v_a_4055_; lean_object* v_mainEnv_4056_; lean_object* v_asyncEnv_4057_; lean_object* v___f_4058_; lean_object* v___f_4059_; lean_object* v___x_4060_; 
v_a_4055_ = lean_ctor_get(v___x_4054_, 0);
lean_inc_n(v_a_4055_, 3);
lean_dec_ref_known(v___x_4054_, 1);
v_mainEnv_4056_ = lean_ctor_get(v_a_4055_, 0);
lean_inc_ref(v_mainEnv_4056_);
v_asyncEnv_4057_ = lean_ctor_get(v_a_4055_, 1);
lean_inc_ref_n(v_asyncEnv_4057_, 2);
lean_inc(v_ref_4052_);
lean_inc(v___y_4049_);
v___f_4058_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4058_, 0, v___y_4049_);
lean_closure_set(v___f_4058_, 1, v_a_4055_);
lean_closure_set(v___f_4058_, 2, v_ref_4052_);
lean_inc(v_decl_3908_);
v___f_4059_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4059_, 0, v_a_4055_);
lean_closure_set(v___f_4059_, 1, v_asyncEnv_4057_);
lean_closure_set(v___f_4059_, 2, v_decl_3908_);
v___x_4060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4060_, 0, v___y_4048_);
if (lean_obj_tag(v___y_4047_) == 0)
{
lean_inc(v_ref_4052_);
lean_inc_ref(v___x_4060_);
v___y_3970_ = v_mainEnv_4056_;
v___y_3971_ = v___f_4059_;
v___y_3972_ = v___y_4046_;
v___y_3973_ = v_a_4055_;
v___y_3974_ = v___y_4050_;
v___y_3975_ = v___x_4053_;
v___y_3976_ = v___x_4060_;
v___y_3977_ = v_ref_4052_;
v___y_3978_ = v_asyncEnv_4057_;
v___y_3979_ = v___y_4049_;
v___y_3980_ = v___f_4058_;
v___y_3981_ = v___x_4060_;
goto v___jp_3969_;
}
else
{
lean_inc(v_ref_4052_);
v___y_3970_ = v_mainEnv_4056_;
v___y_3971_ = v___f_4059_;
v___y_3972_ = v___y_4046_;
v___y_3973_ = v_a_4055_;
v___y_3974_ = v___y_4050_;
v___y_3975_ = v___x_4053_;
v___y_3976_ = v___x_4060_;
v___y_3977_ = v_ref_4052_;
v___y_3978_ = v_asyncEnv_4057_;
v___y_3979_ = v___y_4049_;
v___y_3980_ = v___f_4058_;
v___y_3981_ = v___y_4047_;
goto v___jp_3969_;
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v___y_4050_);
lean_dec_ref(v___y_4048_);
lean_dec(v___y_4047_);
lean_dec(v_decl_3908_);
v_a_4061_ = lean_ctor_get(v___x_4054_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4063_ = v___x_4054_;
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4054_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4072_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
v___x_4065_ = lean_io_error_to_string(v_a_4061_);
v___x_4066_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
v___x_4067_ = l_Lean_MessageData_ofFormat(v___x_4066_);
lean_inc(v_ref_4052_);
v___x_4068_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4068_, 0, v_ref_4052_);
lean_ctor_set(v___x_4068_, 1, v___x_4067_);
if (v_isShared_4064_ == 0)
{
lean_ctor_set(v___x_4063_, 0, v___x_4068_);
v___x_4070_ = v___x_4063_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v___x_4068_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
v___jp_4073_:
{
lean_object* v___x_4080_; 
v___x_4080_ = lean_st_ref_get(v___y_4079_);
if (lean_obj_tag(v_exportedInfo_x3f_4077_) == 0)
{
lean_object* v_env_4081_; lean_object* v___x_4082_; 
v_env_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4080_);
v___x_4082_ = lean_box(0);
v___y_4044_ = v___y_4075_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4078_;
v___y_4047_ = v_exportedInfo_x3f_4077_;
v___y_4048_ = v___y_4076_;
v___y_4049_ = v___y_4079_;
v___y_4050_ = v_env_4081_;
v___y_4051_ = v___x_4082_;
goto v___jp_4043_;
}
else
{
lean_object* v_env_4083_; lean_object* v_val_4084_; uint8_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
v_env_4083_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4080_);
v_val_4084_ = lean_ctor_get(v_exportedInfo_x3f_4077_, 0);
v___x_4085_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4084_);
v___x_4086_ = lean_box(v___x_4085_);
v___x_4087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4087_, 0, v___x_4086_);
v___y_4044_ = v___y_4075_;
v___y_4045_ = v___y_4074_;
v___y_4046_ = v___y_4078_;
v___y_4047_ = v_exportedInfo_x3f_4077_;
v___y_4048_ = v___y_4076_;
v___y_4049_ = v___y_4079_;
v___y_4050_ = v_env_4083_;
v___y_4051_ = v___x_4087_;
goto v___jp_4043_;
}
}
v___jp_4088_:
{
lean_object* v___x_4094_; 
lean_inc_ref(v___y_4091_);
v___x_4094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4094_, 0, v___y_4091_);
v___y_4074_ = v___y_4089_;
v___y_4075_ = v___y_4090_;
v___y_4076_ = v___y_4091_;
v_exportedInfo_x3f_4077_ = v___x_4094_;
v___y_4078_ = v___y_4092_;
v___y_4079_ = v___y_4093_;
goto v___jp_4073_;
}
v___jp_4095_:
{
lean_object* v___x_4101_; 
lean_inc_ref(v___y_4098_);
v___x_4101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4101_, 0, v___y_4098_);
v___y_4074_ = v___y_4096_;
v___y_4075_ = v___y_4097_;
v___y_4076_ = v___y_4098_;
v_exportedInfo_x3f_4077_ = v___x_4101_;
v___y_4078_ = v___y_4099_;
v___y_4079_ = v___y_4100_;
goto v___jp_4073_;
}
v___jp_4104_:
{
lean_object* v___x_4109_; uint8_t v___x_4110_; 
v___x_4109_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4110_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4107_, v_options_4106_, v___x_4109_);
if (v___x_4110_ == 0)
{
lean_object* v___x_4111_; 
v___x_4111_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v___y_4105_, v___y_4108_);
return v___x_4111_;
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4113_; 
v___x_4112_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_4113_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_4103_, v___x_4112_, v___y_4105_, v___y_4108_);
if (lean_obj_tag(v___x_4113_) == 0)
{
lean_object* v___x_4114_; 
lean_dec_ref_known(v___x_4113_, 1);
v___x_4114_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3908_, v___y_4105_, v___y_4108_);
return v___x_4114_;
}
else
{
lean_dec(v_decl_3908_);
return v___x_4113_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_AddDecl_0__Lean_addDeclCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_3908_ = stack[0].m_obj;
uint8_t v_forceExpose_3909_ = stack[1].m_num;
lean_object* v_a_3910_ = stack[2].m_obj;
lean_object* v_a_3911_ = stack[3].m_obj;
lean_object* v_res_5045_;
v_res_5045_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_3908_, v_forceExpose_3909_, v_a_3910_, v_a_3911_);
stack->m_obj
 = v_res_5045_;
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_5046_, lean_object* v_forceExpose_5047_, lean_object* v_a_5048_, lean_object* v_a_5049_, lean_object* v_a_5050_){
_start:
{
uint8_t v_forceExpose_boxed_5051_; lean_object* v_res_5052_; 
v_forceExpose_boxed_5051_ = lean_unbox(v_forceExpose_5047_);
v_res_5052_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_5046_, v_forceExpose_boxed_5051_, v_a_5048_, v_a_5049_);
lean_dec(v_a_5049_);
lean_dec_ref(v_a_5048_);
return v_res_5052_;
}
}
lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_5053_, lean_object* v___y_5054_, lean_object* v___y_5055_){
_start:
{
lean_object* v___x_5057_; 
v___x_5057_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_5053_, v___y_5054_);
return v___x_5057_;
}
}
LEAN_EXPORT void l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_opt_5053_ = stack[0].m_obj;
lean_object* v___y_5054_ = stack[1].m_obj;
lean_object* v___y_5055_ = stack[2].m_obj;
lean_object* v_res_5058_;
v_res_5058_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_5053_, v___y_5054_, v___y_5055_);
stack->m_obj
 = v_res_5058_;
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_5059_, lean_object* v___y_5060_, lean_object* v___y_5061_, lean_object* v___y_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_5059_, v___y_5060_, v___y_5061_);
lean_dec(v___y_5061_);
lean_dec_ref(v___y_5060_);
lean_dec_ref(v_opt_5059_);
return v_res_5063_;
}
}
lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_5064_, lean_object* v_x_5065_, lean_object* v___y_5066_, lean_object* v___y_5067_){
_start:
{
if (lean_obj_tag(v_x_5064_) == 0)
{
lean_object* v___x_5069_; lean_object* v___x_5070_; 
v___x_5069_ = l_List_reverse___redArg(v_x_5065_);
v___x_5070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5070_, 0, v___x_5069_);
return v___x_5070_;
}
else
{
lean_object* v_head_5071_; lean_object* v_tail_5072_; lean_object* v___x_5074_; uint8_t v_isShared_5075_; uint8_t v_isSharedCheck_5090_; 
v_head_5071_ = lean_ctor_get(v_x_5064_, 0);
v_tail_5072_ = lean_ctor_get(v_x_5064_, 1);
v_isSharedCheck_5090_ = !lean_is_exclusive(v_x_5064_);
if (v_isSharedCheck_5090_ == 0)
{
v___x_5074_ = v_x_5064_;
v_isShared_5075_ = v_isSharedCheck_5090_;
goto v_resetjp_5073_;
}
else
{
lean_inc(v_tail_5072_);
lean_inc(v_head_5071_);
lean_dec(v_x_5064_);
v___x_5074_ = lean_box(0);
v_isShared_5075_ = v_isSharedCheck_5090_;
goto v_resetjp_5073_;
}
v_resetjp_5073_:
{
lean_object* v___x_5076_; 
v___x_5076_ = l_Lean_snapshotEnvLinterOptions(v_head_5071_, v___y_5066_, v___y_5067_);
if (lean_obj_tag(v___x_5076_) == 0)
{
lean_object* v_a_5077_; lean_object* v___x_5079_; 
v_a_5077_ = lean_ctor_get(v___x_5076_, 0);
lean_inc(v_a_5077_);
lean_dec_ref_known(v___x_5076_, 1);
if (v_isShared_5075_ == 0)
{
lean_ctor_set(v___x_5074_, 1, v_x_5065_);
lean_ctor_set(v___x_5074_, 0, v_a_5077_);
v___x_5079_ = v___x_5074_;
goto v_reusejp_5078_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5077_);
lean_ctor_set(v_reuseFailAlloc_5081_, 1, v_x_5065_);
v___x_5079_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5078_;
}
v_reusejp_5078_:
{
v_x_5064_ = v_tail_5072_;
v_x_5065_ = v___x_5079_;
goto _start;
}
}
else
{
lean_object* v_a_5082_; lean_object* v___x_5084_; uint8_t v_isShared_5085_; uint8_t v_isSharedCheck_5089_; 
lean_del_object(v___x_5074_);
lean_dec(v_tail_5072_);
lean_dec(v_x_5065_);
v_a_5082_ = lean_ctor_get(v___x_5076_, 0);
v_isSharedCheck_5089_ = !lean_is_exclusive(v___x_5076_);
if (v_isSharedCheck_5089_ == 0)
{
v___x_5084_ = v___x_5076_;
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
else
{
lean_inc(v_a_5082_);
lean_dec(v___x_5076_);
v___x_5084_ = lean_box(0);
v_isShared_5085_ = v_isSharedCheck_5089_;
goto v_resetjp_5083_;
}
v_resetjp_5083_:
{
lean_object* v___x_5087_; 
if (v_isShared_5085_ == 0)
{
v___x_5087_ = v___x_5084_;
goto v_reusejp_5086_;
}
else
{
lean_object* v_reuseFailAlloc_5088_; 
v_reuseFailAlloc_5088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5088_, 0, v_a_5082_);
v___x_5087_ = v_reuseFailAlloc_5088_;
goto v_reusejp_5086_;
}
v_reusejp_5086_:
{
return v___x_5087_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_List_mapM_loop___at___00Lean_addDecl_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_5064_ = stack[0].m_obj;
lean_object* v_x_5065_ = stack[1].m_obj;
lean_object* v___y_5066_ = stack[2].m_obj;
lean_object* v___y_5067_ = stack[3].m_obj;
lean_object* v_res_5091_;
v_res_5091_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_5064_, v_x_5065_, v___y_5066_, v___y_5067_);
stack->m_obj
 = v_res_5091_;
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_5092_, lean_object* v_x_5093_, lean_object* v___y_5094_, lean_object* v___y_5095_, lean_object* v___y_5096_){
_start:
{
lean_object* v_res_5097_; 
v_res_5097_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_5092_, v_x_5093_, v___y_5094_, v___y_5095_);
lean_dec(v___y_5095_);
lean_dec_ref(v___y_5094_);
return v_res_5097_;
}
}
lean_object* l_Lean_addDecl(lean_object* v_decl_5098_, uint8_t v_forceExpose_5099_, lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v___x_5103_; 
lean_inc(v_decl_5098_);
v___x_5103_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_5098_, v_forceExpose_5099_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5103_) == 0)
{
lean_object* v___x_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
lean_dec_ref_known(v___x_5103_, 1);
v___x_5104_ = l_Lean_Declaration_getTopLevelNames(v_decl_5098_);
v___x_5105_ = lean_box(0);
v___x_5106_ = lean_box(0);
v___x_5107_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_5104_, v___x_5105_, v_a_5100_, v_a_5101_);
if (lean_obj_tag(v___x_5107_) == 0)
{
lean_object* v___x_5109_; uint8_t v_isShared_5110_; uint8_t v_isSharedCheck_5114_; 
v_isSharedCheck_5114_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5114_ == 0)
{
lean_object* v_unused_5115_; 
v_unused_5115_ = lean_ctor_get(v___x_5107_, 0);
lean_dec(v_unused_5115_);
v___x_5109_ = v___x_5107_;
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
else
{
lean_dec(v___x_5107_);
v___x_5109_ = lean_box(0);
v_isShared_5110_ = v_isSharedCheck_5114_;
goto v_resetjp_5108_;
}
v_resetjp_5108_:
{
lean_object* v___x_5112_; 
if (v_isShared_5110_ == 0)
{
lean_ctor_set(v___x_5109_, 0, v___x_5106_);
v___x_5112_ = v___x_5109_;
goto v_reusejp_5111_;
}
else
{
lean_object* v_reuseFailAlloc_5113_; 
v_reuseFailAlloc_5113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5113_, 0, v___x_5106_);
v___x_5112_ = v_reuseFailAlloc_5113_;
goto v_reusejp_5111_;
}
v_reusejp_5111_:
{
return v___x_5112_;
}
}
}
else
{
lean_object* v_a_5116_; lean_object* v___x_5118_; uint8_t v_isShared_5119_; uint8_t v_isSharedCheck_5123_; 
v_a_5116_ = lean_ctor_get(v___x_5107_, 0);
v_isSharedCheck_5123_ = !lean_is_exclusive(v___x_5107_);
if (v_isSharedCheck_5123_ == 0)
{
v___x_5118_ = v___x_5107_;
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
else
{
lean_inc(v_a_5116_);
lean_dec(v___x_5107_);
v___x_5118_ = lean_box(0);
v_isShared_5119_ = v_isSharedCheck_5123_;
goto v_resetjp_5117_;
}
v_resetjp_5117_:
{
lean_object* v___x_5121_; 
if (v_isShared_5119_ == 0)
{
v___x_5121_ = v___x_5118_;
goto v_reusejp_5120_;
}
else
{
lean_object* v_reuseFailAlloc_5122_; 
v_reuseFailAlloc_5122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5122_, 0, v_a_5116_);
v___x_5121_ = v_reuseFailAlloc_5122_;
goto v_reusejp_5120_;
}
v_reusejp_5120_:
{
return v___x_5121_;
}
}
}
}
else
{
lean_dec(v_decl_5098_);
return v___x_5103_;
}
}
}
LEAN_EXPORT void l_Lean_addDecl_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_5098_ = stack[0].m_obj;
uint8_t v_forceExpose_5099_ = stack[1].m_num;
lean_object* v_a_5100_ = stack[2].m_obj;
lean_object* v_a_5101_ = stack[3].m_obj;
lean_object* v_res_5124_;
v_res_5124_ = l_Lean_addDecl(v_decl_5098_, v_forceExpose_5099_, v_a_5100_, v_a_5101_);
stack->m_obj
 = v_res_5124_;
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_5125_, lean_object* v_forceExpose_5126_, lean_object* v_a_5127_, lean_object* v_a_5128_, lean_object* v_a_5129_){
_start:
{
uint8_t v_forceExpose_boxed_5130_; lean_object* v_res_5131_; 
v_forceExpose_boxed_5130_ = lean_unbox(v_forceExpose_5126_);
v_res_5131_ = l_Lean_addDecl(v_decl_5125_, v_forceExpose_boxed_5130_, v_a_5127_, v_a_5128_);
lean_dec(v_a_5128_);
lean_dec_ref(v_a_5127_);
return v_res_5131_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_5132_, lean_object* v_b_5133_, lean_object* v___y_5134_){
_start:
{
if (lean_obj_tag(v_as_x27_5132_) == 0)
{
lean_object* v___x_5136_; 
v___x_5136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5136_, 0, v_b_5133_);
return v___x_5136_;
}
else
{
lean_object* v_head_5137_; lean_object* v_tail_5138_; lean_object* v___x_5139_; lean_object* v___x_5140_; lean_object* v_env_5141_; lean_object* v_nextMacroScope_5142_; lean_object* v_ngen_5143_; lean_object* v_auxDeclNGen_5144_; lean_object* v_traceState_5145_; lean_object* v_recordedDeps_5146_; lean_object* v_messages_5147_; lean_object* v_infoState_5148_; lean_object* v_snapshotTasks_5149_; lean_object* v___x_5151_; uint8_t v_isShared_5152_; uint8_t v_isSharedCheck_5160_; 
v_head_5137_ = lean_ctor_get(v_as_x27_5132_, 0);
v_tail_5138_ = lean_ctor_get(v_as_x27_5132_, 1);
v___x_5139_ = lean_box(0);
v___x_5140_ = lean_st_ref_take(v___y_5134_);
v_env_5141_ = lean_ctor_get(v___x_5140_, 0);
v_nextMacroScope_5142_ = lean_ctor_get(v___x_5140_, 1);
v_ngen_5143_ = lean_ctor_get(v___x_5140_, 2);
v_auxDeclNGen_5144_ = lean_ctor_get(v___x_5140_, 3);
v_traceState_5145_ = lean_ctor_get(v___x_5140_, 4);
v_recordedDeps_5146_ = lean_ctor_get(v___x_5140_, 6);
v_messages_5147_ = lean_ctor_get(v___x_5140_, 7);
v_infoState_5148_ = lean_ctor_get(v___x_5140_, 8);
v_snapshotTasks_5149_ = lean_ctor_get(v___x_5140_, 9);
v_isSharedCheck_5160_ = !lean_is_exclusive(v___x_5140_);
if (v_isSharedCheck_5160_ == 0)
{
lean_object* v_unused_5161_; 
v_unused_5161_ = lean_ctor_get(v___x_5140_, 5);
lean_dec(v_unused_5161_);
v___x_5151_ = v___x_5140_;
v_isShared_5152_ = v_isSharedCheck_5160_;
goto v_resetjp_5150_;
}
else
{
lean_inc(v_snapshotTasks_5149_);
lean_inc(v_infoState_5148_);
lean_inc(v_messages_5147_);
lean_inc(v_recordedDeps_5146_);
lean_inc(v_traceState_5145_);
lean_inc(v_auxDeclNGen_5144_);
lean_inc(v_ngen_5143_);
lean_inc(v_nextMacroScope_5142_);
lean_inc(v_env_5141_);
lean_dec(v___x_5140_);
v___x_5151_ = lean_box(0);
v_isShared_5152_ = v_isSharedCheck_5160_;
goto v_resetjp_5150_;
}
v_resetjp_5150_:
{
lean_object* v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5156_; 
lean_inc(v_head_5137_);
v___x_5153_ = l_Lean_markMeta(v_env_5141_, v_head_5137_);
v___x_5154_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_5152_ == 0)
{
lean_ctor_set(v___x_5151_, 5, v___x_5154_);
lean_ctor_set(v___x_5151_, 0, v___x_5153_);
v___x_5156_ = v___x_5151_;
goto v_reusejp_5155_;
}
else
{
lean_object* v_reuseFailAlloc_5159_; 
v_reuseFailAlloc_5159_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5159_, 0, v___x_5153_);
lean_ctor_set(v_reuseFailAlloc_5159_, 1, v_nextMacroScope_5142_);
lean_ctor_set(v_reuseFailAlloc_5159_, 2, v_ngen_5143_);
lean_ctor_set(v_reuseFailAlloc_5159_, 3, v_auxDeclNGen_5144_);
lean_ctor_set(v_reuseFailAlloc_5159_, 4, v_traceState_5145_);
lean_ctor_set(v_reuseFailAlloc_5159_, 5, v___x_5154_);
lean_ctor_set(v_reuseFailAlloc_5159_, 6, v_recordedDeps_5146_);
lean_ctor_set(v_reuseFailAlloc_5159_, 7, v_messages_5147_);
lean_ctor_set(v_reuseFailAlloc_5159_, 8, v_infoState_5148_);
lean_ctor_set(v_reuseFailAlloc_5159_, 9, v_snapshotTasks_5149_);
v___x_5156_ = v_reuseFailAlloc_5159_;
goto v_reusejp_5155_;
}
v_reusejp_5155_:
{
lean_object* v___x_5157_; 
v___x_5157_ = lean_st_ref_put(v___y_5134_, v___x_5156_);
v_as_x27_5132_ = v_tail_5138_;
v_b_5133_ = v___x_5139_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_x27_5132_ = stack[0].m_obj;
lean_object* v_b_5133_ = stack[1].m_obj;
lean_object* v___y_5134_ = stack[2].m_obj;
lean_object* v_res_5162_;
v_res_5162_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5132_, v_b_5133_, v___y_5134_);
stack->m_obj
 = v_res_5162_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_5163_, lean_object* v_b_5164_, lean_object* v___y_5165_, lean_object* v___y_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5163_, v_b_5164_, v___y_5165_);
lean_dec(v___y_5165_);
lean_dec(v_as_x27_5163_);
return v_res_5167_;
}
}
lean_object* l_Lean_addAndCompile(lean_object* v_decl_5168_, uint8_t v_logCompileErrors_5169_, uint8_t v_markMeta_5170_, lean_object* v_a_5171_, lean_object* v_a_5172_){
_start:
{
uint8_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = 0;
lean_inc(v_decl_5168_);
v___x_5175_ = l_Lean_addDecl(v_decl_5168_, v___x_5174_, v_a_5171_, v_a_5172_);
if (lean_obj_tag(v___x_5175_) == 0)
{
lean_dec_ref_known(v___x_5175_, 1);
if (v_markMeta_5170_ == 0)
{
lean_object* v___x_5176_; 
v___x_5176_ = l_Lean_compileDecl(v_decl_5168_, v_logCompileErrors_5169_, v_a_5171_, v_a_5172_);
return v___x_5176_;
}
else
{
lean_object* v___x_5177_; lean_object* v___x_5178_; lean_object* v___x_5179_; lean_object* v___x_5180_; 
lean_inc(v_decl_5168_);
v___x_5177_ = l_Lean_Declaration_getNames(v_decl_5168_);
v___x_5178_ = lean_box(0);
v___x_5179_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5177_, v___x_5178_, v_a_5172_);
lean_dec(v___x_5177_);
lean_dec_ref(v___x_5179_);
v___x_5180_ = l_Lean_compileDecl(v_decl_5168_, v_logCompileErrors_5169_, v_a_5171_, v_a_5172_);
return v___x_5180_;
}
}
else
{
lean_dec(v_decl_5168_);
return v___x_5175_;
}
}
}
LEAN_EXPORT void l_Lean_addAndCompile_0interp(lean_interpreter_value* stack)
{
lean_object* v_decl_5168_ = stack[0].m_obj;
uint8_t v_logCompileErrors_5169_ = stack[1].m_num;
uint8_t v_markMeta_5170_ = stack[2].m_num;
lean_object* v_a_5171_ = stack[3].m_obj;
lean_object* v_a_5172_ = stack[4].m_obj;
lean_object* v_res_5181_;
v_res_5181_ = l_Lean_addAndCompile(v_decl_5168_, v_logCompileErrors_5169_, v_markMeta_5170_, v_a_5171_, v_a_5172_);
stack->m_obj
 = v_res_5181_;
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5182_, lean_object* v_logCompileErrors_5183_, lean_object* v_markMeta_5184_, lean_object* v_a_5185_, lean_object* v_a_5186_, lean_object* v_a_5187_){
_start:
{
uint8_t v_logCompileErrors_boxed_5188_; uint8_t v_markMeta_boxed_5189_; lean_object* v_res_5190_; 
v_logCompileErrors_boxed_5188_ = lean_unbox(v_logCompileErrors_5183_);
v_markMeta_boxed_5189_ = lean_unbox(v_markMeta_5184_);
v_res_5190_ = l_Lean_addAndCompile(v_decl_5182_, v_logCompileErrors_boxed_5188_, v_markMeta_boxed_5189_, v_a_5185_, v_a_5186_);
lean_dec(v_a_5186_);
lean_dec_ref(v_a_5185_);
return v_res_5190_;
}
}
lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5191_, lean_object* v_as_x27_5192_, lean_object* v_b_5193_, lean_object* v_a_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v___x_5198_; 
v___x_5198_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5192_, v_b_5193_, v___y_5196_);
return v___x_5198_;
}
}
LEAN_EXPORT void l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_5191_ = stack[0].m_obj;
lean_object* v_as_x27_5192_ = stack[1].m_obj;
lean_object* v_b_5193_ = stack[2].m_obj;
lean_object* v___y_5195_ = stack[4].m_obj;
lean_object* v___y_5196_ = stack[5].m_obj;
lean_object* v_res_5199_;
v_res_5199_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5191_, v_as_x27_5192_, v_b_5193_, lean_box(0), v___y_5195_, v___y_5196_);
stack->m_obj
 = v_res_5199_;
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5200_, lean_object* v_as_x27_5201_, lean_object* v_b_5202_, lean_object* v_a_5203_, lean_object* v___y_5204_, lean_object* v___y_5205_, lean_object* v___y_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5200_, v_as_x27_5201_, v_b_5202_, v_a_5203_, v___y_5204_, v___y_5205_);
lean_dec(v___y_5205_);
lean_dec_ref(v___y_5204_);
lean_dec(v_as_x27_5201_);
lean_dec(v_as_5200_);
return v_res_5207_;
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
