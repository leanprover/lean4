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
v___x_170_ = lean_st_ref_set(v_a_130_, v___x_169_);
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
v___x_363_ = lean_st_ref_set(v___y_346_, v___x_362_);
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
uint8_t v___y_15938__boxed_416_; uint8_t v_suppressElabErrors_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v___y_15938__boxed_416_ = lean_unbox(v___y_413_);
v_suppressElabErrors_boxed_417_ = lean_unbox(v_suppressElabErrors_414_);
v_res_418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15938__boxed_416_, v_suppressElabErrors_boxed_417_, v_x_415_);
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
v___x_425_ = lean_alloc_ctor(0, 10, 0);
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
lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; uint8_t v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; lean_object* v___y_526_; lean_object* v___y_527_; uint8_t v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; lean_object* v___y_541_; uint8_t v___y_542_; uint8_t v___y_543_; uint8_t v___x_548_; lean_object* v___y_550_; uint8_t v___y_551_; lean_object* v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; uint8_t v___y_556_; uint8_t v___y_558_; uint8_t v___x_573_; 
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
lean_ctor_set(v___x_490_, 1, v___y_471_);
lean_inc_ref(v___y_465_);
lean_inc_ref(v___y_470_);
v___x_491_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_491_, 0, v___y_470_);
lean_ctor_set(v___x_491_, 1, v___y_467_);
lean_ctor_set(v___x_491_, 2, v___y_466_);
lean_ctor_set(v___x_491_, 3, v___y_465_);
lean_ctor_set(v___x_491_, 4, v___x_490_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5, v___y_469_);
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
v___x_495_ = lean_st_ref_set(v___y_473_, v___x_494_);
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
lean_inc_ref_n(v___y_502_, 2);
v___x_515_ = l_Lean_FileMap_toPosition(v___y_502_, v___y_504_);
lean_dec(v___y_504_);
v___x_516_ = l_Lean_FileMap_toPosition(v___y_502_, v___y_508_);
lean_dec(v___y_508_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_518_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_503_ == 0)
{
lean_del_object(v___x_513_);
lean_dec_ref(v___y_501_);
v___y_465_ = v___x_518_;
v___y_466_ = v___x_517_;
v___y_467_ = v___x_515_;
v___y_468_ = v___y_505_;
v___y_469_ = v___y_507_;
v___y_470_ = v___y_506_;
v___y_471_ = v_a_511_;
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
v___y_465_ = v___x_518_;
v___y_466_ = v___x_517_;
v___y_467_ = v___x_515_;
v___y_468_ = v___y_505_;
v___y_469_ = v___y_507_;
v___y_470_ = v___y_506_;
v___y_471_ = v_a_511_;
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
v___x_534_ = l_Lean_Syntax_getTailPos_x3f(v___y_529_, v___y_531_);
lean_dec(v___y_529_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_inc(v___y_533_);
v___y_501_ = v___y_526_;
v___y_502_ = v___y_527_;
v___y_503_ = v___y_528_;
v___y_504_ = v___y_533_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_532_;
v___y_507_ = v___y_531_;
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
v___y_504_ = v___y_533_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_532_;
v___y_507_ = v___y_531_;
v___y_508_ = v_val_535_;
goto v___jp_500_;
}
}
v___jp_536_:
{
lean_object* v_ref_544_; lean_object* v___x_545_; 
v_ref_544_ = l_Lean_replaceRef(v_ref_457_, v___y_540_);
v___x_545_ = l_Lean_Syntax_getPos_x3f(v_ref_544_, v___y_542_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___y_526_ = v___y_537_;
v___y_527_ = v___y_538_;
v___y_528_ = v___y_539_;
v___y_529_ = v_ref_544_;
v___y_530_ = v___y_543_;
v___y_531_ = v___y_542_;
v___y_532_ = v___y_541_;
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
v___y_528_ = v___y_539_;
v___y_529_ = v_ref_544_;
v___y_530_ = v___y_543_;
v___y_531_ = v___y_542_;
v___y_532_ = v___y_541_;
v___y_533_ = v_val_547_;
goto v___jp_525_;
}
}
v___jp_549_:
{
if (v___y_556_ == 0)
{
v___y_537_ = v___y_553_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_554_;
v___y_542_ = v___y_555_;
v___y_543_ = v_severity_459_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___y_553_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___y_554_;
v___y_542_ = v___y_555_;
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
v___y_550_ = v_fileMap_560_;
v___y_551_ = v_suppressElabErrors_563_;
v___y_552_ = v_ref_562_;
v___y_553_ = v___f_566_;
v___y_554_ = v_fileName_559_;
v___y_555_ = v___y_558_;
v___y_556_ = v___x_568_;
goto v___jp_549_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = l_Lean_warningAsError;
v___x_570_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_561_, v___x_569_);
v___y_550_ = v_fileMap_560_;
v___y_551_ = v_suppressElabErrors_563_;
v___y_552_ = v_ref_562_;
v___y_553_ = v___f_566_;
v___y_554_ = v_fileName_559_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_617_, size_t v_sz_618_, size_t v_i_619_, lean_object* v_b_620_){
_start:
{
uint8_t v___x_621_; 
v___x_621_ = lean_usize_dec_lt(v_i_619_, v_sz_618_);
if (v___x_621_ == 0)
{
lean_inc_ref(v_b_620_);
return v_b_620_;
}
else
{
lean_object* v_a_622_; lean_object* v_fst_623_; lean_object* v___x_624_; uint8_t v___x_625_; 
v_a_622_ = lean_array_uget_borrowed(v_as_617_, v_i_619_);
v_fst_623_ = lean_ctor_get(v_a_622_, 0);
v___x_624_ = lean_box(0);
v___x_625_ = lean_unbox(v_fst_623_);
if (v___x_625_ == 0)
{
lean_object* v___x_626_; size_t v___x_627_; size_t v___x_628_; 
v___x_626_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_627_ = ((size_t)1ULL);
v___x_628_ = lean_usize_add(v_i_619_, v___x_627_);
v_i_619_ = v___x_628_;
v_b_620_ = v___x_626_;
goto _start;
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_inc(v_a_622_);
v___x_630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_630_, 0, v_a_622_);
v___x_631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
v___x_632_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
lean_ctor_set(v___x_632_, 1, v___x_624_);
return v___x_632_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_633_, lean_object* v_sz_634_, lean_object* v_i_635_, lean_object* v_b_636_){
_start:
{
size_t v_sz_boxed_637_; size_t v_i_boxed_638_; lean_object* v_res_639_; 
v_sz_boxed_637_ = lean_unbox_usize(v_sz_634_);
lean_dec(v_sz_634_);
v_i_boxed_638_ = lean_unbox_usize(v_i_635_);
lean_dec(v_i_635_);
v_res_639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_633_, v_sz_boxed_637_, v_i_boxed_638_, v_b_636_);
lean_dec_ref(v_b_636_);
lean_dec_ref(v_as_633_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_640_, lean_object* v_e_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; 
v___x_648_ = l_Lean_Expr_getSorry_x3f(v_e_641_);
if (lean_obj_tag(v___x_648_) == 1)
{
lean_object* v_val_649_; lean_object* v___x_650_; 
v_val_649_ = lean_ctor_get(v___x_648_, 0);
lean_inc(v_val_649_);
lean_dec_ref_known(v___x_648_, 1);
lean_inc(v___y_646_);
lean_inc_ref(v___y_645_);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
v___x_650_ = lean_apply_7(v_fn_640_, v_val_649_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, lean_box(0));
if (lean_obj_tag(v___x_650_) == 0)
{
lean_object* v___x_652_; uint8_t v_isShared_653_; uint8_t v_isSharedCheck_659_; 
v_isSharedCheck_659_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_659_ == 0)
{
lean_object* v_unused_660_; 
v_unused_660_ = lean_ctor_get(v___x_650_, 0);
lean_dec(v_unused_660_);
v___x_652_ = v___x_650_;
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
else
{
lean_dec(v___x_650_);
v___x_652_ = lean_box(0);
v_isShared_653_ = v_isSharedCheck_659_;
goto v_resetjp_651_;
}
v_resetjp_651_:
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_657_; 
v___x_654_ = 0;
v___x_655_ = lean_box(v___x_654_);
if (v_isShared_653_ == 0)
{
lean_ctor_set(v___x_652_, 0, v___x_655_);
v___x_657_ = v___x_652_;
goto v_reusejp_656_;
}
else
{
lean_object* v_reuseFailAlloc_658_; 
v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
v___x_657_ = v_reuseFailAlloc_658_;
goto v_reusejp_656_;
}
v_reusejp_656_:
{
return v___x_657_;
}
}
}
else
{
lean_object* v_a_661_; lean_object* v___x_663_; uint8_t v_isShared_664_; uint8_t v_isSharedCheck_668_; 
v_a_661_ = lean_ctor_get(v___x_650_, 0);
v_isSharedCheck_668_ = !lean_is_exclusive(v___x_650_);
if (v_isSharedCheck_668_ == 0)
{
v___x_663_ = v___x_650_;
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
else
{
lean_inc(v_a_661_);
lean_dec(v___x_650_);
v___x_663_ = lean_box(0);
v_isShared_664_ = v_isSharedCheck_668_;
goto v_resetjp_662_;
}
v_resetjp_662_:
{
lean_object* v___x_666_; 
if (v_isShared_664_ == 0)
{
v___x_666_ = v___x_663_;
goto v_reusejp_665_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v_a_661_);
v___x_666_ = v_reuseFailAlloc_667_;
goto v_reusejp_665_;
}
v_reusejp_665_:
{
return v___x_666_;
}
}
}
}
else
{
uint8_t v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
lean_dec(v___x_648_);
lean_dec_ref(v_fn_640_);
v___x_669_ = 1;
v___x_670_ = lean_box(v___x_669_);
v___x_671_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_672_, lean_object* v_e_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_672_, v_e_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v_e_673_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_681_, lean_object* v_x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = lean_apply_1(v_x_682_, lean_box(0));
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
return v___x_690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_691_, lean_object* v_x_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_res_699_; 
v_res_699_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_691_, v_x_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_);
lean_dec(v___y_697_);
lean_dec_ref(v___y_696_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
return v_res_699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v_b_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v___x_709_; 
lean_inc(v___y_707_);
lean_inc_ref(v___y_706_);
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_702_);
lean_inc(v___y_701_);
v___x_709_ = lean_apply_8(v_k_700_, v_b_703_, v___y_701_, v___y_702_, v___y_704_, v___y_705_, v___y_706_, v___y_707_, lean_box(0));
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v_b_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_710_, v___y_711_, v___y_712_, v_b_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_712_);
lean_dec(v___y_711_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_720_, lean_object* v_type_721_, lean_object* v_val_722_, lean_object* v_k_723_, uint8_t v_nondep_724_, uint8_t v_kind_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_){
_start:
{
lean_object* v___f_733_; lean_object* v___x_734_; 
lean_inc(v___y_727_);
lean_inc(v___y_726_);
v___f_733_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_733_, 0, v_k_723_);
lean_closure_set(v___f_733_, 1, v___y_726_);
lean_closure_set(v___f_733_, 2, v___y_727_);
v___x_734_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_720_, v_type_721_, v_val_722_, v___f_733_, v_nondep_724_, v_kind_725_, v___y_728_, v___y_729_, v___y_730_, v___y_731_);
if (lean_obj_tag(v___x_734_) == 0)
{
return v___x_734_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_743_, lean_object* v_type_744_, lean_object* v_val_745_, lean_object* v_k_746_, lean_object* v_nondep_747_, lean_object* v_kind_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
uint8_t v_nondep_boxed_756_; uint8_t v_kind_boxed_757_; lean_object* v_res_758_; 
v_nondep_boxed_756_ = lean_unbox(v_nondep_747_);
v_kind_boxed_757_ = lean_unbox(v_kind_748_);
v_res_758_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_743_, v_type_744_, v_val_745_, v_k_746_, v_nondep_boxed_756_, v_kind_boxed_757_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
lean_dec(v___y_754_);
lean_dec_ref(v___y_753_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_749_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_759_, lean_object* v_f_760_, lean_object* v_body_761_, lean_object* v_x_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_759_, v_f_760_, v_body_761_, v_x_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec(v___y_763_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_771_, lean_object* v_fvars_772_, lean_object* v_a_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_){
_start:
{
if (lean_obj_tag(v_a_773_) == 8)
{
lean_object* v_declName_781_; lean_object* v_type_782_; lean_object* v_value_783_; lean_object* v_body_784_; lean_object* v_d_785_; lean_object* v___x_786_; 
v_declName_781_ = lean_ctor_get(v_a_773_, 0);
lean_inc(v_declName_781_);
v_type_782_ = lean_ctor_get(v_a_773_, 1);
lean_inc_ref(v_type_782_);
v_value_783_ = lean_ctor_get(v_a_773_, 2);
lean_inc_ref(v_value_783_);
v_body_784_ = lean_ctor_get(v_a_773_, 3);
lean_inc_ref(v_body_784_);
lean_dec_ref_known(v_a_773_, 4);
v_d_785_ = lean_expr_instantiate_rev(v_type_782_, v_fvars_772_);
lean_dec_ref(v_type_782_);
lean_inc_ref(v_f_771_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v_d_785_);
v___x_786_ = lean_apply_8(v_f_771_, v_d_785_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_v_787_; lean_object* v___x_788_; 
lean_dec_ref_known(v___x_786_, 1);
v_v_787_ = lean_expr_instantiate_rev(v_value_783_, v_fvars_772_);
lean_dec_ref(v_value_783_);
lean_inc_ref(v_f_771_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v_v_787_);
v___x_788_ = lean_apply_8(v_f_771_, v_v_787_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
if (lean_obj_tag(v___x_788_) == 0)
{
lean_object* v___f_789_; uint8_t v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; 
lean_dec_ref_known(v___x_788_, 1);
v___f_789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_789_, 0, v_fvars_772_);
lean_closure_set(v___f_789_, 1, v_f_771_);
lean_closure_set(v___f_789_, 2, v_body_784_);
v___x_790_ = 0;
v___x_791_ = 0;
v___x_792_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_781_, v_d_785_, v_v_787_, v___f_789_, v___x_790_, v___x_791_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
return v___x_792_;
}
else
{
lean_dec_ref(v_v_787_);
lean_dec_ref(v_d_785_);
lean_dec_ref(v_body_784_);
lean_dec(v_declName_781_);
lean_dec_ref(v_fvars_772_);
lean_dec_ref(v_f_771_);
return v___x_788_;
}
}
else
{
lean_dec_ref(v_d_785_);
lean_dec_ref(v_body_784_);
lean_dec_ref(v_value_783_);
lean_dec(v_declName_781_);
lean_dec_ref(v_fvars_772_);
lean_dec_ref(v_f_771_);
return v___x_786_;
}
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_793_ = lean_expr_instantiate_rev(v_a_773_, v_fvars_772_);
lean_dec_ref(v_fvars_772_);
lean_dec_ref(v_a_773_);
lean_inc(v___y_779_);
lean_inc_ref(v___y_778_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc(v___y_774_);
v___x_794_ = lean_apply_8(v_f_771_, v___x_793_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, lean_box(0));
return v___x_794_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_795_, lean_object* v_f_796_, lean_object* v_body_797_, lean_object* v_x_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_806_ = lean_array_push(v_fvars_795_, v_x_798_);
v___x_807_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_796_, v___x_806_, v_body_797_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_808_, lean_object* v_fvars_809_, lean_object* v_a_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_808_, v_fvars_809_, v_a_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
lean_dec(v___y_816_);
lean_dec_ref(v___y_815_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec(v___y_811_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_821_, lean_object* v_e_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_830_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_831_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_821_, v___x_830_, v_e_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_832_, lean_object* v_e_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_832_, v_e_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec(v___y_834_);
return v_res_841_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_842_, uint8_t v_bi_843_, lean_object* v_type_844_, lean_object* v_k_845_, uint8_t v_kind_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v___f_854_; lean_object* v___x_855_; 
lean_inc(v___y_848_);
lean_inc(v___y_847_);
v___f_854_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_854_, 0, v_k_845_);
lean_closure_set(v___f_854_, 1, v___y_847_);
lean_closure_set(v___f_854_, 2, v___y_848_);
v___x_855_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_842_, v_bi_843_, v_type_844_, v___f_854_, v_kind_846_, v___y_849_, v___y_850_, v___y_851_, v___y_852_);
if (lean_obj_tag(v___x_855_) == 0)
{
return v___x_855_;
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_855_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_855_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_864_, lean_object* v_bi_865_, lean_object* v_type_866_, lean_object* v_k_867_, lean_object* v_kind_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v_bi_boxed_876_; uint8_t v_kind_boxed_877_; lean_object* v_res_878_; 
v_bi_boxed_876_ = lean_unbox(v_bi_865_);
v_kind_boxed_877_ = lean_unbox(v_kind_868_);
v_res_878_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_864_, v_bi_boxed_876_, v_type_866_, v_k_867_, v_kind_boxed_877_, v___y_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v___y_869_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_879_, lean_object* v_f_880_, lean_object* v_body_881_, lean_object* v_x_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_){
_start:
{
lean_object* v_res_890_; 
v_res_890_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_879_, v_f_880_, v_body_881_, v_x_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_);
lean_dec(v___y_888_);
lean_dec_ref(v___y_887_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_891_, lean_object* v_fvars_892_, lean_object* v_a_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_){
_start:
{
if (lean_obj_tag(v_a_893_) == 7)
{
lean_object* v_binderName_901_; lean_object* v_binderType_902_; lean_object* v_body_903_; uint8_t v_binderInfo_904_; lean_object* v_d_905_; lean_object* v___x_906_; 
v_binderName_901_ = lean_ctor_get(v_a_893_, 0);
lean_inc(v_binderName_901_);
v_binderType_902_ = lean_ctor_get(v_a_893_, 1);
lean_inc_ref(v_binderType_902_);
v_body_903_ = lean_ctor_get(v_a_893_, 2);
lean_inc_ref(v_body_903_);
v_binderInfo_904_ = lean_ctor_get_uint8(v_a_893_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_893_, 3);
v_d_905_ = lean_expr_instantiate_rev(v_binderType_902_, v_fvars_892_);
lean_dec_ref(v_binderType_902_);
lean_inc_ref(v_f_891_);
lean_inc(v___y_899_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v_d_905_);
v___x_906_ = lean_apply_8(v_f_891_, v_d_905_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, lean_box(0));
if (lean_obj_tag(v___x_906_) == 0)
{
lean_object* v___f_907_; uint8_t v___x_908_; lean_object* v___x_909_; 
lean_dec_ref_known(v___x_906_, 1);
v___f_907_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_907_, 0, v_fvars_892_);
lean_closure_set(v___f_907_, 1, v_f_891_);
lean_closure_set(v___f_907_, 2, v_body_903_);
v___x_908_ = 0;
v___x_909_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_901_, v_binderInfo_904_, v_d_905_, v___f_907_, v___x_908_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_);
return v___x_909_;
}
else
{
lean_dec_ref(v_d_905_);
lean_dec_ref(v_body_903_);
lean_dec(v_binderName_901_);
lean_dec_ref(v_fvars_892_);
lean_dec_ref(v_f_891_);
return v___x_906_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_910_ = lean_expr_instantiate_rev(v_a_893_, v_fvars_892_);
lean_dec_ref(v_fvars_892_);
lean_dec_ref(v_a_893_);
lean_inc(v___y_899_);
lean_inc_ref(v___y_898_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc(v___y_894_);
v___x_911_ = lean_apply_8(v_f_891_, v___x_910_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, lean_box(0));
return v___x_911_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_912_, lean_object* v_f_913_, lean_object* v_body_914_, lean_object* v_x_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_923_ = lean_array_push(v_fvars_912_, v_x_915_);
v___x_924_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_913_, v___x_923_, v_body_914_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_);
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_925_, lean_object* v_fvars_926_, lean_object* v_a_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_res_935_; 
v_res_935_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_925_, v_fvars_926_, v_a_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
lean_dec(v___y_933_);
lean_dec_ref(v___y_932_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec(v___y_928_);
return v_res_935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_936_, lean_object* v_e_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_){
_start:
{
lean_object* v___x_945_; lean_object* v___x_946_; 
v___x_945_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_946_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_936_, v___x_945_, v_e_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_947_, lean_object* v_e_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_947_, v_e_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec(v___y_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_957_, lean_object* v_f_958_, lean_object* v_body_959_, lean_object* v_x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_957_, v_f_958_, v_body_959_, v_x_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_969_, lean_object* v_fvars_970_, lean_object* v_a_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_){
_start:
{
if (lean_obj_tag(v_a_971_) == 6)
{
lean_object* v_binderName_979_; lean_object* v_binderType_980_; lean_object* v_body_981_; uint8_t v_binderInfo_982_; lean_object* v_d_983_; lean_object* v___x_984_; 
v_binderName_979_ = lean_ctor_get(v_a_971_, 0);
lean_inc(v_binderName_979_);
v_binderType_980_ = lean_ctor_get(v_a_971_, 1);
lean_inc_ref(v_binderType_980_);
v_body_981_ = lean_ctor_get(v_a_971_, 2);
lean_inc_ref(v_body_981_);
v_binderInfo_982_ = lean_ctor_get_uint8(v_a_971_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_971_, 3);
v_d_983_ = lean_expr_instantiate_rev(v_binderType_980_, v_fvars_970_);
lean_dec_ref(v_binderType_980_);
lean_inc_ref(v_f_969_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v_d_983_);
v___x_984_ = lean_apply_8(v_f_969_, v_d_983_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, lean_box(0));
if (lean_obj_tag(v___x_984_) == 0)
{
lean_object* v___f_985_; uint8_t v___x_986_; lean_object* v___x_987_; 
lean_dec_ref_known(v___x_984_, 1);
v___f_985_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_985_, 0, v_fvars_970_);
lean_closure_set(v___f_985_, 1, v_f_969_);
lean_closure_set(v___f_985_, 2, v_body_981_);
v___x_986_ = 0;
v___x_987_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_979_, v_binderInfo_982_, v_d_983_, v___f_985_, v___x_986_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
return v___x_987_;
}
else
{
lean_dec_ref(v_d_983_);
lean_dec_ref(v_body_981_);
lean_dec(v_binderName_979_);
lean_dec_ref(v_fvars_970_);
lean_dec_ref(v_f_969_);
return v___x_984_;
}
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_988_ = lean_expr_instantiate_rev(v_a_971_, v_fvars_970_);
lean_dec_ref(v_fvars_970_);
lean_dec_ref(v_a_971_);
lean_inc(v___y_977_);
lean_inc_ref(v___y_976_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc(v___y_972_);
v___x_989_ = lean_apply_8(v_f_969_, v___x_988_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, lean_box(0));
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_990_, lean_object* v_f_991_, lean_object* v_body_992_, lean_object* v_x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_array_push(v_fvars_990_, v_x_993_);
v___x_1002_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_991_, v___x_1001_, v_body_992_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1003_, lean_object* v_fvars_1004_, lean_object* v_a_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1003_, v_fvars_1004_, v_a_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
lean_dec(v___y_1011_);
lean_dec_ref(v___y_1010_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec(v___y_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1014_, lean_object* v_e_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1024_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1014_, v___x_1023_, v_e_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1025_, lean_object* v_e_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v_res_1034_; 
v_res_1034_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1025_, v_e_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec(v___y_1027_);
return v_res_1034_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1036_) == 0)
{
lean_object* v___x_1037_; 
v___x_1037_ = lean_box(0);
return v___x_1037_;
}
else
{
lean_object* v_key_1038_; lean_object* v_value_1039_; lean_object* v_tail_1040_; uint8_t v___x_1041_; 
v_key_1038_ = lean_ctor_get(v_x_1036_, 0);
v_value_1039_ = lean_ctor_get(v_x_1036_, 1);
v_tail_1040_ = lean_ctor_get(v_x_1036_, 2);
v___x_1041_ = lean_expr_eqv(v_key_1038_, v_a_1035_);
if (v___x_1041_ == 0)
{
v_x_1036_ = v_tail_1040_;
goto _start;
}
else
{
lean_object* v___x_1043_; 
lean_inc(v_value_1039_);
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v_value_1039_);
return v___x_1043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1044_, lean_object* v_x_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1044_, v_x_1045_);
lean_dec(v_x_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1047_, lean_object* v_a_1048_){
_start:
{
lean_object* v_buckets_1049_; lean_object* v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; uint64_t v___x_1053_; uint64_t v_fold_1054_; uint64_t v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v_buckets_1049_ = lean_ctor_get(v_m_1047_, 1);
v___x_1050_ = lean_array_get_size(v_buckets_1049_);
v___x_1051_ = l_Lean_Expr_hash(v_a_1048_);
v___x_1052_ = 32ULL;
v___x_1053_ = lean_uint64_shift_right(v___x_1051_, v___x_1052_);
v_fold_1054_ = lean_uint64_xor(v___x_1051_, v___x_1053_);
v___x_1055_ = 16ULL;
v___x_1056_ = lean_uint64_shift_right(v_fold_1054_, v___x_1055_);
v___x_1057_ = lean_uint64_xor(v_fold_1054_, v___x_1056_);
v___x_1058_ = lean_uint64_to_usize(v___x_1057_);
v___x_1059_ = lean_usize_of_nat(v___x_1050_);
v___x_1060_ = ((size_t)1ULL);
v___x_1061_ = lean_usize_sub(v___x_1059_, v___x_1060_);
v___x_1062_ = lean_usize_land(v___x_1058_, v___x_1061_);
v___x_1063_ = lean_array_uget_borrowed(v_buckets_1049_, v___x_1062_);
v___x_1064_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1048_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1065_, v_a_1066_);
lean_dec_ref(v_a_1066_);
lean_dec_ref(v_m_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1068_, lean_object* v_x_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
v___x_1076_ = lean_apply_1(v_x_1069_, lean_box(0));
v___x_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1078_, lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v_res_1086_; 
v_res_1086_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1078_, v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
return v_res_1086_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
if (lean_obj_tag(v_x_1088_) == 0)
{
return v_x_1087_;
}
else
{
lean_object* v_key_1089_; lean_object* v_value_1090_; lean_object* v_tail_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1114_; 
v_key_1089_ = lean_ctor_get(v_x_1088_, 0);
v_value_1090_ = lean_ctor_get(v_x_1088_, 1);
v_tail_1091_ = lean_ctor_get(v_x_1088_, 2);
v_isSharedCheck_1114_ = !lean_is_exclusive(v_x_1088_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1093_ = v_x_1088_;
v_isShared_1094_ = v_isSharedCheck_1114_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_tail_1091_);
lean_inc(v_value_1090_);
lean_inc(v_key_1089_);
lean_dec(v_x_1088_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1114_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; uint64_t v___x_1098_; uint64_t v_fold_1099_; uint64_t v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; size_t v___x_1106_; size_t v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1110_; 
v___x_1095_ = lean_array_get_size(v_x_1087_);
v___x_1096_ = l_Lean_Expr_hash(v_key_1089_);
v___x_1097_ = 32ULL;
v___x_1098_ = lean_uint64_shift_right(v___x_1096_, v___x_1097_);
v_fold_1099_ = lean_uint64_xor(v___x_1096_, v___x_1098_);
v___x_1100_ = 16ULL;
v___x_1101_ = lean_uint64_shift_right(v_fold_1099_, v___x_1100_);
v___x_1102_ = lean_uint64_xor(v_fold_1099_, v___x_1101_);
v___x_1103_ = lean_uint64_to_usize(v___x_1102_);
v___x_1104_ = lean_usize_of_nat(v___x_1095_);
v___x_1105_ = ((size_t)1ULL);
v___x_1106_ = lean_usize_sub(v___x_1104_, v___x_1105_);
v___x_1107_ = lean_usize_land(v___x_1103_, v___x_1106_);
v___x_1108_ = lean_array_uget_borrowed(v_x_1087_, v___x_1107_);
lean_inc(v___x_1108_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 2, v___x_1108_);
v___x_1110_ = v___x_1093_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_key_1089_);
lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_value_1090_);
lean_ctor_set(v_reuseFailAlloc_1113_, 2, v___x_1108_);
v___x_1110_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_array_uset(v_x_1087_, v___x_1107_, v___x_1110_);
v_x_1087_ = v___x_1111_;
v_x_1088_ = v_tail_1091_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1115_, lean_object* v_source_1116_, lean_object* v_target_1117_){
_start:
{
lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1118_ = lean_array_get_size(v_source_1116_);
v___x_1119_ = lean_nat_dec_lt(v_i_1115_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_dec_ref(v_source_1116_);
lean_dec(v_i_1115_);
return v_target_1117_;
}
else
{
lean_object* v_es_1120_; lean_object* v___x_1121_; lean_object* v_source_1122_; lean_object* v_target_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; 
v_es_1120_ = lean_array_fget(v_source_1116_, v_i_1115_);
v___x_1121_ = lean_box(0);
v_source_1122_ = lean_array_fset(v_source_1116_, v_i_1115_, v___x_1121_);
v_target_1123_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1117_, v_es_1120_);
v___x_1124_ = lean_unsigned_to_nat(1u);
v___x_1125_ = lean_nat_add(v_i_1115_, v___x_1124_);
lean_dec(v_i_1115_);
v_i_1115_ = v___x_1125_;
v_source_1116_ = v_source_1122_;
v_target_1117_ = v_target_1123_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_nbuckets_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1128_ = lean_array_get_size(v_data_1127_);
v___x_1129_ = lean_unsigned_to_nat(2u);
v_nbuckets_1130_ = lean_nat_mul(v___x_1128_, v___x_1129_);
v___x_1131_ = lean_unsigned_to_nat(0u);
v___x_1132_ = lean_box(0);
v___x_1133_ = lean_mk_array(v_nbuckets_1130_, v___x_1132_);
v___x_1134_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1131_, v_data_1127_, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1135_, lean_object* v_b_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
lean_dec(v_b_1136_);
lean_dec_ref(v_a_1135_);
return v_x_1137_;
}
else
{
lean_object* v_key_1138_; lean_object* v_value_1139_; lean_object* v_tail_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1152_; 
v_key_1138_ = lean_ctor_get(v_x_1137_, 0);
v_value_1139_ = lean_ctor_get(v_x_1137_, 1);
v_tail_1140_ = lean_ctor_get(v_x_1137_, 2);
v_isSharedCheck_1152_ = !lean_is_exclusive(v_x_1137_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1142_ = v_x_1137_;
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_tail_1140_);
lean_inc(v_value_1139_);
lean_inc(v_key_1138_);
lean_dec(v_x_1137_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1152_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
uint8_t v___x_1144_; 
v___x_1144_ = lean_expr_eqv(v_key_1138_, v_a_1135_);
if (v___x_1144_ == 0)
{
lean_object* v___x_1145_; lean_object* v___x_1147_; 
v___x_1145_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1135_, v_b_1136_, v_tail_1140_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 2, v___x_1145_);
v___x_1147_ = v___x_1142_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_key_1138_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_value_1139_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v___x_1145_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
else
{
lean_object* v___x_1150_; 
lean_dec(v_value_1139_);
lean_dec(v_key_1138_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 1, v_b_1136_);
lean_ctor_set(v___x_1142_, 0, v_a_1135_);
v___x_1150_ = v___x_1142_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1135_);
lean_ctor_set(v_reuseFailAlloc_1151_, 1, v_b_1136_);
lean_ctor_set(v_reuseFailAlloc_1151_, 2, v_tail_1140_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1153_, lean_object* v_x_1154_){
_start:
{
if (lean_obj_tag(v_x_1154_) == 0)
{
uint8_t v___x_1155_; 
v___x_1155_ = 0;
return v___x_1155_;
}
else
{
lean_object* v_key_1156_; lean_object* v_tail_1157_; uint8_t v___x_1158_; 
v_key_1156_ = lean_ctor_get(v_x_1154_, 0);
v_tail_1157_ = lean_ctor_get(v_x_1154_, 2);
v___x_1158_ = lean_expr_eqv(v_key_1156_, v_a_1153_);
if (v___x_1158_ == 0)
{
v_x_1154_ = v_tail_1157_;
goto _start;
}
else
{
return v___x_1158_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1160_, lean_object* v_x_1161_){
_start:
{
uint8_t v_res_1162_; lean_object* v_r_1163_; 
v_res_1162_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1160_, v_x_1161_);
lean_dec(v_x_1161_);
lean_dec_ref(v_a_1160_);
v_r_1163_ = lean_box(v_res_1162_);
return v_r_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1164_, lean_object* v_a_1165_, lean_object* v_b_1166_){
_start:
{
lean_object* v_size_1167_; lean_object* v_buckets_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1211_; 
v_size_1167_ = lean_ctor_get(v_m_1164_, 0);
v_buckets_1168_ = lean_ctor_get(v_m_1164_, 1);
v_isSharedCheck_1211_ = !lean_is_exclusive(v_m_1164_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1170_ = v_m_1164_;
v_isShared_1171_ = v_isSharedCheck_1211_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_buckets_1168_);
lean_inc(v_size_1167_);
lean_dec(v_m_1164_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1211_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v_fold_1176_; uint64_t v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; size_t v___x_1182_; size_t v___x_1183_; size_t v___x_1184_; lean_object* v_bkt_1185_; uint8_t v___x_1186_; 
v___x_1172_ = lean_array_get_size(v_buckets_1168_);
v___x_1173_ = l_Lean_Expr_hash(v_a_1165_);
v___x_1174_ = 32ULL;
v___x_1175_ = lean_uint64_shift_right(v___x_1173_, v___x_1174_);
v_fold_1176_ = lean_uint64_xor(v___x_1173_, v___x_1175_);
v___x_1177_ = 16ULL;
v___x_1178_ = lean_uint64_shift_right(v_fold_1176_, v___x_1177_);
v___x_1179_ = lean_uint64_xor(v_fold_1176_, v___x_1178_);
v___x_1180_ = lean_uint64_to_usize(v___x_1179_);
v___x_1181_ = lean_usize_of_nat(v___x_1172_);
v___x_1182_ = ((size_t)1ULL);
v___x_1183_ = lean_usize_sub(v___x_1181_, v___x_1182_);
v___x_1184_ = lean_usize_land(v___x_1180_, v___x_1183_);
v_bkt_1185_ = lean_array_uget_borrowed(v_buckets_1168_, v___x_1184_);
v___x_1186_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1165_, v_bkt_1185_);
if (v___x_1186_ == 0)
{
lean_object* v___x_1187_; lean_object* v_size_x27_1188_; lean_object* v___x_1189_; lean_object* v_buckets_x27_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; uint8_t v___x_1196_; 
v___x_1187_ = lean_unsigned_to_nat(1u);
v_size_x27_1188_ = lean_nat_add(v_size_1167_, v___x_1187_);
lean_dec(v_size_1167_);
lean_inc(v_bkt_1185_);
v___x_1189_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1189_, 0, v_a_1165_);
lean_ctor_set(v___x_1189_, 1, v_b_1166_);
lean_ctor_set(v___x_1189_, 2, v_bkt_1185_);
v_buckets_x27_1190_ = lean_array_uset(v_buckets_1168_, v___x_1184_, v___x_1189_);
v___x_1191_ = lean_unsigned_to_nat(4u);
v___x_1192_ = lean_nat_mul(v_size_x27_1188_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(3u);
v___x_1194_ = lean_nat_div(v___x_1192_, v___x_1193_);
lean_dec(v___x_1192_);
v___x_1195_ = lean_array_get_size(v_buckets_x27_1190_);
v___x_1196_ = lean_nat_dec_le(v___x_1194_, v___x_1195_);
lean_dec(v___x_1194_);
if (v___x_1196_ == 0)
{
lean_object* v_val_1197_; lean_object* v___x_1199_; 
v_val_1197_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1190_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_val_1197_);
lean_ctor_set(v___x_1170_, 0, v_size_x27_1188_);
v___x_1199_ = v___x_1170_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_size_x27_1188_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_val_1197_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
else
{
lean_object* v___x_1202_; 
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v_buckets_x27_1190_);
lean_ctor_set(v___x_1170_, 0, v_size_x27_1188_);
v___x_1202_ = v___x_1170_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_size_x27_1188_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_buckets_x27_1190_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v_buckets_x27_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; 
lean_inc(v_bkt_1185_);
v___x_1204_ = lean_box(0);
v_buckets_x27_1205_ = lean_array_uset(v_buckets_1168_, v___x_1184_, v___x_1204_);
v___x_1206_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1165_, v_b_1166_, v_bkt_1185_);
v___x_1207_ = lean_array_uset(v_buckets_x27_1205_, v___x_1184_, v___x_1206_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1207_);
v___x_1209_ = v___x_1170_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_size_1167_);
lean_ctor_set(v_reuseFailAlloc_1210_, 1, v___x_1207_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1212_, lean_object* v_e_1213_, lean_object* v_a_1214_){
_start:
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1216_ = lean_st_ref_take(v_a_1212_);
v___x_1217_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1216_, v_e_1213_, v_a_1214_);
v___x_1218_ = lean_st_ref_set(v_a_1212_, v___x_1217_);
v___x_1219_ = lean_box(0);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1220_, lean_object* v_e_1221_, lean_object* v_a_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1220_, v_e_1221_, v_a_1222_);
lean_dec(v_a_1220_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1225_, lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1225_, v_e_1226_, v_a_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v_a_1227_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1235_, lean_object* v_e_1236_, lean_object* v_a_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v_a_1245_; lean_object* v___y_1257_; lean_object* v___x_1259_; lean_object* v___x_1260_; 
lean_inc(v_a_1237_);
v___x_1259_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1259_, 0, lean_box(0));
lean_closure_set(v___x_1259_, 1, lean_box(0));
lean_closure_set(v___x_1259_, 2, v_a_1237_);
v___x_1260_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1259_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1297_; 
v_a_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1297_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1297_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; 
v___x_1265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1261_, v_e_1236_);
lean_dec(v_a_1261_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v___x_1266_; 
lean_del_object(v___x_1263_);
lean_inc_ref(v_fn_1235_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v_e_1236_);
v___x_1266_ = lean_apply_7(v_fn_1235_, v_e_1236_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; uint8_t v___x_1268_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
lean_inc(v_a_1267_);
lean_dec_ref_known(v___x_1266_, 1);
v___x_1268_ = lean_unbox(v_a_1267_);
lean_dec(v_a_1267_);
if (v___x_1268_ == 0)
{
lean_object* v___x_1269_; 
lean_dec_ref(v_fn_1235_);
v___x_1269_ = lean_box(0);
v_a_1245_ = v___x_1269_;
goto v___jp_1244_;
}
else
{
switch(lean_obj_tag(v_e_1236_))
{
case 7:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1270_, 0, v_fn_1235_);
lean_inc_ref(v_e_1236_);
v___x_1271_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1270_, v_e_1236_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1271_;
goto v___jp_1256_;
}
case 6:
{
lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___x_1272_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1272_, 0, v_fn_1235_);
lean_inc_ref(v_e_1236_);
v___x_1273_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1272_, v_e_1236_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1273_;
goto v___jp_1256_;
}
case 8:
{
lean_object* v___x_1274_; lean_object* v___x_1275_; 
v___x_1274_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1274_, 0, v_fn_1235_);
lean_inc_ref(v_e_1236_);
v___x_1275_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1274_, v_e_1236_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1275_;
goto v___jp_1256_;
}
case 5:
{
lean_object* v_fn_1276_; lean_object* v_arg_1277_; lean_object* v___x_1278_; 
v_fn_1276_ = lean_ctor_get(v_e_1236_, 0);
v_arg_1277_ = lean_ctor_get(v_e_1236_, 1);
lean_inc_ref(v_fn_1276_);
lean_inc_ref(v_fn_1235_);
v___x_1278_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1235_, v_fn_1276_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; 
lean_dec_ref_known(v___x_1278_, 1);
lean_inc_ref(v_arg_1277_);
v___x_1279_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1235_, v_arg_1277_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1279_;
goto v___jp_1256_;
}
else
{
lean_dec_ref(v_fn_1235_);
v___y_1257_ = v___x_1278_;
goto v___jp_1256_;
}
}
case 10:
{
lean_object* v_expr_1280_; lean_object* v___x_1281_; 
v_expr_1280_ = lean_ctor_get(v_e_1236_, 1);
lean_inc_ref(v_expr_1280_);
v___x_1281_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1235_, v_expr_1280_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1281_;
goto v___jp_1256_;
}
case 11:
{
lean_object* v_struct_1282_; lean_object* v___x_1283_; 
v_struct_1282_ = lean_ctor_get(v_e_1236_, 2);
lean_inc_ref(v_struct_1282_);
v___x_1283_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1235_, v_struct_1282_, v_a_1237_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
v___y_1257_ = v___x_1283_;
goto v___jp_1256_;
}
default: 
{
lean_object* v___x_1284_; 
lean_dec_ref(v_fn_1235_);
v___x_1284_ = lean_box(0);
v_a_1245_ = v___x_1284_;
goto v___jp_1244_;
}
}
}
}
else
{
lean_object* v_a_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1292_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_fn_1235_);
v_a_1285_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1292_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1292_ == 0)
{
v___x_1287_ = v___x_1266_;
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_a_1285_);
lean_dec(v___x_1266_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1292_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1290_; 
if (v_isShared_1288_ == 0)
{
v___x_1290_ = v___x_1287_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1291_; 
v_reuseFailAlloc_1291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1291_, 0, v_a_1285_);
v___x_1290_ = v_reuseFailAlloc_1291_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
return v___x_1290_;
}
}
}
}
else
{
lean_object* v_val_1293_; lean_object* v___x_1295_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_fn_1235_);
v_val_1293_ = lean_ctor_get(v___x_1265_, 0);
lean_inc(v_val_1293_);
lean_dec_ref_known(v___x_1265_, 1);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v_val_1293_);
v___x_1295_ = v___x_1263_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_val_1293_);
v___x_1295_ = v_reuseFailAlloc_1296_;
goto v_reusejp_1294_;
}
v_reusejp_1294_:
{
return v___x_1295_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_e_1236_);
lean_dec_ref(v_fn_1235_);
v_a_1298_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1260_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1260_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
v___jp_1244_:
{
lean_object* v___f_1246_; lean_object* v___x_1247_; 
lean_inc(v_a_1237_);
v___f_1246_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1246_, 0, v_a_1237_);
lean_closure_set(v___f_1246_, 1, v_e_1236_);
lean_closure_set(v___f_1246_, 2, v_a_1245_);
v___x_1247_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1246_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v___x_1249_; uint8_t v_isShared_1250_; uint8_t v_isSharedCheck_1254_; 
v_isSharedCheck_1254_ = !lean_is_exclusive(v___x_1247_);
if (v_isSharedCheck_1254_ == 0)
{
lean_object* v_unused_1255_; 
v_unused_1255_ = lean_ctor_get(v___x_1247_, 0);
lean_dec(v_unused_1255_);
v___x_1249_ = v___x_1247_;
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
else
{
lean_dec(v___x_1247_);
v___x_1249_ = lean_box(0);
v_isShared_1250_ = v_isSharedCheck_1254_;
goto v_resetjp_1248_;
}
v_resetjp_1248_:
{
lean_object* v___x_1252_; 
if (v_isShared_1250_ == 0)
{
lean_ctor_set(v___x_1249_, 0, v_a_1245_);
v___x_1252_ = v___x_1249_;
goto v_reusejp_1251_;
}
else
{
lean_object* v_reuseFailAlloc_1253_; 
v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1253_, 0, v_a_1245_);
v___x_1252_ = v_reuseFailAlloc_1253_;
goto v_reusejp_1251_;
}
v_reusejp_1251_:
{
return v___x_1252_;
}
}
}
else
{
return v___x_1247_;
}
}
v___jp_1256_:
{
if (lean_obj_tag(v___y_1257_) == 0)
{
lean_object* v_a_1258_; 
v_a_1258_ = lean_ctor_get(v___y_1257_, 0);
lean_inc(v_a_1258_);
lean_dec_ref_known(v___y_1257_, 1);
v_a_1245_ = v_a_1258_;
goto v___jp_1244_;
}
else
{
lean_dec_ref(v_e_1236_);
return v___y_1257_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_box(0);
v___x_1307_ = lean_unsigned_to_nat(16u);
v___x_1308_ = lean_mk_array(v___x_1307_, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v___x_1309_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1310_ = lean_unsigned_to_nat(0u);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v___x_1309_);
return v___x_1311_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1312_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1313_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1313_, 0, lean_box(0));
lean_closure_set(v___x_1313_, 1, lean_box(0));
lean_closure_set(v___x_1313_, 2, v___x_1312_);
return v___x_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1314_, lean_object* v_fn_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v_a_1324_; lean_object* v___x_1325_; 
v___x_1322_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1323_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1322_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
v_a_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_a_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1315_, v_input_1314_, v_a_1324_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1330_; uint8_t v_isShared_1331_; uint8_t v_isSharedCheck_1335_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_a_1326_);
lean_dec_ref_known(v___x_1325_, 1);
v___x_1327_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1327_, 0, lean_box(0));
lean_closure_set(v___x_1327_, 1, lean_box(0));
lean_closure_set(v___x_1327_, 2, v_a_1324_);
v___x_1328_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1327_, v___y_1316_, v___y_1317_, v___y_1318_, v___y_1319_, v___y_1320_);
v_isSharedCheck_1335_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1335_ == 0)
{
lean_object* v_unused_1336_; 
v_unused_1336_ = lean_ctor_get(v___x_1328_, 0);
lean_dec(v_unused_1336_);
v___x_1330_ = v___x_1328_;
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
else
{
lean_dec(v___x_1328_);
v___x_1330_ = lean_box(0);
v_isShared_1331_ = v_isSharedCheck_1335_;
goto v_resetjp_1329_;
}
v_resetjp_1329_:
{
lean_object* v___x_1333_; 
if (v_isShared_1331_ == 0)
{
lean_ctor_set(v___x_1330_, 0, v_a_1326_);
v___x_1333_ = v___x_1330_;
goto v_reusejp_1332_;
}
else
{
lean_object* v_reuseFailAlloc_1334_; 
v_reuseFailAlloc_1334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1334_, 0, v_a_1326_);
v___x_1333_ = v_reuseFailAlloc_1334_;
goto v_reusejp_1332_;
}
v_reusejp_1332_:
{
return v___x_1333_;
}
}
}
else
{
lean_dec(v_a_1324_);
return v___x_1325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1337_, lean_object* v_fn_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1337_, v_fn_1338_, v___y_1339_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1346_, lean_object* v_fn_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v___f_1354_; lean_object* v___x_1355_; 
v___f_1354_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1354_, 0, v_fn_1347_);
v___x_1355_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1346_, v___f_1354_, v___y_1348_, v___y_1349_, v___y_1350_, v___y_1351_, v___y_1352_);
return v___x_1355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1356_, lean_object* v_fn_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_){
_start:
{
lean_object* v_res_1364_; 
v_res_1364_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1356_, v_fn_1357_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
lean_dec(v___y_1360_);
lean_dec_ref(v___y_1359_);
lean_dec(v___y_1358_);
return v_res_1364_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1365_, lean_object* v_x_1366_, lean_object* v_x_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
if (lean_obj_tag(v_x_1367_) == 0)
{
lean_object* v___x_1374_; 
lean_dec_ref(v_fn_1365_);
v___x_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1374_, 0, v_x_1366_);
return v___x_1374_;
}
else
{
lean_object* v_head_1375_; lean_object* v_tail_1376_; lean_object* v_type_1377_; lean_object* v___x_1378_; 
v_head_1375_ = lean_ctor_get(v_x_1367_, 0);
lean_inc(v_head_1375_);
v_tail_1376_ = lean_ctor_get(v_x_1367_, 1);
lean_inc(v_tail_1376_);
lean_dec_ref_known(v_x_1367_, 2);
v_type_1377_ = lean_ctor_get(v_head_1375_, 1);
lean_inc_ref(v_type_1377_);
lean_dec(v_head_1375_);
lean_inc_ref(v_fn_1365_);
v___x_1378_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1377_, v_fn_1365_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_object* v_a_1379_; 
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
lean_inc(v_a_1379_);
lean_dec_ref_known(v___x_1378_, 1);
v_x_1366_ = v_a_1379_;
v_x_1367_ = v_tail_1376_;
goto _start;
}
else
{
lean_dec(v_tail_1376_);
lean_dec_ref(v_fn_1365_);
return v___x_1378_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1381_, lean_object* v_x_1382_, lean_object* v_x_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1381_, v_x_1382_, v_x_1383_, v___y_1384_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
lean_dec(v___y_1384_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1391_, lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
if (lean_obj_tag(v_x_1393_) == 0)
{
lean_object* v___x_1400_; 
lean_dec_ref(v_fn_1391_);
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_x_1392_);
return v___x_1400_;
}
else
{
lean_object* v_head_1401_; lean_object* v_tail_1402_; lean_object* v___y_1404_; lean_object* v_type_1407_; lean_object* v_ctors_1408_; lean_object* v___x_1409_; 
v_head_1401_ = lean_ctor_get(v_x_1393_, 0);
lean_inc(v_head_1401_);
v_tail_1402_ = lean_ctor_get(v_x_1393_, 1);
lean_inc(v_tail_1402_);
lean_dec_ref_known(v_x_1393_, 2);
v_type_1407_ = lean_ctor_get(v_head_1401_, 1);
lean_inc_ref(v_type_1407_);
v_ctors_1408_ = lean_ctor_get(v_head_1401_, 2);
lean_inc(v_ctors_1408_);
lean_dec(v_head_1401_);
lean_inc_ref(v_fn_1391_);
v___x_1409_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1407_, v_fn_1391_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_object* v_a_1410_; lean_object* v___x_1411_; 
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___x_1409_, 1);
lean_inc_ref(v_fn_1391_);
v___x_1411_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1391_, v_a_1410_, v_ctors_1408_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
v___y_1404_ = v___x_1411_;
goto v___jp_1403_;
}
else
{
lean_dec(v_ctors_1408_);
v___y_1404_ = v___x_1409_;
goto v___jp_1403_;
}
v___jp_1403_:
{
if (lean_obj_tag(v___y_1404_) == 0)
{
lean_object* v_a_1405_; 
v_a_1405_ = lean_ctor_get(v___y_1404_, 0);
lean_inc(v_a_1405_);
lean_dec_ref_known(v___y_1404_, 1);
v_x_1392_ = v_a_1405_;
v_x_1393_ = v_tail_1402_;
goto _start;
}
else
{
lean_dec(v_tail_1402_);
lean_dec_ref(v_fn_1391_);
return v___y_1404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1412_, lean_object* v_x_1413_, lean_object* v_x_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_res_1421_; 
v_res_1421_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1412_, v_x_1413_, v_x_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, v___y_1419_);
lean_dec(v___y_1419_);
lean_dec_ref(v___y_1418_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1422_, lean_object* v_x_1423_, lean_object* v_x_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
if (lean_obj_tag(v_x_1424_) == 0)
{
lean_object* v___x_1431_; 
lean_dec_ref(v_fn_1422_);
v___x_1431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_x_1423_);
return v___x_1431_;
}
else
{
lean_object* v_head_1432_; lean_object* v_tail_1433_; lean_object* v___y_1435_; lean_object* v_toConstantVal_1438_; lean_object* v_value_1439_; lean_object* v_type_1440_; lean_object* v___x_1441_; 
v_head_1432_ = lean_ctor_get(v_x_1424_, 0);
lean_inc(v_head_1432_);
v_tail_1433_ = lean_ctor_get(v_x_1424_, 1);
lean_inc(v_tail_1433_);
lean_dec_ref_known(v_x_1424_, 2);
v_toConstantVal_1438_ = lean_ctor_get(v_head_1432_, 0);
lean_inc_ref(v_toConstantVal_1438_);
v_value_1439_ = lean_ctor_get(v_head_1432_, 1);
lean_inc_ref(v_value_1439_);
lean_dec(v_head_1432_);
v_type_1440_ = lean_ctor_get(v_toConstantVal_1438_, 2);
lean_inc_ref(v_type_1440_);
lean_dec_ref(v_toConstantVal_1438_);
lean_inc_ref(v_fn_1422_);
v___x_1441_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1440_, v_fn_1422_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1441_) == 0)
{
lean_object* v___x_1442_; 
lean_dec_ref_known(v___x_1441_, 1);
lean_inc_ref(v_fn_1422_);
v___x_1442_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1439_, v_fn_1422_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
v___y_1435_ = v___x_1442_;
goto v___jp_1434_;
}
else
{
lean_dec_ref(v_value_1439_);
v___y_1435_ = v___x_1441_;
goto v___jp_1434_;
}
v___jp_1434_:
{
if (lean_obj_tag(v___y_1435_) == 0)
{
lean_object* v_a_1436_; 
v_a_1436_ = lean_ctor_get(v___y_1435_, 0);
lean_inc(v_a_1436_);
lean_dec_ref_known(v___y_1435_, 1);
v_x_1423_ = v_a_1436_;
v_x_1424_ = v_tail_1433_;
goto _start;
}
else
{
lean_dec(v_tail_1433_);
lean_dec_ref(v_fn_1422_);
return v___y_1435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1443_, lean_object* v_x_1444_, lean_object* v_x_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_){
_start:
{
lean_object* v_res_1452_; 
v_res_1452_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1443_, v_x_1444_, v_x_1445_, v___y_1446_, v___y_1447_, v___y_1448_, v___y_1449_, v___y_1450_);
lean_dec(v___y_1450_);
lean_dec_ref(v___y_1449_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
return v_res_1452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1453_, lean_object* v_d_1454_, lean_object* v_a_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
switch(lean_obj_tag(v_d_1454_))
{
case 0:
{
lean_object* v_val_1462_; lean_object* v_toConstantVal_1463_; lean_object* v_type_1464_; lean_object* v___x_1465_; 
v_val_1462_ = lean_ctor_get(v_d_1454_, 0);
lean_inc_ref(v_val_1462_);
lean_dec_ref_known(v_d_1454_, 1);
v_toConstantVal_1463_ = lean_ctor_get(v_val_1462_, 0);
lean_inc_ref(v_toConstantVal_1463_);
lean_dec_ref(v_val_1462_);
v_type_1464_ = lean_ctor_get(v_toConstantVal_1463_, 2);
lean_inc_ref(v_type_1464_);
lean_dec_ref(v_toConstantVal_1463_);
v___x_1465_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1464_, v_fn_1453_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1465_;
}
case 4:
{
lean_object* v___x_1466_; 
lean_dec_ref(v_fn_1453_);
v___x_1466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1466_, 0, v_a_1455_);
return v___x_1466_;
}
case 5:
{
lean_object* v_defns_1467_; lean_object* v___x_1468_; 
v_defns_1467_ = lean_ctor_get(v_d_1454_, 0);
lean_inc(v_defns_1467_);
lean_dec_ref_known(v_d_1454_, 1);
v___x_1468_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1453_, v_a_1455_, v_defns_1467_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1468_;
}
case 6:
{
lean_object* v_types_1469_; lean_object* v___x_1470_; 
v_types_1469_ = lean_ctor_get(v_d_1454_, 2);
lean_inc(v_types_1469_);
lean_dec_ref_known(v_d_1454_, 3);
v___x_1470_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1453_, v_a_1455_, v_types_1469_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1470_;
}
default: 
{
lean_object* v_val_1471_; lean_object* v_toConstantVal_1472_; lean_object* v_value_1473_; lean_object* v_type_1474_; lean_object* v___x_1475_; 
v_val_1471_ = lean_ctor_get(v_d_1454_, 0);
lean_inc_ref(v_val_1471_);
lean_dec(v_d_1454_);
v_toConstantVal_1472_ = lean_ctor_get(v_val_1471_, 0);
lean_inc_ref(v_toConstantVal_1472_);
v_value_1473_ = lean_ctor_get(v_val_1471_, 1);
lean_inc_ref(v_value_1473_);
lean_dec_ref(v_val_1471_);
v_type_1474_ = lean_ctor_get(v_toConstantVal_1472_, 2);
lean_inc_ref(v_type_1474_);
lean_dec_ref(v_toConstantVal_1472_);
lean_inc_ref(v_fn_1453_);
v___x_1475_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1474_, v_fn_1453_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1475_) == 0)
{
lean_object* v___x_1476_; 
lean_dec_ref_known(v___x_1475_, 1);
v___x_1476_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1473_, v_fn_1453_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
return v___x_1476_;
}
else
{
lean_dec_ref(v_value_1473_);
lean_dec_ref(v_fn_1453_);
return v___x_1475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1477_, lean_object* v_d_1478_, lean_object* v_a_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_){
_start:
{
lean_object* v_res_1486_; 
v_res_1486_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1477_, v_d_1478_, v_a_1479_, v___y_1480_, v___y_1481_, v___y_1482_, v___y_1483_, v___y_1484_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
return v_res_1486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1487_, lean_object* v_fn_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_, lean_object* v___y_1492_, lean_object* v___y_1493_){
_start:
{
lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1495_ = lean_box(0);
v___x_1496_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1488_, v_decl_1487_, v___x_1495_, v___y_1489_, v___y_1490_, v___y_1491_, v___y_1492_, v___y_1493_);
return v___x_1496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1497_, lean_object* v_fn_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1497_, v_fn_1498_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
return v_res_1505_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1506_; 
v___x_1506_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1507_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1508_, 0, v___x_1507_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1509_ = lean_box(1);
v___x_1510_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1511_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1512_, 0, v___x_1511_);
lean_ctor_set(v___x_1512_, 1, v___x_1510_);
lean_ctor_set(v___x_1512_, 2, v___x_1509_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1516_ = lean_unsigned_to_nat(0u);
v___x_1517_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
lean_ctor_set(v___x_1517_, 3, v___x_1516_);
lean_ctor_set(v___x_1517_, 4, v___x_1515_);
lean_ctor_set(v___x_1517_, 5, v___x_1515_);
lean_ctor_set(v___x_1517_, 6, v___x_1515_);
lean_ctor_set(v___x_1517_, 7, v___x_1515_);
lean_ctor_set(v___x_1517_, 8, v___x_1515_);
lean_ctor_set(v___x_1517_, 9, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; 
v___x_1518_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1519_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1519_, 0, v___x_1518_);
lean_ctor_set(v___x_1519_, 1, v___x_1518_);
lean_ctor_set(v___x_1519_, 2, v___x_1518_);
lean_ctor_set(v___x_1519_, 3, v___x_1518_);
lean_ctor_set(v___x_1519_, 4, v___x_1518_);
lean_ctor_set(v___x_1519_, 5, v___x_1518_);
return v___x_1519_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1520_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1520_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
lean_ctor_set(v___x_1521_, 2, v___x_1520_);
lean_ctor_set(v___x_1521_, 3, v___x_1520_);
lean_ctor_set(v___x_1521_, 4, v___x_1520_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1522_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1523_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1524_ = lean_box(1);
v___x_1525_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1526_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
lean_ctor_set(v___x_1527_, 2, v___x_1524_);
lean_ctor_set(v___x_1527_, 3, v___x_1523_);
lean_ctor_set(v___x_1527_, 4, v___x_1522_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1541_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1542_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1543_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1541_);
return v___x_1543_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_){
_start:
{
lean_object* v_options_1551_; lean_object* v___x_1552_; uint8_t v___x_1553_; 
v_options_1551_ = lean_ctor_get(v_a_1548_, 2);
v___x_1552_ = l_Lean_warn_sorry;
v___x_1553_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; lean_object* v___x_1555_; 
lean_dec(v_decl_1547_);
v___x_1554_ = lean_box(0);
v___x_1555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
return v___x_1555_;
}
else
{
lean_object* v___x_1556_; lean_object* v_messages_1560_; uint8_t v___x_1561_; 
v___x_1556_ = lean_st_ref_get(v_a_1549_);
v_messages_1560_ = lean_ctor_get(v___x_1556_, 6);
lean_inc_ref(v_messages_1560_);
lean_dec(v___x_1556_);
v___x_1561_ = l_Lean_MessageLog_hasErrors(v_messages_1560_);
lean_dec_ref(v_messages_1560_);
if (v___x_1561_ == 0)
{
if (v___x_1553_ == 0)
{
lean_dec(v_decl_1547_);
goto v___jp_1557_;
}
else
{
uint8_t v___x_1562_; 
v___x_1562_ = l_Lean_Declaration_hasSorry(v_decl_1547_);
if (v___x_1562_ == 0)
{
lean_dec(v_decl_1547_);
goto v___jp_1557_;
}
else
{
uint8_t v___x_1563_; uint8_t v___x_1564_; uint8_t v___x_1565_; lean_object* v___x_1566_; uint64_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___f_1578_; lean_object* v___x_1579_; 
v___x_1563_ = 1;
v___x_1564_ = 0;
v___x_1565_ = 2;
v___x_1566_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1566_, 0, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 1, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 2, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 3, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 4, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 5, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 6, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 7, v___x_1561_);
lean_ctor_set_uint8(v___x_1566_, 8, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 9, v___x_1563_);
lean_ctor_set_uint8(v___x_1566_, 10, v___x_1564_);
lean_ctor_set_uint8(v___x_1566_, 11, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 12, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 13, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 14, v___x_1565_);
lean_ctor_set_uint8(v___x_1566_, 15, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 16, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 17, v___x_1562_);
lean_ctor_set_uint8(v___x_1566_, 18, v___x_1562_);
v___x_1567_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1566_);
v___x_1568_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1568_, 0, v___x_1566_);
lean_ctor_set_uint64(v___x_1568_, sizeof(void*)*1, v___x_1567_);
v___x_1569_ = lean_box(1);
v___x_1570_ = lean_unsigned_to_nat(0u);
v___x_1571_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1572_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1574_, 0, v___x_1568_);
lean_ctor_set(v___x_1574_, 1, v___x_1569_);
lean_ctor_set(v___x_1574_, 2, v___x_1571_);
lean_ctor_set(v___x_1574_, 3, v___x_1572_);
lean_ctor_set(v___x_1574_, 4, v___x_1573_);
lean_ctor_set(v___x_1574_, 5, v___x_1570_);
lean_ctor_set(v___x_1574_, 6, v___x_1573_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*7, v___x_1561_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*7 + 1, v___x_1561_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*7 + 2, v___x_1561_);
lean_ctor_set_uint8(v___x_1574_, sizeof(void*)*7 + 3, v___x_1553_);
v___x_1575_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1576_ = lean_st_mk_ref(v___x_1575_);
v___x_1577_ = lean_st_mk_ref(v___x_1572_);
v___f_1578_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1579_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1547_, v___f_1578_, v___x_1577_, v___x_1574_, v___x_1576_, v_a_1548_, v_a_1549_);
lean_dec_ref_known(v___x_1574_, 7);
if (lean_obj_tag(v___x_1579_) == 0)
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v_val_1583_; lean_object* v___x_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; 
lean_dec_ref_known(v___x_1579_, 1);
v___x_1580_ = lean_st_ref_get(v___x_1577_);
lean_dec(v___x_1577_);
v___x_1581_ = lean_st_ref_get(v___x_1576_);
lean_dec(v___x_1576_);
lean_dec(v___x_1581_);
v___x_1605_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1606_ = lean_array_size(v___x_1580_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1580_, v_sz_1606_, v___x_1607_, v___x_1605_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_fst_1609_);
lean_dec_ref(v___x_1608_);
if (lean_obj_tag(v_fst_1609_) == 0)
{
goto v___jp_1599_;
}
else
{
lean_object* v_val_1610_; 
v_val_1610_ = lean_ctor_get(v_fst_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_fst_1609_, 1);
if (lean_obj_tag(v_val_1610_) == 0)
{
goto v___jp_1599_;
}
else
{
lean_object* v_val_1611_; 
lean_dec(v___x_1580_);
v_val_1611_ = lean_ctor_get(v_val_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_val_1610_, 1);
v_val_1583_ = v_val_1611_;
goto v___jp_1582_;
}
}
v___jp_1582_:
{
lean_object* v_snd_1584_; lean_object* v___x_1586_; uint8_t v_isShared_1587_; uint8_t v_isSharedCheck_1597_; 
v_snd_1584_ = lean_ctor_get(v_val_1583_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_val_1583_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_val_1583_, 0);
lean_dec(v_unused_1598_);
v___x_1586_ = v_val_1583_;
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
else
{
lean_inc(v_snd_1584_);
lean_dec(v_val_1583_);
v___x_1586_ = lean_box(0);
v_isShared_1587_ = v_isSharedCheck_1597_;
goto v_resetjp_1585_;
}
v_resetjp_1585_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1591_; 
v___x_1588_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1589_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1587_ == 0)
{
lean_ctor_set_tag(v___x_1586_, 7);
lean_ctor_set(v___x_1586_, 0, v___x_1589_);
v___x_1591_ = v___x_1586_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1596_; 
v_reuseFailAlloc_1596_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1596_, 0, v___x_1589_);
lean_ctor_set(v_reuseFailAlloc_1596_, 1, v_snd_1584_);
v___x_1591_ = v_reuseFailAlloc_1596_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1592_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1593_, 0, v___x_1591_);
lean_ctor_set(v___x_1593_, 1, v___x_1592_);
v___x_1594_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1594_, 0, v___x_1588_);
lean_ctor_set(v___x_1594_, 1, v___x_1593_);
v___x_1595_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1594_, v_a_1548_, v_a_1549_);
return v___x_1595_;
}
}
}
v___jp_1599_:
{
lean_object* v___x_1600_; uint8_t v___x_1601_; 
v___x_1600_ = lean_array_get_size(v___x_1580_);
v___x_1601_ = lean_nat_dec_lt(v___x_1570_, v___x_1600_);
if (v___x_1601_ == 0)
{
lean_object* v___x_1602_; lean_object* v___x_1603_; 
lean_dec(v___x_1580_);
v___x_1602_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1603_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1602_, v_a_1548_, v_a_1549_);
return v___x_1603_;
}
else
{
lean_object* v___x_1604_; 
v___x_1604_ = lean_array_fget(v___x_1580_, v___x_1570_);
lean_dec(v___x_1580_);
v_val_1583_ = v___x_1604_;
goto v___jp_1582_;
}
}
}
else
{
lean_dec(v___x_1577_);
lean_dec(v___x_1576_);
return v___x_1579_;
}
}
}
}
else
{
lean_dec(v_decl_1547_);
goto v___jp_1557_;
}
v___jp_1557_:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1612_, lean_object* v_a_1613_, lean_object* v_a_1614_, lean_object* v_a_1615_){
_start:
{
lean_object* v_res_1616_; 
v_res_1616_ = l_Lean_warnIfUsesSorry(v_decl_1612_, v_a_1613_, v_a_1614_);
lean_dec(v_a_1614_);
lean_dec_ref(v_a_1613_);
return v_res_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1617_, lean_object* v_m_1618_, lean_object* v_a_1619_){
_start:
{
lean_object* v___x_1620_; 
v___x_1620_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1618_, v_a_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1621_, lean_object* v_m_1622_, lean_object* v_a_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1621_, v_m_1622_, v_a_1623_);
lean_dec_ref(v_a_1623_);
lean_dec_ref(v_m_1622_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1625_, lean_object* v_m_1626_, lean_object* v_a_1627_, lean_object* v_b_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1626_, v_a_1627_, v_b_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1630_, lean_object* v_a_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1631_, v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_a_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1634_, v_a_1635_, v_x_1636_);
lean_dec(v_x_1636_);
lean_dec_ref(v_a_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1638_, lean_object* v_a_1639_, lean_object* v_x_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_a_1643_, lean_object* v_x_1644_){
_start:
{
uint8_t v_res_1645_; lean_object* v_r_1646_; 
v_res_1645_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1642_, v_a_1643_, v_x_1644_);
lean_dec(v_x_1644_);
lean_dec_ref(v_a_1643_);
v_r_1646_ = lean_box(v_res_1645_);
return v_r_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1647_, lean_object* v_data_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1650_, lean_object* v_a_1651_, lean_object* v_b_1652_, lean_object* v_x_1653_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1651_, v_b_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1655_, lean_object* v_name_1656_, uint8_t v_bi_1657_, lean_object* v_type_1658_, lean_object* v_k_1659_, uint8_t v_kind_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_, lean_object* v___y_1665_, lean_object* v___y_1666_){
_start:
{
lean_object* v___x_1668_; 
v___x_1668_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1656_, v_bi_1657_, v_type_1658_, v_k_1659_, v_kind_1660_, v___y_1661_, v___y_1662_, v___y_1663_, v___y_1664_, v___y_1665_, v___y_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1669_, lean_object* v_name_1670_, lean_object* v_bi_1671_, lean_object* v_type_1672_, lean_object* v_k_1673_, lean_object* v_kind_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_){
_start:
{
uint8_t v_bi_boxed_1682_; uint8_t v_kind_boxed_1683_; lean_object* v_res_1684_; 
v_bi_boxed_1682_ = lean_unbox(v_bi_1671_);
v_kind_boxed_1683_ = lean_unbox(v_kind_1674_);
v_res_1684_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1669_, v_name_1670_, v_bi_boxed_1682_, v_type_1672_, v_k_1673_, v_kind_boxed_1683_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v___y_1676_);
lean_dec(v___y_1675_);
return v_res_1684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1685_, lean_object* v_name_1686_, lean_object* v_type_1687_, lean_object* v_val_1688_, lean_object* v_k_1689_, uint8_t v_nondep_1690_, uint8_t v_kind_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
lean_object* v___x_1699_; 
v___x_1699_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1686_, v_type_1687_, v_val_1688_, v_k_1689_, v_nondep_1690_, v_kind_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
return v___x_1699_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1700_, lean_object* v_name_1701_, lean_object* v_type_1702_, lean_object* v_val_1703_, lean_object* v_k_1704_, lean_object* v_nondep_1705_, lean_object* v_kind_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
uint8_t v_nondep_boxed_1714_; uint8_t v_kind_boxed_1715_; lean_object* v_res_1716_; 
v_nondep_boxed_1714_ = lean_unbox(v_nondep_1705_);
v_kind_boxed_1715_ = lean_unbox(v_kind_1706_);
v_res_1716_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1700_, v_name_1701_, v_type_1702_, v_val_1703_, v_k_1704_, v_nondep_boxed_1714_, v_kind_boxed_1715_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_, v___y_1711_, v___y_1712_);
lean_dec(v___y_1712_);
lean_dec_ref(v___y_1711_);
lean_dec(v___y_1710_);
lean_dec_ref(v___y_1709_);
lean_dec(v___y_1708_);
lean_dec(v___y_1707_);
return v_res_1716_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1717_, lean_object* v_i_1718_, lean_object* v_source_1719_, lean_object* v_target_1720_){
_start:
{
lean_object* v___x_1721_; 
v___x_1721_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1718_, v_source_1719_, v_target_1720_);
return v___x_1721_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
lean_object* v___x_1725_; 
v___x_1725_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1723_, v_x_1724_);
return v___x_1725_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1775_; uint8_t v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; 
v___x_1775_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1776_ = 0;
v___x_1777_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1778_ = l_Lean_registerTraceClass(v___x_1775_, v___x_1776_, v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1779_){
_start:
{
lean_object* v_res_1780_; 
v_res_1780_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1780_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1781_, lean_object* v___y_1782_){
_start:
{
lean_object* v___x_1784_; lean_object* v_nextMacroScope_1785_; lean_object* v_ngen_1786_; lean_object* v_auxDeclNGen_1787_; lean_object* v_traceState_1788_; lean_object* v_messages_1789_; lean_object* v_infoState_1790_; lean_object* v_snapshotTasks_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1802_; 
v___x_1784_ = lean_st_ref_take(v___y_1782_);
v_nextMacroScope_1785_ = lean_ctor_get(v___x_1784_, 1);
v_ngen_1786_ = lean_ctor_get(v___x_1784_, 2);
v_auxDeclNGen_1787_ = lean_ctor_get(v___x_1784_, 3);
v_traceState_1788_ = lean_ctor_get(v___x_1784_, 4);
v_messages_1789_ = lean_ctor_get(v___x_1784_, 6);
v_infoState_1790_ = lean_ctor_get(v___x_1784_, 7);
v_snapshotTasks_1791_ = lean_ctor_get(v___x_1784_, 8);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1784_);
if (v_isSharedCheck_1802_ == 0)
{
lean_object* v_unused_1803_; lean_object* v_unused_1804_; 
v_unused_1803_ = lean_ctor_get(v___x_1784_, 5);
lean_dec(v_unused_1803_);
v_unused_1804_ = lean_ctor_get(v___x_1784_, 0);
lean_dec(v_unused_1804_);
v___x_1793_ = v___x_1784_;
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_snapshotTasks_1791_);
lean_inc(v_infoState_1790_);
lean_inc(v_messages_1789_);
lean_inc(v_traceState_1788_);
lean_inc(v_auxDeclNGen_1787_);
lean_inc(v_ngen_1786_);
lean_inc(v_nextMacroScope_1785_);
lean_dec(v___x_1784_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1802_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1795_; lean_object* v___x_1797_; 
v___x_1795_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1794_ == 0)
{
lean_ctor_set(v___x_1793_, 5, v___x_1795_);
lean_ctor_set(v___x_1793_, 0, v_env_1781_);
v___x_1797_ = v___x_1793_;
goto v_reusejp_1796_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_env_1781_);
lean_ctor_set(v_reuseFailAlloc_1801_, 1, v_nextMacroScope_1785_);
lean_ctor_set(v_reuseFailAlloc_1801_, 2, v_ngen_1786_);
lean_ctor_set(v_reuseFailAlloc_1801_, 3, v_auxDeclNGen_1787_);
lean_ctor_set(v_reuseFailAlloc_1801_, 4, v_traceState_1788_);
lean_ctor_set(v_reuseFailAlloc_1801_, 5, v___x_1795_);
lean_ctor_set(v_reuseFailAlloc_1801_, 6, v_messages_1789_);
lean_ctor_set(v_reuseFailAlloc_1801_, 7, v_infoState_1790_);
lean_ctor_set(v_reuseFailAlloc_1801_, 8, v_snapshotTasks_1791_);
v___x_1797_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1796_;
}
v_reusejp_1796_:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_st_ref_set(v___y_1782_, v___x_1797_);
v___x_1799_ = lean_box(0);
v___x_1800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1800_, 0, v___x_1799_);
return v___x_1800_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1805_, v___y_1806_);
lean_dec(v___y_1806_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_){
_start:
{
lean_object* v___x_1813_; 
v___x_1813_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1809_, v___y_1811_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1814_, lean_object* v___y_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v_res_1818_; 
v_res_1818_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1814_, v___y_1815_, v___y_1816_);
lean_dec(v___y_1816_);
lean_dec_ref(v___y_1815_);
return v_res_1818_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = lean_box(0);
v___x_1820_ = l_Lean_interruptExceptionId;
v___x_1821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
lean_ctor_set(v___x_1821_, 1, v___x_1819_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1823_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1825_){
_start:
{
lean_object* v_res_1826_; 
v_res_1826_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_ref_1831_; lean_object* v___x_1832_; lean_object* v_a_1833_; lean_object* v___x_1835_; uint8_t v_isShared_1836_; uint8_t v_isSharedCheck_1841_; 
v_ref_1831_ = lean_ctor_get(v___y_1828_, 5);
v___x_1832_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1827_, v___y_1828_, v___y_1829_);
v_a_1833_ = lean_ctor_get(v___x_1832_, 0);
v_isSharedCheck_1841_ = !lean_is_exclusive(v___x_1832_);
if (v_isSharedCheck_1841_ == 0)
{
v___x_1835_ = v___x_1832_;
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
else
{
lean_inc(v_a_1833_);
lean_dec(v___x_1832_);
v___x_1835_ = lean_box(0);
v_isShared_1836_ = v_isSharedCheck_1841_;
goto v_resetjp_1834_;
}
v_resetjp_1834_:
{
lean_object* v___x_1837_; lean_object* v___x_1839_; 
lean_inc(v_ref_1831_);
v___x_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1837_, 0, v_ref_1831_);
lean_ctor_set(v___x_1837_, 1, v_a_1833_);
if (v_isShared_1836_ == 0)
{
lean_ctor_set_tag(v___x_1835_, 1);
lean_ctor_set(v___x_1835_, 0, v___x_1837_);
v___x_1839_ = v___x_1835_;
goto v_reusejp_1838_;
}
else
{
lean_object* v_reuseFailAlloc_1840_; 
v_reuseFailAlloc_1840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1840_, 0, v___x_1837_);
v___x_1839_ = v_reuseFailAlloc_1840_;
goto v_reusejp_1838_;
}
v_reusejp_1838_:
{
return v___x_1839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
lean_object* v___y_1852_; lean_object* v___y_1853_; 
if (lean_obj_tag(v_ex_1847_) == 16)
{
lean_object* v___x_1857_; lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
v___x_1857_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1857_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
else
{
v___y_1852_ = v___y_1848_;
v___y_1853_ = v___y_1849_;
goto v___jp_1851_;
}
v___jp_1851_:
{
lean_object* v_options_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_options_1854_ = lean_ctor_get(v___y_1852_, 2);
lean_inc_ref(v_options_1854_);
v___x_1855_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1847_, v_options_1854_);
v___x_1856_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1855_, v___y_1852_, v___y_1853_);
return v___x_1856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1866_, lean_object* v___y_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
lean_object* v_res_1870_; 
v_res_1870_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1866_, v___y_1867_, v___y_1868_);
lean_dec(v___y_1868_);
lean_dec_ref(v___y_1867_);
return v_res_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
if (lean_obj_tag(v_x_1871_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v_x_1871_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v_x_1871_, 1);
v___x_1876_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1875_, v___y_1872_, v___y_1873_);
return v___x_1876_;
}
else
{
lean_object* v_a_1877_; lean_object* v___x_1879_; uint8_t v_isShared_1880_; uint8_t v_isSharedCheck_1884_; 
v_a_1877_ = lean_ctor_get(v_x_1871_, 0);
v_isSharedCheck_1884_ = !lean_is_exclusive(v_x_1871_);
if (v_isSharedCheck_1884_ == 0)
{
v___x_1879_ = v_x_1871_;
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
else
{
lean_inc(v_a_1877_);
lean_dec(v_x_1871_);
v___x_1879_ = lean_box(0);
v_isShared_1880_ = v_isSharedCheck_1884_;
goto v_resetjp_1878_;
}
v_resetjp_1878_:
{
lean_object* v___x_1882_; 
if (v_isShared_1880_ == 0)
{
lean_ctor_set_tag(v___x_1879_, 0);
v___x_1882_ = v___x_1879_;
goto v_reusejp_1881_;
}
else
{
lean_object* v_reuseFailAlloc_1883_; 
v_reuseFailAlloc_1883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1883_, 0, v_a_1877_);
v___x_1882_ = v_reuseFailAlloc_1883_;
goto v_reusejp_1881_;
}
v_reusejp_1881_:
{
return v___x_1882_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_, lean_object* v___y_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1885_, v___y_1886_, v___y_1887_);
lean_dec(v___y_1887_);
lean_dec_ref(v___y_1886_);
return v_res_1889_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1890_ = lean_unsigned_to_nat(1u);
v___x_1891_ = l_Lean_Level_ofNat(v___x_1890_);
return v___x_1891_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_box(0);
v___x_1893_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1902_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1903_ = l_Lean_mkConst(v___x_1902_, v___x_1901_);
return v___x_1903_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1904_ = lean_unsigned_to_nat(0u);
v___x_1905_ = l_Lean_Level_ofNat(v___x_1904_);
return v___x_1905_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1907_ = l_Lean_mkSort(v___x_1906_);
return v___x_1907_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_box(0);
v___x_1914_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1915_ = l_Lean_mkConst(v___x_1914_, v___x_1913_);
return v___x_1915_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1917_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1918_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1919_ = l_Lean_mkAppB(v___x_1918_, v___x_1917_, v___x_1916_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1925_, lean_object* v_b_1926_, lean_object* v___y_1927_, lean_object* v___y_1928_){
_start:
{
if (lean_obj_tag(v_as_x27_1925_) == 0)
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1930_, 0, v_b_1926_);
return v___x_1930_;
}
else
{
lean_object* v_head_1931_; lean_object* v_tail_1932_; lean_object* v___x_1933_; lean_object* v_env_1934_; lean_object* v_options_1935_; lean_object* v_cancelTk_x3f_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___y_1940_; uint8_t v___y_1941_; lean_object* v_a_1945_; lean_object* v___x_1948_; lean_object* v___x_1949_; uint8_t v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; 
lean_dec_ref(v_b_1926_);
v_head_1931_ = lean_ctor_get(v_as_x27_1925_, 0);
v_tail_1932_ = lean_ctor_get(v_as_x27_1925_, 1);
v___x_1933_ = lean_st_ref_get(v___y_1928_);
v_env_1934_ = lean_ctor_get(v___x_1933_, 0);
lean_inc_ref(v_env_1934_);
lean_dec(v___x_1933_);
v_options_1935_ = lean_ctor_get(v___y_1927_, 2);
v_cancelTk_x3f_1936_ = lean_ctor_get(v___y_1927_, 12);
v___x_1937_ = lean_box(0);
v___x_1938_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1948_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1931_);
v___x_1949_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1949_, 0, v_head_1931_);
lean_ctor_set(v___x_1949_, 1, v___x_1937_);
lean_ctor_set(v___x_1949_, 2, v___x_1948_);
v___x_1950_ = 0;
v___x_1951_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1951_, 0, v___x_1949_);
lean_ctor_set_uint8(v___x_1951_, sizeof(void*)*1, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
v___x_1953_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1934_, v_options_1935_, v___x_1952_, v_cancelTk_x3f_1936_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1953_, v___y_1927_, v___y_1928_);
if (lean_obj_tag(v___x_1954_) == 0)
{
lean_object* v_a_1955_; lean_object* v___x_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1964_; 
v_a_1955_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1955_);
lean_dec_ref_known(v___x_1954_, 1);
v___x_1956_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1955_, v___y_1928_);
v_isSharedCheck_1964_ = !lean_is_exclusive(v___x_1956_);
if (v_isSharedCheck_1964_ == 0)
{
lean_object* v_unused_1965_; 
v_unused_1965_ = lean_ctor_get(v___x_1956_, 0);
lean_dec(v_unused_1965_);
v___x_1958_ = v___x_1956_;
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
else
{
lean_dec(v___x_1956_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1964_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v___x_1962_; 
v___x_1960_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 0, v___x_1960_);
v___x_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1963_; 
v_reuseFailAlloc_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1963_, 0, v___x_1960_);
v___x_1962_ = v_reuseFailAlloc_1963_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
return v___x_1962_;
}
}
}
else
{
lean_object* v_a_1966_; 
v_a_1966_ = lean_ctor_get(v___x_1954_, 0);
lean_inc(v_a_1966_);
lean_dec_ref_known(v___x_1954_, 1);
v_a_1945_ = v_a_1966_;
goto v___jp_1944_;
}
v___jp_1939_:
{
if (v___y_1941_ == 0)
{
lean_dec_ref(v___y_1940_);
v_as_x27_1925_ = v_tail_1932_;
v_b_1926_ = v___x_1938_;
goto _start;
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___y_1940_);
return v___x_1943_;
}
}
v___jp_1944_:
{
uint8_t v___x_1946_; 
v___x_1946_ = l_Lean_Exception_isInterrupt(v_a_1945_);
if (v___x_1946_ == 0)
{
uint8_t v___x_1947_; 
lean_inc_ref(v_a_1945_);
v___x_1947_ = l_Lean_Exception_isRuntime(v_a_1945_);
v___y_1940_ = v_a_1945_;
v___y_1941_ = v___x_1947_;
goto v___jp_1939_;
}
else
{
v___y_1940_ = v_a_1945_;
v___y_1941_ = v___x_1946_;
goto v___jp_1939_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1967_, lean_object* v_b_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1967_, v_b_1968_, v___y_1969_, v___y_1970_);
lean_dec(v___y_1970_);
lean_dec_ref(v___y_1969_);
lean_dec(v_as_x27_1967_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_){
_start:
{
lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v___y_2006_; uint8_t v___y_2007_; lean_object* v_a_2010_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v_a_2018_; 
switch(lean_obj_tag(v_decl_1973_))
{
case 1:
{
lean_object* v_val_2021_; lean_object* v___x_2022_; lean_object* v_toConstantVal_2023_; lean_object* v_env_2024_; lean_object* v_options_2025_; lean_object* v_cancelTk_x3f_2026_; uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v_fallbackDecl_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_val_2021_ = lean_ctor_get(v_decl_1973_, 0);
v___x_2022_ = lean_st_ref_get(v_a_1975_);
v_toConstantVal_2023_ = lean_ctor_get(v_val_2021_, 0);
v_env_2024_ = lean_ctor_get(v___x_2022_, 0);
lean_inc_ref(v_env_2024_);
lean_dec(v___x_2022_);
v_options_2025_ = lean_ctor_get(v_a_1974_, 2);
v_cancelTk_x3f_2026_ = lean_ctor_get(v_a_1974_, 12);
v___x_2027_ = 0;
lean_inc_ref(v_toConstantVal_2023_);
v___x_2028_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2028_, 0, v_toConstantVal_2023_);
lean_ctor_set_uint8(v___x_2028_, sizeof(void*)*1, v___x_2027_);
v_fallbackDecl_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2029_, 0, v___x_2028_);
v___x_2030_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2024_, v_options_2025_, v_fallbackDecl_2029_, v_cancelTk_x3f_2026_);
lean_dec_ref_known(v_fallbackDecl_2029_, 1);
v___x_2031_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2030_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2041_; 
lean_dec_ref_known(v_decl_1973_, 1);
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2032_, v_a_1975_);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2041_ == 0)
{
lean_object* v_unused_2042_; 
v_unused_2042_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2042_);
v___x_2035_ = v___x_2033_;
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
else
{
lean_dec(v___x_2033_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2041_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v___x_2039_; 
v___x_2037_ = lean_box(0);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 0, v___x_2037_);
v___x_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
else
{
lean_object* v_a_2043_; 
v_a_2043_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2031_, 1);
v_a_2010_ = v_a_2043_;
goto v___jp_2009_;
}
}
case 2:
{
lean_object* v_val_2044_; lean_object* v___x_2045_; lean_object* v_toConstantVal_2046_; lean_object* v_env_2047_; lean_object* v_options_2048_; lean_object* v_cancelTk_x3f_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v_fallbackDecl_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_val_2044_ = lean_ctor_get(v_decl_1973_, 0);
v___x_2045_ = lean_st_ref_get(v_a_1975_);
v_toConstantVal_2046_ = lean_ctor_get(v_val_2044_, 0);
v_env_2047_ = lean_ctor_get(v___x_2045_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2045_);
v_options_2048_ = lean_ctor_get(v_a_1974_, 2);
v_cancelTk_x3f_2049_ = lean_ctor_get(v_a_1974_, 12);
v___x_2050_ = 0;
lean_inc_ref(v_toConstantVal_2046_);
v___x_2051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2051_, 0, v_toConstantVal_2046_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v___x_2050_);
v_fallbackDecl_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2052_, 0, v___x_2051_);
v___x_2053_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2047_, v_options_2048_, v_fallbackDecl_2052_, v_cancelTk_x3f_2049_);
lean_dec_ref_known(v_fallbackDecl_2052_, 1);
v___x_2054_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2053_, v_a_1974_, v_a_1975_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref_known(v_decl_1973_, 1);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2055_, v_a_1975_);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2064_ == 0)
{
lean_object* v_unused_2065_; 
v_unused_2065_ = lean_ctor_get(v___x_2056_, 0);
lean_dec(v_unused_2065_);
v___x_2058_ = v___x_2056_;
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
else
{
lean_dec(v___x_2056_);
v___x_2058_ = lean_box(0);
v_isShared_2059_ = v_isSharedCheck_2064_;
goto v_resetjp_2057_;
}
v_resetjp_2057_:
{
lean_object* v___x_2060_; lean_object* v___x_2062_; 
v___x_2060_ = lean_box(0);
if (v_isShared_2059_ == 0)
{
lean_ctor_set(v___x_2058_, 0, v___x_2060_);
v___x_2062_ = v___x_2058_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v___x_2060_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
else
{
lean_object* v_a_2066_; 
v_a_2066_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2054_, 1);
v_a_2018_ = v_a_2066_;
goto v___jp_2017_;
}
}
default: 
{
v___y_1978_ = v_a_1974_;
v___y_1979_ = v_a_1975_;
goto v___jp_1977_;
}
}
v___jp_1977_:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1980_ = l_Lean_Declaration_getNames(v_decl_1973_);
v___x_1981_ = lean_box(0);
v___x_1982_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1983_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1980_, v___x_1982_, v___y_1978_, v___y_1979_);
lean_dec(v___x_1980_);
if (lean_obj_tag(v___x_1983_) == 0)
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1996_; 
v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_1996_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_1996_ == 0)
{
v___x_1986_ = v___x_1983_;
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1996_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v_fst_1988_; 
v_fst_1988_ = lean_ctor_get(v_a_1984_, 0);
lean_inc(v_fst_1988_);
lean_dec(v_a_1984_);
if (lean_obj_tag(v_fst_1988_) == 0)
{
lean_object* v___x_1990_; 
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1981_);
v___x_1990_ = v___x_1986_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v___x_1981_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
else
{
lean_object* v_val_1992_; lean_object* v___x_1994_; 
v_val_1992_ = lean_ctor_get(v_fst_1988_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v_fst_1988_, 1);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v_val_1992_);
v___x_1994_ = v___x_1986_;
goto v_reusejp_1993_;
}
else
{
lean_object* v_reuseFailAlloc_1995_; 
v_reuseFailAlloc_1995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1995_, 0, v_val_1992_);
v___x_1994_ = v_reuseFailAlloc_1995_;
goto v_reusejp_1993_;
}
v_reusejp_1993_:
{
return v___x_1994_;
}
}
}
}
else
{
lean_object* v_a_1997_; lean_object* v___x_1999_; uint8_t v_isShared_2000_; uint8_t v_isSharedCheck_2004_; 
v_a_1997_ = lean_ctor_get(v___x_1983_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1983_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1999_ = v___x_1983_;
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
else
{
lean_inc(v_a_1997_);
lean_dec(v___x_1983_);
v___x_1999_ = lean_box(0);
v_isShared_2000_ = v_isSharedCheck_2004_;
goto v_resetjp_1998_;
}
v_resetjp_1998_:
{
lean_object* v___x_2002_; 
if (v_isShared_2000_ == 0)
{
v___x_2002_ = v___x_1999_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_a_1997_);
v___x_2002_ = v_reuseFailAlloc_2003_;
goto v_reusejp_2001_;
}
v_reusejp_2001_:
{
return v___x_2002_;
}
}
}
}
v___jp_2005_:
{
if (v___y_2007_ == 0)
{
lean_dec_ref(v___y_2006_);
v___y_1978_ = v_a_1974_;
v___y_1979_ = v_a_1975_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_2008_; 
lean_dec(v_decl_1973_);
v___x_2008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2008_, 0, v___y_2006_);
return v___x_2008_;
}
}
v___jp_2009_:
{
uint8_t v___x_2011_; 
v___x_2011_ = l_Lean_Exception_isInterrupt(v_a_2010_);
if (v___x_2011_ == 0)
{
uint8_t v___x_2012_; 
lean_inc_ref(v_a_2010_);
v___x_2012_ = l_Lean_Exception_isRuntime(v_a_2010_);
v___y_2006_ = v_a_2010_;
v___y_2007_ = v___x_2012_;
goto v___jp_2005_;
}
else
{
v___y_2006_ = v_a_2010_;
v___y_2007_ = v___x_2011_;
goto v___jp_2005_;
}
}
v___jp_2013_:
{
if (v___y_2015_ == 0)
{
lean_dec_ref(v___y_2014_);
v___y_1978_ = v_a_1974_;
v___y_1979_ = v_a_1975_;
goto v___jp_1977_;
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_decl_1973_);
v___x_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2016_, 0, v___y_2014_);
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
v___y_2014_ = v_a_2018_;
v___y_2015_ = v___x_2020_;
goto v___jp_2013_;
}
else
{
v___y_2014_ = v_a_2018_;
v___y_2015_ = v___x_2019_;
goto v___jp_2013_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v_res_2071_; 
v_res_2071_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2067_, v_a_2068_, v_a_2069_);
lean_dec(v_a_2069_);
lean_dec_ref(v_a_2068_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2072_, lean_object* v_x_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
lean_object* v___x_2077_; 
v___x_2077_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2073_, v___y_2074_, v___y_2075_);
return v___x_2077_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2078_, lean_object* v_x_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2078_, v_x_2079_, v___y_2080_, v___y_2081_);
lean_dec(v___y_2081_);
lean_dec_ref(v___y_2080_);
return v_res_2083_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2084_, lean_object* v_as_x27_2085_, lean_object* v_b_2086_, lean_object* v_a_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2085_, v_b_2086_, v___y_2088_, v___y_2089_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2092_, lean_object* v_as_x27_2093_, lean_object* v_b_2094_, lean_object* v_a_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_){
_start:
{
lean_object* v_res_2099_; 
v_res_2099_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2092_, v_as_x27_2093_, v_b_2094_, v_a_2095_, v___y_2096_, v___y_2097_);
lean_dec(v___y_2097_);
lean_dec_ref(v___y_2096_);
lean_dec(v_as_x27_2093_);
lean_dec(v_as_2092_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2110_, lean_object* v_ex_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2111_, v___y_2112_, v___y_2113_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2116_, lean_object* v_ex_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2116_, v_ex_2117_, v___y_2118_, v___y_2119_);
lean_dec(v___y_2119_);
lean_dec_ref(v___y_2118_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2122_, lean_object* v_msg_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v___x_2127_; 
v___x_2127_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2123_, v___y_2124_, v___y_2125_);
return v___x_2127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2128_, lean_object* v_msg_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_, lean_object* v___y_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2128_, v_msg_2129_, v___y_2130_, v___y_2131_);
lean_dec(v___y_2131_);
lean_dec_ref(v___y_2130_);
return v_res_2133_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; 
v___x_2134_ = lean_unsigned_to_nat(32u);
v___x_2135_ = lean_mk_empty_array_with_capacity(v___x_2134_);
v___x_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2136_, 0, v___x_2135_);
return v___x_2136_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2137_ = ((size_t)5ULL);
v___x_2138_ = lean_unsigned_to_nat(0u);
v___x_2139_ = lean_unsigned_to_nat(32u);
v___x_2140_ = lean_mk_empty_array_with_capacity(v___x_2139_);
v___x_2141_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2142_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2140_);
lean_ctor_set(v___x_2142_, 2, v___x_2138_);
lean_ctor_set(v___x_2142_, 3, v___x_2138_);
lean_ctor_set_usize(v___x_2142_, 4, v___x_2137_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2143_){
_start:
{
lean_object* v___x_2145_; lean_object* v_traceState_2146_; lean_object* v_traces_2147_; lean_object* v___x_2148_; lean_object* v_traceState_2149_; lean_object* v_env_2150_; lean_object* v_nextMacroScope_2151_; lean_object* v_ngen_2152_; lean_object* v_auxDeclNGen_2153_; lean_object* v_cache_2154_; lean_object* v_messages_2155_; lean_object* v_infoState_2156_; lean_object* v_snapshotTasks_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2176_; 
v___x_2145_ = lean_st_ref_get(v___y_2143_);
v_traceState_2146_ = lean_ctor_get(v___x_2145_, 4);
lean_inc_ref(v_traceState_2146_);
lean_dec(v___x_2145_);
v_traces_2147_ = lean_ctor_get(v_traceState_2146_, 0);
lean_inc_ref(v_traces_2147_);
lean_dec_ref(v_traceState_2146_);
v___x_2148_ = lean_st_ref_take(v___y_2143_);
v_traceState_2149_ = lean_ctor_get(v___x_2148_, 4);
v_env_2150_ = lean_ctor_get(v___x_2148_, 0);
v_nextMacroScope_2151_ = lean_ctor_get(v___x_2148_, 1);
v_ngen_2152_ = lean_ctor_get(v___x_2148_, 2);
v_auxDeclNGen_2153_ = lean_ctor_get(v___x_2148_, 3);
v_cache_2154_ = lean_ctor_get(v___x_2148_, 5);
v_messages_2155_ = lean_ctor_get(v___x_2148_, 6);
v_infoState_2156_ = lean_ctor_get(v___x_2148_, 7);
v_snapshotTasks_2157_ = lean_ctor_get(v___x_2148_, 8);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2148_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2159_ = v___x_2148_;
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snapshotTasks_2157_);
lean_inc(v_infoState_2156_);
lean_inc(v_messages_2155_);
lean_inc(v_cache_2154_);
lean_inc(v_traceState_2149_);
lean_inc(v_auxDeclNGen_2153_);
lean_inc(v_ngen_2152_);
lean_inc(v_nextMacroScope_2151_);
lean_inc(v_env_2150_);
lean_dec(v___x_2148_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
uint64_t v_tid_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2174_; 
v_tid_2161_ = lean_ctor_get_uint64(v_traceState_2149_, sizeof(void*)*1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_traceState_2149_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v_traceState_2149_, 0);
lean_dec(v_unused_2175_);
v___x_2163_ = v_traceState_2149_;
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v_traceState_2149_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v___x_2165_; lean_object* v___x_2167_; 
v___x_2165_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2165_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v___x_2165_);
lean_ctor_set_uint64(v_reuseFailAlloc_2173_, sizeof(void*)*1, v_tid_2161_);
v___x_2167_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
lean_object* v___x_2169_; 
if (v_isShared_2160_ == 0)
{
lean_ctor_set(v___x_2159_, 4, v___x_2167_);
v___x_2169_ = v___x_2159_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_env_2150_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_nextMacroScope_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_ngen_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_auxDeclNGen_2153_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_cache_2154_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_messages_2155_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_infoState_2156_);
lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_snapshotTasks_2157_);
v___x_2169_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_st_ref_set(v___y_2143_, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_traces_2147_);
return v___x_2171_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
lean_object* v_res_2179_; 
v_res_2179_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2177_);
lean_dec(v___y_2177_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v___x_2183_; 
v___x_2183_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2181_);
return v___x_2183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2188_, lean_object* v_opts_2189_, lean_object* v_act_2190_, lean_object* v_decl_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; 
lean_inc(v___y_2193_);
lean_inc_ref(v___y_2192_);
v___x_2195_ = lean_apply_2(v_act_2190_, v___y_2192_, v___y_2193_);
v___x_2196_ = l_Lean_profileitIOUnsafe___redArg(v_category_2188_, v_opts_2189_, v___x_2195_, v_decl_2191_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2197_, lean_object* v_opts_2198_, lean_object* v_act_2199_, lean_object* v_decl_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2197_, v_opts_2198_, v_act_2199_, v_decl_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec_ref(v_opts_2198_);
lean_dec_ref(v_category_2197_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2205_, lean_object* v_category_2206_, lean_object* v_opts_2207_, lean_object* v_act_2208_, lean_object* v_decl_2209_, lean_object* v___y_2210_, lean_object* v___y_2211_){
_start:
{
lean_object* v___x_2213_; 
v___x_2213_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2206_, v_opts_2207_, v_act_2208_, v_decl_2209_, v___y_2210_, v___y_2211_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2214_, lean_object* v_category_2215_, lean_object* v_opts_2216_, lean_object* v_act_2217_, lean_object* v_decl_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2214_, v_category_2215_, v_opts_2216_, v_act_2217_, v_decl_2218_, v___y_2219_, v___y_2220_);
lean_dec(v___y_2220_);
lean_dec_ref(v___y_2219_);
lean_dec_ref(v_opts_2216_);
lean_dec_ref(v_category_2215_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2223_, lean_object* v_a_2224_){
_start:
{
if (lean_obj_tag(v_a_2223_) == 0)
{
lean_object* v___x_2225_; 
v___x_2225_ = l_List_reverse___redArg(v_a_2224_);
return v___x_2225_;
}
else
{
lean_object* v_head_2226_; lean_object* v_tail_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2236_; 
v_head_2226_ = lean_ctor_get(v_a_2223_, 0);
v_tail_2227_ = lean_ctor_get(v_a_2223_, 1);
v_isSharedCheck_2236_ = !lean_is_exclusive(v_a_2223_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2229_ = v_a_2223_;
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_tail_2227_);
lean_inc(v_head_2226_);
lean_dec(v_a_2223_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2236_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = l_Lean_MessageData_ofName(v_head_2226_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 1, v_a_2224_);
lean_ctor_set(v___x_2229_, 0, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v___x_2231_);
lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2224_);
v___x_2233_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
v_a_2223_ = v_tail_2227_;
v_a_2224_ = v___x_2233_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2239_ = l_Lean_stringToMessageData(v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2240_, lean_object* v_x_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2245_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2246_ = l_Lean_Declaration_getTopLevelNames(v_decl_2240_);
v___x_2247_ = lean_box(0);
v___x_2248_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2246_, v___x_2247_);
v___x_2249_ = l_Lean_MessageData_ofList(v___x_2248_);
v___x_2250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2245_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2252_, lean_object* v_x_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_){
_start:
{
lean_object* v_res_2257_; 
v_res_2257_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2252_, v_x_2253_, v___y_2254_, v___y_2255_);
lean_dec(v___y_2255_);
lean_dec_ref(v___y_2254_);
lean_dec_ref(v_x_2253_);
return v_res_2257_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2258_, size_t v_i_2259_, lean_object* v_bs_2260_){
_start:
{
uint8_t v___x_2261_; 
v___x_2261_ = lean_usize_dec_lt(v_i_2259_, v_sz_2258_);
if (v___x_2261_ == 0)
{
return v_bs_2260_;
}
else
{
lean_object* v_v_2262_; lean_object* v_msg_2263_; lean_object* v___x_2264_; lean_object* v_bs_x27_2265_; size_t v___x_2266_; size_t v___x_2267_; lean_object* v___x_2268_; 
v_v_2262_ = lean_array_uget_borrowed(v_bs_2260_, v_i_2259_);
v_msg_2263_ = lean_ctor_get(v_v_2262_, 1);
lean_inc_ref(v_msg_2263_);
v___x_2264_ = lean_unsigned_to_nat(0u);
v_bs_x27_2265_ = lean_array_uset(v_bs_2260_, v_i_2259_, v___x_2264_);
v___x_2266_ = ((size_t)1ULL);
v___x_2267_ = lean_usize_add(v_i_2259_, v___x_2266_);
v___x_2268_ = lean_array_uset(v_bs_x27_2265_, v_i_2259_, v_msg_2263_);
v_i_2259_ = v___x_2267_;
v_bs_2260_ = v___x_2268_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2270_, lean_object* v_i_2271_, lean_object* v_bs_2272_){
_start:
{
size_t v_sz_boxed_2273_; size_t v_i_boxed_2274_; lean_object* v_res_2275_; 
v_sz_boxed_2273_ = lean_unbox_usize(v_sz_2270_);
lean_dec(v_sz_2270_);
v_i_boxed_2274_ = lean_unbox_usize(v_i_2271_);
lean_dec(v_i_2271_);
v_res_2275_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2273_, v_i_boxed_2274_, v_bs_2272_);
return v_res_2275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2276_, lean_object* v_data_2277_, lean_object* v_ref_2278_, lean_object* v_msg_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_fileName_2283_; lean_object* v_fileMap_2284_; lean_object* v_options_2285_; lean_object* v_currRecDepth_2286_; lean_object* v_maxRecDepth_2287_; lean_object* v_ref_2288_; lean_object* v_currNamespace_2289_; lean_object* v_openDecls_2290_; lean_object* v_initHeartbeats_2291_; lean_object* v_maxHeartbeats_2292_; lean_object* v_quotContext_2293_; lean_object* v_currMacroScope_2294_; uint8_t v_diag_2295_; lean_object* v_cancelTk_x3f_2296_; uint8_t v_suppressElabErrors_2297_; lean_object* v_inheritedTraceOptions_2298_; lean_object* v___x_2299_; lean_object* v_traceState_2300_; lean_object* v_traces_2301_; lean_object* v_ref_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; size_t v_sz_2305_; size_t v___x_2306_; lean_object* v___x_2307_; lean_object* v_msg_2308_; lean_object* v___x_2309_; lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2347_; 
v_fileName_2283_ = lean_ctor_get(v___y_2280_, 0);
v_fileMap_2284_ = lean_ctor_get(v___y_2280_, 1);
v_options_2285_ = lean_ctor_get(v___y_2280_, 2);
v_currRecDepth_2286_ = lean_ctor_get(v___y_2280_, 3);
v_maxRecDepth_2287_ = lean_ctor_get(v___y_2280_, 4);
v_ref_2288_ = lean_ctor_get(v___y_2280_, 5);
v_currNamespace_2289_ = lean_ctor_get(v___y_2280_, 6);
v_openDecls_2290_ = lean_ctor_get(v___y_2280_, 7);
v_initHeartbeats_2291_ = lean_ctor_get(v___y_2280_, 8);
v_maxHeartbeats_2292_ = lean_ctor_get(v___y_2280_, 9);
v_quotContext_2293_ = lean_ctor_get(v___y_2280_, 10);
v_currMacroScope_2294_ = lean_ctor_get(v___y_2280_, 11);
v_diag_2295_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*14);
v_cancelTk_x3f_2296_ = lean_ctor_get(v___y_2280_, 12);
v_suppressElabErrors_2297_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2298_ = lean_ctor_get(v___y_2280_, 13);
v___x_2299_ = lean_st_ref_get(v___y_2281_);
v_traceState_2300_ = lean_ctor_get(v___x_2299_, 4);
lean_inc_ref(v_traceState_2300_);
lean_dec(v___x_2299_);
v_traces_2301_ = lean_ctor_get(v_traceState_2300_, 0);
lean_inc_ref(v_traces_2301_);
lean_dec_ref(v_traceState_2300_);
v_ref_2302_ = l_Lean_replaceRef(v_ref_2278_, v_ref_2288_);
lean_inc_ref(v_inheritedTraceOptions_2298_);
lean_inc(v_cancelTk_x3f_2296_);
lean_inc(v_currMacroScope_2294_);
lean_inc(v_quotContext_2293_);
lean_inc(v_maxHeartbeats_2292_);
lean_inc(v_initHeartbeats_2291_);
lean_inc(v_openDecls_2290_);
lean_inc(v_currNamespace_2289_);
lean_inc(v_maxRecDepth_2287_);
lean_inc(v_currRecDepth_2286_);
lean_inc_ref(v_options_2285_);
lean_inc_ref(v_fileMap_2284_);
lean_inc_ref(v_fileName_2283_);
v___x_2303_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2303_, 0, v_fileName_2283_);
lean_ctor_set(v___x_2303_, 1, v_fileMap_2284_);
lean_ctor_set(v___x_2303_, 2, v_options_2285_);
lean_ctor_set(v___x_2303_, 3, v_currRecDepth_2286_);
lean_ctor_set(v___x_2303_, 4, v_maxRecDepth_2287_);
lean_ctor_set(v___x_2303_, 5, v_ref_2302_);
lean_ctor_set(v___x_2303_, 6, v_currNamespace_2289_);
lean_ctor_set(v___x_2303_, 7, v_openDecls_2290_);
lean_ctor_set(v___x_2303_, 8, v_initHeartbeats_2291_);
lean_ctor_set(v___x_2303_, 9, v_maxHeartbeats_2292_);
lean_ctor_set(v___x_2303_, 10, v_quotContext_2293_);
lean_ctor_set(v___x_2303_, 11, v_currMacroScope_2294_);
lean_ctor_set(v___x_2303_, 12, v_cancelTk_x3f_2296_);
lean_ctor_set(v___x_2303_, 13, v_inheritedTraceOptions_2298_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*14, v_diag_2295_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*14 + 1, v_suppressElabErrors_2297_);
v___x_2304_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2301_);
lean_dec_ref(v_traces_2301_);
v_sz_2305_ = lean_array_size(v___x_2304_);
v___x_2306_ = ((size_t)0ULL);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2305_, v___x_2306_, v___x_2304_);
v_msg_2308_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2308_, 0, v_data_2277_);
lean_ctor_set(v_msg_2308_, 1, v_msg_2279_);
lean_ctor_set(v_msg_2308_, 2, v___x_2307_);
v___x_2309_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2308_, v___x_2303_, v___y_2281_);
lean_dec_ref_known(v___x_2303_, 14);
v_a_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2347_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2347_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v_traceState_2315_; lean_object* v_env_2316_; lean_object* v_nextMacroScope_2317_; lean_object* v_ngen_2318_; lean_object* v_auxDeclNGen_2319_; lean_object* v_cache_2320_; lean_object* v_messages_2321_; lean_object* v_infoState_2322_; lean_object* v_snapshotTasks_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2346_; 
v___x_2314_ = lean_st_ref_take(v___y_2281_);
v_traceState_2315_ = lean_ctor_get(v___x_2314_, 4);
v_env_2316_ = lean_ctor_get(v___x_2314_, 0);
v_nextMacroScope_2317_ = lean_ctor_get(v___x_2314_, 1);
v_ngen_2318_ = lean_ctor_get(v___x_2314_, 2);
v_auxDeclNGen_2319_ = lean_ctor_get(v___x_2314_, 3);
v_cache_2320_ = lean_ctor_get(v___x_2314_, 5);
v_messages_2321_ = lean_ctor_get(v___x_2314_, 6);
v_infoState_2322_ = lean_ctor_get(v___x_2314_, 7);
v_snapshotTasks_2323_ = lean_ctor_get(v___x_2314_, 8);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2325_ = v___x_2314_;
v_isShared_2326_ = v_isSharedCheck_2346_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_snapshotTasks_2323_);
lean_inc(v_infoState_2322_);
lean_inc(v_messages_2321_);
lean_inc(v_cache_2320_);
lean_inc(v_traceState_2315_);
lean_inc(v_auxDeclNGen_2319_);
lean_inc(v_ngen_2318_);
lean_inc(v_nextMacroScope_2317_);
lean_inc(v_env_2316_);
lean_dec(v___x_2314_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2346_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
uint64_t v_tid_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2344_; 
v_tid_2327_ = lean_ctor_get_uint64(v_traceState_2315_, sizeof(void*)*1);
v_isSharedCheck_2344_ = !lean_is_exclusive(v_traceState_2315_);
if (v_isSharedCheck_2344_ == 0)
{
lean_object* v_unused_2345_; 
v_unused_2345_ = lean_ctor_get(v_traceState_2315_, 0);
lean_dec(v_unused_2345_);
v___x_2329_ = v_traceState_2315_;
v_isShared_2330_ = v_isSharedCheck_2344_;
goto v_resetjp_2328_;
}
else
{
lean_dec(v_traceState_2315_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2344_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2334_; 
v___x_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2331_, 0, v_ref_2278_);
lean_ctor_set(v___x_2331_, 1, v_a_2310_);
v___x_2332_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2276_, v___x_2331_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2332_);
v___x_2334_ = v___x_2329_;
goto v_reusejp_2333_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v___x_2332_);
lean_ctor_set_uint64(v_reuseFailAlloc_2343_, sizeof(void*)*1, v_tid_2327_);
v___x_2334_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2333_;
}
v_reusejp_2333_:
{
lean_object* v___x_2336_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 4, v___x_2334_);
v___x_2336_ = v___x_2325_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v_env_2316_);
lean_ctor_set(v_reuseFailAlloc_2342_, 1, v_nextMacroScope_2317_);
lean_ctor_set(v_reuseFailAlloc_2342_, 2, v_ngen_2318_);
lean_ctor_set(v_reuseFailAlloc_2342_, 3, v_auxDeclNGen_2319_);
lean_ctor_set(v_reuseFailAlloc_2342_, 4, v___x_2334_);
lean_ctor_set(v_reuseFailAlloc_2342_, 5, v_cache_2320_);
lean_ctor_set(v_reuseFailAlloc_2342_, 6, v_messages_2321_);
lean_ctor_set(v_reuseFailAlloc_2342_, 7, v_infoState_2322_);
lean_ctor_set(v_reuseFailAlloc_2342_, 8, v_snapshotTasks_2323_);
v___x_2336_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2337_ = lean_st_ref_set(v___y_2281_, v___x_2336_);
v___x_2338_ = lean_box(0);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2338_);
v___x_2340_ = v___x_2312_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2348_, lean_object* v_data_2349_, lean_object* v_ref_2350_, lean_object* v_msg_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_){
_start:
{
lean_object* v_res_2355_; 
v_res_2355_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2348_, v_data_2349_, v_ref_2350_, v_msg_2351_, v___y_2352_, v___y_2353_);
lean_dec(v___y_2353_);
lean_dec_ref(v___y_2352_);
return v_res_2355_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2356_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 0)
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
v_a_2358_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v_x_2356_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v_x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set_tag(v___x_2360_, 1);
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
else
{
lean_object* v_a_2366_; lean_object* v___x_2368_; uint8_t v_isShared_2369_; uint8_t v_isSharedCheck_2373_; 
v_a_2366_ = lean_ctor_get(v_x_2356_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_x_2356_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2368_ = v_x_2356_;
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
else
{
lean_inc(v_a_2366_);
lean_dec(v_x_2356_);
v___x_2368_ = lean_box(0);
v_isShared_2369_ = v_isSharedCheck_2373_;
goto v_resetjp_2367_;
}
v_resetjp_2367_:
{
lean_object* v___x_2371_; 
if (v_isShared_2369_ == 0)
{
lean_ctor_set_tag(v___x_2368_, 0);
v___x_2371_ = v___x_2368_;
goto v_reusejp_2370_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
v___x_2371_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2370_;
}
v_reusejp_2370_:
{
return v___x_2371_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2374_);
return v_res_2376_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2377_){
_start:
{
if (lean_obj_tag(v_e_2377_) == 0)
{
uint8_t v___x_2378_; 
v___x_2378_ = 2;
return v___x_2378_;
}
else
{
uint8_t v___x_2379_; 
v___x_2379_ = 0;
return v___x_2379_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2380_){
_start:
{
uint8_t v_res_2381_; lean_object* v_r_2382_; 
v_res_2381_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2380_);
lean_dec_ref(v_e_2380_);
v_r_2382_ = lean_box(v_res_2381_);
return v_r_2382_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2383_; double v___x_2384_; 
v___x_2383_ = lean_unsigned_to_nat(0u);
v___x_2384_ = lean_float_of_nat(v___x_2383_);
return v___x_2384_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2387_ = l_Lean_stringToMessageData(v___x_2386_);
return v___x_2387_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2388_; double v___x_2389_; 
v___x_2388_ = lean_unsigned_to_nat(1000u);
v___x_2389_ = lean_float_of_nat(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2390_, uint8_t v_collapsed_2391_, lean_object* v_tag_2392_, lean_object* v_opts_2393_, uint8_t v_clsEnabled_2394_, lean_object* v_oldTraces_2395_, lean_object* v_msg_2396_, lean_object* v_resStartStop_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_fst_2401_; lean_object* v_snd_2402_; lean_object* v___y_2404_; lean_object* v___y_2405_; lean_object* v_data_2406_; lean_object* v_fst_2409_; lean_object* v_snd_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___y_2414_; lean_object* v_a_2415_; uint8_t v___y_2430_; double v___y_2461_; 
v_fst_2401_ = lean_ctor_get(v_resStartStop_2397_, 0);
lean_inc(v_fst_2401_);
v_snd_2402_ = lean_ctor_get(v_resStartStop_2397_, 1);
lean_inc(v_snd_2402_);
lean_dec_ref(v_resStartStop_2397_);
v_fst_2409_ = lean_ctor_get(v_snd_2402_, 0);
lean_inc(v_fst_2409_);
v_snd_2410_ = lean_ctor_get(v_snd_2402_, 1);
lean_inc(v_snd_2410_);
lean_dec(v_snd_2402_);
v___x_2411_ = l_Lean_trace_profiler;
v___x_2412_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2393_, v___x_2411_);
if (v___x_2412_ == 0)
{
v___y_2430_ = v___x_2412_;
goto v___jp_2429_;
}
else
{
lean_object* v___x_2466_; uint8_t v___x_2467_; 
v___x_2466_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2467_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2393_, v___x_2466_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; lean_object* v___x_2469_; double v___x_2470_; double v___x_2471_; double v___x_2472_; 
v___x_2468_ = l_Lean_trace_profiler_threshold;
v___x_2469_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2393_, v___x_2468_);
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
v___x_2474_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2393_, v___x_2473_);
v___x_2475_ = lean_float_of_nat(v___x_2474_);
v___y_2461_ = v___x_2475_;
goto v___jp_2460_;
}
}
v___jp_2403_:
{
lean_object* v___x_2407_; 
lean_inc(v___y_2405_);
v___x_2407_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2395_, v_data_2406_, v___y_2405_, v___y_2404_, v___y_2398_, v___y_2399_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; 
lean_dec_ref_known(v___x_2407_, 1);
v___x_2408_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2401_);
return v___x_2408_;
}
else
{
lean_dec(v_fst_2401_);
return v___x_2407_;
}
}
v___jp_2413_:
{
uint8_t v_result_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; double v___x_2419_; lean_object* v_data_2420_; 
v_result_2416_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2401_);
v___x_2417_ = lean_box(v_result_2416_);
v___x_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
v___x_2419_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2392_);
lean_inc_ref(v___x_2418_);
lean_inc(v_cls_2390_);
v_data_2420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2420_, 0, v_cls_2390_);
lean_ctor_set(v_data_2420_, 1, v___x_2418_);
lean_ctor_set(v_data_2420_, 2, v_tag_2392_);
lean_ctor_set_float(v_data_2420_, sizeof(void*)*3, v___x_2419_);
lean_ctor_set_float(v_data_2420_, sizeof(void*)*3 + 8, v___x_2419_);
lean_ctor_set_uint8(v_data_2420_, sizeof(void*)*3 + 16, v_collapsed_2391_);
if (v___x_2412_ == 0)
{
lean_dec_ref_known(v___x_2418_, 1);
lean_dec(v_snd_2410_);
lean_dec(v_fst_2409_);
lean_dec_ref(v_tag_2392_);
lean_dec(v_cls_2390_);
v___y_2404_ = v_a_2415_;
v___y_2405_ = v___y_2414_;
v_data_2406_ = v_data_2420_;
goto v___jp_2403_;
}
else
{
lean_object* v_data_2421_; double v___x_2422_; double v___x_2423_; 
lean_dec_ref_known(v_data_2420_, 3);
v_data_2421_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2421_, 0, v_cls_2390_);
lean_ctor_set(v_data_2421_, 1, v___x_2418_);
lean_ctor_set(v_data_2421_, 2, v_tag_2392_);
v___x_2422_ = lean_unbox_float(v_fst_2409_);
lean_dec(v_fst_2409_);
lean_ctor_set_float(v_data_2421_, sizeof(void*)*3, v___x_2422_);
v___x_2423_ = lean_unbox_float(v_snd_2410_);
lean_dec(v_snd_2410_);
lean_ctor_set_float(v_data_2421_, sizeof(void*)*3 + 8, v___x_2423_);
lean_ctor_set_uint8(v_data_2421_, sizeof(void*)*3 + 16, v_collapsed_2391_);
v___y_2404_ = v_a_2415_;
v___y_2405_ = v___y_2414_;
v_data_2406_ = v_data_2421_;
goto v___jp_2403_;
}
}
v___jp_2424_:
{
lean_object* v_ref_2425_; lean_object* v___x_2426_; 
v_ref_2425_ = lean_ctor_get(v___y_2398_, 5);
lean_inc(v___y_2399_);
lean_inc_ref(v___y_2398_);
lean_inc(v_fst_2401_);
v___x_2426_ = lean_apply_4(v_msg_2396_, v_fst_2401_, v___y_2398_, v___y_2399_, lean_box(0));
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v___y_2414_ = v_ref_2425_;
v_a_2415_ = v_a_2427_;
goto v___jp_2413_;
}
else
{
lean_object* v___x_2428_; 
lean_dec_ref_known(v___x_2426_, 1);
v___x_2428_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2414_ = v_ref_2425_;
v_a_2415_ = v___x_2428_;
goto v___jp_2413_;
}
}
v___jp_2429_:
{
if (v_clsEnabled_2394_ == 0)
{
if (v___y_2430_ == 0)
{
lean_object* v___x_2431_; lean_object* v_traceState_2432_; lean_object* v_env_2433_; lean_object* v_nextMacroScope_2434_; lean_object* v_ngen_2435_; lean_object* v_auxDeclNGen_2436_; lean_object* v_cache_2437_; lean_object* v_messages_2438_; lean_object* v_infoState_2439_; lean_object* v_snapshotTasks_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_snd_2410_);
lean_dec(v_fst_2409_);
lean_dec_ref(v_msg_2396_);
lean_dec_ref(v_tag_2392_);
lean_dec(v_cls_2390_);
v___x_2431_ = lean_st_ref_take(v___y_2399_);
v_traceState_2432_ = lean_ctor_get(v___x_2431_, 4);
v_env_2433_ = lean_ctor_get(v___x_2431_, 0);
v_nextMacroScope_2434_ = lean_ctor_get(v___x_2431_, 1);
v_ngen_2435_ = lean_ctor_get(v___x_2431_, 2);
v_auxDeclNGen_2436_ = lean_ctor_get(v___x_2431_, 3);
v_cache_2437_ = lean_ctor_get(v___x_2431_, 5);
v_messages_2438_ = lean_ctor_get(v___x_2431_, 6);
v_infoState_2439_ = lean_ctor_get(v___x_2431_, 7);
v_snapshotTasks_2440_ = lean_ctor_get(v___x_2431_, 8);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2431_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2442_ = v___x_2431_;
v_isShared_2443_ = v_isSharedCheck_2459_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_snapshotTasks_2440_);
lean_inc(v_infoState_2439_);
lean_inc(v_messages_2438_);
lean_inc(v_cache_2437_);
lean_inc(v_traceState_2432_);
lean_inc(v_auxDeclNGen_2436_);
lean_inc(v_ngen_2435_);
lean_inc(v_nextMacroScope_2434_);
lean_inc(v_env_2433_);
lean_dec(v___x_2431_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2459_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
uint64_t v_tid_2444_; lean_object* v_traces_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2458_; 
v_tid_2444_ = lean_ctor_get_uint64(v_traceState_2432_, sizeof(void*)*1);
v_traces_2445_ = lean_ctor_get(v_traceState_2432_, 0);
v_isSharedCheck_2458_ = !lean_is_exclusive(v_traceState_2432_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2447_ = v_traceState_2432_;
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_traces_2445_);
lean_dec(v_traceState_2432_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2458_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2449_; lean_object* v___x_2451_; 
v___x_2449_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2395_, v_traces_2445_);
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
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v_env_2433_);
lean_ctor_set(v_reuseFailAlloc_2456_, 1, v_nextMacroScope_2434_);
lean_ctor_set(v_reuseFailAlloc_2456_, 2, v_ngen_2435_);
lean_ctor_set(v_reuseFailAlloc_2456_, 3, v_auxDeclNGen_2436_);
lean_ctor_set(v_reuseFailAlloc_2456_, 4, v___x_2451_);
lean_ctor_set(v_reuseFailAlloc_2456_, 5, v_cache_2437_);
lean_ctor_set(v_reuseFailAlloc_2456_, 6, v_messages_2438_);
lean_ctor_set(v_reuseFailAlloc_2456_, 7, v_infoState_2439_);
lean_ctor_set(v_reuseFailAlloc_2456_, 8, v_snapshotTasks_2440_);
v___x_2453_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2454_ = lean_st_ref_set(v___y_2399_, v___x_2453_);
v___x_2455_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2401_);
return v___x_2455_;
}
}
}
}
}
else
{
goto v___jp_2424_;
}
}
else
{
goto v___jp_2424_;
}
}
v___jp_2460_:
{
double v___x_2462_; double v___x_2463_; double v___x_2464_; uint8_t v___x_2465_; 
v___x_2462_ = lean_unbox_float(v_snd_2410_);
v___x_2463_ = lean_unbox_float(v_fst_2409_);
v___x_2464_ = lean_float_sub(v___x_2462_, v___x_2463_);
v___x_2465_ = lean_float_decLt(v___y_2461_, v___x_2464_);
v___y_2430_ = v___x_2465_;
goto v___jp_2429_;
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
lean_object* v___y_2503_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v___y_2516_; lean_object* v_a_2517_; lean_object* v___y_2521_; lean_object* v___y_2522_; uint8_t v___y_2523_; lean_object* v___y_2534_; lean_object* v_a_2535_; lean_object* v_options_2538_; uint8_t v_hasTrace_2539_; 
v_options_2538_ = lean_ctor_get(v___y_2499_, 2);
v_hasTrace_2539_ = lean_ctor_get_uint8(v_options_2538_, sizeof(void*)*1);
if (v_hasTrace_2539_ == 0)
{
lean_object* v_cancelTk_x3f_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___x_2497_);
lean_dec(v___x_2495_);
v_cancelTk_x3f_2540_ = lean_ctor_get(v___y_2499_, 12);
lean_inc(v_decl_2494_);
v___x_2541_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; lean_object* v_env_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec_ref_known(v___x_2541_, 1);
v___x_2542_ = lean_st_ref_get(v___y_2500_);
v_env_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_env_2543_);
lean_dec(v___x_2542_);
v___x_2544_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2543_, v_options_2538_, v_decl_2494_, v_cancelTk_x3f_2540_);
v___x_2545_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2544_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
lean_dec(v_decl_2494_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2546_, v___y_2500_);
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
v___y_2534_ = v___x_2553_;
v_a_2535_ = v_a_2548_;
goto v___jp_2533_;
}
}
}
}
else
{
lean_dec(v_decl_2494_);
return v___x_2541_;
}
}
else
{
lean_object* v_cancelTk_x3f_2556_; lean_object* v_inheritedTraceOptions_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_a_2564_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2596_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v_a_2607_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v_a_2624_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v_a_2641_; 
v_cancelTk_x3f_2556_ = lean_ctor_get(v___y_2499_, 12);
v_inheritedTraceOptions_2557_ = lean_ctor_get(v___y_2499_, 13);
v___x_2558_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2495_);
v___x_2559_ = l_Lean_Name_append(v___x_2558_, v___x_2495_);
v___x_2560_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2557_, v_options_2538_, v___x_2559_);
lean_dec(v___x_2559_);
if (v___x_2560_ == 0)
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = l_Lean_trace_profiler;
v___x_2670_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2538_, v___x_2669_);
if (v___x_2670_ == 0)
{
lean_object* v___x_2671_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___x_2497_);
lean_dec(v___x_2495_);
lean_inc(v_decl_2494_);
v___x_2671_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2672_; lean_object* v_env_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref_known(v___x_2671_, 1);
v___x_2672_ = lean_st_ref_get(v___y_2500_);
v_env_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref(v_env_2673_);
lean_dec(v___x_2672_);
v___x_2674_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2673_, v_options_2538_, v_decl_2494_, v_cancelTk_x3f_2556_);
v___x_2675_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2674_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
lean_dec(v_decl_2494_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2676_, v___y_2500_);
return v___x_2677_;
}
else
{
lean_object* v_a_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2678_ = lean_ctor_get(v___x_2675_, 0);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2675_);
if (v_isSharedCheck_2685_ == 0)
{
v___x_2680_ = v___x_2675_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_inc(v_a_2678_);
lean_dec(v___x_2675_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
lean_inc(v_a_2678_);
if (v_isShared_2681_ == 0)
{
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2678_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
v___y_2516_ = v___x_2683_;
v_a_2517_ = v_a_2678_;
goto v___jp_2515_;
}
}
}
}
else
{
lean_dec(v_decl_2494_);
return v___x_2671_;
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
v___x_2566_ = lean_float_of_nat(v___y_2563_);
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
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2538_, v___x_2560_, v___y_2562_, v___f_2498_, v___x_2574_, v___y_2499_, v___y_2500_);
return v___x_2575_;
}
v___jp_2576_:
{
lean_object* v___x_2580_; 
v___x_2580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2580_, 0, v_a_2579_);
v___y_2562_ = v___y_2578_;
v___y_2563_ = v___y_2577_;
v_a_2564_ = v___x_2580_;
goto v___jp_2561_;
}
v___jp_2581_:
{
lean_object* v___x_2585_; 
v___x_2585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2585_, 0, v_a_2584_);
v___y_2562_ = v___y_2583_;
v___y_2563_ = v___y_2582_;
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
v___y_2582_ = v___y_2588_;
v___y_2583_ = v___y_2587_;
v_a_2584_ = v_a_2590_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___y_2589_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___y_2589_, 1);
v___y_2577_ = v___y_2588_;
v___y_2578_ = v___y_2587_;
v_a_2579_ = v_a_2591_;
goto v___jp_2576_;
}
}
v___jp_2592_:
{
if (v___y_2596_ == 0)
{
lean_object* v___x_2597_; 
v___x_2597_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_dec_ref_known(v___x_2597_, 1);
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2593_;
v_a_2579_ = v___y_2595_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v___y_2595_);
v___y_2587_ = v___y_2593_;
v___y_2588_ = v___y_2594_;
v___y_2589_ = v___x_2597_;
goto v___jp_2586_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2593_;
v_a_2579_ = v___y_2595_;
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
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___y_2599_;
v___y_2595_ = v_a_2601_;
v___y_2596_ = v___x_2603_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___y_2599_;
v___y_2595_ = v_a_2601_;
v___y_2596_ = v___x_2602_;
goto v___jp_2592_;
}
}
v___jp_2604_:
{
lean_object* v___x_2608_; double v___x_2609_; double v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; 
v___x_2608_ = lean_io_get_num_heartbeats();
v___x_2609_ = lean_float_of_nat(v___y_2606_);
v___x_2610_ = lean_float_of_nat(v___x_2608_);
v___x_2611_ = lean_box_float(v___x_2609_);
v___x_2612_ = lean_box_float(v___x_2610_);
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2611_);
lean_ctor_set(v___x_2613_, 1, v___x_2612_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v_a_2607_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2538_, v___x_2560_, v___y_2605_, v___f_2498_, v___x_2614_, v___y_2499_, v___y_2500_);
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
v___x_2637_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_dec_ref_known(v___x_2637_, 1);
v___y_2617_ = v___y_2633_;
v___y_2618_ = v___y_2634_;
v_a_2619_ = v___y_2635_;
goto v___jp_2616_;
}
else
{
lean_dec_ref(v___y_2635_);
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2634_;
v___y_2629_ = v___x_2637_;
goto v___jp_2626_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2617_ = v___y_2633_;
v___y_2618_ = v___y_2634_;
v_a_2619_ = v___y_2635_;
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
v___y_2633_ = v___y_2639_;
v___y_2634_ = v___y_2640_;
v___y_2635_ = v_a_2641_;
v___y_2636_ = v___x_2643_;
goto v___jp_2632_;
}
else
{
v___y_2633_ = v___y_2639_;
v___y_2634_ = v___y_2640_;
v___y_2635_ = v_a_2641_;
v___y_2636_ = v___x_2642_;
goto v___jp_2632_;
}
}
v___jp_2644_:
{
lean_object* v___x_2645_; lean_object* v_a_2646_; lean_object* v___x_2647_; uint8_t v___x_2648_; 
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2500_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2648_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2538_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2494_);
v___x_2650_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v_env_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2651_ = lean_st_ref_get(v___y_2500_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v___x_2653_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2652_, v_options_2538_, v_decl_2494_, v_cancelTk_x3f_2556_);
v___x_2654_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2653_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v_a_2657_; 
lean_dec(v_decl_2494_);
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2655_, v___y_2500_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v___y_2582_ = v___x_2649_;
v___y_2583_ = v_a_2646_;
v_a_2584_ = v_a_2657_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2654_, 1);
v___y_2599_ = v___x_2649_;
v___y_2600_ = v_a_2646_;
v_a_2601_ = v_a_2658_;
goto v___jp_2598_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2587_ = v_a_2646_;
v___y_2588_ = v___x_2649_;
v___y_2589_ = v___x_2650_;
goto v___jp_2586_;
}
}
else
{
lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2659_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2494_);
v___x_2660_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; lean_object* v_env_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec_ref_known(v___x_2660_, 1);
v___x_2661_ = lean_st_ref_get(v___y_2500_);
v_env_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_ref(v_env_2662_);
lean_dec(v___x_2661_);
v___x_2663_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2662_, v_options_2538_, v_decl_2494_, v_cancelTk_x3f_2556_);
v___x_2664_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2663_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; 
lean_dec(v_decl_2494_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2665_, v___y_2500_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v___y_2622_ = v_a_2646_;
v___y_2623_ = v___x_2659_;
v_a_2624_ = v_a_2667_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2668_; 
v_a_2668_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2664_, 1);
v___y_2639_ = v_a_2646_;
v___y_2640_ = v___x_2659_;
v_a_2641_ = v_a_2668_;
goto v___jp_2638_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2627_ = v_a_2646_;
v___y_2628_ = v___x_2659_;
v___y_2629_ = v___x_2660_;
goto v___jp_2626_;
}
}
}
}
v___jp_2502_:
{
if (v___y_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec_ref(v___y_2503_);
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
lean_ctor_set(v___x_2508_, 0, v___y_2504_);
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___y_2504_);
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
lean_dec_ref(v___y_2504_);
return v___x_2506_;
}
}
else
{
lean_dec_ref(v___y_2504_);
lean_dec(v_decl_2494_);
return v___y_2503_;
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
v___y_2503_ = v___y_2516_;
v___y_2504_ = v_a_2517_;
v___y_2505_ = v___x_2519_;
goto v___jp_2502_;
}
else
{
v___y_2503_ = v___y_2516_;
v___y_2504_ = v_a_2517_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2686_, lean_object* v___x_2687_, lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___f_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___x_7927__boxed_2694_; lean_object* v_res_2695_; 
v___x_7927__boxed_2694_ = lean_unbox(v___x_2688_);
v_res_2695_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2686_, v___x_2687_, v___x_7927__boxed_2694_, v___x_2689_, v___f_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_options_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; uint8_t v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___f_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_options_2704_ = lean_ctor_get(v_a_2701_, 2);
lean_inc(v_decl_2700_);
v___f_2705_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2705_, 0, v_decl_2700_);
v___x_2706_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2707_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2708_ = 1;
v___x_2709_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2710_ = lean_box(v___x_2708_);
v___f_2711_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2711_, 0, v_decl_2700_);
lean_closure_set(v___f_2711_, 1, v___x_2707_);
lean_closure_set(v___f_2711_, 2, v___x_2710_);
lean_closure_set(v___f_2711_, 3, v___x_2709_);
lean_closure_set(v___f_2711_, 4, v___f_2705_);
v___x_2712_ = lean_box(0);
v___x_2713_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2706_, v_options_2704_, v___f_2711_, v___x_2712_, v_a_2701_, v_a_2702_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v_res_2718_; 
v_res_2718_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2714_, v_a_2715_, v_a_2716_);
lean_dec(v_a_2716_);
lean_dec_ref(v_a_2715_);
return v_res_2718_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2719_, lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2720_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_){
_start:
{
lean_object* v_res_2730_; 
v_res_2730_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2725_, v_x_2726_, v___y_2727_, v___y_2728_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2731_, lean_object* v_a_2732_, lean_object* v___y_2733_, lean_object* v_a_x3f_2734_){
_start:
{
lean_object* v___x_2736_; lean_object* v_env_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_st_ref_get(v___y_2731_);
v_env_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc_ref(v_env_2737_);
lean_dec(v___x_2736_);
v___x_2738_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2732_, v_env_2737_);
if (lean_obj_tag(v___x_2738_) == 0)
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
v_a_2739_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2738_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2738_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
else
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2759_; 
v_a_2747_ = lean_ctor_get(v___x_2738_, 0);
v_isSharedCheck_2759_ = !lean_is_exclusive(v___x_2738_);
if (v_isSharedCheck_2759_ == 0)
{
v___x_2749_ = v___x_2738_;
v_isShared_2750_ = v_isSharedCheck_2759_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2738_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2759_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v_ref_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2757_; 
v_ref_2751_ = lean_ctor_get(v___y_2733_, 5);
v___x_2752_ = lean_io_error_to_string(v_a_2747_);
v___x_2753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2753_, 0, v___x_2752_);
v___x_2754_ = l_Lean_MessageData_ofFormat(v___x_2753_);
lean_inc(v_ref_2751_);
v___x_2755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2755_, 0, v_ref_2751_);
lean_ctor_set(v___x_2755_, 1, v___x_2754_);
if (v_isShared_2750_ == 0)
{
lean_ctor_set(v___x_2749_, 0, v___x_2755_);
v___x_2757_ = v___x_2749_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
return v___x_2757_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2760_, lean_object* v_a_2761_, lean_object* v___y_2762_, lean_object* v_a_x3f_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2760_, v_a_2761_, v___y_2762_, v_a_x3f_2763_);
lean_dec(v_a_x3f_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2760_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2766_, lean_object* v_a_2767_, lean_object* v_decl_2768_, lean_object* v_x_2769_, lean_object* v___y_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v___x_2773_; lean_object* v_r_2774_; 
v___x_2773_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2766_, v___y_2771_);
lean_dec_ref(v___x_2773_);
v_r_2774_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2768_, v___y_2770_, v___y_2771_);
if (lean_obj_tag(v_r_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2791_; 
v_a_2775_ = lean_ctor_get(v_r_2774_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v_r_2774_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2777_ = v_r_2774_;
v_isShared_2778_ = v_isSharedCheck_2791_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v_r_2774_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2791_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
lean_inc(v_a_2775_);
if (v_isShared_2778_ == 0)
{
lean_ctor_set_tag(v___x_2777_, 1);
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
lean_object* v___x_2781_; 
v___x_2781_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2771_, v_a_2767_, v___y_2770_, v___x_2780_);
lean_dec_ref(v___x_2780_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v___x_2783_; uint8_t v_isShared_2784_; uint8_t v_isSharedCheck_2788_; 
v_isSharedCheck_2788_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2788_ == 0)
{
lean_object* v_unused_2789_; 
v_unused_2789_ = lean_ctor_get(v___x_2781_, 0);
lean_dec(v_unused_2789_);
v___x_2783_ = v___x_2781_;
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
else
{
lean_dec(v___x_2781_);
v___x_2783_ = lean_box(0);
v_isShared_2784_ = v_isSharedCheck_2788_;
goto v_resetjp_2782_;
}
v_resetjp_2782_:
{
lean_object* v___x_2786_; 
if (v_isShared_2784_ == 0)
{
lean_ctor_set(v___x_2783_, 0, v_a_2775_);
v___x_2786_ = v___x_2783_;
goto v_reusejp_2785_;
}
else
{
lean_object* v_reuseFailAlloc_2787_; 
v_reuseFailAlloc_2787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2787_, 0, v_a_2775_);
v___x_2786_ = v_reuseFailAlloc_2787_;
goto v_reusejp_2785_;
}
v_reusejp_2785_:
{
return v___x_2786_;
}
}
}
else
{
lean_dec(v_a_2775_);
return v___x_2781_;
}
}
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; 
v_a_2792_ = lean_ctor_get(v_r_2774_, 0);
lean_inc(v_a_2792_);
lean_dec_ref_known(v_r_2774_, 1);
v___x_2793_ = lean_box(0);
v___x_2794_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2771_, v_a_2767_, v___y_2770_, v___x_2793_);
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
lean_ctor_set_tag(v___x_2796_, 1);
lean_ctor_set(v___x_2796_, 0, v_a_2792_);
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2792_);
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
lean_dec(v_a_2792_);
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2803_, lean_object* v_a_2804_, lean_object* v_decl_2805_, lean_object* v_x_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2803_, v_a_2804_, v_decl_2805_, v_x_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v_x_2806_);
return v_res_2810_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2813_ = l_Lean_stringToMessageData(v___x_2812_);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2814_, lean_object* v_x_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2819_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2820_ = l_Lean_Declaration_getNames(v_decl_2814_);
v___x_2821_ = lean_box(0);
v___x_2822_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2820_, v___x_2821_);
v___x_2823_ = l_Lean_MessageData_ofList(v___x_2822_);
v___x_2824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2824_, 0, v___x_2819_);
lean_ctor_set(v___x_2824_, 1, v___x_2823_);
v___x_2825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2826_, lean_object* v_x_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2826_, v_x_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec_ref(v_x_2827_);
return v_res_2831_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2834_, lean_object* v_msg_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_ref_2839_; lean_object* v___x_2840_; lean_object* v_a_2841_; lean_object* v___x_2843_; uint8_t v_isShared_2844_; uint8_t v_isSharedCheck_2885_; 
v_ref_2839_ = lean_ctor_get(v___y_2836_, 5);
v___x_2840_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2835_, v___y_2836_, v___y_2837_);
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2843_ = v___x_2840_;
v_isShared_2844_ = v_isSharedCheck_2885_;
goto v_resetjp_2842_;
}
else
{
lean_inc(v_a_2841_);
lean_dec(v___x_2840_);
v___x_2843_ = lean_box(0);
v_isShared_2844_ = v_isSharedCheck_2885_;
goto v_resetjp_2842_;
}
v_resetjp_2842_:
{
lean_object* v___x_2845_; lean_object* v_traceState_2846_; lean_object* v_env_2847_; lean_object* v_nextMacroScope_2848_; lean_object* v_ngen_2849_; lean_object* v_auxDeclNGen_2850_; lean_object* v_cache_2851_; lean_object* v_messages_2852_; lean_object* v_infoState_2853_; lean_object* v_snapshotTasks_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2884_; 
v___x_2845_ = lean_st_ref_take(v___y_2837_);
v_traceState_2846_ = lean_ctor_get(v___x_2845_, 4);
v_env_2847_ = lean_ctor_get(v___x_2845_, 0);
v_nextMacroScope_2848_ = lean_ctor_get(v___x_2845_, 1);
v_ngen_2849_ = lean_ctor_get(v___x_2845_, 2);
v_auxDeclNGen_2850_ = lean_ctor_get(v___x_2845_, 3);
v_cache_2851_ = lean_ctor_get(v___x_2845_, 5);
v_messages_2852_ = lean_ctor_get(v___x_2845_, 6);
v_infoState_2853_ = lean_ctor_get(v___x_2845_, 7);
v_snapshotTasks_2854_ = lean_ctor_get(v___x_2845_, 8);
v_isSharedCheck_2884_ = !lean_is_exclusive(v___x_2845_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2856_ = v___x_2845_;
v_isShared_2857_ = v_isSharedCheck_2884_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_snapshotTasks_2854_);
lean_inc(v_infoState_2853_);
lean_inc(v_messages_2852_);
lean_inc(v_cache_2851_);
lean_inc(v_traceState_2846_);
lean_inc(v_auxDeclNGen_2850_);
lean_inc(v_ngen_2849_);
lean_inc(v_nextMacroScope_2848_);
lean_inc(v_env_2847_);
lean_dec(v___x_2845_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2884_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
uint64_t v_tid_2858_; lean_object* v_traces_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2883_; 
v_tid_2858_ = lean_ctor_get_uint64(v_traceState_2846_, sizeof(void*)*1);
v_traces_2859_ = lean_ctor_get(v_traceState_2846_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v_traceState_2846_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2861_ = v_traceState_2846_;
v_isShared_2862_ = v_isSharedCheck_2883_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_traces_2859_);
lean_dec(v_traceState_2846_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2883_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2863_; double v___x_2864_; uint8_t v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2863_ = lean_box(0);
v___x_2864_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2865_ = 0;
v___x_2866_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2867_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2867_, 0, v_cls_2834_);
lean_ctor_set(v___x_2867_, 1, v___x_2863_);
lean_ctor_set(v___x_2867_, 2, v___x_2866_);
lean_ctor_set_float(v___x_2867_, sizeof(void*)*3, v___x_2864_);
lean_ctor_set_float(v___x_2867_, sizeof(void*)*3 + 8, v___x_2864_);
lean_ctor_set_uint8(v___x_2867_, sizeof(void*)*3 + 16, v___x_2865_);
v___x_2868_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2869_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2869_, 0, v___x_2867_);
lean_ctor_set(v___x_2869_, 1, v_a_2841_);
lean_ctor_set(v___x_2869_, 2, v___x_2868_);
lean_inc(v_ref_2839_);
v___x_2870_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2870_, 0, v_ref_2839_);
lean_ctor_set(v___x_2870_, 1, v___x_2869_);
v___x_2871_ = l_Lean_PersistentArray_push___redArg(v_traces_2859_, v___x_2870_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2871_);
v___x_2873_ = v___x_2861_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2871_);
lean_ctor_set_uint64(v_reuseFailAlloc_2882_, sizeof(void*)*1, v_tid_2858_);
v___x_2873_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2875_; 
if (v_isShared_2857_ == 0)
{
lean_ctor_set(v___x_2856_, 4, v___x_2873_);
v___x_2875_ = v___x_2856_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v_env_2847_);
lean_ctor_set(v_reuseFailAlloc_2881_, 1, v_nextMacroScope_2848_);
lean_ctor_set(v_reuseFailAlloc_2881_, 2, v_ngen_2849_);
lean_ctor_set(v_reuseFailAlloc_2881_, 3, v_auxDeclNGen_2850_);
lean_ctor_set(v_reuseFailAlloc_2881_, 4, v___x_2873_);
lean_ctor_set(v_reuseFailAlloc_2881_, 5, v_cache_2851_);
lean_ctor_set(v_reuseFailAlloc_2881_, 6, v_messages_2852_);
lean_ctor_set(v_reuseFailAlloc_2881_, 7, v_infoState_2853_);
lean_ctor_set(v_reuseFailAlloc_2881_, 8, v_snapshotTasks_2854_);
v___x_2875_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2879_; 
v___x_2876_ = lean_st_ref_set(v___y_2837_, v___x_2875_);
v___x_2877_ = lean_box(0);
if (v_isShared_2844_ == 0)
{
lean_ctor_set(v___x_2843_, 0, v___x_2877_);
v___x_2879_ = v___x_2843_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2877_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2886_, lean_object* v_msg_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2886_, v_msg_2887_, v___y_2888_, v___y_2889_);
lean_dec(v___y_2889_);
lean_dec_ref(v___y_2888_);
return v_res_2891_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; 
v___x_2893_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2894_ = l_Lean_stringToMessageData(v___x_2893_);
return v___x_2894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2895_, lean_object* v_cls_2896_, lean_object* v_x_2897_, lean_object* v___y_2898_, lean_object* v___y_2899_){
_start:
{
lean_object* v_options_2901_; uint8_t v_hasTrace_2902_; 
v_options_2901_ = lean_ctor_get(v___y_2898_, 2);
v_hasTrace_2902_ = lean_ctor_get_uint8(v_options_2901_, sizeof(void*)*1);
if (v_hasTrace_2902_ == 0)
{
lean_object* v___x_2903_; 
lean_dec(v_cls_2896_);
v___x_2903_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2895_, v___y_2898_, v___y_2899_);
return v___x_2903_;
}
else
{
lean_object* v_inheritedTraceOptions_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_inheritedTraceOptions_2904_ = lean_ctor_get(v___y_2898_, 13);
v___x_2905_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2896_);
v___x_2906_ = l_Lean_Name_append(v___x_2905_, v_cls_2896_);
v___x_2907_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2904_, v_options_2901_, v___x_2906_);
lean_dec(v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_dec(v_cls_2896_);
v___x_2908_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2895_, v___y_2898_, v___y_2899_);
return v___x_2908_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2910_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2896_, v___x_2909_, v___y_2898_, v___y_2899_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v___x_2911_; 
lean_dec_ref_known(v___x_2910_, 1);
v___x_2911_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2895_, v___y_2898_, v___y_2899_);
return v___x_2911_;
}
else
{
lean_dec(v_decl_2895_);
return v___x_2910_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2912_, lean_object* v_cls_2913_, lean_object* v_x_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_, lean_object* v___y_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2912_, v_cls_2913_, v_x_2914_, v___y_2915_, v___y_2916_);
lean_dec(v___y_2916_);
lean_dec_ref(v___y_2915_);
lean_dec(v_x_2914_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_options_2922_; uint8_t v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v_options_2922_ = lean_ctor_get(v___y_2920_, 2);
v___x_2923_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2922_, v_opt_2919_);
v___x_2924_ = lean_box(v___x_2923_);
v___x_2925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2925_, 0, v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_){
_start:
{
lean_object* v_res_2929_; 
v_res_2929_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2926_, v___y_2927_);
lean_dec_ref(v___y_2927_);
lean_dec_ref(v_opt_2926_);
return v_res_2929_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2930_){
_start:
{
if (lean_obj_tag(v_x_2930_) == 0)
{
uint8_t v___x_2931_; 
v___x_2931_ = 1;
return v___x_2931_;
}
else
{
lean_object* v_head_2932_; lean_object* v_tail_2933_; uint8_t v___x_2934_; 
v_head_2932_ = lean_ctor_get(v_x_2930_, 0);
v_tail_2933_ = lean_ctor_get(v_x_2930_, 1);
v___x_2934_ = l_Lean_isPrivateName(v_head_2932_);
if (v___x_2934_ == 0)
{
return v___x_2934_;
}
else
{
v_x_2930_ = v_tail_2933_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2936_){
_start:
{
uint8_t v_res_2937_; lean_object* v_r_2938_; 
v_res_2937_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2936_);
lean_dec(v_x_2936_);
v_r_2938_ = lean_box(v_res_2937_);
return v_r_2938_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2945_ = l_Lean_stringToMessageData(v___x_2944_);
return v___x_2945_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2948_ = l_Lean_stringToMessageData(v___x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2951_ = l_Lean_stringToMessageData(v___x_2950_);
return v___x_2951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2952_, uint8_t v_hasTrace_2953_, uint8_t v___x_2954_, lean_object* v___x_2955_, lean_object* v_cls_2956_, lean_object* v___x_2957_, lean_object* v_____x_2958_, lean_object* v_exportedInfo_x3f_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v_a_2966_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v_a_2979_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v_snd_3062_; lean_object* v_fst_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3190_; 
v_snd_3062_ = lean_ctor_get(v_____x_2958_, 1);
v_fst_3063_ = lean_ctor_get(v_____x_2958_, 0);
v_isSharedCheck_3190_ = !lean_is_exclusive(v_____x_2958_);
if (v_isSharedCheck_3190_ == 0)
{
v___x_3065_ = v_____x_2958_;
v_isShared_3066_ = v_isSharedCheck_3190_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_snd_3062_);
lean_inc(v_fst_3063_);
lean_dec(v_____x_2958_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3190_;
goto v_resetjp_3064_;
}
v___jp_2963_:
{
lean_object* v___x_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
v___x_2967_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2964_, v___y_2965_);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v___x_2967_, 0);
lean_dec(v_unused_2975_);
v___x_2969_ = v___x_2967_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_dec(v___x_2967_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
lean_ctor_set_tag(v___x_2969_, 1);
lean_ctor_set(v___x_2969_, 0, v_a_2966_);
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2966_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
v___jp_2976_:
{
lean_object* v___x_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
v___x_2980_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2977_, v___y_2978_);
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
lean_ctor_set(v___x_2982_, 0, v_a_2979_);
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v___x_3000_; 
lean_inc_ref(v___y_2994_);
v___x_3000_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2990_, v___y_2994_, v___y_2996_, v___y_2999_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref_known(v___x_3000_, 1);
lean_inc_ref(v___y_2991_);
v___x_3001_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2991_, v___y_2997_);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3047_ == 0)
{
lean_object* v_unused_3048_; 
v_unused_3048_ = lean_ctor_get(v___x_3001_, 0);
lean_dec(v_unused_3048_);
v___x_3003_ = v___x_3001_;
v_isShared_3004_ = v_isSharedCheck_3047_;
goto v_resetjp_3002_;
}
else
{
lean_dec(v___x_3001_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3047_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v_options_3005_; lean_object* v___x_3006_; uint8_t v___x_3007_; 
v_options_3005_ = lean_ctor_get(v___y_2998_, 2);
v___x_3006_ = l_Lean_Elab_async;
v___x_3007_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v_r_3009_; 
lean_del_object(v___x_3003_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2992_);
v___x_3008_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2994_, v___y_2997_);
lean_dec_ref(v___x_3008_);
v_r_3009_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2952_, v___y_2998_, v___y_2997_);
if (lean_obj_tag(v_r_3009_) == 0)
{
lean_object* v_a_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3019_; 
v_a_3010_ = lean_ctor_get(v_r_3009_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v_r_3009_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3012_ = v_r_3009_;
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_a_3010_);
lean_dec(v_r_3009_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3019_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3015_; 
lean_inc(v_a_3010_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set_tag(v___x_3012_, 1);
v___x_3015_ = v___x_3012_;
goto v_reusejp_3014_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3010_);
v___x_3015_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3014_;
}
v_reusejp_3014_:
{
lean_object* v___x_3016_; 
v___x_3016_ = lean_apply_2(v___y_2995_, v___x_3015_, lean_box(0));
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
v___y_2977_ = v___y_2991_;
v___y_2978_ = v___y_2997_;
v_a_2979_ = v_a_3010_;
goto v___jp_2976_;
}
else
{
lean_object* v_a_3017_; 
lean_dec(v_a_3010_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___y_2964_ = v___y_2991_;
v___y_2965_ = v___y_2997_;
v_a_2966_ = v_a_3017_;
goto v___jp_2963_;
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3020_ = lean_ctor_get(v_r_3009_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v_r_3009_, 1);
v___x_3021_ = lean_box(0);
v___x_3022_ = lean_apply_2(v___y_2995_, v___x_3021_, lean_box(0));
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec_ref_known(v___x_3022_, 1);
v___y_2964_ = v___y_2991_;
v___y_2965_ = v___y_2997_;
v_a_2966_ = v_a_3020_;
goto v___jp_2963_;
}
else
{
lean_object* v_a_3023_; 
lean_dec(v_a_3020_);
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___y_2964_ = v___y_2991_;
v___y_2965_ = v___y_2997_;
v_a_2966_ = v_a_3023_;
goto v___jp_2963_;
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2991_);
lean_dec(v_decl_2952_);
v___x_3024_ = l_IO_CancelToken_new();
if (v_isShared_3004_ == 0)
{
lean_ctor_set_tag(v___x_3003_, 1);
lean_ctor_set(v___x_3003_, 0, v___x_3024_);
v___x_3026_ = v___x_3003_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3027_ = lean_unsigned_to_nat(0u);
v___x_3028_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3029_ = l_Lean_Name_toString(v___x_3028_, v_hasTrace_2953_);
lean_inc_ref(v___x_3026_);
v___x_3030_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2992_, v___x_3026_, v___x_3029_, v___y_2998_, v___y_2997_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_checked_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v_checked_3032_ = lean_ctor_get(v___y_2993_, 2);
lean_inc_ref(v_checked_3032_);
lean_dec_ref(v___y_2993_);
v___x_3033_ = lean_io_map_task(v_a_3031_, v_checked_3032_, v___x_3027_, v___x_2954_);
v___x_3034_ = lean_box(0);
v___x_3035_ = lean_box(2);
v___x_3036_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3034_);
lean_ctor_set(v___x_3036_, 1, v___x_3035_);
lean_ctor_set(v___x_3036_, 2, v___x_3026_);
lean_ctor_set(v___x_3036_, 3, v___x_3033_);
v___x_3037_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3036_, v___y_2997_);
return v___x_3037_;
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v___x_3026_);
lean_dec_ref(v___y_2993_);
v_a_3038_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3030_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3030_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3061_; 
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec(v_decl_2952_);
v_a_3049_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3051_ = v___x_3000_;
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_3000_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3061_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v_ref_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3059_; 
v_ref_3053_ = lean_ctor_get(v___y_2998_, 5);
v___x_3054_ = lean_io_error_to_string(v_a_3049_);
v___x_3055_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = l_Lean_MessageData_ofFormat(v___x_3055_);
lean_inc(v_ref_3053_);
v___x_3057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3057_, 0, v_ref_3053_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 0, v___x_3057_);
v___x_3059_ = v___x_3051_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v___x_3057_);
v___x_3059_ = v_reuseFailAlloc_3060_;
goto v_reusejp_3058_;
}
v_reusejp_3058_:
{
return v___x_3059_;
}
}
}
}
v_resetjp_3064_:
{
lean_object* v_fst_3067_; lean_object* v_snd_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3189_; 
v_fst_3067_ = lean_ctor_get(v_snd_3062_, 0);
v_snd_3068_ = lean_ctor_get(v_snd_3062_, 1);
v_isSharedCheck_3189_ = !lean_is_exclusive(v_snd_3062_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3070_ = v_snd_3062_;
v_isShared_3071_ = v_isSharedCheck_3189_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_snd_3068_);
lean_inc(v_fst_3067_);
lean_dec(v_snd_3062_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3189_;
goto v_resetjp_3069_;
}
v_resetjp_3069_:
{
lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v_exportedInfo_x3f_3104_; lean_object* v___y_3105_; lean_object* v___y_3106_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___x_3179_; lean_object* v_env_3180_; uint8_t v___x_3181_; 
v___x_3179_ = lean_st_ref_get(v___y_2961_);
v_env_3180_ = lean_ctor_get(v___x_3179_, 0);
lean_inc_ref(v_env_3180_);
lean_dec(v___x_3179_);
v___x_3181_ = l_Lean_Environment_containsOnBranch(v_env_3180_, v_fst_3063_);
lean_dec_ref(v_env_3180_);
if (v___x_3181_ == 0)
{
lean_del_object(v___x_3065_);
v___y_3147_ = v___y_2960_;
v___y_3148_ = v___y_2961_;
goto v___jp_3146_;
}
else
{
lean_object* v___x_3182_; lean_object* v_env_3183_; lean_object* v___x_3184_; lean_object* v___x_3186_; 
lean_del_object(v___x_3070_);
lean_dec(v_snd_3068_);
lean_dec(v_fst_3067_);
lean_dec(v_exportedInfo_x3f_2959_);
lean_dec(v___x_2957_);
lean_dec(v_cls_2956_);
lean_dec_ref(v___x_2955_);
lean_dec(v_decl_2952_);
v___x_3182_ = lean_st_ref_get(v___y_2961_);
v_env_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc_ref(v_env_3183_);
lean_dec(v___x_3182_);
v___x_3184_ = lean_elab_environment_to_kernel_env(v_env_3183_);
if (v_isShared_3066_ == 0)
{
lean_ctor_set_tag(v___x_3065_, 1);
lean_ctor_set(v___x_3065_, 1, v_fst_3063_);
lean_ctor_set(v___x_3065_, 0, v___x_3184_);
v___x_3186_ = v___x_3065_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v___x_3184_);
lean_ctor_set(v_reuseFailAlloc_3188_, 1, v_fst_3063_);
v___x_3186_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
lean_object* v___x_3187_; 
v___x_3187_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3186_, v___y_2960_, v___y_2961_);
return v___x_3187_;
}
}
v___jp_3072_:
{
uint8_t v___x_3080_; lean_object* v___x_3081_; 
v___x_3080_ = lean_unbox(v_snd_3068_);
lean_dec(v_snd_3068_);
lean_inc_ref(v___y_3075_);
v___x_3081_ = l_Lean_Environment_addConstAsync(v___y_3075_, v_fst_3063_, v___x_3080_, v___y_3079_, v___x_2954_, v_hasTrace_2953_);
if (lean_obj_tag(v___x_3081_) == 0)
{
lean_object* v_a_3082_; lean_object* v_mainEnv_3083_; lean_object* v_asyncEnv_3084_; lean_object* v___f_3085_; lean_object* v___f_3086_; lean_object* v___x_3087_; 
lean_del_object(v___x_3070_);
v_a_3082_ = lean_ctor_get(v___x_3081_, 0);
lean_inc_n(v_a_3082_, 3);
lean_dec_ref_known(v___x_3081_, 1);
v_mainEnv_3083_ = lean_ctor_get(v_a_3082_, 0);
lean_inc_ref(v_mainEnv_3083_);
v_asyncEnv_3084_ = lean_ctor_get(v_a_3082_, 1);
lean_inc_ref_n(v_asyncEnv_3084_, 2);
lean_inc_ref(v___y_3074_);
lean_inc(v___y_3073_);
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3085_, 0, v___y_3073_);
lean_closure_set(v___f_3085_, 1, v_a_3082_);
lean_closure_set(v___f_3085_, 2, v___y_3074_);
lean_inc(v_decl_2952_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3086_, 0, v_asyncEnv_3084_);
lean_closure_set(v___f_3086_, 1, v_a_3082_);
lean_closure_set(v___f_3086_, 2, v_decl_2952_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_fst_3067_);
if (lean_obj_tag(v___y_3076_) == 0)
{
lean_inc_ref(v___x_3087_);
v___y_2990_ = v_a_3082_;
v___y_2991_ = v_mainEnv_3083_;
v___y_2992_ = v___f_3086_;
v___y_2993_ = v___y_3075_;
v___y_2994_ = v_asyncEnv_3084_;
v___y_2995_ = v___f_3085_;
v___y_2996_ = v___x_3087_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___y_3078_;
v___y_2999_ = v___x_3087_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v_a_3082_;
v___y_2991_ = v_mainEnv_3083_;
v___y_2992_ = v___f_3086_;
v___y_2993_ = v___y_3075_;
v___y_2994_ = v_asyncEnv_3084_;
v___y_2995_ = v___f_3085_;
v___y_2996_ = v___x_3087_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___y_3078_;
v___y_2999_ = v___y_3076_;
goto v___jp_2989_;
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v___y_3076_);
lean_dec_ref(v___y_3075_);
lean_dec(v_fst_3067_);
lean_dec(v_decl_2952_);
v_a_3088_ = lean_ctor_get(v___x_3081_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3081_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3090_ = v___x_3081_;
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
else
{
lean_inc(v_a_3088_);
lean_dec(v___x_3081_);
v___x_3090_ = lean_box(0);
v_isShared_3091_ = v_isSharedCheck_3102_;
goto v_resetjp_3089_;
}
v_resetjp_3089_:
{
lean_object* v_ref_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; lean_object* v___x_3097_; 
v_ref_3092_ = lean_ctor_get(v___y_3078_, 5);
v___x_3093_ = lean_io_error_to_string(v_a_3088_);
v___x_3094_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
v___x_3095_ = l_Lean_MessageData_ofFormat(v___x_3094_);
lean_inc(v_ref_3092_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set(v___x_3070_, 1, v___x_3095_);
lean_ctor_set(v___x_3070_, 0, v_ref_3092_);
v___x_3097_ = v___x_3070_;
goto v_reusejp_3096_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_ref_3092_);
lean_ctor_set(v_reuseFailAlloc_3101_, 1, v___x_3095_);
v___x_3097_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3096_;
}
v_reusejp_3096_:
{
lean_object* v___x_3099_; 
if (v_isShared_3091_ == 0)
{
lean_ctor_set(v___x_3090_, 0, v___x_3097_);
v___x_3099_ = v___x_3090_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v___x_3097_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
v___jp_3103_:
{
lean_object* v___x_3107_; 
v___x_3107_ = lean_st_ref_get(v___y_3106_);
if (lean_obj_tag(v_exportedInfo_x3f_3104_) == 0)
{
lean_object* v_env_3108_; lean_object* v___x_3109_; 
v_env_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3108_);
lean_dec(v___x_3107_);
v___x_3109_ = lean_box(0);
v___y_3073_ = v___y_3106_;
v___y_3074_ = v___y_3105_;
v___y_3075_ = v_env_3108_;
v___y_3076_ = v_exportedInfo_x3f_3104_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v___y_3105_;
v___y_3079_ = v___x_3109_;
goto v___jp_3072_;
}
else
{
lean_object* v_env_3110_; lean_object* v_val_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v_env_3110_ = lean_ctor_get(v___x_3107_, 0);
lean_inc_ref(v_env_3110_);
lean_dec(v___x_3107_);
v_val_3111_ = lean_ctor_get(v_exportedInfo_x3f_3104_, 0);
v___x_3112_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3111_);
v___x_3113_ = lean_box(v___x_3112_);
v___x_3114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3114_, 0, v___x_3113_);
v___y_3073_ = v___y_3106_;
v___y_3074_ = v___y_3105_;
v___y_3075_ = v_env_3110_;
v___y_3076_ = v_exportedInfo_x3f_3104_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v___y_3105_;
v___y_3079_ = v___x_3114_;
goto v___jp_3072_;
}
}
v___jp_3115_:
{
lean_object* v___x_3118_; 
lean_inc(v_fst_3067_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v_fst_3067_);
v_exportedInfo_x3f_3104_ = v___x_3118_;
v___y_3105_ = v___y_3116_;
v___y_3106_ = v___y_3117_;
goto v___jp_3103_;
}
v___jp_3119_:
{
lean_object* v___x_3122_; 
lean_inc(v_fst_3067_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_fst_3067_);
v_exportedInfo_x3f_3104_ = v___x_3122_;
v___y_3105_ = v___y_3120_;
v___y_3106_ = v___y_3121_;
goto v___jp_3103_;
}
v___jp_3123_:
{
lean_object* v___x_3126_; lean_object* v_env_3127_; lean_object* v_nextMacroScope_3128_; lean_object* v_ngen_3129_; lean_object* v_auxDeclNGen_3130_; lean_object* v_traceState_3131_; lean_object* v_messages_3132_; lean_object* v_infoState_3133_; lean_object* v_snapshotTasks_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3144_; 
v___x_3126_ = lean_st_ref_take(v___y_3125_);
v_env_3127_ = lean_ctor_get(v___x_3126_, 0);
v_nextMacroScope_3128_ = lean_ctor_get(v___x_3126_, 1);
v_ngen_3129_ = lean_ctor_get(v___x_3126_, 2);
v_auxDeclNGen_3130_ = lean_ctor_get(v___x_3126_, 3);
v_traceState_3131_ = lean_ctor_get(v___x_3126_, 4);
v_messages_3132_ = lean_ctor_get(v___x_3126_, 6);
v_infoState_3133_ = lean_ctor_get(v___x_3126_, 7);
v_snapshotTasks_3134_ = lean_ctor_get(v___x_3126_, 8);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3144_ == 0)
{
lean_object* v_unused_3145_; 
v_unused_3145_ = lean_ctor_get(v___x_3126_, 5);
lean_dec(v_unused_3145_);
v___x_3136_ = v___x_3126_;
v_isShared_3137_ = v_isSharedCheck_3144_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_snapshotTasks_3134_);
lean_inc(v_infoState_3133_);
lean_inc(v_messages_3132_);
lean_inc(v_traceState_3131_);
lean_inc(v_auxDeclNGen_3130_);
lean_inc(v_ngen_3129_);
lean_inc(v_nextMacroScope_3128_);
lean_inc(v_env_3127_);
lean_dec(v___x_3126_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3144_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3138_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3068_);
lean_inc(v_fst_3063_);
v___x_3139_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3138_, v_env_3127_, v_fst_3063_, v_snd_3068_);
if (v_isShared_3137_ == 0)
{
lean_ctor_set(v___x_3136_, 5, v___x_2955_);
lean_ctor_set(v___x_3136_, 0, v___x_3139_);
v___x_3141_ = v___x_3136_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3139_);
lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_nextMacroScope_3128_);
lean_ctor_set(v_reuseFailAlloc_3143_, 2, v_ngen_3129_);
lean_ctor_set(v_reuseFailAlloc_3143_, 3, v_auxDeclNGen_3130_);
lean_ctor_set(v_reuseFailAlloc_3143_, 4, v_traceState_3131_);
lean_ctor_set(v_reuseFailAlloc_3143_, 5, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_3143_, 6, v_messages_3132_);
lean_ctor_set(v_reuseFailAlloc_3143_, 7, v_infoState_3133_);
lean_ctor_set(v_reuseFailAlloc_3143_, 8, v_snapshotTasks_3134_);
v___x_3141_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3142_; 
v___x_3142_ = lean_st_ref_set(v___y_3125_, v___x_3141_);
v_exportedInfo_x3f_3104_ = v_exportedInfo_x3f_2959_;
v___y_3105_ = v___y_3124_;
v___y_3106_ = v___y_3125_;
goto v___jp_3103_;
}
}
}
v___jp_3146_:
{
lean_object* v___x_3149_; uint8_t v___x_3150_; 
lean_inc(v_decl_2952_);
v___x_3149_ = l_Lean_Declaration_getTopLevelNames(v_decl_2952_);
v___x_3150_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3149_);
lean_dec(v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec(v___x_2957_);
if (lean_obj_tag(v_exportedInfo_x3f_2959_) == 0)
{
if (v___x_2954_ == 0)
{
lean_object* v_options_3151_; uint8_t v_hasTrace_3152_; 
lean_dec_ref(v___x_2955_);
v_options_3151_ = lean_ctor_get(v___y_3147_, 2);
v_hasTrace_3152_ = lean_ctor_get_uint8(v_options_3151_, sizeof(void*)*1);
if (v_hasTrace_3152_ == 0)
{
lean_dec(v_cls_2956_);
v___y_3116_ = v___y_3147_;
v___y_3117_ = v___y_3148_;
goto v___jp_3115_;
}
else
{
lean_object* v_inheritedTraceOptions_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v_inheritedTraceOptions_3153_ = lean_ctor_get(v___y_3147_, 13);
v___x_3154_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2956_);
v___x_3155_ = l_Lean_Name_append(v___x_3154_, v_cls_2956_);
v___x_3156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3153_, v_options_3151_, v___x_3155_);
lean_dec(v___x_3155_);
if (v___x_3156_ == 0)
{
lean_dec(v_cls_2956_);
v___y_3116_ = v___y_3147_;
v___y_3117_ = v___y_3148_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3158_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2956_, v___x_3157_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_dec_ref_known(v___x_3158_, 1);
v___y_3116_ = v___y_3147_;
v___y_3117_ = v___y_3148_;
goto v___jp_3115_;
}
else
{
lean_del_object(v___x_3070_);
lean_dec(v_snd_3068_);
lean_dec(v_fst_3067_);
lean_dec(v_fst_3063_);
lean_dec(v_decl_2952_);
return v___x_3158_;
}
}
}
}
else
{
lean_dec(v_cls_2956_);
v___y_3124_ = v___y_3147_;
v___y_3125_ = v___y_3148_;
goto v___jp_3123_;
}
}
else
{
lean_dec(v_cls_2956_);
v___y_3124_ = v___y_3147_;
v___y_3125_ = v___y_3148_;
goto v___jp_3123_;
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v_a_3161_; uint8_t v___x_3162_; 
lean_dec(v_exportedInfo_x3f_2959_);
lean_dec_ref(v___x_2955_);
v___x_3159_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3160_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3159_, v___y_3147_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___x_3160_);
v___x_3162_ = lean_unbox(v_a_3161_);
lean_dec(v_a_3161_);
if (v___x_3162_ == 0)
{
lean_object* v_options_3163_; uint8_t v_hasTrace_3164_; 
v_options_3163_ = lean_ctor_get(v___y_3147_, 2);
v_hasTrace_3164_ = lean_ctor_get_uint8(v_options_3163_, sizeof(void*)*1);
if (v_hasTrace_3164_ == 0)
{
lean_dec(v_cls_2956_);
v_exportedInfo_x3f_3104_ = v___x_2957_;
v___y_3105_ = v___y_3147_;
v___y_3106_ = v___y_3148_;
goto v___jp_3103_;
}
else
{
lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_inheritedTraceOptions_3165_ = lean_ctor_get(v___y_3147_, 13);
v___x_3166_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2956_);
v___x_3167_ = l_Lean_Name_append(v___x_3166_, v_cls_2956_);
v___x_3168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3165_, v_options_3163_, v___x_3167_);
lean_dec(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_dec(v_cls_2956_);
v_exportedInfo_x3f_3104_ = v___x_2957_;
v___y_3105_ = v___y_3147_;
v___y_3106_ = v___y_3148_;
goto v___jp_3103_;
}
else
{
lean_object* v___x_3169_; lean_object* v___x_3170_; 
v___x_3169_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3170_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2956_, v___x_3169_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3170_) == 0)
{
lean_dec_ref_known(v___x_3170_, 1);
v_exportedInfo_x3f_3104_ = v___x_2957_;
v___y_3105_ = v___y_3147_;
v___y_3106_ = v___y_3148_;
goto v___jp_3103_;
}
else
{
lean_del_object(v___x_3070_);
lean_dec(v_snd_3068_);
lean_dec(v_fst_3067_);
lean_dec(v_fst_3063_);
lean_dec(v___x_2957_);
lean_dec(v_decl_2952_);
return v___x_3170_;
}
}
}
}
else
{
lean_object* v_options_3171_; uint8_t v_hasTrace_3172_; 
lean_dec(v___x_2957_);
v_options_3171_ = lean_ctor_get(v___y_3147_, 2);
v_hasTrace_3172_ = lean_ctor_get_uint8(v_options_3171_, sizeof(void*)*1);
if (v_hasTrace_3172_ == 0)
{
lean_dec(v_cls_2956_);
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3148_;
goto v___jp_3119_;
}
else
{
lean_object* v_inheritedTraceOptions_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; uint8_t v___x_3176_; 
v_inheritedTraceOptions_3173_ = lean_ctor_get(v___y_3147_, 13);
v___x_3174_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2956_);
v___x_3175_ = l_Lean_Name_append(v___x_3174_, v_cls_2956_);
v___x_3176_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3173_, v_options_3171_, v___x_3175_);
lean_dec(v___x_3175_);
if (v___x_3176_ == 0)
{
lean_dec(v_cls_2956_);
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3148_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3178_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2956_, v___x_3177_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3178_) == 0)
{
lean_dec_ref_known(v___x_3178_, 1);
v___y_3120_ = v___y_3147_;
v___y_3121_ = v___y_3148_;
goto v___jp_3119_;
}
else
{
lean_del_object(v___x_3070_);
lean_dec(v_snd_3068_);
lean_dec(v_fst_3067_);
lean_dec(v_fst_3063_);
lean_dec(v_decl_2952_);
return v___x_3178_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3191_, lean_object* v_hasTrace_3192_, lean_object* v___x_3193_, lean_object* v___x_3194_, lean_object* v_cls_3195_, lean_object* v___x_3196_, lean_object* v_____x_3197_, lean_object* v_exportedInfo_x3f_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v_hasTrace_boxed_3202_; uint8_t v___x_62744__boxed_3203_; lean_object* v_res_3204_; 
v_hasTrace_boxed_3202_ = lean_unbox(v_hasTrace_3192_);
v___x_62744__boxed_3203_ = lean_unbox(v___x_3193_);
v_res_3204_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3191_, v_hasTrace_boxed_3202_, v___x_62744__boxed_3203_, v___x_3194_, v_cls_3195_, v___x_3196_, v_____x_3197_, v_exportedInfo_x3f_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
return v_res_3204_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3207_ = l_Lean_stringToMessageData(v___x_3206_);
return v___x_3207_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3210_ = l_Lean_stringToMessageData(v___x_3209_);
return v___x_3210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3211_, lean_object* v_cls_3212_, lean_object* v___x_3213_, uint8_t v___x_3214_, uint8_t v_forceExpose_3215_, lean_object* v_defn_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_){
_start:
{
lean_object* v_exportedInfo_x3f_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3233_; lean_object* v___y_3234_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v_env_3259_; lean_object* v_env_3260_; 
v___x_3242_ = lean_st_ref_get(v___y_3218_);
v___x_3243_ = lean_st_ref_get(v___y_3218_);
v_env_3259_ = lean_ctor_get(v___x_3242_, 0);
lean_inc_ref(v_env_3259_);
lean_dec(v___x_3242_);
v_env_3260_ = lean_ctor_get(v___x_3243_, 0);
lean_inc_ref(v_env_3260_);
lean_dec(v___x_3243_);
if (v_forceExpose_3215_ == 0)
{
goto v___jp_3261_;
}
else
{
if (v___x_3214_ == 0)
{
lean_dec_ref(v_env_3260_);
lean_dec_ref(v_env_3259_);
lean_dec(v_cls_3212_);
v_exportedInfo_x3f_3221_ = v___x_3213_;
v___y_3222_ = v___y_3217_;
v___y_3223_ = v___y_3218_;
goto v___jp_3220_;
}
else
{
goto v___jp_3261_;
}
}
v___jp_3220_:
{
lean_object* v_toConstantVal_3224_; lean_object* v_name_3225_; lean_object* v___x_3226_; uint8_t v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
v_toConstantVal_3224_ = lean_ctor_get(v_defn_3216_, 0);
v_name_3225_ = lean_ctor_get(v_toConstantVal_3224_, 0);
lean_inc(v_name_3225_);
v___x_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3226_, 0, v_defn_3216_);
v___x_3227_ = 0;
v___x_3228_ = lean_box(v___x_3227_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3226_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v_name_3225_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
lean_inc(v___y_3223_);
lean_inc_ref(v___y_3222_);
v___x_3231_ = lean_apply_5(v___f_3211_, v___x_3230_, v_exportedInfo_x3f_3221_, v___y_3222_, v___y_3223_, lean_box(0));
return v___x_3231_;
}
v___jp_3232_:
{
lean_object* v_toConstantVal_3235_; uint8_t v_safety_3236_; uint8_t v___x_3237_; uint8_t v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v_toConstantVal_3235_ = lean_ctor_get(v_defn_3216_, 0);
v_safety_3236_ = lean_ctor_get_uint8(v_defn_3216_, sizeof(void*)*4);
v___x_3237_ = 0;
v___x_3238_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3236_, v___x_3237_);
lean_inc_ref(v_toConstantVal_3235_);
v___x_3239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3239_, 0, v_toConstantVal_3235_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*1, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
v_exportedInfo_x3f_3221_ = v___x_3241_;
v___y_3222_ = v___y_3233_;
v___y_3223_ = v___y_3234_;
goto v___jp_3220_;
}
v___jp_3244_:
{
lean_object* v_options_3245_; uint8_t v_hasTrace_3246_; 
v_options_3245_ = lean_ctor_get(v___y_3217_, 2);
v_hasTrace_3246_ = lean_ctor_get_uint8(v_options_3245_, sizeof(void*)*1);
if (v_hasTrace_3246_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3233_ = v___y_3217_;
v___y_3234_ = v___y_3218_;
goto v___jp_3232_;
}
else
{
lean_object* v_inheritedTraceOptions_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_inheritedTraceOptions_3247_ = lean_ctor_get(v___y_3217_, 13);
v___x_3248_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3212_);
v___x_3249_ = l_Lean_Name_append(v___x_3248_, v_cls_3212_);
v___x_3250_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3247_, v_options_3245_, v___x_3249_);
lean_dec(v___x_3249_);
if (v___x_3250_ == 0)
{
lean_dec(v_cls_3212_);
v___y_3233_ = v___y_3217_;
v___y_3234_ = v___y_3218_;
goto v___jp_3232_;
}
else
{
lean_object* v_toConstantVal_3251_; lean_object* v_name_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_toConstantVal_3251_ = lean_ctor_get(v_defn_3216_, 0);
v_name_3252_ = lean_ctor_get(v_toConstantVal_3251_, 0);
v___x_3253_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3252_);
v___x_3254_ = l_Lean_MessageData_ofName(v_name_3252_);
v___x_3255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3255_, 0, v___x_3253_);
lean_ctor_set(v___x_3255_, 1, v___x_3254_);
v___x_3256_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3255_);
lean_ctor_set(v___x_3257_, 1, v___x_3256_);
v___x_3258_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3212_, v___x_3257_, v___y_3217_, v___y_3218_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_dec_ref_known(v___x_3258_, 1);
v___y_3233_ = v___y_3217_;
v___y_3234_ = v___y_3218_;
goto v___jp_3232_;
}
else
{
lean_dec_ref(v_defn_3216_);
lean_dec_ref(v___f_3211_);
return v___x_3258_;
}
}
}
}
v___jp_3261_:
{
lean_object* v___x_3262_; uint8_t v_isModule_3263_; 
v___x_3262_ = l_Lean_Environment_header(v_env_3259_);
lean_dec_ref(v_env_3259_);
v_isModule_3263_ = lean_ctor_get_uint8(v___x_3262_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3262_);
if (v_isModule_3263_ == 0)
{
lean_dec_ref(v_env_3260_);
lean_dec(v_cls_3212_);
v_exportedInfo_x3f_3221_ = v___x_3213_;
v___y_3222_ = v___y_3217_;
v___y_3223_ = v___y_3218_;
goto v___jp_3220_;
}
else
{
uint8_t v_isExporting_3264_; 
v_isExporting_3264_ = lean_ctor_get_uint8(v_env_3260_, sizeof(void*)*8);
lean_dec_ref(v_env_3260_);
if (v_isExporting_3264_ == 0)
{
lean_dec(v___x_3213_);
goto v___jp_3244_;
}
else
{
if (v___x_3214_ == 0)
{
lean_dec(v_cls_3212_);
v_exportedInfo_x3f_3221_ = v___x_3213_;
v___y_3222_ = v___y_3217_;
v___y_3223_ = v___y_3218_;
goto v___jp_3220_;
}
else
{
lean_dec(v___x_3213_);
goto v___jp_3244_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3265_, lean_object* v_cls_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v_forceExpose_3269_, lean_object* v_defn_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
uint8_t v___x_63218__boxed_3274_; uint8_t v_forceExpose_boxed_3275_; lean_object* v_res_3276_; 
v___x_63218__boxed_3274_ = lean_unbox(v___x_3268_);
v_forceExpose_boxed_3275_ = lean_unbox(v_forceExpose_3269_);
v_res_3276_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3265_, v_cls_3266_, v___x_3267_, v___x_63218__boxed_3274_, v_forceExpose_boxed_3275_, v_defn_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3277_, lean_object* v___f_3278_, lean_object* v_____r_3279_, lean_object* v_exportedInfo_x3f_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v_toConstantVal_3284_; lean_object* v_name_3285_; lean_object* v___x_3286_; uint8_t v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v_toConstantVal_3284_ = lean_ctor_get(v_val_3277_, 0);
v_name_3285_ = lean_ctor_get(v_toConstantVal_3284_, 0);
lean_inc(v_name_3285_);
v___x_3286_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3286_, 0, v_val_3277_);
v___x_3287_ = 1;
v___x_3288_ = lean_box(v___x_3287_);
v___x_3289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3286_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3290_, 0, v_name_3285_);
lean_ctor_set(v___x_3290_, 1, v___x_3289_);
lean_inc(v___y_3282_);
lean_inc_ref(v___y_3281_);
v___x_3291_ = lean_apply_5(v___f_3278_, v___x_3290_, v_exportedInfo_x3f_3280_, v___y_3281_, v___y_3282_, lean_box(0));
return v___x_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3292_, lean_object* v___f_3293_, lean_object* v_____r_3294_, lean_object* v_exportedInfo_x3f_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_res_3299_; 
v_res_3299_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3292_, v___f_3293_, v_____r_3294_, v_exportedInfo_x3f_3295_, v___y_3296_, v___y_3297_);
lean_dec(v___y_3297_);
lean_dec_ref(v___y_3296_);
return v_res_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3300_, uint8_t v___x_3301_, lean_object* v___f_3302_, lean_object* v_____r_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_toConstantVal_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_toConstantVal_3307_ = lean_ctor_get(v_val_3300_, 0);
lean_inc_ref(v_toConstantVal_3307_);
v___x_3308_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3308_, 0, v_toConstantVal_3307_);
lean_ctor_set_uint8(v___x_3308_, sizeof(void*)*1, v___x_3301_);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3309_);
v___x_3311_ = lean_box(0);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3304_);
v___x_3312_ = lean_apply_5(v___f_3302_, v___x_3311_, v___x_3310_, v___y_3304_, v___y_3305_, lean_box(0));
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3313_, lean_object* v___x_3314_, lean_object* v___f_3315_, lean_object* v_____r_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_){
_start:
{
uint8_t v___x_63337__boxed_3320_; lean_object* v_res_3321_; 
v___x_63337__boxed_3320_ = lean_unbox(v___x_3314_);
v_res_3321_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3313_, v___x_63337__boxed_3320_, v___f_3315_, v_____r_3316_, v___y_3317_, v___y_3318_);
lean_dec(v___y_3318_);
lean_dec_ref(v___y_3317_);
lean_dec_ref(v_val_3313_);
return v_res_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3322_, lean_object* v___f_3323_, lean_object* v_____r_3324_, lean_object* v_exportedInfo_x3f_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
lean_object* v_toConstantVal_3329_; lean_object* v_name_3330_; lean_object* v___x_3331_; uint8_t v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_toConstantVal_3329_ = lean_ctor_get(v_val_3322_, 0);
v_name_3330_ = lean_ctor_get(v_toConstantVal_3329_, 0);
lean_inc(v_name_3330_);
v___x_3331_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_val_3322_);
v___x_3332_ = 3;
v___x_3333_ = lean_box(v___x_3332_);
v___x_3334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3334_, 0, v___x_3331_);
lean_ctor_set(v___x_3334_, 1, v___x_3333_);
v___x_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3335_, 0, v_name_3330_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
lean_inc(v___y_3327_);
lean_inc_ref(v___y_3326_);
v___x_3336_ = lean_apply_5(v___f_3323_, v___x_3335_, v_exportedInfo_x3f_3325_, v___y_3326_, v___y_3327_, lean_box(0));
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3337_, lean_object* v___f_3338_, lean_object* v_____r_3339_, lean_object* v_exportedInfo_x3f_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_res_3344_; 
v_res_3344_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3337_, v___f_3338_, v_____r_3339_, v_exportedInfo_x3f_3340_, v___y_3341_, v___y_3342_);
lean_dec(v___y_3342_);
lean_dec_ref(v___y_3341_);
return v_res_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3345_, lean_object* v___f_3346_, lean_object* v_____r_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_toConstantVal_3351_; uint8_t v_isUnsafe_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v_toConstantVal_3351_ = lean_ctor_get(v_val_3345_, 0);
v_isUnsafe_3352_ = lean_ctor_get_uint8(v_val_3345_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3351_);
v___x_3353_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3353_, 0, v_toConstantVal_3351_);
lean_ctor_set_uint8(v___x_3353_, sizeof(void*)*1, v_isUnsafe_3352_);
v___x_3354_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3354_, 0, v___x_3353_);
v___x_3355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3355_, 0, v___x_3354_);
v___x_3356_ = lean_box(0);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
v___x_3357_ = lean_apply_5(v___f_3346_, v___x_3356_, v___x_3355_, v___y_3348_, v___y_3349_, lean_box(0));
return v___x_3357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3358_, lean_object* v___f_3359_, lean_object* v_____r_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3358_, v___f_3359_, v_____r_3360_, v___y_3361_, v___y_3362_);
lean_dec(v___y_3362_);
lean_dec_ref(v___y_3361_);
lean_dec_ref(v_val_3358_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3365_, uint8_t v___x_3366_, lean_object* v_cls_3367_, lean_object* v___x_3368_, lean_object* v___x_3369_, lean_object* v_____x_3370_, lean_object* v_exportedInfo_x3f_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v___y_3376_; lean_object* v___y_3377_; lean_object* v_a_3378_; lean_object* v___y_3389_; lean_object* v___y_3390_; lean_object* v_a_3391_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v_snd_3475_; lean_object* v_fst_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3605_; 
v_snd_3475_ = lean_ctor_get(v_____x_3370_, 1);
v_fst_3476_ = lean_ctor_get(v_____x_3370_, 0);
v_isSharedCheck_3605_ = !lean_is_exclusive(v_____x_3370_);
if (v_isSharedCheck_3605_ == 0)
{
v___x_3478_ = v_____x_3370_;
v_isShared_3479_ = v_isSharedCheck_3605_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_snd_3475_);
lean_inc(v_fst_3476_);
lean_dec(v_____x_3370_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3605_;
goto v_resetjp_3477_;
}
v___jp_3375_:
{
lean_object* v___x_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v___x_3379_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3377_, v___y_3376_);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3386_ == 0)
{
lean_object* v_unused_3387_; 
v_unused_3387_ = lean_ctor_get(v___x_3379_, 0);
lean_dec(v_unused_3387_);
v___x_3381_ = v___x_3379_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_dec(v___x_3379_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
lean_ctor_set_tag(v___x_3381_, 1);
lean_ctor_set(v___x_3381_, 0, v_a_3378_);
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3378_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
v___jp_3388_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; uint8_t v_isShared_3395_; uint8_t v_isSharedCheck_3399_; 
v___x_3392_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3390_, v___y_3389_);
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
lean_ctor_set(v___x_3394_, 0, v_a_3391_);
v___x_3397_ = v___x_3394_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v___x_3413_; 
lean_inc_ref(v___y_3411_);
v___x_3413_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3408_, v___y_3411_, v___y_3404_, v___y_3412_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v___x_3414_; lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3460_; 
lean_dec_ref_known(v___x_3413_, 1);
lean_inc_ref(v___y_3407_);
v___x_3414_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3407_, v___y_3402_);
v_isSharedCheck_3460_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3460_ == 0)
{
lean_object* v_unused_3461_; 
v_unused_3461_ = lean_ctor_get(v___x_3414_, 0);
lean_dec(v_unused_3461_);
v___x_3416_ = v___x_3414_;
v_isShared_3417_ = v_isSharedCheck_3460_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v___x_3414_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3460_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v_options_3418_; lean_object* v___x_3419_; uint8_t v___x_3420_; 
v_options_3418_ = lean_ctor_get(v___y_3403_, 2);
v___x_3419_ = l_Lean_Elab_async;
v___x_3420_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3418_, v___x_3419_);
if (v___x_3420_ == 0)
{
lean_object* v___x_3421_; lean_object* v_r_3422_; 
lean_del_object(v___x_3416_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3405_);
v___x_3421_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3411_, v___y_3402_);
lean_dec_ref(v___x_3421_);
v_r_3422_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3365_, v___y_3403_, v___y_3402_);
if (lean_obj_tag(v_r_3422_) == 0)
{
lean_object* v_a_3423_; lean_object* v___x_3425_; uint8_t v_isShared_3426_; uint8_t v_isSharedCheck_3432_; 
v_a_3423_ = lean_ctor_get(v_r_3422_, 0);
v_isSharedCheck_3432_ = !lean_is_exclusive(v_r_3422_);
if (v_isSharedCheck_3432_ == 0)
{
v___x_3425_ = v_r_3422_;
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
else
{
lean_inc(v_a_3423_);
lean_dec(v_r_3422_);
v___x_3425_ = lean_box(0);
v_isShared_3426_ = v_isSharedCheck_3432_;
goto v_resetjp_3424_;
}
v_resetjp_3424_:
{
lean_object* v___x_3428_; 
lean_inc(v_a_3423_);
if (v_isShared_3426_ == 0)
{
lean_ctor_set_tag(v___x_3425_, 1);
v___x_3428_ = v___x_3425_;
goto v_reusejp_3427_;
}
else
{
lean_object* v_reuseFailAlloc_3431_; 
v_reuseFailAlloc_3431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3431_, 0, v_a_3423_);
v___x_3428_ = v_reuseFailAlloc_3431_;
goto v_reusejp_3427_;
}
v_reusejp_3427_:
{
lean_object* v___x_3429_; 
v___x_3429_ = lean_apply_2(v___y_3406_, v___x_3428_, lean_box(0));
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref_known(v___x_3429_, 1);
v___y_3389_ = v___y_3402_;
v___y_3390_ = v___y_3407_;
v_a_3391_ = v_a_3423_;
goto v___jp_3388_;
}
else
{
lean_object* v_a_3430_; 
lean_dec(v_a_3423_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___y_3376_ = v___y_3402_;
v___y_3377_ = v___y_3407_;
v_a_3378_ = v_a_3430_;
goto v___jp_3375_;
}
}
}
}
else
{
lean_object* v_a_3433_; lean_object* v___x_3434_; lean_object* v___x_3435_; 
v_a_3433_ = lean_ctor_get(v_r_3422_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v_r_3422_, 1);
v___x_3434_ = lean_box(0);
v___x_3435_ = lean_apply_2(v___y_3406_, v___x_3434_, lean_box(0));
if (lean_obj_tag(v___x_3435_) == 0)
{
lean_dec_ref_known(v___x_3435_, 1);
v___y_3376_ = v___y_3402_;
v___y_3377_ = v___y_3407_;
v_a_3378_ = v_a_3433_;
goto v___jp_3375_;
}
else
{
lean_object* v_a_3436_; 
lean_dec(v_a_3433_);
v_a_3436_ = lean_ctor_get(v___x_3435_, 0);
lean_inc(v_a_3436_);
lean_dec_ref_known(v___x_3435_, 1);
v___y_3376_ = v___y_3402_;
v___y_3377_ = v___y_3407_;
v_a_3378_ = v_a_3436_;
goto v___jp_3375_;
}
}
}
else
{
lean_object* v___x_3437_; lean_object* v___x_3439_; 
lean_dec_ref(v___y_3411_);
lean_dec_ref(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v_decl_3365_);
v___x_3437_ = l_IO_CancelToken_new();
if (v_isShared_3417_ == 0)
{
lean_ctor_set_tag(v___x_3416_, 1);
lean_ctor_set(v___x_3416_, 0, v___x_3437_);
v___x_3439_ = v___x_3416_;
goto v_reusejp_3438_;
}
else
{
lean_object* v_reuseFailAlloc_3459_; 
v_reuseFailAlloc_3459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3459_, 0, v___x_3437_);
v___x_3439_ = v_reuseFailAlloc_3459_;
goto v_reusejp_3438_;
}
v_reusejp_3438_:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3440_ = lean_unsigned_to_nat(0u);
v___x_3441_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3442_ = l_Lean_Name_toString(v___x_3441_, v___x_3366_);
lean_inc_ref(v___x_3439_);
v___x_3443_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3410_, v___x_3439_, v___x_3442_, v___y_3403_, v___y_3402_);
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_object* v_a_3444_; lean_object* v_checked_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; 
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v_checked_3445_ = lean_ctor_get(v___y_3405_, 2);
lean_inc_ref(v_checked_3445_);
lean_dec_ref(v___y_3405_);
v___x_3446_ = lean_io_map_task(v_a_3444_, v_checked_3445_, v___x_3440_, v___y_3409_);
v___x_3447_ = lean_box(0);
v___x_3448_ = lean_box(2);
v___x_3449_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3447_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
lean_ctor_set(v___x_3449_, 2, v___x_3439_);
lean_ctor_set(v___x_3449_, 3, v___x_3446_);
v___x_3450_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3449_, v___y_3402_);
return v___x_3450_;
}
else
{
lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3458_; 
lean_dec_ref(v___x_3439_);
lean_dec_ref(v___y_3405_);
v_a_3451_ = lean_ctor_get(v___x_3443_, 0);
v_isSharedCheck_3458_ = !lean_is_exclusive(v___x_3443_);
if (v_isSharedCheck_3458_ == 0)
{
v___x_3453_ = v___x_3443_;
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3443_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3458_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3456_; 
if (v_isShared_3454_ == 0)
{
v___x_3456_ = v___x_3453_;
goto v_reusejp_3455_;
}
else
{
lean_object* v_reuseFailAlloc_3457_; 
v_reuseFailAlloc_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3457_, 0, v_a_3451_);
v___x_3456_ = v_reuseFailAlloc_3457_;
goto v_reusejp_3455_;
}
v_reusejp_3455_:
{
return v___x_3456_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3462_; lean_object* v___x_3464_; uint8_t v_isShared_3465_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec_ref(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v_decl_3365_);
v_a_3462_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3464_ = v___x_3413_;
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
else
{
lean_inc(v_a_3462_);
lean_dec(v___x_3413_);
v___x_3464_ = lean_box(0);
v_isShared_3465_ = v_isSharedCheck_3474_;
goto v_resetjp_3463_;
}
v_resetjp_3463_:
{
lean_object* v_ref_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3472_; 
v_ref_3466_ = lean_ctor_get(v___y_3403_, 5);
v___x_3467_ = lean_io_error_to_string(v_a_3462_);
v___x_3468_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3468_, 0, v___x_3467_);
v___x_3469_ = l_Lean_MessageData_ofFormat(v___x_3468_);
lean_inc(v_ref_3466_);
v___x_3470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3470_, 0, v_ref_3466_);
lean_ctor_set(v___x_3470_, 1, v___x_3469_);
if (v_isShared_3465_ == 0)
{
lean_ctor_set(v___x_3464_, 0, v___x_3470_);
v___x_3472_ = v___x_3464_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v___x_3470_);
v___x_3472_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
return v___x_3472_;
}
}
}
}
v_resetjp_3477_:
{
lean_object* v_fst_3480_; lean_object* v_snd_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3604_; 
v_fst_3480_ = lean_ctor_get(v_snd_3475_, 0);
v_snd_3481_ = lean_ctor_get(v_snd_3475_, 1);
v_isSharedCheck_3604_ = !lean_is_exclusive(v_snd_3475_);
if (v_isSharedCheck_3604_ == 0)
{
v___x_3483_ = v_snd_3475_;
v_isShared_3484_ = v_isSharedCheck_3604_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_snd_3481_);
lean_inc(v_fst_3480_);
lean_dec(v_snd_3475_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3604_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___y_3486_; lean_object* v___y_3487_; lean_object* v___y_3488_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v_exportedInfo_x3f_3518_; lean_object* v___y_3519_; lean_object* v___y_3520_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v___y_3534_; lean_object* v___y_3535_; lean_object* v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3570_; lean_object* v___y_3571_; lean_object* v___x_3594_; lean_object* v_env_3595_; uint8_t v___x_3596_; 
v___x_3594_ = lean_st_ref_get(v___y_3373_);
v_env_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc_ref(v_env_3595_);
lean_dec(v___x_3594_);
v___x_3596_ = l_Lean_Environment_containsOnBranch(v_env_3595_, v_fst_3476_);
lean_dec_ref(v_env_3595_);
if (v___x_3596_ == 0)
{
lean_del_object(v___x_3478_);
v___y_3570_ = v___y_3372_;
v___y_3571_ = v___y_3373_;
goto v___jp_3569_;
}
else
{
lean_object* v___x_3597_; lean_object* v_env_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_del_object(v___x_3483_);
lean_dec(v_snd_3481_);
lean_dec(v_fst_3480_);
lean_dec(v_exportedInfo_x3f_3371_);
lean_dec(v___x_3369_);
lean_dec_ref(v___x_3368_);
lean_dec(v_cls_3367_);
lean_dec(v_decl_3365_);
v___x_3597_ = lean_st_ref_get(v___y_3373_);
v_env_3598_ = lean_ctor_get(v___x_3597_, 0);
lean_inc_ref(v_env_3598_);
lean_dec(v___x_3597_);
v___x_3599_ = lean_elab_environment_to_kernel_env(v_env_3598_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set_tag(v___x_3478_, 1);
lean_ctor_set(v___x_3478_, 1, v_fst_3476_);
lean_ctor_set(v___x_3478_, 0, v___x_3599_);
v___x_3601_ = v___x_3478_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3603_; 
v_reuseFailAlloc_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3603_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3603_, 1, v_fst_3476_);
v___x_3601_ = v_reuseFailAlloc_3603_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; 
v___x_3602_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3601_, v___y_3372_, v___y_3373_);
return v___x_3602_;
}
}
v___jp_3485_:
{
uint8_t v___x_3493_; uint8_t v___x_3494_; lean_object* v___x_3495_; 
v___x_3493_ = 0;
v___x_3494_ = lean_unbox(v_snd_3481_);
lean_dec(v_snd_3481_);
lean_inc_ref(v___y_3487_);
v___x_3495_ = l_Lean_Environment_addConstAsync(v___y_3487_, v_fst_3476_, v___x_3494_, v___y_3492_, v___x_3493_, v___x_3366_);
if (lean_obj_tag(v___x_3495_) == 0)
{
lean_object* v_a_3496_; lean_object* v_mainEnv_3497_; lean_object* v_asyncEnv_3498_; lean_object* v___f_3499_; lean_object* v___f_3500_; lean_object* v___x_3501_; 
lean_del_object(v___x_3483_);
v_a_3496_ = lean_ctor_get(v___x_3495_, 0);
lean_inc_n(v_a_3496_, 3);
lean_dec_ref_known(v___x_3495_, 1);
v_mainEnv_3497_ = lean_ctor_get(v_a_3496_, 0);
lean_inc_ref(v_mainEnv_3497_);
v_asyncEnv_3498_ = lean_ctor_get(v_a_3496_, 1);
lean_inc_ref_n(v_asyncEnv_3498_, 2);
lean_inc_ref(v___y_3486_);
lean_inc(v___y_3488_);
v___f_3499_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3499_, 0, v___y_3488_);
lean_closure_set(v___f_3499_, 1, v_a_3496_);
lean_closure_set(v___f_3499_, 2, v___y_3486_);
lean_inc(v_decl_3365_);
v___f_3500_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3500_, 0, v_asyncEnv_3498_);
lean_closure_set(v___f_3500_, 1, v_a_3496_);
lean_closure_set(v___f_3500_, 2, v_decl_3365_);
v___x_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3501_, 0, v_fst_3480_);
if (lean_obj_tag(v___y_3491_) == 0)
{
lean_inc_ref(v___x_3501_);
v___y_3402_ = v___y_3489_;
v___y_3403_ = v___y_3490_;
v___y_3404_ = v___x_3501_;
v___y_3405_ = v___y_3487_;
v___y_3406_ = v___f_3499_;
v___y_3407_ = v_mainEnv_3497_;
v___y_3408_ = v_a_3496_;
v___y_3409_ = v___x_3493_;
v___y_3410_ = v___f_3500_;
v___y_3411_ = v_asyncEnv_3498_;
v___y_3412_ = v___x_3501_;
goto v___jp_3401_;
}
else
{
v___y_3402_ = v___y_3489_;
v___y_3403_ = v___y_3490_;
v___y_3404_ = v___x_3501_;
v___y_3405_ = v___y_3487_;
v___y_3406_ = v___f_3499_;
v___y_3407_ = v_mainEnv_3497_;
v___y_3408_ = v_a_3496_;
v___y_3409_ = v___x_3493_;
v___y_3410_ = v___f_3500_;
v___y_3411_ = v_asyncEnv_3498_;
v___y_3412_ = v___y_3491_;
goto v___jp_3401_;
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3487_);
lean_dec(v_fst_3480_);
lean_dec(v_decl_3365_);
v_a_3502_ = lean_ctor_get(v___x_3495_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3495_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3504_ = v___x_3495_;
v_isShared_3505_ = v_isSharedCheck_3516_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3495_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3516_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v_ref_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3511_; 
v_ref_3506_ = lean_ctor_get(v___y_3490_, 5);
v___x_3507_ = lean_io_error_to_string(v_a_3502_);
v___x_3508_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
v___x_3509_ = l_Lean_MessageData_ofFormat(v___x_3508_);
lean_inc(v_ref_3506_);
if (v_isShared_3484_ == 0)
{
lean_ctor_set(v___x_3483_, 1, v___x_3509_);
lean_ctor_set(v___x_3483_, 0, v_ref_3506_);
v___x_3511_ = v___x_3483_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_ref_3506_);
lean_ctor_set(v_reuseFailAlloc_3515_, 1, v___x_3509_);
v___x_3511_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
lean_object* v___x_3513_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 0, v___x_3511_);
v___x_3513_ = v___x_3504_;
goto v_reusejp_3512_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3511_);
v___x_3513_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3512_;
}
v_reusejp_3512_:
{
return v___x_3513_;
}
}
}
}
}
v___jp_3517_:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_st_ref_get(v___y_3520_);
if (lean_obj_tag(v_exportedInfo_x3f_3518_) == 0)
{
lean_object* v_env_3522_; lean_object* v___x_3523_; 
v_env_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc_ref(v_env_3522_);
lean_dec(v___x_3521_);
v___x_3523_ = lean_box(0);
v___y_3486_ = v___y_3519_;
v___y_3487_ = v_env_3522_;
v___y_3488_ = v___y_3520_;
v___y_3489_ = v___y_3520_;
v___y_3490_ = v___y_3519_;
v___y_3491_ = v_exportedInfo_x3f_3518_;
v___y_3492_ = v___x_3523_;
goto v___jp_3485_;
}
else
{
lean_object* v_env_3524_; lean_object* v_val_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; 
v_env_3524_ = lean_ctor_get(v___x_3521_, 0);
lean_inc_ref(v_env_3524_);
lean_dec(v___x_3521_);
v_val_3525_ = lean_ctor_get(v_exportedInfo_x3f_3518_, 0);
v___x_3526_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3525_);
v___x_3527_ = lean_box(v___x_3526_);
v___x_3528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3528_, 0, v___x_3527_);
v___y_3486_ = v___y_3519_;
v___y_3487_ = v_env_3524_;
v___y_3488_ = v___y_3520_;
v___y_3489_ = v___y_3520_;
v___y_3490_ = v___y_3519_;
v___y_3491_ = v_exportedInfo_x3f_3518_;
v___y_3492_ = v___x_3528_;
goto v___jp_3485_;
}
}
v___jp_3529_:
{
lean_object* v___x_3532_; 
lean_inc(v_fst_3480_);
v___x_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3532_, 0, v_fst_3480_);
v_exportedInfo_x3f_3518_ = v___x_3532_;
v___y_3519_ = v___y_3530_;
v___y_3520_ = v___y_3531_;
goto v___jp_3517_;
}
v___jp_3533_:
{
lean_object* v___x_3536_; 
lean_inc(v_fst_3480_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v_fst_3480_);
v_exportedInfo_x3f_3518_ = v___x_3536_;
v___y_3519_ = v___y_3534_;
v___y_3520_ = v___y_3535_;
goto v___jp_3517_;
}
v___jp_3537_:
{
if (v___y_3540_ == 0)
{
lean_object* v_options_3541_; uint8_t v_hasTrace_3542_; 
lean_dec(v_exportedInfo_x3f_3371_);
lean_dec_ref(v___x_3368_);
v_options_3541_ = lean_ctor_get(v___y_3538_, 2);
v_hasTrace_3542_ = lean_ctor_get_uint8(v_options_3541_, sizeof(void*)*1);
if (v_hasTrace_3542_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3530_ = v___y_3538_;
v___y_3531_ = v___y_3539_;
goto v___jp_3529_;
}
else
{
lean_object* v_inheritedTraceOptions_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; uint8_t v___x_3546_; 
v_inheritedTraceOptions_3543_ = lean_ctor_get(v___y_3538_, 13);
v___x_3544_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3367_);
v___x_3545_ = l_Lean_Name_append(v___x_3544_, v_cls_3367_);
v___x_3546_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3543_, v_options_3541_, v___x_3545_);
lean_dec(v___x_3545_);
if (v___x_3546_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3530_ = v___y_3538_;
v___y_3531_ = v___y_3539_;
goto v___jp_3529_;
}
else
{
lean_object* v___x_3547_; lean_object* v___x_3548_; 
v___x_3547_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3548_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3367_, v___x_3547_, v___y_3538_, v___y_3539_);
if (lean_obj_tag(v___x_3548_) == 0)
{
lean_dec_ref_known(v___x_3548_, 1);
v___y_3530_ = v___y_3538_;
v___y_3531_ = v___y_3539_;
goto v___jp_3529_;
}
else
{
lean_del_object(v___x_3483_);
lean_dec(v_snd_3481_);
lean_dec(v_fst_3480_);
lean_dec(v_fst_3476_);
lean_dec(v_decl_3365_);
return v___x_3548_;
}
}
}
}
else
{
lean_object* v___x_3549_; lean_object* v_env_3550_; lean_object* v_nextMacroScope_3551_; lean_object* v_ngen_3552_; lean_object* v_auxDeclNGen_3553_; lean_object* v_traceState_3554_; lean_object* v_messages_3555_; lean_object* v_infoState_3556_; lean_object* v_snapshotTasks_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3567_; 
lean_dec(v_cls_3367_);
v___x_3549_ = lean_st_ref_take(v___y_3539_);
v_env_3550_ = lean_ctor_get(v___x_3549_, 0);
v_nextMacroScope_3551_ = lean_ctor_get(v___x_3549_, 1);
v_ngen_3552_ = lean_ctor_get(v___x_3549_, 2);
v_auxDeclNGen_3553_ = lean_ctor_get(v___x_3549_, 3);
v_traceState_3554_ = lean_ctor_get(v___x_3549_, 4);
v_messages_3555_ = lean_ctor_get(v___x_3549_, 6);
v_infoState_3556_ = lean_ctor_get(v___x_3549_, 7);
v_snapshotTasks_3557_ = lean_ctor_get(v___x_3549_, 8);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3567_ == 0)
{
lean_object* v_unused_3568_; 
v_unused_3568_ = lean_ctor_get(v___x_3549_, 5);
lean_dec(v_unused_3568_);
v___x_3559_ = v___x_3549_;
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_snapshotTasks_3557_);
lean_inc(v_infoState_3556_);
lean_inc(v_messages_3555_);
lean_inc(v_traceState_3554_);
lean_inc(v_auxDeclNGen_3553_);
lean_inc(v_ngen_3552_);
lean_inc(v_nextMacroScope_3551_);
lean_inc(v_env_3550_);
lean_dec(v___x_3549_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3567_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3561_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3481_);
lean_inc(v_fst_3476_);
v___x_3562_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3561_, v_env_3550_, v_fst_3476_, v_snd_3481_);
if (v_isShared_3560_ == 0)
{
lean_ctor_set(v___x_3559_, 5, v___x_3368_);
lean_ctor_set(v___x_3559_, 0, v___x_3562_);
v___x_3564_ = v___x_3559_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v___x_3562_);
lean_ctor_set(v_reuseFailAlloc_3566_, 1, v_nextMacroScope_3551_);
lean_ctor_set(v_reuseFailAlloc_3566_, 2, v_ngen_3552_);
lean_ctor_set(v_reuseFailAlloc_3566_, 3, v_auxDeclNGen_3553_);
lean_ctor_set(v_reuseFailAlloc_3566_, 4, v_traceState_3554_);
lean_ctor_set(v_reuseFailAlloc_3566_, 5, v___x_3368_);
lean_ctor_set(v_reuseFailAlloc_3566_, 6, v_messages_3555_);
lean_ctor_set(v_reuseFailAlloc_3566_, 7, v_infoState_3556_);
lean_ctor_set(v_reuseFailAlloc_3566_, 8, v_snapshotTasks_3557_);
v___x_3564_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3565_; 
v___x_3565_ = lean_st_ref_set(v___y_3539_, v___x_3564_);
v_exportedInfo_x3f_3518_ = v_exportedInfo_x3f_3371_;
v___y_3519_ = v___y_3538_;
v___y_3520_ = v___y_3539_;
goto v___jp_3517_;
}
}
}
}
v___jp_3569_:
{
lean_object* v___x_3572_; uint8_t v___x_3573_; 
lean_inc(v_decl_3365_);
v___x_3572_ = l_Lean_Declaration_getTopLevelNames(v_decl_3365_);
v___x_3573_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3572_);
lean_dec(v___x_3572_);
if (v___x_3573_ == 0)
{
lean_dec(v___x_3369_);
if (lean_obj_tag(v_exportedInfo_x3f_3371_) == 0)
{
v___y_3538_ = v___y_3570_;
v___y_3539_ = v___y_3571_;
v___y_3540_ = v___x_3573_;
goto v___jp_3537_;
}
else
{
v___y_3538_ = v___y_3570_;
v___y_3539_ = v___y_3571_;
v___y_3540_ = v___x_3366_;
goto v___jp_3537_;
}
}
else
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v_a_3576_; uint8_t v___x_3577_; 
lean_dec(v_exportedInfo_x3f_3371_);
lean_dec_ref(v___x_3368_);
v___x_3574_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3575_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3574_, v___y_3570_);
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
lean_inc(v_a_3576_);
lean_dec_ref(v___x_3575_);
v___x_3577_ = lean_unbox(v_a_3576_);
lean_dec(v_a_3576_);
if (v___x_3577_ == 0)
{
lean_object* v_options_3578_; uint8_t v_hasTrace_3579_; 
v_options_3578_ = lean_ctor_get(v___y_3570_, 2);
v_hasTrace_3579_ = lean_ctor_get_uint8(v_options_3578_, sizeof(void*)*1);
if (v_hasTrace_3579_ == 0)
{
lean_dec(v_cls_3367_);
v_exportedInfo_x3f_3518_ = v___x_3369_;
v___y_3519_ = v___y_3570_;
v___y_3520_ = v___y_3571_;
goto v___jp_3517_;
}
else
{
lean_object* v_inheritedTraceOptions_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; uint8_t v___x_3583_; 
v_inheritedTraceOptions_3580_ = lean_ctor_get(v___y_3570_, 13);
v___x_3581_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3367_);
v___x_3582_ = l_Lean_Name_append(v___x_3581_, v_cls_3367_);
v___x_3583_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3580_, v_options_3578_, v___x_3582_);
lean_dec(v___x_3582_);
if (v___x_3583_ == 0)
{
lean_dec(v_cls_3367_);
v_exportedInfo_x3f_3518_ = v___x_3369_;
v___y_3519_ = v___y_3570_;
v___y_3520_ = v___y_3571_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; 
v___x_3584_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3585_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3367_, v___x_3584_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3585_) == 0)
{
lean_dec_ref_known(v___x_3585_, 1);
v_exportedInfo_x3f_3518_ = v___x_3369_;
v___y_3519_ = v___y_3570_;
v___y_3520_ = v___y_3571_;
goto v___jp_3517_;
}
else
{
lean_del_object(v___x_3483_);
lean_dec(v_snd_3481_);
lean_dec(v_fst_3480_);
lean_dec(v_fst_3476_);
lean_dec(v___x_3369_);
lean_dec(v_decl_3365_);
return v___x_3585_;
}
}
}
}
else
{
lean_object* v_options_3586_; uint8_t v_hasTrace_3587_; 
lean_dec(v___x_3369_);
v_options_3586_ = lean_ctor_get(v___y_3570_, 2);
v_hasTrace_3587_ = lean_ctor_get_uint8(v_options_3586_, sizeof(void*)*1);
if (v_hasTrace_3587_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3534_ = v___y_3570_;
v___y_3535_ = v___y_3571_;
goto v___jp_3533_;
}
else
{
lean_object* v_inheritedTraceOptions_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_inheritedTraceOptions_3588_ = lean_ctor_get(v___y_3570_, 13);
v___x_3589_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3367_);
v___x_3590_ = l_Lean_Name_append(v___x_3589_, v_cls_3367_);
v___x_3591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3588_, v_options_3586_, v___x_3590_);
lean_dec(v___x_3590_);
if (v___x_3591_ == 0)
{
lean_dec(v_cls_3367_);
v___y_3534_ = v___y_3570_;
v___y_3535_ = v___y_3571_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3593_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3367_, v___x_3592_, v___y_3570_, v___y_3571_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_dec_ref_known(v___x_3593_, 1);
v___y_3534_ = v___y_3570_;
v___y_3535_ = v___y_3571_;
goto v___jp_3533_;
}
else
{
lean_del_object(v___x_3483_);
lean_dec(v_snd_3481_);
lean_dec(v_fst_3480_);
lean_dec(v_fst_3476_);
lean_dec(v_decl_3365_);
return v___x_3593_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3606_, lean_object* v___x_3607_, lean_object* v_cls_3608_, lean_object* v___x_3609_, lean_object* v___x_3610_, lean_object* v_____x_3611_, lean_object* v_exportedInfo_x3f_3612_, lean_object* v___y_3613_, lean_object* v___y_3614_, lean_object* v___y_3615_){
_start:
{
uint8_t v___x_63468__boxed_3616_; lean_object* v_res_3617_; 
v___x_63468__boxed_3616_ = lean_unbox(v___x_3607_);
v_res_3617_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3606_, v___x_63468__boxed_3616_, v_cls_3608_, v___x_3609_, v___x_3610_, v_____x_3611_, v_exportedInfo_x3f_3612_, v___y_3613_, v___y_3614_);
lean_dec(v___y_3614_);
lean_dec_ref(v___y_3613_);
return v_res_3617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3618_, uint8_t v_forceExpose_3619_, uint8_t v___x_3620_, lean_object* v___x_3621_, lean_object* v_cls_3622_, lean_object* v_defn_3623_, lean_object* v___y_3624_, lean_object* v___y_3625_){
_start:
{
lean_object* v_exportedInfo_x3f_3628_; lean_object* v___y_3629_; lean_object* v___y_3630_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = lean_st_ref_get(v___y_3625_);
v___x_3650_ = lean_st_ref_get(v___y_3625_);
if (v_forceExpose_3619_ == 0)
{
if (v___x_3620_ == 0)
{
lean_dec(v___x_3650_);
lean_dec(v___x_3649_);
lean_dec(v_cls_3622_);
v_exportedInfo_x3f_3628_ = v___x_3621_;
v___y_3629_ = v___y_3624_;
v___y_3630_ = v___y_3625_;
goto v___jp_3627_;
}
else
{
lean_object* v_env_3651_; lean_object* v_env_3652_; lean_object* v___x_3653_; uint8_t v_isModule_3654_; 
v_env_3651_ = lean_ctor_get(v___x_3649_, 0);
lean_inc_ref(v_env_3651_);
lean_dec(v___x_3649_);
v_env_3652_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_ref(v_env_3652_);
lean_dec(v___x_3650_);
v___x_3653_ = l_Lean_Environment_header(v_env_3651_);
lean_dec_ref(v_env_3651_);
v_isModule_3654_ = lean_ctor_get_uint8(v___x_3653_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3653_);
if (v_isModule_3654_ == 0)
{
lean_dec_ref(v_env_3652_);
lean_dec(v_cls_3622_);
v_exportedInfo_x3f_3628_ = v___x_3621_;
v___y_3629_ = v___y_3624_;
v___y_3630_ = v___y_3625_;
goto v___jp_3627_;
}
else
{
uint8_t v_isExporting_3655_; 
v_isExporting_3655_ = lean_ctor_get_uint8(v_env_3652_, sizeof(void*)*8);
lean_dec_ref(v_env_3652_);
if (v_isExporting_3655_ == 0)
{
lean_object* v_options_3656_; uint8_t v_hasTrace_3657_; 
lean_dec(v___x_3621_);
v_options_3656_ = lean_ctor_get(v___y_3624_, 2);
v_hasTrace_3657_ = lean_ctor_get_uint8(v_options_3656_, sizeof(void*)*1);
if (v_hasTrace_3657_ == 0)
{
lean_dec(v_cls_3622_);
v___y_3640_ = v___y_3624_;
v___y_3641_ = v___y_3625_;
goto v___jp_3639_;
}
else
{
lean_object* v_inheritedTraceOptions_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; uint8_t v___x_3661_; 
v_inheritedTraceOptions_3658_ = lean_ctor_get(v___y_3624_, 13);
v___x_3659_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3622_);
v___x_3660_ = l_Lean_Name_append(v___x_3659_, v_cls_3622_);
v___x_3661_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3658_, v_options_3656_, v___x_3660_);
lean_dec(v___x_3660_);
if (v___x_3661_ == 0)
{
lean_dec(v_cls_3622_);
v___y_3640_ = v___y_3624_;
v___y_3641_ = v___y_3625_;
goto v___jp_3639_;
}
else
{
lean_object* v_toConstantVal_3662_; lean_object* v_name_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_toConstantVal_3662_ = lean_ctor_get(v_defn_3623_, 0);
v_name_3663_ = lean_ctor_get(v_toConstantVal_3662_, 0);
v___x_3664_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3663_);
v___x_3665_ = l_Lean_MessageData_ofName(v_name_3663_);
v___x_3666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3664_);
lean_ctor_set(v___x_3666_, 1, v___x_3665_);
v___x_3667_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3666_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3622_, v___x_3668_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_dec_ref_known(v___x_3669_, 1);
v___y_3640_ = v___y_3624_;
v___y_3641_ = v___y_3625_;
goto v___jp_3639_;
}
else
{
lean_dec_ref(v_defn_3623_);
lean_dec_ref(v___f_3618_);
return v___x_3669_;
}
}
}
}
else
{
lean_dec(v_cls_3622_);
v_exportedInfo_x3f_3628_ = v___x_3621_;
v___y_3629_ = v___y_3624_;
v___y_3630_ = v___y_3625_;
goto v___jp_3627_;
}
}
}
}
else
{
lean_dec(v___x_3650_);
lean_dec(v___x_3649_);
lean_dec(v_cls_3622_);
v_exportedInfo_x3f_3628_ = v___x_3621_;
v___y_3629_ = v___y_3624_;
v___y_3630_ = v___y_3625_;
goto v___jp_3627_;
}
v___jp_3627_:
{
lean_object* v_toConstantVal_3631_; lean_object* v_name_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; 
v_toConstantVal_3631_ = lean_ctor_get(v_defn_3623_, 0);
v_name_3632_ = lean_ctor_get(v_toConstantVal_3631_, 0);
lean_inc(v_name_3632_);
v___x_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3633_, 0, v_defn_3623_);
v___x_3634_ = 0;
v___x_3635_ = lean_box(v___x_3634_);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3633_);
lean_ctor_set(v___x_3636_, 1, v___x_3635_);
v___x_3637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3637_, 0, v_name_3632_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
lean_inc(v___y_3630_);
lean_inc_ref(v___y_3629_);
v___x_3638_ = lean_apply_5(v___f_3618_, v___x_3637_, v_exportedInfo_x3f_3628_, v___y_3629_, v___y_3630_, lean_box(0));
return v___x_3638_;
}
v___jp_3639_:
{
lean_object* v_toConstantVal_3642_; uint8_t v_safety_3643_; uint8_t v___x_3644_; uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_toConstantVal_3642_ = lean_ctor_get(v_defn_3623_, 0);
v_safety_3643_ = lean_ctor_get_uint8(v_defn_3623_, sizeof(void*)*4);
v___x_3644_ = 0;
v___x_3645_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3643_, v___x_3644_);
lean_inc_ref(v_toConstantVal_3642_);
v___x_3646_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3646_, 0, v_toConstantVal_3642_);
lean_ctor_set_uint8(v___x_3646_, sizeof(void*)*1, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
v___x_3648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3647_);
v_exportedInfo_x3f_3628_ = v___x_3648_;
v___y_3629_ = v___y_3640_;
v___y_3630_ = v___y_3641_;
goto v___jp_3627_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3670_, lean_object* v_forceExpose_3671_, lean_object* v___x_3672_, lean_object* v___x_3673_, lean_object* v_cls_3674_, lean_object* v_defn_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
uint8_t v_forceExpose_boxed_3679_; uint8_t v___x_63943__boxed_3680_; lean_object* v_res_3681_; 
v_forceExpose_boxed_3679_ = lean_unbox(v_forceExpose_3671_);
v___x_63943__boxed_3680_ = lean_unbox(v___x_3672_);
v_res_3681_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3670_, v_forceExpose_boxed_3679_, v___x_63943__boxed_3680_, v___x_3673_, v_cls_3674_, v_defn_3675_, v___y_3676_, v___y_3677_);
lean_dec(v___y_3677_);
lean_dec_ref(v___y_3676_);
return v_res_3681_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3682_, uint8_t v_forceExpose_3683_, lean_object* v___f_3684_, lean_object* v_____r_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_){
_start:
{
lean_object* v_toConstantVal_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_toConstantVal_3689_ = lean_ctor_get(v_val_3682_, 0);
lean_inc_ref(v_toConstantVal_3689_);
v___x_3690_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3690_, 0, v_toConstantVal_3689_);
lean_ctor_set_uint8(v___x_3690_, sizeof(void*)*1, v_forceExpose_3683_);
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
v___x_3693_ = lean_box(0);
lean_inc(v___y_3687_);
lean_inc_ref(v___y_3686_);
v___x_3694_ = lean_apply_5(v___f_3684_, v___x_3693_, v___x_3692_, v___y_3686_, v___y_3687_, lean_box(0));
return v___x_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3695_, lean_object* v_forceExpose_3696_, lean_object* v___f_3697_, lean_object* v_____r_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_){
_start:
{
uint8_t v_forceExpose_boxed_3702_; lean_object* v_res_3703_; 
v_forceExpose_boxed_3702_ = lean_unbox(v_forceExpose_3696_);
v_res_3703_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3695_, v_forceExpose_boxed_3702_, v___f_3697_, v_____r_3698_, v___y_3699_, v___y_3700_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_val_3695_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3704_, lean_object* v_x_3705_){
_start:
{
if (lean_obj_tag(v_x_3705_) == 0)
{
return v_x_3704_;
}
else
{
lean_object* v_head_3706_; lean_object* v_tail_3707_; lean_object* v___x_3708_; 
v_head_3706_ = lean_ctor_get(v_x_3705_, 0);
lean_inc(v_head_3706_);
v_tail_3707_ = lean_ctor_get(v_x_3705_, 1);
lean_inc(v_tail_3707_);
lean_dec_ref_known(v_x_3705_, 2);
v___x_3708_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3704_, v_head_3706_);
v_x_3704_ = v___x_3708_;
v_x_3705_ = v_tail_3707_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; 
v_cls_3710_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3711_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3712_ = l_Lean_Name_append(v___x_3711_, v_cls_3710_);
return v___x_3712_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3715_ = l_Lean_stringToMessageData(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3719_, uint8_t v_forceExpose_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_){
_start:
{
lean_object* v___y_3725_; lean_object* v___y_3726_; lean_object* v_a_3727_; lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_a_3740_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_a_3753_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_a_3766_; lean_object* v_options_3776_; lean_object* v_inheritedTraceOptions_3777_; uint8_t v_hasTrace_3778_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; uint8_t v___y_3784_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v___y_3787_; lean_object* v___y_3788_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3858_; uint8_t v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; lean_object* v___y_3863_; uint8_t v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v_exportedInfo_x3f_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; uint8_t v___y_3901_; lean_object* v___y_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; uint8_t v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v_cls_3914_; 
v_options_3776_ = lean_ctor_get(v_a_3721_, 2);
v_inheritedTraceOptions_3777_ = lean_ctor_get(v_a_3721_, 13);
v_hasTrace_3778_ = lean_ctor_get_uint8(v_options_3776_, sizeof(void*)*1);
v_cls_3914_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3778_ == 0)
{
lean_object* v___x_3915_; lean_object* v_env_3916_; lean_object* v_nextMacroScope_3917_; lean_object* v_ngen_3918_; lean_object* v_auxDeclNGen_3919_; lean_object* v_traceState_3920_; lean_object* v_messages_3921_; lean_object* v_infoState_3922_; lean_object* v_snapshotTasks_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_4112_; 
v___x_3915_ = lean_st_ref_take(v_a_3722_);
v_env_3916_ = lean_ctor_get(v___x_3915_, 0);
v_nextMacroScope_3917_ = lean_ctor_get(v___x_3915_, 1);
v_ngen_3918_ = lean_ctor_get(v___x_3915_, 2);
v_auxDeclNGen_3919_ = lean_ctor_get(v___x_3915_, 3);
v_traceState_3920_ = lean_ctor_get(v___x_3915_, 4);
v_messages_3921_ = lean_ctor_get(v___x_3915_, 6);
v_infoState_3922_ = lean_ctor_get(v___x_3915_, 7);
v_snapshotTasks_3923_ = lean_ctor_get(v___x_3915_, 8);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_4112_ == 0)
{
lean_object* v_unused_4113_; 
v_unused_4113_ = lean_ctor_get(v___x_3915_, 5);
lean_dec(v_unused_4113_);
v___x_3925_ = v___x_3915_;
v_isShared_3926_ = v_isSharedCheck_4112_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_snapshotTasks_3923_);
lean_inc(v_infoState_3922_);
lean_inc(v_messages_3921_);
lean_inc(v_traceState_3920_);
lean_inc(v_auxDeclNGen_3919_);
lean_inc(v_ngen_3918_);
lean_inc(v_nextMacroScope_3917_);
lean_inc(v_env_3916_);
lean_dec(v___x_3915_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_4112_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
lean_inc(v_decl_3719_);
v___x_3927_ = l_Lean_Declaration_getNames(v_decl_3719_);
v___x_3928_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3916_, v___x_3927_);
v___x_3929_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 5, v___x_3929_);
lean_ctor_set(v___x_3925_, 0, v___x_3928_);
v___x_3931_ = v___x_3925_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_4111_, 1, v_nextMacroScope_3917_);
lean_ctor_set(v_reuseFailAlloc_4111_, 2, v_ngen_3918_);
lean_ctor_set(v_reuseFailAlloc_4111_, 3, v_auxDeclNGen_3919_);
lean_ctor_set(v_reuseFailAlloc_4111_, 4, v_traceState_3920_);
lean_ctor_set(v_reuseFailAlloc_4111_, 5, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_4111_, 6, v_messages_3921_);
lean_ctor_set(v_reuseFailAlloc_4111_, 7, v_infoState_3922_);
lean_ctor_set(v_reuseFailAlloc_4111_, 8, v_snapshotTasks_3923_);
v___x_3931_ = v_reuseFailAlloc_4111_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; uint8_t v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v_fst_3990_; lean_object* v_fst_3991_; uint8_t v_snd_3992_; lean_object* v_exportedInfo_x3f_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_4005_; lean_object* v_toConstantVal_4006_; lean_object* v_exportedInfo_x3f_4007_; lean_object* v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4014_; lean_object* v_exportedInfo_x3f_4015_; lean_object* v___y_4016_; lean_object* v___y_4017_; lean_object* v___y_4020_; lean_object* v_toConstantVal_4021_; uint8_t v_safety_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v_defn_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; 
v___x_3932_ = lean_st_ref_set(v_a_3722_, v___x_3931_);
v___x_3933_ = lean_box(0);
switch(lean_obj_tag(v_decl_3719_))
{
case 2:
{
lean_object* v_val_4061_; lean_object* v_exportedInfo_x3f_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; lean_object* v___x_4070_; 
v_val_4061_ = lean_ctor_get(v_decl_3719_, 0);
v___x_4070_ = lean_st_ref_get(v_a_3722_);
if (v_forceExpose_3720_ == 0)
{
lean_object* v_env_4071_; lean_object* v___x_4072_; uint8_t v_isModule_4073_; 
v_env_4071_ = lean_ctor_get(v___x_4070_, 0);
lean_inc_ref(v_env_4071_);
lean_dec(v___x_4070_);
v___x_4072_ = l_Lean_Environment_header(v_env_4071_);
lean_dec_ref(v_env_4071_);
v_isModule_4073_ = lean_ctor_get_uint8(v___x_4072_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4072_);
if (v_isModule_4073_ == 0)
{
v_exportedInfo_x3f_4063_ = v___x_3933_;
v___y_4064_ = v_a_3721_;
v___y_4065_ = v_a_3722_;
goto v___jp_4062_;
}
else
{
lean_object* v_toConstantVal_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_toConstantVal_4074_ = lean_ctor_get(v_val_4061_, 0);
lean_inc_ref(v_toConstantVal_4074_);
v___x_4075_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4075_, 0, v_toConstantVal_4074_);
lean_ctor_set_uint8(v___x_4075_, sizeof(void*)*1, v_hasTrace_3778_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4075_);
v___x_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4077_, 0, v___x_4076_);
v_exportedInfo_x3f_4063_ = v___x_4077_;
v___y_4064_ = v_a_3721_;
v___y_4065_ = v_a_3722_;
goto v___jp_4062_;
}
}
else
{
lean_dec(v___x_4070_);
v_exportedInfo_x3f_4063_ = v___x_3933_;
v___y_4064_ = v_a_3721_;
v___y_4065_ = v_a_3722_;
goto v___jp_4062_;
}
v___jp_4062_:
{
lean_object* v_toConstantVal_4066_; lean_object* v_name_4067_; lean_object* v___x_4068_; uint8_t v___x_4069_; 
v_toConstantVal_4066_ = lean_ctor_get(v_val_4061_, 0);
v_name_4067_ = lean_ctor_get(v_toConstantVal_4066_, 0);
lean_inc_ref(v_val_4061_);
v___x_4068_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4068_, 0, v_val_4061_);
v___x_4069_ = 1;
lean_inc(v_name_4067_);
v_fst_3990_ = v_name_4067_;
v_fst_3991_ = v___x_4068_;
v_snd_3992_ = v___x_4069_;
v_exportedInfo_x3f_3993_ = v_exportedInfo_x3f_4063_;
v___y_3994_ = v___y_4064_;
v___y_3995_ = v___y_4065_;
goto v___jp_3989_;
}
}
case 1:
{
lean_object* v_val_4078_; 
v_val_4078_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref(v_val_4078_);
v_defn_4037_ = v_val_4078_;
v___y_4038_ = v_a_3721_;
v___y_4039_ = v_a_3722_;
goto v___jp_4036_;
}
case 5:
{
lean_object* v_defns_4079_; 
v_defns_4079_ = lean_ctor_get(v_decl_3719_, 0);
if (lean_obj_tag(v_defns_4079_) == 1)
{
lean_object* v_tail_4080_; 
v_tail_4080_ = lean_ctor_get(v_defns_4079_, 1);
if (lean_obj_tag(v_tail_4080_) == 0)
{
lean_object* v_head_4081_; 
v_head_4081_ = lean_ctor_get(v_defns_4079_, 0);
lean_inc(v_head_4081_);
v_defn_4037_ = v_head_4081_;
v___y_4038_ = v_a_3721_;
v___y_4039_ = v_a_3722_;
goto v___jp_4036_;
}
else
{
lean_object* v___x_4082_; 
v___x_4082_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v_a_3721_, v_a_3722_);
return v___x_4082_;
}
}
else
{
lean_object* v___x_4083_; 
v___x_4083_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v_a_3721_, v_a_3722_);
return v___x_4083_;
}
}
case 3:
{
lean_object* v_val_4084_; lean_object* v_exportedInfo_x3f_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v_val_4084_ = lean_ctor_get(v_decl_3719_, 0);
v___x_4093_ = lean_st_ref_get(v_a_3722_);
v___x_4094_ = lean_st_ref_get(v_a_3722_);
if (v_forceExpose_3720_ == 0)
{
lean_object* v_env_4095_; lean_object* v_env_4096_; lean_object* v___x_4097_; uint8_t v_isModule_4098_; 
v_env_4095_ = lean_ctor_get(v___x_4093_, 0);
lean_inc_ref(v_env_4095_);
lean_dec(v___x_4093_);
v_env_4096_ = lean_ctor_get(v___x_4094_, 0);
lean_inc_ref(v_env_4096_);
lean_dec(v___x_4094_);
v___x_4097_ = l_Lean_Environment_header(v_env_4095_);
lean_dec_ref(v_env_4095_);
v_isModule_4098_ = lean_ctor_get_uint8(v___x_4097_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4097_);
if (v_isModule_4098_ == 0)
{
lean_dec_ref(v_env_4096_);
v_exportedInfo_x3f_4086_ = v___x_3933_;
v___y_4087_ = v_a_3721_;
v___y_4088_ = v_a_3722_;
goto v___jp_4085_;
}
else
{
uint8_t v_isExporting_4099_; 
v_isExporting_4099_ = lean_ctor_get_uint8(v_env_4096_, sizeof(void*)*8);
lean_dec_ref(v_env_4096_);
if (v_isExporting_4099_ == 0)
{
lean_object* v_toConstantVal_4100_; uint8_t v_isUnsafe_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v_toConstantVal_4100_ = lean_ctor_get(v_val_4084_, 0);
v_isUnsafe_4101_ = lean_ctor_get_uint8(v_val_4084_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4100_);
v___x_4102_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4102_, 0, v_toConstantVal_4100_);
lean_ctor_set_uint8(v___x_4102_, sizeof(void*)*1, v_isUnsafe_4101_);
v___x_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
v___x_4104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
v_exportedInfo_x3f_4086_ = v___x_4104_;
v___y_4087_ = v_a_3721_;
v___y_4088_ = v_a_3722_;
goto v___jp_4085_;
}
else
{
v_exportedInfo_x3f_4086_ = v___x_3933_;
v___y_4087_ = v_a_3721_;
v___y_4088_ = v_a_3722_;
goto v___jp_4085_;
}
}
}
else
{
lean_dec(v___x_4094_);
lean_dec(v___x_4093_);
v_exportedInfo_x3f_4086_ = v___x_3933_;
v___y_4087_ = v_a_3721_;
v___y_4088_ = v_a_3722_;
goto v___jp_4085_;
}
v___jp_4085_:
{
lean_object* v_toConstantVal_4089_; lean_object* v_name_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v_toConstantVal_4089_ = lean_ctor_get(v_val_4084_, 0);
v_name_4090_ = lean_ctor_get(v_toConstantVal_4089_, 0);
lean_inc_ref(v_val_4084_);
v___x_4091_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4091_, 0, v_val_4084_);
v___x_4092_ = 3;
lean_inc(v_name_4090_);
v_fst_3990_ = v_name_4090_;
v_fst_3991_ = v___x_4091_;
v_snd_3992_ = v___x_4092_;
v_exportedInfo_x3f_3993_ = v_exportedInfo_x3f_4086_;
v___y_3994_ = v___y_4087_;
v___y_3995_ = v___y_4088_;
goto v___jp_3989_;
}
}
case 0:
{
lean_object* v_val_4105_; lean_object* v_toConstantVal_4106_; lean_object* v_name_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v_val_4105_ = lean_ctor_get(v_decl_3719_, 0);
v_toConstantVal_4106_ = lean_ctor_get(v_val_4105_, 0);
v_name_4107_ = lean_ctor_get(v_toConstantVal_4106_, 0);
lean_inc_ref(v_val_4105_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_val_4105_);
v___x_4109_ = 2;
lean_inc(v_name_4107_);
v_fst_3990_ = v_name_4107_;
v_fst_3991_ = v___x_4108_;
v_snd_3992_ = v___x_4109_;
v_exportedInfo_x3f_3993_ = v___x_3933_;
v___y_3994_ = v_a_3721_;
v___y_3995_ = v_a_3722_;
goto v___jp_3989_;
}
default: 
{
lean_object* v___x_4110_; 
v___x_4110_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v_a_3721_, v_a_3722_);
return v___x_4110_;
}
}
v___jp_3934_:
{
lean_object* v___x_3941_; uint8_t v___x_3942_; 
lean_inc(v_decl_3719_);
v___x_3941_ = l_Lean_Declaration_getTopLevelNames(v_decl_3719_);
v___x_3942_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3941_);
lean_dec(v___x_3941_);
if (v___x_3942_ == 0)
{
if (lean_obj_tag(v___y_3937_) == 0)
{
lean_object* v_options_3943_; uint8_t v_hasTrace_3944_; 
v_options_3943_ = lean_ctor_get(v___y_3939_, 2);
v_hasTrace_3944_ = lean_ctor_get_uint8(v_options_3943_, sizeof(void*)*1);
if (v_hasTrace_3944_ == 0)
{
v___y_3901_ = v___y_3935_;
v___y_3902_ = v___y_3936_;
v___y_3903_ = v___y_3938_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3940_;
goto v___jp_3900_;
}
else
{
lean_object* v_inheritedTraceOptions_3945_; lean_object* v___x_3946_; uint8_t v___x_3947_; 
v_inheritedTraceOptions_3945_ = lean_ctor_get(v___y_3939_, 13);
v___x_3946_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3947_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3945_, v_options_3943_, v___x_3946_);
if (v___x_3947_ == 0)
{
v___y_3901_ = v___y_3935_;
v___y_3902_ = v___y_3936_;
v___y_3903_ = v___y_3938_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3940_;
goto v___jp_3900_;
}
else
{
lean_object* v___x_3948_; lean_object* v___x_3949_; 
v___x_3948_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3949_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_3948_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_dec_ref_known(v___x_3949_, 1);
v___y_3901_ = v___y_3935_;
v___y_3902_ = v___y_3936_;
v___y_3903_ = v___y_3938_;
v___y_3904_ = v___y_3939_;
v___y_3905_ = v___y_3940_;
goto v___jp_3900_;
}
else
{
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3936_);
lean_dec(v_decl_3719_);
return v___x_3949_;
}
}
}
}
else
{
lean_object* v___x_3950_; lean_object* v_env_3951_; lean_object* v_nextMacroScope_3952_; lean_object* v_ngen_3953_; lean_object* v_auxDeclNGen_3954_; lean_object* v_traceState_3955_; lean_object* v_messages_3956_; lean_object* v_infoState_3957_; lean_object* v_snapshotTasks_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3969_; 
v___x_3950_ = lean_st_ref_take(v___y_3940_);
v_env_3951_ = lean_ctor_get(v___x_3950_, 0);
v_nextMacroScope_3952_ = lean_ctor_get(v___x_3950_, 1);
v_ngen_3953_ = lean_ctor_get(v___x_3950_, 2);
v_auxDeclNGen_3954_ = lean_ctor_get(v___x_3950_, 3);
v_traceState_3955_ = lean_ctor_get(v___x_3950_, 4);
v_messages_3956_ = lean_ctor_get(v___x_3950_, 6);
v_infoState_3957_ = lean_ctor_get(v___x_3950_, 7);
v_snapshotTasks_3958_ = lean_ctor_get(v___x_3950_, 8);
v_isSharedCheck_3969_ = !lean_is_exclusive(v___x_3950_);
if (v_isSharedCheck_3969_ == 0)
{
lean_object* v_unused_3970_; 
v_unused_3970_ = lean_ctor_get(v___x_3950_, 5);
lean_dec(v_unused_3970_);
v___x_3960_ = v___x_3950_;
v_isShared_3961_ = v_isSharedCheck_3969_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_snapshotTasks_3958_);
lean_inc(v_infoState_3957_);
lean_inc(v_messages_3956_);
lean_inc(v_traceState_3955_);
lean_inc(v_auxDeclNGen_3954_);
lean_inc(v_ngen_3953_);
lean_inc(v_nextMacroScope_3952_);
lean_inc(v_env_3951_);
lean_dec(v___x_3950_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3969_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3966_; 
v___x_3962_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3963_ = lean_box(v___y_3935_);
lean_inc(v___y_3936_);
v___x_3964_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3962_, v_env_3951_, v___y_3936_, v___x_3963_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 5, v___x_3929_);
lean_ctor_set(v___x_3960_, 0, v___x_3964_);
v___x_3966_ = v___x_3960_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3964_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_nextMacroScope_3952_);
lean_ctor_set(v_reuseFailAlloc_3968_, 2, v_ngen_3953_);
lean_ctor_set(v_reuseFailAlloc_3968_, 3, v_auxDeclNGen_3954_);
lean_ctor_set(v_reuseFailAlloc_3968_, 4, v_traceState_3955_);
lean_ctor_set(v_reuseFailAlloc_3968_, 5, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3968_, 6, v_messages_3956_);
lean_ctor_set(v_reuseFailAlloc_3968_, 7, v_infoState_3957_);
lean_ctor_set(v_reuseFailAlloc_3968_, 8, v_snapshotTasks_3958_);
v___x_3966_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
lean_object* v___x_3967_; 
v___x_3967_ = lean_st_ref_set(v___y_3940_, v___x_3966_);
v___y_3886_ = v___y_3935_;
v___y_3887_ = v___y_3936_;
v___y_3888_ = v___y_3938_;
v_exportedInfo_x3f_3889_ = v___y_3937_;
v___y_3890_ = v___y_3939_;
v___y_3891_ = v___y_3940_;
goto v___jp_3885_;
}
}
}
}
else
{
lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v_a_3973_; uint8_t v___x_3974_; 
lean_dec(v___y_3937_);
v___x_3971_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3972_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3971_, v___y_3939_);
v_a_3973_ = lean_ctor_get(v___x_3972_, 0);
lean_inc(v_a_3973_);
lean_dec_ref(v___x_3972_);
v___x_3974_ = lean_unbox(v_a_3973_);
lean_dec(v_a_3973_);
if (v___x_3974_ == 0)
{
lean_object* v_options_3975_; uint8_t v_hasTrace_3976_; 
v_options_3975_ = lean_ctor_get(v___y_3939_, 2);
v_hasTrace_3976_ = lean_ctor_get_uint8(v_options_3975_, sizeof(void*)*1);
if (v_hasTrace_3976_ == 0)
{
v___y_3886_ = v___y_3935_;
v___y_3887_ = v___y_3936_;
v___y_3888_ = v___y_3938_;
v_exportedInfo_x3f_3889_ = v___x_3933_;
v___y_3890_ = v___y_3939_;
v___y_3891_ = v___y_3940_;
goto v___jp_3885_;
}
else
{
lean_object* v_inheritedTraceOptions_3977_; lean_object* v___x_3978_; uint8_t v___x_3979_; 
v_inheritedTraceOptions_3977_ = lean_ctor_get(v___y_3939_, 13);
v___x_3978_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3979_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3977_, v_options_3975_, v___x_3978_);
if (v___x_3979_ == 0)
{
v___y_3886_ = v___y_3935_;
v___y_3887_ = v___y_3936_;
v___y_3888_ = v___y_3938_;
v_exportedInfo_x3f_3889_ = v___x_3933_;
v___y_3890_ = v___y_3939_;
v___y_3891_ = v___y_3940_;
goto v___jp_3885_;
}
else
{
lean_object* v___x_3980_; lean_object* v___x_3981_; 
v___x_3980_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3981_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_3980_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3981_) == 0)
{
lean_dec_ref_known(v___x_3981_, 1);
v___y_3886_ = v___y_3935_;
v___y_3887_ = v___y_3936_;
v___y_3888_ = v___y_3938_;
v_exportedInfo_x3f_3889_ = v___x_3933_;
v___y_3890_ = v___y_3939_;
v___y_3891_ = v___y_3940_;
goto v___jp_3885_;
}
else
{
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3936_);
lean_dec(v_decl_3719_);
return v___x_3981_;
}
}
}
}
else
{
lean_object* v_options_3982_; uint8_t v_hasTrace_3983_; 
v_options_3982_ = lean_ctor_get(v___y_3939_, 2);
v_hasTrace_3983_ = lean_ctor_get_uint8(v_options_3982_, sizeof(void*)*1);
if (v_hasTrace_3983_ == 0)
{
v___y_3908_ = v___y_3935_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3938_;
v___y_3911_ = v___y_3939_;
v___y_3912_ = v___y_3940_;
goto v___jp_3907_;
}
else
{
lean_object* v_inheritedTraceOptions_3984_; lean_object* v___x_3985_; uint8_t v___x_3986_; 
v_inheritedTraceOptions_3984_ = lean_ctor_get(v___y_3939_, 13);
v___x_3985_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3986_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3984_, v_options_3982_, v___x_3985_);
if (v___x_3986_ == 0)
{
v___y_3908_ = v___y_3935_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3938_;
v___y_3911_ = v___y_3939_;
v___y_3912_ = v___y_3940_;
goto v___jp_3907_;
}
else
{
lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3987_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3988_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_3987_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3988_) == 0)
{
lean_dec_ref_known(v___x_3988_, 1);
v___y_3908_ = v___y_3935_;
v___y_3909_ = v___y_3936_;
v___y_3910_ = v___y_3938_;
v___y_3911_ = v___y_3939_;
v___y_3912_ = v___y_3940_;
goto v___jp_3907_;
}
else
{
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3936_);
lean_dec(v_decl_3719_);
return v___x_3988_;
}
}
}
}
}
}
v___jp_3989_:
{
lean_object* v___x_3996_; lean_object* v_env_3997_; uint8_t v___x_3998_; 
v___x_3996_ = lean_st_ref_get(v___y_3995_);
v_env_3997_ = lean_ctor_get(v___x_3996_, 0);
lean_inc_ref(v_env_3997_);
lean_dec(v___x_3996_);
v___x_3998_ = l_Lean_Environment_containsOnBranch(v_env_3997_, v_fst_3990_);
lean_dec_ref(v_env_3997_);
if (v___x_3998_ == 0)
{
v___y_3935_ = v_snd_3992_;
v___y_3936_ = v_fst_3990_;
v___y_3937_ = v_exportedInfo_x3f_3993_;
v___y_3938_ = v_fst_3991_;
v___y_3939_ = v___y_3994_;
v___y_3940_ = v___y_3995_;
goto v___jp_3934_;
}
else
{
lean_object* v___x_3999_; lean_object* v_env_4000_; lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec(v_exportedInfo_x3f_3993_);
lean_dec_ref(v_fst_3991_);
lean_dec(v_decl_3719_);
v___x_3999_ = lean_st_ref_get(v___y_3995_);
v_env_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc_ref(v_env_4000_);
lean_dec(v___x_3999_);
v___x_4001_ = lean_elab_environment_to_kernel_env(v_env_4000_);
v___x_4002_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4002_, 0, v___x_4001_);
lean_ctor_set(v___x_4002_, 1, v_fst_3990_);
v___x_4003_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4002_, v___y_3994_, v___y_3995_);
return v___x_4003_;
}
}
v___jp_4004_:
{
lean_object* v_name_4010_; lean_object* v___x_4011_; uint8_t v___x_4012_; 
v_name_4010_ = lean_ctor_get(v_toConstantVal_4006_, 0);
lean_inc(v_name_4010_);
lean_dec_ref(v_toConstantVal_4006_);
v___x_4011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___y_4005_);
v___x_4012_ = 0;
v_fst_3990_ = v_name_4010_;
v_fst_3991_ = v___x_4011_;
v_snd_3992_ = v___x_4012_;
v_exportedInfo_x3f_3993_ = v_exportedInfo_x3f_4007_;
v___y_3994_ = v___y_4008_;
v___y_3995_ = v___y_4009_;
goto v___jp_3989_;
}
v___jp_4013_:
{
lean_object* v_toConstantVal_4018_; 
v_toConstantVal_4018_ = lean_ctor_get(v___y_4014_, 0);
lean_inc_ref(v_toConstantVal_4018_);
v___y_4005_ = v___y_4014_;
v_toConstantVal_4006_ = v_toConstantVal_4018_;
v_exportedInfo_x3f_4007_ = v_exportedInfo_x3f_4015_;
v___y_4008_ = v___y_4016_;
v___y_4009_ = v___y_4017_;
goto v___jp_4004_;
}
v___jp_4019_:
{
uint8_t v___x_4025_; uint8_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v___x_4025_ = 0;
v___x_4026_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4022_, v___x_4025_);
lean_inc_ref(v_toConstantVal_4021_);
v___x_4027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4027_, 0, v_toConstantVal_4021_);
lean_ctor_set_uint8(v___x_4027_, sizeof(void*)*1, v___x_4026_);
v___x_4028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
v___x_4029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
v___y_4005_ = v___y_4020_;
v_toConstantVal_4006_ = v_toConstantVal_4021_;
v_exportedInfo_x3f_4007_ = v___x_4029_;
v___y_4008_ = v___y_4023_;
v___y_4009_ = v___y_4024_;
goto v___jp_4004_;
}
v___jp_4030_:
{
lean_object* v_toConstantVal_4034_; uint8_t v_safety_4035_; 
v_toConstantVal_4034_ = lean_ctor_get(v___y_4031_, 0);
lean_inc_ref(v_toConstantVal_4034_);
v_safety_4035_ = lean_ctor_get_uint8(v___y_4031_, sizeof(void*)*4);
v___y_4020_ = v___y_4031_;
v_toConstantVal_4021_ = v_toConstantVal_4034_;
v_safety_4022_ = v_safety_4035_;
v___y_4023_ = v___y_4032_;
v___y_4024_ = v___y_4033_;
goto v___jp_4019_;
}
v___jp_4036_:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_st_ref_get(v___y_4039_);
v___x_4041_ = lean_st_ref_get(v___y_4039_);
if (v_forceExpose_3720_ == 0)
{
lean_object* v_env_4042_; lean_object* v_env_4043_; lean_object* v___x_4044_; uint8_t v_isModule_4045_; 
v_env_4042_ = lean_ctor_get(v___x_4040_, 0);
lean_inc_ref(v_env_4042_);
lean_dec(v___x_4040_);
v_env_4043_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_ref(v_env_4043_);
lean_dec(v___x_4041_);
v___x_4044_ = l_Lean_Environment_header(v_env_4042_);
lean_dec_ref(v_env_4042_);
v_isModule_4045_ = lean_ctor_get_uint8(v___x_4044_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4044_);
if (v_isModule_4045_ == 0)
{
lean_dec_ref(v_env_4043_);
v___y_4014_ = v_defn_4037_;
v_exportedInfo_x3f_4015_ = v___x_3933_;
v___y_4016_ = v___y_4038_;
v___y_4017_ = v___y_4039_;
goto v___jp_4013_;
}
else
{
uint8_t v_isExporting_4046_; 
v_isExporting_4046_ = lean_ctor_get_uint8(v_env_4043_, sizeof(void*)*8);
lean_dec_ref(v_env_4043_);
if (v_isExporting_4046_ == 0)
{
lean_object* v_options_4047_; uint8_t v_hasTrace_4048_; 
v_options_4047_ = lean_ctor_get(v___y_4038_, 2);
v_hasTrace_4048_ = lean_ctor_get_uint8(v_options_4047_, sizeof(void*)*1);
if (v_hasTrace_4048_ == 0)
{
v___y_4031_ = v_defn_4037_;
v___y_4032_ = v___y_4038_;
v___y_4033_ = v___y_4039_;
goto v___jp_4030_;
}
else
{
lean_object* v_inheritedTraceOptions_4049_; lean_object* v___x_4050_; uint8_t v___x_4051_; 
v_inheritedTraceOptions_4049_ = lean_ctor_get(v___y_4038_, 13);
v___x_4050_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4051_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4049_, v_options_4047_, v___x_4050_);
if (v___x_4051_ == 0)
{
v___y_4031_ = v_defn_4037_;
v___y_4032_ = v___y_4038_;
v___y_4033_ = v___y_4039_;
goto v___jp_4030_;
}
else
{
lean_object* v_toConstantVal_4052_; uint8_t v_safety_4053_; lean_object* v_name_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v_toConstantVal_4052_ = lean_ctor_get(v_defn_4037_, 0);
lean_inc_ref(v_toConstantVal_4052_);
v_safety_4053_ = lean_ctor_get_uint8(v_defn_4037_, sizeof(void*)*4);
v_name_4054_ = lean_ctor_get(v_toConstantVal_4052_, 0);
v___x_4055_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4054_);
v___x_4056_ = l_Lean_MessageData_ofName(v_name_4054_);
v___x_4057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4055_);
lean_ctor_set(v___x_4057_, 1, v___x_4056_);
v___x_4058_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4057_);
lean_ctor_set(v___x_4059_, 1, v___x_4058_);
v___x_4060_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4059_, v___y_4038_, v___y_4039_);
if (lean_obj_tag(v___x_4060_) == 0)
{
lean_dec_ref_known(v___x_4060_, 1);
v___y_4020_ = v_defn_4037_;
v_toConstantVal_4021_ = v_toConstantVal_4052_;
v_safety_4022_ = v_safety_4053_;
v___y_4023_ = v___y_4038_;
v___y_4024_ = v___y_4039_;
goto v___jp_4019_;
}
else
{
lean_dec_ref(v_toConstantVal_4052_);
lean_dec_ref(v_defn_4037_);
lean_dec(v_decl_3719_);
return v___x_4060_;
}
}
}
}
else
{
v___y_4014_ = v_defn_4037_;
v_exportedInfo_x3f_4015_ = v___x_3933_;
v___y_4016_ = v___y_4038_;
v___y_4017_ = v___y_4039_;
goto v___jp_4013_;
}
}
}
else
{
lean_dec(v___x_4041_);
lean_dec(v___x_4040_);
v___y_4014_ = v_defn_4037_;
v_exportedInfo_x3f_4015_ = v___x_3933_;
v___y_4016_ = v___y_4038_;
v___y_4017_ = v___y_4039_;
goto v___jp_4013_;
}
}
}
}
}
else
{
lean_object* v___f_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; uint8_t v___x_4117_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v_a_4121_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4151_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v_a_4167_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4209_; lean_object* v___y_4210_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; uint8_t v___y_4230_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; 
lean_inc(v_decl_3719_);
v___f_4114_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4114_, 0, v_decl_3719_);
v___x_4115_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4116_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4117_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3777_, v_options_3776_, v___x_4116_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4417_; uint8_t v___x_4418_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4427_; lean_object* v___y_4428_; lean_object* v___y_4429_; lean_object* v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; uint8_t v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4524_; lean_object* v___y_4525_; uint8_t v___y_4526_; lean_object* v_exportedInfo_x3f_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4539_; lean_object* v___y_4540_; uint8_t v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4546_; lean_object* v___y_4547_; uint8_t v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; 
v___x_4417_ = l_Lean_trace_profiler;
v___x_4418_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3776_, v___x_4417_);
if (v___x_4418_ == 0)
{
lean_object* v___x_4552_; lean_object* v_env_4553_; lean_object* v_nextMacroScope_4554_; lean_object* v_ngen_4555_; lean_object* v_auxDeclNGen_4556_; lean_object* v_traceState_4557_; lean_object* v_messages_4558_; lean_object* v_infoState_4559_; lean_object* v_snapshotTasks_4560_; lean_object* v___x_4562_; uint8_t v_isShared_4563_; uint8_t v_isSharedCheck_4796_; 
lean_dec_ref(v___f_4114_);
v___x_4552_ = lean_st_ref_take(v_a_3722_);
v_env_4553_ = lean_ctor_get(v___x_4552_, 0);
v_nextMacroScope_4554_ = lean_ctor_get(v___x_4552_, 1);
v_ngen_4555_ = lean_ctor_get(v___x_4552_, 2);
v_auxDeclNGen_4556_ = lean_ctor_get(v___x_4552_, 3);
v_traceState_4557_ = lean_ctor_get(v___x_4552_, 4);
v_messages_4558_ = lean_ctor_get(v___x_4552_, 6);
v_infoState_4559_ = lean_ctor_get(v___x_4552_, 7);
v_snapshotTasks_4560_ = lean_ctor_get(v___x_4552_, 8);
v_isSharedCheck_4796_ = !lean_is_exclusive(v___x_4552_);
if (v_isSharedCheck_4796_ == 0)
{
lean_object* v_unused_4797_; 
v_unused_4797_ = lean_ctor_get(v___x_4552_, 5);
lean_dec(v_unused_4797_);
v___x_4562_ = v___x_4552_;
v_isShared_4563_ = v_isSharedCheck_4796_;
goto v_resetjp_4561_;
}
else
{
lean_inc(v_snapshotTasks_4560_);
lean_inc(v_infoState_4559_);
lean_inc(v_messages_4558_);
lean_inc(v_traceState_4557_);
lean_inc(v_auxDeclNGen_4556_);
lean_inc(v_ngen_4555_);
lean_inc(v_nextMacroScope_4554_);
lean_inc(v_env_4553_);
lean_dec(v___x_4552_);
v___x_4562_ = lean_box(0);
v_isShared_4563_ = v_isSharedCheck_4796_;
goto v_resetjp_4561_;
}
v_resetjp_4561_:
{
lean_object* v___x_4564_; lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; uint8_t v___y_4573_; lean_object* v___x_4596_; 
lean_inc(v_decl_3719_);
v___x_4564_ = l_Lean_Declaration_getNames(v_decl_3719_);
v___x_4565_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4553_, v___x_4564_);
v___x_4566_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4563_ == 0)
{
lean_ctor_set(v___x_4562_, 5, v___x_4566_);
lean_ctor_set(v___x_4562_, 0, v___x_4565_);
v___x_4596_ = v___x_4562_;
goto v_reusejp_4595_;
}
else
{
lean_object* v_reuseFailAlloc_4795_; 
v_reuseFailAlloc_4795_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4795_, 0, v___x_4565_);
lean_ctor_set(v_reuseFailAlloc_4795_, 1, v_nextMacroScope_4554_);
lean_ctor_set(v_reuseFailAlloc_4795_, 2, v_ngen_4555_);
lean_ctor_set(v_reuseFailAlloc_4795_, 3, v_auxDeclNGen_4556_);
lean_ctor_set(v_reuseFailAlloc_4795_, 4, v_traceState_4557_);
lean_ctor_set(v_reuseFailAlloc_4795_, 5, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4795_, 6, v_messages_4558_);
lean_ctor_set(v_reuseFailAlloc_4795_, 7, v_infoState_4559_);
lean_ctor_set(v_reuseFailAlloc_4795_, 8, v_snapshotTasks_4560_);
v___x_4596_ = v_reuseFailAlloc_4795_;
goto v_reusejp_4595_;
}
v___jp_4567_:
{
lean_object* v___x_4574_; lean_object* v_env_4575_; lean_object* v_nextMacroScope_4576_; lean_object* v_ngen_4577_; lean_object* v_auxDeclNGen_4578_; lean_object* v_traceState_4579_; lean_object* v_messages_4580_; lean_object* v_infoState_4581_; lean_object* v_snapshotTasks_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4593_; 
v___x_4574_ = lean_st_ref_take(v___y_4569_);
v_env_4575_ = lean_ctor_get(v___x_4574_, 0);
v_nextMacroScope_4576_ = lean_ctor_get(v___x_4574_, 1);
v_ngen_4577_ = lean_ctor_get(v___x_4574_, 2);
v_auxDeclNGen_4578_ = lean_ctor_get(v___x_4574_, 3);
v_traceState_4579_ = lean_ctor_get(v___x_4574_, 4);
v_messages_4580_ = lean_ctor_get(v___x_4574_, 6);
v_infoState_4581_ = lean_ctor_get(v___x_4574_, 7);
v_snapshotTasks_4582_ = lean_ctor_get(v___x_4574_, 8);
v_isSharedCheck_4593_ = !lean_is_exclusive(v___x_4574_);
if (v_isSharedCheck_4593_ == 0)
{
lean_object* v_unused_4594_; 
v_unused_4594_ = lean_ctor_get(v___x_4574_, 5);
lean_dec(v_unused_4594_);
v___x_4584_ = v___x_4574_;
v_isShared_4585_ = v_isSharedCheck_4593_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_snapshotTasks_4582_);
lean_inc(v_infoState_4581_);
lean_inc(v_messages_4580_);
lean_inc(v_traceState_4579_);
lean_inc(v_auxDeclNGen_4578_);
lean_inc(v_ngen_4577_);
lean_inc(v_nextMacroScope_4576_);
lean_inc(v_env_4575_);
lean_dec(v___x_4574_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4593_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___x_4586_; lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v___x_4590_; 
v___x_4586_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4587_ = lean_box(v___y_4573_);
lean_inc(v___y_4572_);
v___x_4588_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4586_, v_env_4575_, v___y_4572_, v___x_4587_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 5, v___x_4566_);
lean_ctor_set(v___x_4584_, 0, v___x_4588_);
v___x_4590_ = v___x_4584_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4592_; 
v_reuseFailAlloc_4592_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4592_, 0, v___x_4588_);
lean_ctor_set(v_reuseFailAlloc_4592_, 1, v_nextMacroScope_4576_);
lean_ctor_set(v_reuseFailAlloc_4592_, 2, v_ngen_4577_);
lean_ctor_set(v_reuseFailAlloc_4592_, 3, v_auxDeclNGen_4578_);
lean_ctor_set(v_reuseFailAlloc_4592_, 4, v_traceState_4579_);
lean_ctor_set(v_reuseFailAlloc_4592_, 5, v___x_4566_);
lean_ctor_set(v_reuseFailAlloc_4592_, 6, v_messages_4580_);
lean_ctor_set(v_reuseFailAlloc_4592_, 7, v_infoState_4581_);
lean_ctor_set(v_reuseFailAlloc_4592_, 8, v_snapshotTasks_4582_);
v___x_4590_ = v_reuseFailAlloc_4592_;
goto v_reusejp_4589_;
}
v_reusejp_4589_:
{
lean_object* v___x_4591_; 
v___x_4591_ = lean_st_ref_set(v___y_4569_, v___x_4590_);
v___y_4524_ = v___y_4570_;
v___y_4525_ = v___y_4572_;
v___y_4526_ = v___y_4573_;
v_exportedInfo_x3f_4527_ = v___y_4571_;
v___y_4528_ = v___y_4568_;
v___y_4529_ = v___y_4569_;
goto v___jp_4523_;
}
}
}
v_reusejp_4595_:
{
lean_object* v___x_4597_; lean_object* v___y_4599_; lean_object* v_options_4600_; lean_object* v_inheritedTraceOptions_4601_; lean_object* v___y_4602_; lean_object* v___x_4608_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; uint8_t v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v_fst_4641_; lean_object* v_fst_4642_; uint8_t v_snd_4643_; lean_object* v_exportedInfo_x3f_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4656_; lean_object* v_toConstantVal_4657_; lean_object* v_exportedInfo_x3f_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4665_; lean_object* v_toConstantVal_4666_; uint8_t v_safety_4667_; lean_object* v___y_4668_; lean_object* v___y_4669_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4682_; lean_object* v___y_4683_; lean_object* v___y_4684_; lean_object* v___y_4699_; lean_object* v_exportedInfo_x3f_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4705_; lean_object* v___y_4706_; lean_object* v___y_4707_; lean_object* v___y_4708_; lean_object* v___y_4709_; lean_object* v_defn_4714_; lean_object* v___y_4715_; lean_object* v___y_4716_; 
v___x_4597_ = lean_st_ref_set(v_a_3722_, v___x_4596_);
v___x_4608_ = lean_box(0);
switch(lean_obj_tag(v_decl_3719_))
{
case 2:
{
lean_object* v_val_4723_; lean_object* v_exportedInfo_x3f_4725_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4733_; lean_object* v___y_4734_; lean_object* v___x_4739_; lean_object* v_env_4740_; 
v_val_4723_ = lean_ctor_get(v_decl_3719_, 0);
v___x_4739_ = lean_st_ref_get(v_a_3722_);
v_env_4740_ = lean_ctor_get(v___x_4739_, 0);
lean_inc_ref(v_env_4740_);
lean_dec(v___x_4739_);
if (v_forceExpose_3720_ == 0)
{
goto v___jp_4741_;
}
else
{
if (v___x_4418_ == 0)
{
lean_dec_ref(v_env_4740_);
v_exportedInfo_x3f_4725_ = v___x_4608_;
v___y_4726_ = v_a_3721_;
v___y_4727_ = v_a_3722_;
goto v___jp_4724_;
}
else
{
goto v___jp_4741_;
}
}
v___jp_4724_:
{
lean_object* v_toConstantVal_4728_; lean_object* v_name_4729_; lean_object* v___x_4730_; uint8_t v___x_4731_; 
v_toConstantVal_4728_ = lean_ctor_get(v_val_4723_, 0);
v_name_4729_ = lean_ctor_get(v_toConstantVal_4728_, 0);
lean_inc_ref(v_val_4723_);
v___x_4730_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4730_, 0, v_val_4723_);
v___x_4731_ = 1;
lean_inc(v_name_4729_);
v_fst_4641_ = v_name_4729_;
v_fst_4642_ = v___x_4730_;
v_snd_4643_ = v___x_4731_;
v_exportedInfo_x3f_4644_ = v_exportedInfo_x3f_4725_;
v___y_4645_ = v___y_4726_;
v___y_4646_ = v___y_4727_;
goto v___jp_4640_;
}
v___jp_4732_:
{
lean_object* v_toConstantVal_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; lean_object* v___x_4738_; 
v_toConstantVal_4735_ = lean_ctor_get(v_val_4723_, 0);
lean_inc_ref(v_toConstantVal_4735_);
v___x_4736_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4736_, 0, v_toConstantVal_4735_);
lean_ctor_set_uint8(v___x_4736_, sizeof(void*)*1, v___x_4418_);
v___x_4737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
v___x_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4738_, 0, v___x_4737_);
v_exportedInfo_x3f_4725_ = v___x_4738_;
v___y_4726_ = v___y_4733_;
v___y_4727_ = v___y_4734_;
goto v___jp_4724_;
}
v___jp_4741_:
{
lean_object* v___x_4742_; uint8_t v_isModule_4743_; 
v___x_4742_ = l_Lean_Environment_header(v_env_4740_);
lean_dec_ref(v_env_4740_);
v_isModule_4743_ = lean_ctor_get_uint8(v___x_4742_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4742_);
if (v_isModule_4743_ == 0)
{
v_exportedInfo_x3f_4725_ = v___x_4608_;
v___y_4726_ = v_a_3721_;
v___y_4727_ = v_a_3722_;
goto v___jp_4724_;
}
else
{
if (v___x_4117_ == 0)
{
v___y_4733_ = v_a_3721_;
v___y_4734_ = v_a_3722_;
goto v___jp_4732_;
}
else
{
lean_object* v_toConstantVal_4744_; lean_object* v_name_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v_toConstantVal_4744_ = lean_ctor_get(v_val_4723_, 0);
v_name_4745_ = lean_ctor_get(v_toConstantVal_4744_, 0);
v___x_4746_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4745_);
v___x_4747_ = l_Lean_MessageData_ofName(v_name_4745_);
v___x_4748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4750_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_dec_ref_known(v___x_4751_, 1);
v___y_4733_ = v_a_3721_;
v___y_4734_ = v_a_3722_;
goto v___jp_4732_;
}
else
{
lean_dec_ref_known(v_decl_3719_, 1);
return v___x_4751_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4752_; 
v_val_4752_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref(v_val_4752_);
v_defn_4714_ = v_val_4752_;
v___y_4715_ = v_a_3721_;
v___y_4716_ = v_a_3722_;
goto v___jp_4713_;
}
case 5:
{
lean_object* v_defns_4753_; 
v_defns_4753_ = lean_ctor_get(v_decl_3719_, 0);
if (lean_obj_tag(v_defns_4753_) == 1)
{
lean_object* v_tail_4754_; 
v_tail_4754_ = lean_ctor_get(v_defns_4753_, 1);
if (lean_obj_tag(v_tail_4754_) == 0)
{
lean_object* v_head_4755_; 
v_head_4755_ = lean_ctor_get(v_defns_4753_, 0);
lean_inc(v_head_4755_);
v_defn_4714_ = v_head_4755_;
v___y_4715_ = v_a_3721_;
v___y_4716_ = v_a_3722_;
goto v___jp_4713_;
}
else
{
v___y_4599_ = v_a_3721_;
v_options_4600_ = v_options_3776_;
v_inheritedTraceOptions_4601_ = v_inheritedTraceOptions_3777_;
v___y_4602_ = v_a_3722_;
goto v___jp_4598_;
}
}
else
{
v___y_4599_ = v_a_3721_;
v_options_4600_ = v_options_3776_;
v_inheritedTraceOptions_4601_ = v_inheritedTraceOptions_3777_;
v___y_4602_ = v_a_3722_;
goto v___jp_4598_;
}
}
case 3:
{
lean_object* v_val_4756_; lean_object* v_exportedInfo_x3f_4758_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v_env_4784_; lean_object* v_env_4785_; 
v_val_4756_ = lean_ctor_get(v_decl_3719_, 0);
v___x_4773_ = lean_st_ref_get(v_a_3722_);
v___x_4774_ = lean_st_ref_get(v_a_3722_);
v_env_4784_ = lean_ctor_get(v___x_4773_, 0);
lean_inc_ref(v_env_4784_);
lean_dec(v___x_4773_);
v_env_4785_ = lean_ctor_get(v___x_4774_, 0);
lean_inc_ref(v_env_4785_);
lean_dec(v___x_4774_);
if (v_forceExpose_3720_ == 0)
{
goto v___jp_4786_;
}
else
{
if (v___x_4418_ == 0)
{
lean_dec_ref(v_env_4785_);
lean_dec_ref(v_env_4784_);
v_exportedInfo_x3f_4758_ = v___x_4608_;
v___y_4759_ = v_a_3721_;
v___y_4760_ = v_a_3722_;
goto v___jp_4757_;
}
else
{
goto v___jp_4786_;
}
}
v___jp_4757_:
{
lean_object* v_toConstantVal_4761_; lean_object* v_name_4762_; lean_object* v___x_4763_; uint8_t v___x_4764_; 
v_toConstantVal_4761_ = lean_ctor_get(v_val_4756_, 0);
v_name_4762_ = lean_ctor_get(v_toConstantVal_4761_, 0);
lean_inc_ref(v_val_4756_);
v___x_4763_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4763_, 0, v_val_4756_);
v___x_4764_ = 3;
lean_inc(v_name_4762_);
v_fst_4641_ = v_name_4762_;
v_fst_4642_ = v___x_4763_;
v_snd_4643_ = v___x_4764_;
v_exportedInfo_x3f_4644_ = v_exportedInfo_x3f_4758_;
v___y_4645_ = v___y_4759_;
v___y_4646_ = v___y_4760_;
goto v___jp_4640_;
}
v___jp_4765_:
{
lean_object* v_toConstantVal_4768_; uint8_t v_isUnsafe_4769_; lean_object* v___x_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; 
v_toConstantVal_4768_ = lean_ctor_get(v_val_4756_, 0);
v_isUnsafe_4769_ = lean_ctor_get_uint8(v_val_4756_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4768_);
v___x_4770_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4770_, 0, v_toConstantVal_4768_);
lean_ctor_set_uint8(v___x_4770_, sizeof(void*)*1, v_isUnsafe_4769_);
v___x_4771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4771_, 0, v___x_4770_);
v___x_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4772_, 0, v___x_4771_);
v_exportedInfo_x3f_4758_ = v___x_4772_;
v___y_4759_ = v___y_4766_;
v___y_4760_ = v___y_4767_;
goto v___jp_4757_;
}
v___jp_4775_:
{
if (v___x_4117_ == 0)
{
v___y_4766_ = v_a_3721_;
v___y_4767_ = v_a_3722_;
goto v___jp_4765_;
}
else
{
lean_object* v_toConstantVal_4776_; lean_object* v_name_4777_; lean_object* v___x_4778_; lean_object* v___x_4779_; lean_object* v___x_4780_; lean_object* v___x_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; 
v_toConstantVal_4776_ = lean_ctor_get(v_val_4756_, 0);
v_name_4777_ = lean_ctor_get(v_toConstantVal_4776_, 0);
v___x_4778_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4777_);
v___x_4779_ = l_Lean_MessageData_ofName(v_name_4777_);
v___x_4780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4780_, 0, v___x_4778_);
lean_ctor_set(v___x_4780_, 1, v___x_4779_);
v___x_4781_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4782_, 0, v___x_4780_);
lean_ctor_set(v___x_4782_, 1, v___x_4781_);
v___x_4783_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4782_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4783_) == 0)
{
lean_dec_ref_known(v___x_4783_, 1);
v___y_4766_ = v_a_3721_;
v___y_4767_ = v_a_3722_;
goto v___jp_4765_;
}
else
{
lean_dec_ref_known(v_decl_3719_, 1);
return v___x_4783_;
}
}
}
v___jp_4786_:
{
lean_object* v___x_4787_; uint8_t v_isModule_4788_; 
v___x_4787_ = l_Lean_Environment_header(v_env_4784_);
lean_dec_ref(v_env_4784_);
v_isModule_4788_ = lean_ctor_get_uint8(v___x_4787_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4787_);
if (v_isModule_4788_ == 0)
{
lean_dec_ref(v_env_4785_);
v_exportedInfo_x3f_4758_ = v___x_4608_;
v___y_4759_ = v_a_3721_;
v___y_4760_ = v_a_3722_;
goto v___jp_4757_;
}
else
{
uint8_t v_isExporting_4789_; 
v_isExporting_4789_ = lean_ctor_get_uint8(v_env_4785_, sizeof(void*)*8);
lean_dec_ref(v_env_4785_);
if (v_isExporting_4789_ == 0)
{
goto v___jp_4775_;
}
else
{
if (v___x_4418_ == 0)
{
v_exportedInfo_x3f_4758_ = v___x_4608_;
v___y_4759_ = v_a_3721_;
v___y_4760_ = v_a_3722_;
goto v___jp_4757_;
}
else
{
goto v___jp_4775_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4790_; lean_object* v_toConstantVal_4791_; lean_object* v_name_4792_; lean_object* v___x_4793_; uint8_t v___x_4794_; 
v_val_4790_ = lean_ctor_get(v_decl_3719_, 0);
v_toConstantVal_4791_ = lean_ctor_get(v_val_4790_, 0);
v_name_4792_ = lean_ctor_get(v_toConstantVal_4791_, 0);
lean_inc_ref(v_val_4790_);
v___x_4793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4793_, 0, v_val_4790_);
v___x_4794_ = 2;
lean_inc(v_name_4792_);
v_fst_4641_ = v_name_4792_;
v_fst_4642_ = v___x_4793_;
v_snd_4643_ = v___x_4794_;
v_exportedInfo_x3f_4644_ = v___x_4608_;
v___y_4645_ = v_a_3721_;
v___y_4646_ = v_a_3722_;
goto v___jp_4640_;
}
default: 
{
v___y_4599_ = v_a_3721_;
v_options_4600_ = v_options_3776_;
v_inheritedTraceOptions_4601_ = v_inheritedTraceOptions_3777_;
v___y_4602_ = v_a_3722_;
goto v___jp_4598_;
}
}
v___jp_4598_:
{
uint8_t v___x_4603_; 
v___x_4603_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4601_, v_options_4600_, v___x_4116_);
if (v___x_4603_ == 0)
{
lean_object* v___x_4604_; 
v___x_4604_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v___y_4599_, v___y_4602_);
return v___x_4604_;
}
else
{
lean_object* v___x_4605_; lean_object* v___x_4606_; 
v___x_4605_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4606_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4605_, v___y_4599_, v___y_4602_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v___x_4607_; 
lean_dec_ref_known(v___x_4606_, 1);
v___x_4607_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v___y_4599_, v___y_4602_);
return v___x_4607_;
}
else
{
lean_dec(v_decl_3719_);
return v___x_4606_;
}
}
}
v___jp_4609_:
{
lean_object* v___x_4616_; uint8_t v___x_4617_; 
lean_inc(v_decl_3719_);
v___x_4616_ = l_Lean_Declaration_getTopLevelNames(v_decl_3719_);
v___x_4617_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4616_);
lean_dec(v___x_4616_);
if (v___x_4617_ == 0)
{
if (lean_obj_tag(v___y_4611_) == 0)
{
if (v___x_4418_ == 0)
{
lean_object* v_options_4618_; uint8_t v_hasTrace_4619_; 
v_options_4618_ = lean_ctor_get(v___y_4614_, 2);
v_hasTrace_4619_ = lean_ctor_get_uint8(v_options_4618_, sizeof(void*)*1);
if (v_hasTrace_4619_ == 0)
{
v___y_4539_ = v___y_4610_;
v___y_4540_ = v___y_4612_;
v___y_4541_ = v___y_4613_;
v___y_4542_ = v___y_4614_;
v___y_4543_ = v___y_4615_;
goto v___jp_4538_;
}
else
{
lean_object* v_inheritedTraceOptions_4620_; uint8_t v___x_4621_; 
v_inheritedTraceOptions_4620_ = lean_ctor_get(v___y_4614_, 13);
v___x_4621_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4620_, v_options_4618_, v___x_4116_);
if (v___x_4621_ == 0)
{
v___y_4539_ = v___y_4610_;
v___y_4540_ = v___y_4612_;
v___y_4541_ = v___y_4613_;
v___y_4542_ = v___y_4614_;
v___y_4543_ = v___y_4615_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4622_; lean_object* v___x_4623_; 
v___x_4622_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4623_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4622_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_dec_ref_known(v___x_4623_, 1);
v___y_4539_ = v___y_4610_;
v___y_4540_ = v___y_4612_;
v___y_4541_ = v___y_4613_;
v___y_4542_ = v___y_4614_;
v___y_4543_ = v___y_4615_;
goto v___jp_4538_;
}
else
{
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4610_);
lean_dec(v_decl_3719_);
return v___x_4623_;
}
}
}
}
else
{
v___y_4568_ = v___y_4614_;
v___y_4569_ = v___y_4615_;
v___y_4570_ = v___y_4610_;
v___y_4571_ = v___y_4611_;
v___y_4572_ = v___y_4612_;
v___y_4573_ = v___y_4613_;
goto v___jp_4567_;
}
}
else
{
v___y_4568_ = v___y_4614_;
v___y_4569_ = v___y_4615_;
v___y_4570_ = v___y_4610_;
v___y_4571_ = v___y_4611_;
v___y_4572_ = v___y_4612_;
v___y_4573_ = v___y_4613_;
goto v___jp_4567_;
}
}
else
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v_a_4626_; uint8_t v___x_4627_; 
lean_dec(v___y_4611_);
v___x_4624_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4625_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4624_, v___y_4614_);
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v___x_4627_ = lean_unbox(v_a_4626_);
lean_dec(v_a_4626_);
if (v___x_4627_ == 0)
{
lean_object* v_options_4628_; uint8_t v_hasTrace_4629_; 
v_options_4628_ = lean_ctor_get(v___y_4614_, 2);
v_hasTrace_4629_ = lean_ctor_get_uint8(v_options_4628_, sizeof(void*)*1);
if (v_hasTrace_4629_ == 0)
{
v___y_4524_ = v___y_4610_;
v___y_4525_ = v___y_4612_;
v___y_4526_ = v___y_4613_;
v_exportedInfo_x3f_4527_ = v___x_4608_;
v___y_4528_ = v___y_4614_;
v___y_4529_ = v___y_4615_;
goto v___jp_4523_;
}
else
{
lean_object* v_inheritedTraceOptions_4630_; uint8_t v___x_4631_; 
v_inheritedTraceOptions_4630_ = lean_ctor_get(v___y_4614_, 13);
v___x_4631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4630_, v_options_4628_, v___x_4116_);
if (v___x_4631_ == 0)
{
v___y_4524_ = v___y_4610_;
v___y_4525_ = v___y_4612_;
v___y_4526_ = v___y_4613_;
v_exportedInfo_x3f_4527_ = v___x_4608_;
v___y_4528_ = v___y_4614_;
v___y_4529_ = v___y_4615_;
goto v___jp_4523_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4633_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4632_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_dec_ref_known(v___x_4633_, 1);
v___y_4524_ = v___y_4610_;
v___y_4525_ = v___y_4612_;
v___y_4526_ = v___y_4613_;
v_exportedInfo_x3f_4527_ = v___x_4608_;
v___y_4528_ = v___y_4614_;
v___y_4529_ = v___y_4615_;
goto v___jp_4523_;
}
else
{
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4610_);
lean_dec(v_decl_3719_);
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_options_4634_; uint8_t v_hasTrace_4635_; 
v_options_4634_ = lean_ctor_get(v___y_4614_, 2);
v_hasTrace_4635_ = lean_ctor_get_uint8(v_options_4634_, sizeof(void*)*1);
if (v_hasTrace_4635_ == 0)
{
v___y_4546_ = v___y_4610_;
v___y_4547_ = v___y_4612_;
v___y_4548_ = v___y_4613_;
v___y_4549_ = v___y_4614_;
v___y_4550_ = v___y_4615_;
goto v___jp_4545_;
}
else
{
lean_object* v_inheritedTraceOptions_4636_; uint8_t v___x_4637_; 
v_inheritedTraceOptions_4636_ = lean_ctor_get(v___y_4614_, 13);
v___x_4637_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4636_, v_options_4634_, v___x_4116_);
if (v___x_4637_ == 0)
{
v___y_4546_ = v___y_4610_;
v___y_4547_ = v___y_4612_;
v___y_4548_ = v___y_4613_;
v___y_4549_ = v___y_4614_;
v___y_4550_ = v___y_4615_;
goto v___jp_4545_;
}
else
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4639_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4638_, v___y_4614_, v___y_4615_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_dec_ref_known(v___x_4639_, 1);
v___y_4546_ = v___y_4610_;
v___y_4547_ = v___y_4612_;
v___y_4548_ = v___y_4613_;
v___y_4549_ = v___y_4614_;
v___y_4550_ = v___y_4615_;
goto v___jp_4545_;
}
else
{
lean_dec(v___y_4612_);
lean_dec_ref(v___y_4610_);
lean_dec(v_decl_3719_);
return v___x_4639_;
}
}
}
}
}
}
v___jp_4640_:
{
lean_object* v___x_4647_; lean_object* v_env_4648_; uint8_t v___x_4649_; 
v___x_4647_ = lean_st_ref_get(v___y_4646_);
v_env_4648_ = lean_ctor_get(v___x_4647_, 0);
lean_inc_ref(v_env_4648_);
lean_dec(v___x_4647_);
v___x_4649_ = l_Lean_Environment_containsOnBranch(v_env_4648_, v_fst_4641_);
lean_dec_ref(v_env_4648_);
if (v___x_4649_ == 0)
{
v___y_4610_ = v_fst_4642_;
v___y_4611_ = v_exportedInfo_x3f_4644_;
v___y_4612_ = v_fst_4641_;
v___y_4613_ = v_snd_4643_;
v___y_4614_ = v___y_4645_;
v___y_4615_ = v___y_4646_;
goto v___jp_4609_;
}
else
{
lean_object* v___x_4650_; lean_object* v_env_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
lean_dec(v_exportedInfo_x3f_4644_);
lean_dec_ref(v_fst_4642_);
lean_dec(v_decl_3719_);
v___x_4650_ = lean_st_ref_get(v___y_4646_);
v_env_4651_ = lean_ctor_get(v___x_4650_, 0);
lean_inc_ref(v_env_4651_);
lean_dec(v___x_4650_);
v___x_4652_ = lean_elab_environment_to_kernel_env(v_env_4651_);
v___x_4653_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4653_, 0, v___x_4652_);
lean_ctor_set(v___x_4653_, 1, v_fst_4641_);
v___x_4654_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4653_, v___y_4645_, v___y_4646_);
return v___x_4654_;
}
}
v___jp_4655_:
{
lean_object* v_name_4661_; lean_object* v___x_4662_; uint8_t v___x_4663_; 
v_name_4661_ = lean_ctor_get(v_toConstantVal_4657_, 0);
lean_inc(v_name_4661_);
lean_dec_ref(v_toConstantVal_4657_);
v___x_4662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4662_, 0, v___y_4656_);
v___x_4663_ = 0;
v_fst_4641_ = v_name_4661_;
v_fst_4642_ = v___x_4662_;
v_snd_4643_ = v___x_4663_;
v_exportedInfo_x3f_4644_ = v_exportedInfo_x3f_4658_;
v___y_4645_ = v___y_4659_;
v___y_4646_ = v___y_4660_;
goto v___jp_4640_;
}
v___jp_4664_:
{
uint8_t v___x_4670_; uint8_t v___x_4671_; lean_object* v___x_4672_; lean_object* v___x_4673_; lean_object* v___x_4674_; 
v___x_4670_ = 0;
v___x_4671_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4667_, v___x_4670_);
lean_inc_ref(v_toConstantVal_4666_);
v___x_4672_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4672_, 0, v_toConstantVal_4666_);
lean_ctor_set_uint8(v___x_4672_, sizeof(void*)*1, v___x_4671_);
v___x_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4673_, 0, v___x_4672_);
v___x_4674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4674_, 0, v___x_4673_);
v___y_4656_ = v___y_4665_;
v_toConstantVal_4657_ = v_toConstantVal_4666_;
v_exportedInfo_x3f_4658_ = v___x_4674_;
v___y_4659_ = v___y_4668_;
v___y_4660_ = v___y_4669_;
goto v___jp_4655_;
}
v___jp_4675_:
{
lean_object* v_toConstantVal_4679_; uint8_t v_safety_4680_; 
v_toConstantVal_4679_ = lean_ctor_get(v___y_4676_, 0);
lean_inc_ref(v_toConstantVal_4679_);
v_safety_4680_ = lean_ctor_get_uint8(v___y_4676_, sizeof(void*)*4);
v___y_4665_ = v___y_4676_;
v_toConstantVal_4666_ = v_toConstantVal_4679_;
v_safety_4667_ = v_safety_4680_;
v___y_4668_ = v___y_4677_;
v___y_4669_ = v___y_4678_;
goto v___jp_4664_;
}
v___jp_4681_:
{
lean_object* v_options_4685_; uint8_t v_hasTrace_4686_; 
v_options_4685_ = lean_ctor_get(v___y_4684_, 2);
v_hasTrace_4686_ = lean_ctor_get_uint8(v_options_4685_, sizeof(void*)*1);
if (v_hasTrace_4686_ == 0)
{
v___y_4676_ = v___y_4682_;
v___y_4677_ = v___y_4684_;
v___y_4678_ = v___y_4683_;
goto v___jp_4675_;
}
else
{
lean_object* v_inheritedTraceOptions_4687_; uint8_t v___x_4688_; 
v_inheritedTraceOptions_4687_ = lean_ctor_get(v___y_4684_, 13);
v___x_4688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4687_, v_options_4685_, v___x_4116_);
if (v___x_4688_ == 0)
{
v___y_4676_ = v___y_4682_;
v___y_4677_ = v___y_4684_;
v___y_4678_ = v___y_4683_;
goto v___jp_4675_;
}
else
{
lean_object* v_toConstantVal_4689_; uint8_t v_safety_4690_; lean_object* v_name_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; 
v_toConstantVal_4689_ = lean_ctor_get(v___y_4682_, 0);
lean_inc_ref(v_toConstantVal_4689_);
v_safety_4690_ = lean_ctor_get_uint8(v___y_4682_, sizeof(void*)*4);
v_name_4691_ = lean_ctor_get(v_toConstantVal_4689_, 0);
v___x_4692_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4691_);
v___x_4693_ = l_Lean_MessageData_ofName(v_name_4691_);
v___x_4694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4694_, 0, v___x_4692_);
lean_ctor_set(v___x_4694_, 1, v___x_4693_);
v___x_4695_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4696_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4694_);
lean_ctor_set(v___x_4696_, 1, v___x_4695_);
v___x_4697_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4696_, v___y_4684_, v___y_4683_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_dec_ref_known(v___x_4697_, 1);
v___y_4665_ = v___y_4682_;
v_toConstantVal_4666_ = v_toConstantVal_4689_;
v_safety_4667_ = v_safety_4690_;
v___y_4668_ = v___y_4684_;
v___y_4669_ = v___y_4683_;
goto v___jp_4664_;
}
else
{
lean_dec_ref(v_toConstantVal_4689_);
lean_dec_ref(v___y_4682_);
lean_dec(v_decl_3719_);
return v___x_4697_;
}
}
}
}
v___jp_4698_:
{
lean_object* v_toConstantVal_4703_; 
v_toConstantVal_4703_ = lean_ctor_get(v___y_4699_, 0);
lean_inc_ref(v_toConstantVal_4703_);
v___y_4656_ = v___y_4699_;
v_toConstantVal_4657_ = v_toConstantVal_4703_;
v_exportedInfo_x3f_4658_ = v_exportedInfo_x3f_4700_;
v___y_4659_ = v___y_4701_;
v___y_4660_ = v___y_4702_;
goto v___jp_4655_;
}
v___jp_4704_:
{
lean_object* v___x_4710_; uint8_t v_isModule_4711_; 
v___x_4710_ = l_Lean_Environment_header(v___y_4709_);
lean_dec_ref(v___y_4709_);
v_isModule_4711_ = lean_ctor_get_uint8(v___x_4710_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4710_);
if (v_isModule_4711_ == 0)
{
lean_dec_ref(v___y_4705_);
v___y_4699_ = v___y_4706_;
v_exportedInfo_x3f_4700_ = v___x_4608_;
v___y_4701_ = v___y_4708_;
v___y_4702_ = v___y_4707_;
goto v___jp_4698_;
}
else
{
uint8_t v_isExporting_4712_; 
v_isExporting_4712_ = lean_ctor_get_uint8(v___y_4705_, sizeof(void*)*8);
lean_dec_ref(v___y_4705_);
if (v_isExporting_4712_ == 0)
{
v___y_4682_ = v___y_4706_;
v___y_4683_ = v___y_4707_;
v___y_4684_ = v___y_4708_;
goto v___jp_4681_;
}
else
{
if (v___x_4418_ == 0)
{
v___y_4699_ = v___y_4706_;
v_exportedInfo_x3f_4700_ = v___x_4608_;
v___y_4701_ = v___y_4708_;
v___y_4702_ = v___y_4707_;
goto v___jp_4698_;
}
else
{
v___y_4682_ = v___y_4706_;
v___y_4683_ = v___y_4707_;
v___y_4684_ = v___y_4708_;
goto v___jp_4681_;
}
}
}
}
v___jp_4713_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = lean_st_ref_get(v___y_4716_);
v___x_4718_ = lean_st_ref_get(v___y_4716_);
if (v_forceExpose_3720_ == 0)
{
lean_object* v_env_4719_; lean_object* v_env_4720_; 
v_env_4719_ = lean_ctor_get(v___x_4717_, 0);
lean_inc_ref(v_env_4719_);
lean_dec(v___x_4717_);
v_env_4720_ = lean_ctor_get(v___x_4718_, 0);
lean_inc_ref(v_env_4720_);
lean_dec(v___x_4718_);
v___y_4705_ = v_env_4720_;
v___y_4706_ = v_defn_4714_;
v___y_4707_ = v___y_4716_;
v___y_4708_ = v___y_4715_;
v___y_4709_ = v_env_4719_;
goto v___jp_4704_;
}
else
{
if (v___x_4418_ == 0)
{
lean_dec(v___x_4718_);
lean_dec(v___x_4717_);
v___y_4699_ = v_defn_4714_;
v_exportedInfo_x3f_4700_ = v___x_4608_;
v___y_4701_ = v___y_4715_;
v___y_4702_ = v___y_4716_;
goto v___jp_4698_;
}
else
{
lean_object* v_env_4721_; lean_object* v_env_4722_; 
v_env_4721_ = lean_ctor_get(v___x_4717_, 0);
lean_inc_ref(v_env_4721_);
lean_dec(v___x_4717_);
v_env_4722_ = lean_ctor_get(v___x_4718_, 0);
lean_inc_ref(v_env_4722_);
lean_dec(v___x_4718_);
v___y_4705_ = v_env_4722_;
v___y_4706_ = v_defn_4714_;
v___y_4707_ = v___y_4716_;
v___y_4708_ = v___y_4715_;
v___y_4709_ = v_env_4721_;
goto v___jp_4704_;
}
}
}
}
}
}
else
{
goto v___jp_4265_;
}
v___jp_4419_:
{
lean_object* v___x_4430_; 
lean_inc_ref(v___y_4420_);
v___x_4430_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4427_, v___y_4420_, v___y_4422_, v___y_4429_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v___x_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4477_; 
lean_dec_ref_known(v___x_4430_, 1);
lean_inc_ref(v___y_4428_);
v___x_4431_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4428_, v___y_4421_);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4477_ == 0)
{
lean_object* v_unused_4478_; 
v_unused_4478_ = lean_ctor_get(v___x_4431_, 0);
lean_dec(v_unused_4478_);
v___x_4433_ = v___x_4431_;
v_isShared_4434_ = v_isSharedCheck_4477_;
goto v_resetjp_4432_;
}
else
{
lean_dec(v___x_4431_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4477_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v_options_4435_; lean_object* v___x_4436_; uint8_t v___x_4437_; 
v_options_4435_ = lean_ctor_get(v___y_4423_, 2);
v___x_4436_ = l_Lean_Elab_async;
v___x_4437_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4435_, v___x_4436_);
if (v___x_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v_r_4439_; 
lean_del_object(v___x_4433_);
lean_dec_ref(v___y_4425_);
lean_dec_ref(v___y_4424_);
v___x_4438_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4420_, v___y_4421_);
lean_dec_ref(v___x_4438_);
v_r_4439_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v___y_4423_, v___y_4421_);
if (lean_obj_tag(v_r_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v___x_4442_; uint8_t v_isShared_4443_; uint8_t v_isSharedCheck_4449_; 
v_a_4440_ = lean_ctor_get(v_r_4439_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v_r_4439_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4442_ = v_r_4439_;
v_isShared_4443_ = v_isSharedCheck_4449_;
goto v_resetjp_4441_;
}
else
{
lean_inc(v_a_4440_);
lean_dec(v_r_4439_);
v___x_4442_ = lean_box(0);
v_isShared_4443_ = v_isSharedCheck_4449_;
goto v_resetjp_4441_;
}
v_resetjp_4441_:
{
lean_object* v___x_4445_; 
lean_inc(v_a_4440_);
if (v_isShared_4443_ == 0)
{
lean_ctor_set_tag(v___x_4442_, 1);
v___x_4445_ = v___x_4442_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4440_);
v___x_4445_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; 
v___x_4446_ = lean_apply_2(v___y_4426_, v___x_4445_, lean_box(0));
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_dec_ref_known(v___x_4446_, 1);
v___y_3751_ = v___y_4421_;
v___y_3752_ = v___y_4428_;
v_a_3753_ = v_a_4440_;
goto v___jp_3750_;
}
else
{
lean_object* v_a_4447_; 
lean_dec(v_a_4440_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___y_3764_ = v___y_4421_;
v___y_3765_ = v___y_4428_;
v_a_3766_ = v_a_4447_;
goto v___jp_3763_;
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v_a_4450_ = lean_ctor_get(v_r_4439_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v_r_4439_, 1);
v___x_4451_ = lean_box(0);
v___x_4452_ = lean_apply_2(v___y_4426_, v___x_4451_, lean_box(0));
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_dec_ref_known(v___x_4452_, 1);
v___y_3764_ = v___y_4421_;
v___y_3765_ = v___y_4428_;
v_a_3766_ = v_a_4450_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_4453_; 
lean_dec(v_a_4450_);
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v___y_3764_ = v___y_4421_;
v___y_3765_ = v___y_4428_;
v_a_3766_ = v_a_4453_;
goto v___jp_3763_;
}
}
}
else
{
lean_object* v___x_4454_; lean_object* v___x_4456_; 
lean_dec_ref(v___y_4428_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4420_);
lean_dec(v_decl_3719_);
v___x_4454_ = l_IO_CancelToken_new();
if (v_isShared_4434_ == 0)
{
lean_ctor_set_tag(v___x_4433_, 1);
lean_ctor_set(v___x_4433_, 0, v___x_4454_);
v___x_4456_ = v___x_4433_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v___x_4454_);
v___x_4456_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; 
v___x_4457_ = lean_unsigned_to_nat(0u);
v___x_4458_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4459_ = l_Lean_Name_toString(v___x_4458_, v_hasTrace_3778_);
lean_inc_ref(v___x_4456_);
v___x_4460_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4425_, v___x_4456_, v___x_4459_, v___y_4423_, v___y_4421_);
if (lean_obj_tag(v___x_4460_) == 0)
{
lean_object* v_a_4461_; lean_object* v_checked_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_a_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc(v_a_4461_);
lean_dec_ref_known(v___x_4460_, 1);
v_checked_4462_ = lean_ctor_get(v___y_4424_, 2);
lean_inc_ref(v_checked_4462_);
lean_dec_ref(v___y_4424_);
v___x_4463_ = lean_io_map_task(v_a_4461_, v_checked_4462_, v___x_4457_, v___x_4418_);
v___x_4464_ = lean_box(0);
v___x_4465_ = lean_box(2);
v___x_4466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4464_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
lean_ctor_set(v___x_4466_, 2, v___x_4456_);
lean_ctor_set(v___x_4466_, 3, v___x_4463_);
v___x_4467_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4466_, v___y_4421_);
return v___x_4467_;
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___x_4456_);
lean_dec_ref(v___y_4424_);
v_a_4468_ = lean_ctor_get(v___x_4460_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4460_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4460_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4460_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4491_; 
lean_dec_ref(v___y_4428_);
lean_dec_ref(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec_ref(v___y_4424_);
lean_dec_ref(v___y_4420_);
lean_dec(v_decl_3719_);
v_a_4479_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4481_ = v___x_4430_;
v_isShared_4482_ = v_isSharedCheck_4491_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4430_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4491_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v_ref_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4489_; 
v_ref_4483_ = lean_ctor_get(v___y_4423_, 5);
v___x_4484_ = lean_io_error_to_string(v_a_4479_);
v___x_4485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4484_);
v___x_4486_ = l_Lean_MessageData_ofFormat(v___x_4485_);
lean_inc(v_ref_4483_);
v___x_4487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4487_, 0, v_ref_4483_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
if (v_isShared_4482_ == 0)
{
lean_ctor_set(v___x_4481_, 0, v___x_4487_);
v___x_4489_ = v___x_4481_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
v___jp_4492_:
{
lean_object* v___x_4503_; 
lean_inc_ref(v___y_4495_);
v___x_4503_ = l_Lean_Environment_addConstAsync(v___y_4495_, v___y_4499_, v___y_4501_, v___y_4502_, v___x_4418_, v_hasTrace_3778_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; lean_object* v_mainEnv_4505_; lean_object* v_asyncEnv_4506_; lean_object* v___f_4507_; lean_object* v___f_4508_; lean_object* v___x_4509_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc_n(v_a_4504_, 3);
lean_dec_ref_known(v___x_4503_, 1);
v_mainEnv_4505_ = lean_ctor_get(v_a_4504_, 0);
lean_inc_ref(v_mainEnv_4505_);
v_asyncEnv_4506_ = lean_ctor_get(v_a_4504_, 1);
lean_inc_ref_n(v_asyncEnv_4506_, 2);
lean_inc_ref(v___y_4494_);
lean_inc(v___y_4493_);
v___f_4507_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4507_, 0, v___y_4493_);
lean_closure_set(v___f_4507_, 1, v_a_4504_);
lean_closure_set(v___f_4507_, 2, v___y_4494_);
lean_inc(v_decl_3719_);
v___f_4508_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4508_, 0, v_asyncEnv_4506_);
lean_closure_set(v___f_4508_, 1, v_a_4504_);
lean_closure_set(v___f_4508_, 2, v_decl_3719_);
v___x_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4509_, 0, v___y_4498_);
if (lean_obj_tag(v___y_4500_) == 0)
{
lean_inc_ref(v___x_4509_);
v___y_4420_ = v_asyncEnv_4506_;
v___y_4421_ = v___y_4496_;
v___y_4422_ = v___x_4509_;
v___y_4423_ = v___y_4497_;
v___y_4424_ = v___y_4495_;
v___y_4425_ = v___f_4508_;
v___y_4426_ = v___f_4507_;
v___y_4427_ = v_a_4504_;
v___y_4428_ = v_mainEnv_4505_;
v___y_4429_ = v___x_4509_;
goto v___jp_4419_;
}
else
{
v___y_4420_ = v_asyncEnv_4506_;
v___y_4421_ = v___y_4496_;
v___y_4422_ = v___x_4509_;
v___y_4423_ = v___y_4497_;
v___y_4424_ = v___y_4495_;
v___y_4425_ = v___f_4508_;
v___y_4426_ = v___f_4507_;
v___y_4427_ = v_a_4504_;
v___y_4428_ = v_mainEnv_4505_;
v___y_4429_ = v___y_4500_;
goto v___jp_4419_;
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4522_; 
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4498_);
lean_dec_ref(v___y_4495_);
lean_dec(v_decl_3719_);
v_a_4510_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4522_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4522_ == 0)
{
v___x_4512_ = v___x_4503_;
v_isShared_4513_ = v_isSharedCheck_4522_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4503_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4522_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v_ref_4514_; lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4520_; 
v_ref_4514_ = lean_ctor_get(v___y_4497_, 5);
v___x_4515_ = lean_io_error_to_string(v_a_4510_);
v___x_4516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4516_, 0, v___x_4515_);
v___x_4517_ = l_Lean_MessageData_ofFormat(v___x_4516_);
lean_inc(v_ref_4514_);
v___x_4518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4518_, 0, v_ref_4514_);
lean_ctor_set(v___x_4518_, 1, v___x_4517_);
if (v_isShared_4513_ == 0)
{
lean_ctor_set(v___x_4512_, 0, v___x_4518_);
v___x_4520_ = v___x_4512_;
goto v_reusejp_4519_;
}
else
{
lean_object* v_reuseFailAlloc_4521_; 
v_reuseFailAlloc_4521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4521_, 0, v___x_4518_);
v___x_4520_ = v_reuseFailAlloc_4521_;
goto v_reusejp_4519_;
}
v_reusejp_4519_:
{
return v___x_4520_;
}
}
}
}
v___jp_4523_:
{
lean_object* v___x_4530_; 
v___x_4530_ = lean_st_ref_get(v___y_4529_);
if (lean_obj_tag(v_exportedInfo_x3f_4527_) == 0)
{
lean_object* v_env_4531_; lean_object* v___x_4532_; 
v_env_4531_ = lean_ctor_get(v___x_4530_, 0);
lean_inc_ref(v_env_4531_);
lean_dec(v___x_4530_);
v___x_4532_ = lean_box(0);
v___y_4493_ = v___y_4529_;
v___y_4494_ = v___y_4528_;
v___y_4495_ = v_env_4531_;
v___y_4496_ = v___y_4529_;
v___y_4497_ = v___y_4528_;
v___y_4498_ = v___y_4524_;
v___y_4499_ = v___y_4525_;
v___y_4500_ = v_exportedInfo_x3f_4527_;
v___y_4501_ = v___y_4526_;
v___y_4502_ = v___x_4532_;
goto v___jp_4492_;
}
else
{
lean_object* v_env_4533_; lean_object* v_val_4534_; uint8_t v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v_env_4533_ = lean_ctor_get(v___x_4530_, 0);
lean_inc_ref(v_env_4533_);
lean_dec(v___x_4530_);
v_val_4534_ = lean_ctor_get(v_exportedInfo_x3f_4527_, 0);
v___x_4535_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4534_);
v___x_4536_ = lean_box(v___x_4535_);
v___x_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4537_, 0, v___x_4536_);
v___y_4493_ = v___y_4529_;
v___y_4494_ = v___y_4528_;
v___y_4495_ = v_env_4533_;
v___y_4496_ = v___y_4529_;
v___y_4497_ = v___y_4528_;
v___y_4498_ = v___y_4524_;
v___y_4499_ = v___y_4525_;
v___y_4500_ = v_exportedInfo_x3f_4527_;
v___y_4501_ = v___y_4526_;
v___y_4502_ = v___x_4537_;
goto v___jp_4492_;
}
}
v___jp_4538_:
{
lean_object* v___x_4544_; 
lean_inc_ref(v___y_4539_);
v___x_4544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4544_, 0, v___y_4539_);
v___y_4524_ = v___y_4539_;
v___y_4525_ = v___y_4540_;
v___y_4526_ = v___y_4541_;
v_exportedInfo_x3f_4527_ = v___x_4544_;
v___y_4528_ = v___y_4542_;
v___y_4529_ = v___y_4543_;
goto v___jp_4523_;
}
v___jp_4545_:
{
lean_object* v___x_4551_; 
lean_inc_ref(v___y_4546_);
v___x_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___y_4546_);
v___y_4524_ = v___y_4546_;
v___y_4525_ = v___y_4547_;
v___y_4526_ = v___y_4548_;
v_exportedInfo_x3f_4527_ = v___x_4551_;
v___y_4528_ = v___y_4549_;
v___y_4529_ = v___y_4550_;
goto v___jp_4523_;
}
}
else
{
goto v___jp_4265_;
}
v___jp_4118_:
{
lean_object* v___x_4122_; double v___x_4123_; double v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; 
v___x_4122_ = lean_io_get_num_heartbeats();
v___x_4123_ = lean_float_of_nat(v___y_4119_);
v___x_4124_ = lean_float_of_nat(v___x_4122_);
v___x_4125_ = lean_box_float(v___x_4123_);
v___x_4126_ = lean_box_float(v___x_4124_);
v___x_4127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4128_, 0, v_a_4121_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3914_, v_hasTrace_3778_, v___x_4115_, v_options_3776_, v___x_4117_, v___y_4120_, v___f_4114_, v___x_4128_, v_a_3721_, v_a_3722_);
return v___x_4129_;
}
v___jp_4130_:
{
if (lean_obj_tag(v___y_4133_) == 0)
{
lean_object* v_a_4134_; lean_object* v___x_4136_; uint8_t v_isShared_4137_; uint8_t v_isSharedCheck_4141_; 
v_a_4134_ = lean_ctor_get(v___y_4133_, 0);
v_isSharedCheck_4141_ = !lean_is_exclusive(v___y_4133_);
if (v_isSharedCheck_4141_ == 0)
{
v___x_4136_ = v___y_4133_;
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
else
{
lean_inc(v_a_4134_);
lean_dec(v___y_4133_);
v___x_4136_ = lean_box(0);
v_isShared_4137_ = v_isSharedCheck_4141_;
goto v_resetjp_4135_;
}
v_resetjp_4135_:
{
lean_object* v___x_4139_; 
if (v_isShared_4137_ == 0)
{
lean_ctor_set_tag(v___x_4136_, 1);
v___x_4139_ = v___x_4136_;
goto v_reusejp_4138_;
}
else
{
lean_object* v_reuseFailAlloc_4140_; 
v_reuseFailAlloc_4140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4140_, 0, v_a_4134_);
v___x_4139_ = v_reuseFailAlloc_4140_;
goto v_reusejp_4138_;
}
v_reusejp_4138_:
{
v___y_4119_ = v___y_4131_;
v___y_4120_ = v___y_4132_;
v_a_4121_ = v___x_4139_;
goto v___jp_4118_;
}
}
}
else
{
lean_object* v_a_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4149_; 
v_a_4142_ = lean_ctor_get(v___y_4133_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___y_4133_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4144_ = v___y_4133_;
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_a_4142_);
lean_dec(v___y_4133_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4149_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4147_; 
if (v_isShared_4145_ == 0)
{
lean_ctor_set_tag(v___x_4144_, 0);
v___x_4147_ = v___x_4144_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v_a_4142_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
v___y_4119_ = v___y_4131_;
v___y_4120_ = v___y_4132_;
v_a_4121_ = v___x_4147_;
goto v___jp_4118_;
}
}
}
}
v___jp_4150_:
{
lean_object* v___x_4155_; lean_object* v___x_4156_; 
v___x_4155_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4156_ = lean_apply_5(v___y_4151_, v___x_4155_, v___y_4154_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4131_ = v___y_4152_;
v___y_4132_ = v___y_4153_;
v___y_4133_ = v___x_4156_;
goto v___jp_4130_;
}
v___jp_4157_:
{
lean_object* v___x_4162_; lean_object* v___x_4163_; 
v___x_4162_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4163_ = lean_apply_5(v___y_4158_, v___x_4162_, v___y_4161_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4131_ = v___y_4159_;
v___y_4132_ = v___y_4160_;
v___y_4133_ = v___x_4163_;
goto v___jp_4130_;
}
v___jp_4164_:
{
lean_object* v___x_4168_; double v___x_4169_; double v___x_4170_; double v___x_4171_; double v___x_4172_; double v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4168_ = lean_io_mono_nanos_now();
v___x_4169_ = lean_float_of_nat(v___y_4166_);
v___x_4170_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4171_ = lean_float_div(v___x_4169_, v___x_4170_);
v___x_4172_ = lean_float_of_nat(v___x_4168_);
v___x_4173_ = lean_float_div(v___x_4172_, v___x_4170_);
v___x_4174_ = lean_box_float(v___x_4171_);
v___x_4175_ = lean_box_float(v___x_4173_);
v___x_4176_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4174_);
lean_ctor_set(v___x_4176_, 1, v___x_4175_);
v___x_4177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4177_, 0, v_a_4167_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3914_, v_hasTrace_3778_, v___x_4115_, v_options_3776_, v___x_4117_, v___y_4165_, v___f_4114_, v___x_4177_, v_a_3721_, v_a_3722_);
return v___x_4178_;
}
v___jp_4179_:
{
if (lean_obj_tag(v___y_4182_) == 0)
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___y_4182_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___y_4182_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___y_4182_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___y_4182_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 1);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
v___y_4165_ = v___y_4180_;
v___y_4166_ = v___y_4181_;
v_a_4167_ = v___x_4188_;
goto v___jp_4164_;
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
v_a_4191_ = lean_ctor_get(v___y_4182_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___y_4182_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___y_4182_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___y_4182_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
lean_ctor_set_tag(v___x_4193_, 0);
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
v___y_4165_ = v___y_4180_;
v___y_4166_ = v___y_4181_;
v_a_4167_ = v___x_4196_;
goto v___jp_4164_;
}
}
}
}
v___jp_4199_:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4205_ = lean_apply_5(v___y_4201_, v___x_4204_, v___y_4200_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4202_;
v___y_4181_ = v___y_4203_;
v___y_4182_ = v___x_4205_;
goto v___jp_4179_;
}
v___jp_4206_:
{
if (v___x_4117_ == 0)
{
lean_object* v___x_4211_; lean_object* v___x_4212_; 
lean_dec_ref(v___y_4209_);
v___x_4211_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4212_ = lean_apply_4(v___y_4207_, v___x_4211_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4208_;
v___y_4181_ = v___y_4210_;
v___y_4182_ = v___x_4212_;
goto v___jp_4179_;
}
else
{
lean_object* v_toConstantVal_4213_; lean_object* v_name_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; lean_object* v___x_4220_; 
v_toConstantVal_4213_ = lean_ctor_get(v___y_4209_, 0);
lean_inc_ref(v_toConstantVal_4213_);
lean_dec_ref(v___y_4209_);
v_name_4214_ = lean_ctor_get(v_toConstantVal_4213_, 0);
lean_inc(v_name_4214_);
lean_dec_ref(v_toConstantVal_4213_);
v___x_4215_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4216_ = l_Lean_MessageData_ofName(v_name_4214_);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4219_, 0, v___x_4217_);
lean_ctor_set(v___x_4219_, 1, v___x_4218_);
v___x_4220_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4219_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4220_) == 0)
{
lean_object* v_a_4221_; lean_object* v___x_4222_; 
v_a_4221_ = lean_ctor_get(v___x_4220_, 0);
lean_inc(v_a_4221_);
lean_dec_ref_known(v___x_4220_, 1);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4222_ = lean_apply_4(v___y_4207_, v_a_4221_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4208_;
v___y_4181_ = v___y_4210_;
v___y_4182_ = v___x_4222_;
goto v___jp_4179_;
}
else
{
lean_dec_ref(v___y_4207_);
v___y_4180_ = v___y_4208_;
v___y_4181_ = v___y_4210_;
v___y_4182_ = v___x_4220_;
goto v___jp_4179_;
}
}
}
v___jp_4223_:
{
lean_object* v___x_4233_; uint8_t v_isModule_4234_; 
v___x_4233_ = l_Lean_Environment_header(v___y_4225_);
lean_dec_ref(v___y_4225_);
v_isModule_4234_ = lean_ctor_get_uint8(v___x_4233_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4233_);
if (v_isModule_4234_ == 0)
{
lean_dec_ref(v___y_4232_);
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4224_);
v___y_4200_ = v___y_4226_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4228_;
v___y_4203_ = v___y_4231_;
goto v___jp_4199_;
}
else
{
uint8_t v_isExporting_4235_; 
v_isExporting_4235_ = lean_ctor_get_uint8(v___y_4232_, sizeof(void*)*8);
lean_dec_ref(v___y_4232_);
if (v_isExporting_4235_ == 0)
{
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
v___y_4207_ = v___y_4224_;
v___y_4208_ = v___y_4228_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4231_;
goto v___jp_4206_;
}
else
{
if (v___y_4230_ == 0)
{
lean_dec_ref(v___y_4229_);
lean_dec_ref(v___y_4224_);
v___y_4200_ = v___y_4226_;
v___y_4201_ = v___y_4227_;
v___y_4202_ = v___y_4228_;
v___y_4203_ = v___y_4231_;
goto v___jp_4199_;
}
else
{
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
v___y_4207_ = v___y_4224_;
v___y_4208_ = v___y_4228_;
v___y_4209_ = v___y_4229_;
v___y_4210_ = v___y_4231_;
goto v___jp_4206_;
}
}
}
}
v___jp_4236_:
{
lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4241_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4242_ = lean_apply_5(v___y_4239_, v___x_4241_, v___y_4237_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4238_;
v___y_4181_ = v___y_4240_;
v___y_4182_ = v___x_4242_;
goto v___jp_4179_;
}
v___jp_4243_:
{
lean_object* v___x_4251_; uint8_t v_isModule_4252_; 
v___x_4251_ = l_Lean_Environment_header(v___y_4250_);
lean_dec_ref(v___y_4250_);
v_isModule_4252_ = lean_ctor_get_uint8(v___x_4251_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4251_);
if (v_isModule_4252_ == 0)
{
lean_dec_ref(v___y_4246_);
lean_dec_ref(v___y_4244_);
v___y_4237_ = v___y_4245_;
v___y_4238_ = v___y_4247_;
v___y_4239_ = v___y_4248_;
v___y_4240_ = v___y_4249_;
goto v___jp_4236_;
}
else
{
lean_dec_ref(v___y_4248_);
lean_dec(v___y_4245_);
if (v___x_4117_ == 0)
{
lean_object* v___x_4253_; lean_object* v___x_4254_; 
lean_dec_ref(v___y_4246_);
v___x_4253_ = lean_box(0);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4254_ = lean_apply_4(v___y_4244_, v___x_4253_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4247_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___x_4254_;
goto v___jp_4179_;
}
else
{
lean_object* v_toConstantVal_4255_; lean_object* v_name_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; 
v_toConstantVal_4255_ = lean_ctor_get(v___y_4246_, 0);
lean_inc_ref(v_toConstantVal_4255_);
lean_dec_ref(v___y_4246_);
v_name_4256_ = lean_ctor_get(v_toConstantVal_4255_, 0);
lean_inc(v_name_4256_);
lean_dec_ref(v_toConstantVal_4255_);
v___x_4257_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4258_ = l_Lean_MessageData_ofName(v_name_4256_);
v___x_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
v___x_4262_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4261_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4262_) == 0)
{
lean_object* v_a_4263_; lean_object* v___x_4264_; 
v_a_4263_ = lean_ctor_get(v___x_4262_, 0);
lean_inc(v_a_4263_);
lean_dec_ref_known(v___x_4262_, 1);
lean_inc(v_a_3722_);
lean_inc_ref(v_a_3721_);
v___x_4264_ = lean_apply_4(v___y_4244_, v_a_4263_, v_a_3721_, v_a_3722_, lean_box(0));
v___y_4180_ = v___y_4247_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___x_4264_;
goto v___jp_4179_;
}
else
{
lean_dec_ref(v___y_4244_);
v___y_4180_ = v___y_4247_;
v___y_4181_ = v___y_4249_;
v___y_4182_ = v___x_4262_;
goto v___jp_4179_;
}
}
}
}
v___jp_4265_:
{
lean_object* v___x_4266_; lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4416_; 
v___x_4266_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3722_);
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4269_ = v___x_4266_;
v_isShared_4270_ = v_isSharedCheck_4416_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___x_4266_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4416_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
lean_object* v___x_4271_; uint8_t v___x_4272_; 
v___x_4271_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4272_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3776_, v___x_4271_);
if (v___x_4272_ == 0)
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v_env_4275_; lean_object* v_nextMacroScope_4276_; lean_object* v_ngen_4277_; lean_object* v_auxDeclNGen_4278_; lean_object* v_traceState_4279_; lean_object* v_messages_4280_; lean_object* v_infoState_4281_; lean_object* v_snapshotTasks_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4330_; 
v___x_4273_ = lean_io_mono_nanos_now();
v___x_4274_ = lean_st_ref_take(v_a_3722_);
v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
v_nextMacroScope_4276_ = lean_ctor_get(v___x_4274_, 1);
v_ngen_4277_ = lean_ctor_get(v___x_4274_, 2);
v_auxDeclNGen_4278_ = lean_ctor_get(v___x_4274_, 3);
v_traceState_4279_ = lean_ctor_get(v___x_4274_, 4);
v_messages_4280_ = lean_ctor_get(v___x_4274_, 6);
v_infoState_4281_ = lean_ctor_get(v___x_4274_, 7);
v_snapshotTasks_4282_ = lean_ctor_get(v___x_4274_, 8);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4330_ == 0)
{
lean_object* v_unused_4331_; 
v_unused_4331_ = lean_ctor_get(v___x_4274_, 5);
lean_dec(v_unused_4331_);
v___x_4284_ = v___x_4274_;
v_isShared_4285_ = v_isSharedCheck_4330_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_snapshotTasks_4282_);
lean_inc(v_infoState_4281_);
lean_inc(v_messages_4280_);
lean_inc(v_traceState_4279_);
lean_inc(v_auxDeclNGen_4278_);
lean_inc(v_ngen_4277_);
lean_inc(v_nextMacroScope_4276_);
lean_inc(v_env_4275_);
lean_dec(v___x_4274_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4330_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
lean_inc(v_decl_3719_);
v___x_4286_ = l_Lean_Declaration_getNames(v_decl_3719_);
v___x_4287_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4275_, v___x_4286_);
v___x_4288_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 5, v___x_4288_);
lean_ctor_set(v___x_4284_, 0, v___x_4287_);
v___x_4290_ = v___x_4284_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v___x_4287_);
lean_ctor_set(v_reuseFailAlloc_4329_, 1, v_nextMacroScope_4276_);
lean_ctor_set(v_reuseFailAlloc_4329_, 2, v_ngen_4277_);
lean_ctor_set(v_reuseFailAlloc_4329_, 3, v_auxDeclNGen_4278_);
lean_ctor_set(v_reuseFailAlloc_4329_, 4, v_traceState_4279_);
lean_ctor_set(v_reuseFailAlloc_4329_, 5, v___x_4288_);
lean_ctor_set(v_reuseFailAlloc_4329_, 6, v_messages_4280_);
lean_ctor_set(v_reuseFailAlloc_4329_, 7, v_infoState_4281_);
lean_ctor_set(v_reuseFailAlloc_4329_, 8, v_snapshotTasks_4282_);
v___x_4290_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___f_4295_; 
v___x_4291_ = lean_st_ref_set(v_a_3722_, v___x_4290_);
v___x_4292_ = lean_box(0);
v___x_4293_ = lean_box(v_hasTrace_3778_);
v___x_4294_ = lean_box(v___x_4272_);
lean_inc(v_decl_3719_);
v___f_4295_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4295_, 0, v_decl_3719_);
lean_closure_set(v___f_4295_, 1, v___x_4293_);
lean_closure_set(v___f_4295_, 2, v___x_4294_);
lean_closure_set(v___f_4295_, 3, v___x_4288_);
lean_closure_set(v___f_4295_, 4, v_cls_3914_);
lean_closure_set(v___f_4295_, 5, v___x_4292_);
switch(lean_obj_tag(v_decl_3719_))
{
case 2:
{
lean_object* v_val_4296_; lean_object* v___x_4297_; lean_object* v_env_4298_; lean_object* v___f_4299_; lean_object* v___x_4300_; lean_object* v___f_4301_; 
lean_del_object(v___x_4269_);
v_val_4296_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref_n(v_val_4296_, 3);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4297_ = lean_st_ref_get(v_a_3722_);
v_env_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc_ref(v_env_4298_);
lean_dec(v___x_4297_);
v___f_4299_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4299_, 0, v_val_4296_);
lean_closure_set(v___f_4299_, 1, v___f_4295_);
v___x_4300_ = lean_box(v___x_4272_);
lean_inc_ref(v___f_4299_);
v___f_4301_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4301_, 0, v_val_4296_);
lean_closure_set(v___f_4301_, 1, v___x_4300_);
lean_closure_set(v___f_4301_, 2, v___f_4299_);
if (v_forceExpose_3720_ == 0)
{
v___y_4244_ = v___f_4301_;
v___y_4245_ = v___x_4292_;
v___y_4246_ = v_val_4296_;
v___y_4247_ = v_a_4267_;
v___y_4248_ = v___f_4299_;
v___y_4249_ = v___x_4273_;
v___y_4250_ = v_env_4298_;
goto v___jp_4243_;
}
else
{
if (v___x_4272_ == 0)
{
lean_dec_ref(v___f_4301_);
lean_dec_ref(v_env_4298_);
lean_dec_ref(v_val_4296_);
v___y_4237_ = v___x_4292_;
v___y_4238_ = v_a_4267_;
v___y_4239_ = v___f_4299_;
v___y_4240_ = v___x_4273_;
goto v___jp_4236_;
}
else
{
v___y_4244_ = v___f_4301_;
v___y_4245_ = v___x_4292_;
v___y_4246_ = v_val_4296_;
v___y_4247_ = v_a_4267_;
v___y_4248_ = v___f_4299_;
v___y_4249_ = v___x_4273_;
v___y_4250_ = v_env_4298_;
goto v___jp_4243_;
}
}
}
case 1:
{
lean_object* v_val_4302_; lean_object* v___x_4303_; 
lean_del_object(v___x_4269_);
v_val_4302_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref(v_val_4302_);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4303_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4295_, v_cls_3914_, v___x_4292_, v___x_4272_, v_forceExpose_3720_, v_val_4302_, v_a_3721_, v_a_3722_);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4303_;
goto v___jp_4179_;
}
case 5:
{
lean_object* v_defns_4304_; 
lean_del_object(v___x_4269_);
v_defns_4304_ = lean_ctor_get(v_decl_3719_, 0);
if (lean_obj_tag(v_defns_4304_) == 1)
{
lean_object* v_tail_4305_; 
v_tail_4305_ = lean_ctor_get(v_defns_4304_, 1);
if (lean_obj_tag(v_tail_4305_) == 0)
{
lean_object* v_head_4306_; lean_object* v___x_4307_; 
lean_inc_ref(v_defns_4304_);
lean_dec_ref_known(v_decl_3719_, 1);
v_head_4306_ = lean_ctor_get(v_defns_4304_, 0);
lean_inc(v_head_4306_);
lean_dec_ref_known(v_defns_4304_, 2);
v___x_4307_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4295_, v_cls_3914_, v___x_4292_, v___x_4272_, v_forceExpose_3720_, v_head_4306_, v_a_3721_, v_a_3722_);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4307_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4308_; 
lean_dec_ref(v___f_4295_);
lean_inc_ref(v_decl_3719_);
v___x_4308_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec_ref_known(v_decl_3719_, 1);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4308_;
goto v___jp_4179_;
}
}
else
{
lean_object* v___x_4309_; 
lean_dec_ref(v___f_4295_);
lean_inc_ref(v_decl_3719_);
v___x_4309_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec_ref_known(v_decl_3719_, 1);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4309_;
goto v___jp_4179_;
}
}
case 3:
{
lean_object* v_val_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v_env_4313_; lean_object* v_env_4314_; lean_object* v___f_4315_; lean_object* v___f_4316_; 
lean_del_object(v___x_4269_);
v_val_4310_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref_n(v_val_4310_, 3);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4311_ = lean_st_ref_get(v_a_3722_);
v___x_4312_ = lean_st_ref_get(v_a_3722_);
v_env_4313_ = lean_ctor_get(v___x_4311_, 0);
lean_inc_ref(v_env_4313_);
lean_dec(v___x_4311_);
v_env_4314_ = lean_ctor_get(v___x_4312_, 0);
lean_inc_ref(v_env_4314_);
lean_dec(v___x_4312_);
v___f_4315_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4315_, 0, v_val_4310_);
lean_closure_set(v___f_4315_, 1, v___f_4295_);
lean_inc_ref(v___f_4315_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4316_, 0, v_val_4310_);
lean_closure_set(v___f_4316_, 1, v___f_4315_);
if (v_forceExpose_3720_ == 0)
{
v___y_4224_ = v___f_4316_;
v___y_4225_ = v_env_4313_;
v___y_4226_ = v___x_4292_;
v___y_4227_ = v___f_4315_;
v___y_4228_ = v_a_4267_;
v___y_4229_ = v_val_4310_;
v___y_4230_ = v___x_4272_;
v___y_4231_ = v___x_4273_;
v___y_4232_ = v_env_4314_;
goto v___jp_4223_;
}
else
{
if (v___x_4272_ == 0)
{
lean_dec_ref(v___f_4316_);
lean_dec_ref(v_env_4314_);
lean_dec_ref(v_env_4313_);
lean_dec_ref(v_val_4310_);
v___y_4200_ = v___x_4292_;
v___y_4201_ = v___f_4315_;
v___y_4202_ = v_a_4267_;
v___y_4203_ = v___x_4273_;
goto v___jp_4199_;
}
else
{
v___y_4224_ = v___f_4316_;
v___y_4225_ = v_env_4313_;
v___y_4226_ = v___x_4292_;
v___y_4227_ = v___f_4315_;
v___y_4228_ = v_a_4267_;
v___y_4229_ = v_val_4310_;
v___y_4230_ = v___x_4272_;
v___y_4231_ = v___x_4273_;
v___y_4232_ = v_env_4314_;
goto v___jp_4223_;
}
}
}
case 0:
{
lean_object* v_val_4317_; lean_object* v_toConstantVal_4318_; lean_object* v_name_4319_; lean_object* v___x_4321_; 
lean_dec_ref(v___f_4295_);
v_val_4317_ = lean_ctor_get(v_decl_3719_, 0);
v_toConstantVal_4318_ = lean_ctor_get(v_val_4317_, 0);
v_name_4319_ = lean_ctor_get(v_toConstantVal_4318_, 0);
lean_inc_ref(v_val_4317_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v_val_4317_);
v___x_4321_ = v___x_4269_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4327_; 
v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4327_, 0, v_val_4317_);
v___x_4321_ = v_reuseFailAlloc_4327_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
uint8_t v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; 
v___x_4322_ = 2;
v___x_4323_ = lean_box(v___x_4322_);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4321_);
lean_ctor_set(v___x_4324_, 1, v___x_4323_);
lean_inc(v_name_4319_);
v___x_4325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4325_, 0, v_name_4319_);
lean_ctor_set(v___x_4325_, 1, v___x_4324_);
v___x_4326_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3719_, v_hasTrace_3778_, v___x_4272_, v___x_4288_, v_cls_3914_, v___x_4292_, v___x_4325_, v___x_4292_, v_a_3721_, v_a_3722_);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4326_;
goto v___jp_4179_;
}
}
default: 
{
lean_object* v___x_4328_; 
lean_dec_ref(v___f_4295_);
lean_del_object(v___x_4269_);
lean_inc(v_decl_3719_);
v___x_4328_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec(v_decl_3719_);
v___y_4180_ = v_a_4267_;
v___y_4181_ = v___x_4273_;
v___y_4182_ = v___x_4328_;
goto v___jp_4179_;
}
}
}
}
}
else
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v_env_4334_; lean_object* v_nextMacroScope_4335_; lean_object* v_ngen_4336_; lean_object* v_auxDeclNGen_4337_; lean_object* v_traceState_4338_; lean_object* v_messages_4339_; lean_object* v_infoState_4340_; lean_object* v_snapshotTasks_4341_; lean_object* v___x_4343_; uint8_t v_isShared_4344_; uint8_t v_isSharedCheck_4414_; 
v___x_4332_ = lean_io_get_num_heartbeats();
v___x_4333_ = lean_st_ref_take(v_a_3722_);
v_env_4334_ = lean_ctor_get(v___x_4333_, 0);
v_nextMacroScope_4335_ = lean_ctor_get(v___x_4333_, 1);
v_ngen_4336_ = lean_ctor_get(v___x_4333_, 2);
v_auxDeclNGen_4337_ = lean_ctor_get(v___x_4333_, 3);
v_traceState_4338_ = lean_ctor_get(v___x_4333_, 4);
v_messages_4339_ = lean_ctor_get(v___x_4333_, 6);
v_infoState_4340_ = lean_ctor_get(v___x_4333_, 7);
v_snapshotTasks_4341_ = lean_ctor_get(v___x_4333_, 8);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4333_);
if (v_isSharedCheck_4414_ == 0)
{
lean_object* v_unused_4415_; 
v_unused_4415_ = lean_ctor_get(v___x_4333_, 5);
lean_dec(v_unused_4415_);
v___x_4343_ = v___x_4333_;
v_isShared_4344_ = v_isSharedCheck_4414_;
goto v_resetjp_4342_;
}
else
{
lean_inc(v_snapshotTasks_4341_);
lean_inc(v_infoState_4340_);
lean_inc(v_messages_4339_);
lean_inc(v_traceState_4338_);
lean_inc(v_auxDeclNGen_4337_);
lean_inc(v_ngen_4336_);
lean_inc(v_nextMacroScope_4335_);
lean_inc(v_env_4334_);
lean_dec(v___x_4333_);
v___x_4343_ = lean_box(0);
v_isShared_4344_ = v_isSharedCheck_4414_;
goto v_resetjp_4342_;
}
v_resetjp_4342_:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___x_4347_; lean_object* v___x_4349_; 
lean_inc(v_decl_3719_);
v___x_4345_ = l_Lean_Declaration_getNames(v_decl_3719_);
v___x_4346_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4334_, v___x_4345_);
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
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v___x_4346_);
lean_ctor_set(v_reuseFailAlloc_4413_, 1, v_nextMacroScope_4335_);
lean_ctor_set(v_reuseFailAlloc_4413_, 2, v_ngen_4336_);
lean_ctor_set(v_reuseFailAlloc_4413_, 3, v_auxDeclNGen_4337_);
lean_ctor_set(v_reuseFailAlloc_4413_, 4, v_traceState_4338_);
lean_ctor_set(v_reuseFailAlloc_4413_, 5, v___x_4347_);
lean_ctor_set(v_reuseFailAlloc_4413_, 6, v_messages_4339_);
lean_ctor_set(v_reuseFailAlloc_4413_, 7, v_infoState_4340_);
lean_ctor_set(v_reuseFailAlloc_4413_, 8, v_snapshotTasks_4341_);
v___x_4349_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4348_;
}
v_reusejp_4348_:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v___f_4353_; 
v___x_4350_ = lean_st_ref_set(v_a_3722_, v___x_4349_);
v___x_4351_ = lean_box(0);
v___x_4352_ = lean_box(v___x_4272_);
lean_inc(v_decl_3719_);
v___f_4353_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4353_, 0, v_decl_3719_);
lean_closure_set(v___f_4353_, 1, v___x_4352_);
lean_closure_set(v___f_4353_, 2, v_cls_3914_);
lean_closure_set(v___f_4353_, 3, v___x_4347_);
lean_closure_set(v___f_4353_, 4, v___x_4351_);
switch(lean_obj_tag(v_decl_3719_))
{
case 2:
{
lean_object* v_val_4354_; lean_object* v___x_4355_; lean_object* v_env_4356_; lean_object* v___f_4357_; 
lean_del_object(v___x_4269_);
v_val_4354_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref_n(v_val_4354_, 2);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4355_ = lean_st_ref_get(v_a_3722_);
v_env_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc_ref(v_env_4356_);
lean_dec(v___x_4355_);
v___f_4357_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4357_, 0, v_val_4354_);
lean_closure_set(v___f_4357_, 1, v___f_4353_);
if (v_forceExpose_3720_ == 0)
{
if (v___x_4272_ == 0)
{
lean_dec_ref(v_env_4356_);
lean_dec_ref(v_val_4354_);
v___y_4151_ = v___f_4357_;
v___y_4152_ = v___x_4332_;
v___y_4153_ = v_a_4267_;
v___y_4154_ = v___x_4351_;
goto v___jp_4150_;
}
else
{
lean_object* v___x_4358_; uint8_t v_isModule_4359_; 
v___x_4358_ = l_Lean_Environment_header(v_env_4356_);
lean_dec_ref(v_env_4356_);
v_isModule_4359_ = lean_ctor_get_uint8(v___x_4358_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4358_);
if (v_isModule_4359_ == 0)
{
lean_dec_ref(v_val_4354_);
v___y_4151_ = v___f_4357_;
v___y_4152_ = v___x_4332_;
v___y_4153_ = v_a_4267_;
v___y_4154_ = v___x_4351_;
goto v___jp_4150_;
}
else
{
if (v___x_4117_ == 0)
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_box(0);
v___x_4361_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4354_, v_forceExpose_3720_, v___f_4357_, v___x_4360_, v_a_3721_, v_a_3722_);
lean_dec_ref(v_val_4354_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4361_;
goto v___jp_4130_;
}
else
{
lean_object* v_toConstantVal_4362_; lean_object* v_name_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___x_4368_; lean_object* v___x_4369_; 
v_toConstantVal_4362_ = lean_ctor_get(v_val_4354_, 0);
v_name_4363_ = lean_ctor_get(v_toConstantVal_4362_, 0);
v___x_4364_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4363_);
v___x_4365_ = l_Lean_MessageData_ofName(v_name_4363_);
v___x_4366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4364_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4366_);
lean_ctor_set(v___x_4368_, 1, v___x_4367_);
v___x_4369_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4368_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4369_) == 0)
{
lean_object* v_a_4370_; lean_object* v___x_4371_; 
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
lean_inc(v_a_4370_);
lean_dec_ref_known(v___x_4369_, 1);
v___x_4371_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4354_, v_forceExpose_3720_, v___f_4357_, v_a_4370_, v_a_3721_, v_a_3722_);
lean_dec_ref(v_val_4354_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4371_;
goto v___jp_4130_;
}
else
{
lean_dec_ref(v___f_4357_);
lean_dec_ref(v_val_4354_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4369_;
goto v___jp_4130_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4356_);
lean_dec_ref(v_val_4354_);
v___y_4151_ = v___f_4357_;
v___y_4152_ = v___x_4332_;
v___y_4153_ = v_a_4267_;
v___y_4154_ = v___x_4351_;
goto v___jp_4150_;
}
}
case 1:
{
lean_object* v_val_4372_; lean_object* v___x_4373_; 
lean_del_object(v___x_4269_);
v_val_4372_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref(v_val_4372_);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4373_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4353_, v_forceExpose_3720_, v___x_4272_, v___x_4351_, v_cls_3914_, v_val_4372_, v_a_3721_, v_a_3722_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4373_;
goto v___jp_4130_;
}
case 5:
{
lean_object* v_defns_4374_; 
lean_del_object(v___x_4269_);
v_defns_4374_ = lean_ctor_get(v_decl_3719_, 0);
if (lean_obj_tag(v_defns_4374_) == 1)
{
lean_object* v_tail_4375_; 
v_tail_4375_ = lean_ctor_get(v_defns_4374_, 1);
if (lean_obj_tag(v_tail_4375_) == 0)
{
lean_object* v_head_4376_; lean_object* v___x_4377_; 
lean_inc_ref(v_defns_4374_);
lean_dec_ref_known(v_decl_3719_, 1);
v_head_4376_ = lean_ctor_get(v_defns_4374_, 0);
lean_inc(v_head_4376_);
lean_dec_ref_known(v_defns_4374_, 2);
v___x_4377_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4353_, v_forceExpose_3720_, v___x_4272_, v___x_4351_, v_cls_3914_, v_head_4376_, v_a_3721_, v_a_3722_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4377_;
goto v___jp_4130_;
}
else
{
lean_object* v___x_4378_; 
lean_dec_ref(v___f_4353_);
lean_inc_ref(v_decl_3719_);
v___x_4378_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec_ref_known(v_decl_3719_, 1);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4378_;
goto v___jp_4130_;
}
}
else
{
lean_object* v___x_4379_; 
lean_dec_ref(v___f_4353_);
lean_inc_ref(v_decl_3719_);
v___x_4379_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec_ref_known(v_decl_3719_, 1);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4379_;
goto v___jp_4130_;
}
}
case 3:
{
lean_object* v_val_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v_env_4383_; lean_object* v_env_4384_; lean_object* v___f_4385_; 
lean_del_object(v___x_4269_);
v_val_4380_ = lean_ctor_get(v_decl_3719_, 0);
lean_inc_ref_n(v_val_4380_, 2);
lean_dec_ref_known(v_decl_3719_, 1);
v___x_4381_ = lean_st_ref_get(v_a_3722_);
v___x_4382_ = lean_st_ref_get(v_a_3722_);
v_env_4383_ = lean_ctor_get(v___x_4381_, 0);
lean_inc_ref(v_env_4383_);
lean_dec(v___x_4381_);
v_env_4384_ = lean_ctor_get(v___x_4382_, 0);
lean_inc_ref(v_env_4384_);
lean_dec(v___x_4382_);
v___f_4385_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4385_, 0, v_val_4380_);
lean_closure_set(v___f_4385_, 1, v___f_4353_);
if (v_forceExpose_3720_ == 0)
{
if (v___x_4272_ == 0)
{
lean_dec_ref(v_env_4384_);
lean_dec_ref(v_env_4383_);
lean_dec_ref(v_val_4380_);
v___y_4158_ = v___f_4385_;
v___y_4159_ = v___x_4332_;
v___y_4160_ = v_a_4267_;
v___y_4161_ = v___x_4351_;
goto v___jp_4157_;
}
else
{
lean_object* v___x_4386_; uint8_t v_isModule_4387_; 
v___x_4386_ = l_Lean_Environment_header(v_env_4383_);
lean_dec_ref(v_env_4383_);
v_isModule_4387_ = lean_ctor_get_uint8(v___x_4386_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4386_);
if (v_isModule_4387_ == 0)
{
lean_dec_ref(v_env_4384_);
lean_dec_ref(v_val_4380_);
v___y_4158_ = v___f_4385_;
v___y_4159_ = v___x_4332_;
v___y_4160_ = v_a_4267_;
v___y_4161_ = v___x_4351_;
goto v___jp_4157_;
}
else
{
uint8_t v_isExporting_4388_; 
v_isExporting_4388_ = lean_ctor_get_uint8(v_env_4384_, sizeof(void*)*8);
lean_dec_ref(v_env_4384_);
if (v_isExporting_4388_ == 0)
{
if (v___x_4117_ == 0)
{
lean_object* v___x_4389_; lean_object* v___x_4390_; 
v___x_4389_ = lean_box(0);
v___x_4390_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4380_, v___f_4385_, v___x_4389_, v_a_3721_, v_a_3722_);
lean_dec_ref(v_val_4380_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4390_;
goto v___jp_4130_;
}
else
{
lean_object* v_toConstantVal_4391_; lean_object* v_name_4392_; lean_object* v___x_4393_; lean_object* v___x_4394_; lean_object* v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; 
v_toConstantVal_4391_ = lean_ctor_get(v_val_4380_, 0);
v_name_4392_ = lean_ctor_get(v_toConstantVal_4391_, 0);
v___x_4393_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4392_);
v___x_4394_ = l_Lean_MessageData_ofName(v_name_4392_);
v___x_4395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4395_, 0, v___x_4393_);
lean_ctor_set(v___x_4395_, 1, v___x_4394_);
v___x_4396_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4397_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4397_, 0, v___x_4395_);
lean_ctor_set(v___x_4397_, 1, v___x_4396_);
v___x_4398_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3914_, v___x_4397_, v_a_3721_, v_a_3722_);
if (lean_obj_tag(v___x_4398_) == 0)
{
lean_object* v_a_4399_; lean_object* v___x_4400_; 
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref_known(v___x_4398_, 1);
v___x_4400_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4380_, v___f_4385_, v_a_4399_, v_a_3721_, v_a_3722_);
lean_dec_ref(v_val_4380_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4400_;
goto v___jp_4130_;
}
else
{
lean_dec_ref(v___f_4385_);
lean_dec_ref(v_val_4380_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4398_;
goto v___jp_4130_;
}
}
}
else
{
lean_dec_ref(v_val_4380_);
v___y_4158_ = v___f_4385_;
v___y_4159_ = v___x_4332_;
v___y_4160_ = v_a_4267_;
v___y_4161_ = v___x_4351_;
goto v___jp_4157_;
}
}
}
}
else
{
lean_dec_ref(v_env_4384_);
lean_dec_ref(v_env_4383_);
lean_dec_ref(v_val_4380_);
v___y_4158_ = v___f_4385_;
v___y_4159_ = v___x_4332_;
v___y_4160_ = v_a_4267_;
v___y_4161_ = v___x_4351_;
goto v___jp_4157_;
}
}
case 0:
{
lean_object* v_val_4401_; lean_object* v_toConstantVal_4402_; lean_object* v_name_4403_; lean_object* v___x_4405_; 
lean_dec_ref(v___f_4353_);
v_val_4401_ = lean_ctor_get(v_decl_3719_, 0);
v_toConstantVal_4402_ = lean_ctor_get(v_val_4401_, 0);
v_name_4403_ = lean_ctor_get(v_toConstantVal_4402_, 0);
lean_inc_ref(v_val_4401_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v_val_4401_);
v___x_4405_ = v___x_4269_;
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
v___x_4410_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3719_, v___x_4272_, v_cls_3914_, v___x_4347_, v___x_4351_, v___x_4409_, v___x_4351_, v_a_3721_, v_a_3722_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4410_;
goto v___jp_4130_;
}
}
default: 
{
lean_object* v___x_4412_; 
lean_dec_ref(v___f_4353_);
lean_del_object(v___x_4269_);
lean_inc(v_decl_3719_);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3719_, v_cls_3914_, v_decl_3719_, v_a_3721_, v_a_3722_);
lean_dec(v_decl_3719_);
v___y_4131_ = v___x_4332_;
v___y_4132_ = v_a_4267_;
v___y_4133_ = v___x_4412_;
goto v___jp_4130_;
}
}
}
}
}
}
}
}
v___jp_3724_:
{
lean_object* v___x_3728_; lean_object* v___x_3730_; uint8_t v_isShared_3731_; uint8_t v_isSharedCheck_3735_; 
v___x_3728_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3726_, v___y_3725_);
v_isSharedCheck_3735_ = !lean_is_exclusive(v___x_3728_);
if (v_isSharedCheck_3735_ == 0)
{
lean_object* v_unused_3736_; 
v_unused_3736_ = lean_ctor_get(v___x_3728_, 0);
lean_dec(v_unused_3736_);
v___x_3730_ = v___x_3728_;
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
else
{
lean_dec(v___x_3728_);
v___x_3730_ = lean_box(0);
v_isShared_3731_ = v_isSharedCheck_3735_;
goto v_resetjp_3729_;
}
v_resetjp_3729_:
{
lean_object* v___x_3733_; 
if (v_isShared_3731_ == 0)
{
lean_ctor_set_tag(v___x_3730_, 1);
lean_ctor_set(v___x_3730_, 0, v_a_3727_);
v___x_3733_ = v___x_3730_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3727_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
}
v___jp_3737_:
{
lean_object* v___x_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3748_; 
v___x_3741_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3739_, v___y_3738_);
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
lean_ctor_set(v___x_3743_, 0, v_a_3740_);
v___x_3746_ = v___x_3743_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
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
v___x_3754_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3752_, v___y_3751_);
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
v___x_3767_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3765_, v___y_3764_);
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
lean_ctor_set_tag(v___x_3769_, 1);
lean_ctor_set(v___x_3769_, 0, v_a_3766_);
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_3779_:
{
lean_object* v___x_3791_; 
lean_inc_ref(v___y_3789_);
v___x_3791_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3781_, v___y_3789_, v___y_3785_, v___y_3790_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v___x_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3838_; 
lean_dec_ref_known(v___x_3791_, 1);
lean_inc_ref(v___y_3787_);
v___x_3792_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3787_, v___y_3786_);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3839_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3838_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3838_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v_options_3796_; lean_object* v___x_3797_; uint8_t v___x_3798_; 
v_options_3796_ = lean_ctor_get(v___y_3783_, 2);
v___x_3797_ = l_Lean_Elab_async;
v___x_3798_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3796_, v___x_3797_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; lean_object* v_r_3800_; 
lean_del_object(v___x_3794_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v___y_3780_);
v___x_3799_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3789_, v___y_3786_);
lean_dec_ref(v___x_3799_);
v_r_3800_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3719_, v___y_3783_, v___y_3786_);
if (lean_obj_tag(v_r_3800_) == 0)
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3810_; 
v_a_3801_ = lean_ctor_get(v_r_3800_, 0);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_r_3800_);
if (v_isSharedCheck_3810_ == 0)
{
v___x_3803_ = v_r_3800_;
v_isShared_3804_ = v_isSharedCheck_3810_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v_r_3800_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3810_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
lean_inc(v_a_3801_);
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 1);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3809_; 
v_reuseFailAlloc_3809_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3809_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; 
v___x_3807_ = lean_apply_2(v___y_3788_, v___x_3806_, lean_box(0));
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_dec_ref_known(v___x_3807_, 1);
v___y_3738_ = v___y_3786_;
v___y_3739_ = v___y_3787_;
v_a_3740_ = v_a_3801_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_3808_; 
lean_dec(v_a_3801_);
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v___y_3725_ = v___y_3786_;
v___y_3726_ = v___y_3787_;
v_a_3727_ = v_a_3808_;
goto v___jp_3724_;
}
}
}
}
else
{
lean_object* v_a_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; 
v_a_3811_ = lean_ctor_get(v_r_3800_, 0);
lean_inc(v_a_3811_);
lean_dec_ref_known(v_r_3800_, 1);
v___x_3812_ = lean_box(0);
v___x_3813_ = lean_apply_2(v___y_3788_, v___x_3812_, lean_box(0));
if (lean_obj_tag(v___x_3813_) == 0)
{
lean_dec_ref_known(v___x_3813_, 1);
v___y_3725_ = v___y_3786_;
v___y_3726_ = v___y_3787_;
v_a_3727_ = v_a_3811_;
goto v___jp_3724_;
}
else
{
lean_object* v_a_3814_; 
lean_dec(v_a_3811_);
v_a_3814_ = lean_ctor_get(v___x_3813_, 0);
lean_inc(v_a_3814_);
lean_dec_ref_known(v___x_3813_, 1);
v___y_3725_ = v___y_3786_;
v___y_3726_ = v___y_3787_;
v_a_3727_ = v_a_3814_;
goto v___jp_3724_;
}
}
}
else
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v_decl_3719_);
v___x_3815_ = l_IO_CancelToken_new();
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 1);
lean_ctor_set(v___x_3794_, 0, v___x_3815_);
v___x_3817_ = v___x_3794_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v___x_3815_);
v___x_3817_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3818_ = lean_unsigned_to_nat(0u);
v___x_3819_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3820_ = l_Lean_Name_toString(v___x_3819_, v___y_3784_);
lean_inc_ref(v___x_3817_);
v___x_3821_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3782_, v___x_3817_, v___x_3820_, v___y_3783_, v___y_3786_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v_checked_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3821_, 1);
v_checked_3823_ = lean_ctor_get(v___y_3780_, 2);
lean_inc_ref(v_checked_3823_);
lean_dec_ref(v___y_3780_);
v___x_3824_ = lean_io_map_task(v_a_3822_, v_checked_3823_, v___x_3818_, v_hasTrace_3778_);
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_box(2);
v___x_3827_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3825_);
lean_ctor_set(v___x_3827_, 1, v___x_3826_);
lean_ctor_set(v___x_3827_, 2, v___x_3817_);
lean_ctor_set(v___x_3827_, 3, v___x_3824_);
v___x_3828_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3827_, v___y_3786_);
return v___x_3828_;
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v___x_3817_);
lean_dec_ref(v___y_3780_);
v_a_3829_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3821_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3821_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3852_; 
lean_dec_ref(v___y_3789_);
lean_dec_ref(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v___y_3782_);
lean_dec_ref(v___y_3780_);
lean_dec(v_decl_3719_);
v_a_3840_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3842_ = v___x_3791_;
v_isShared_3843_ = v_isSharedCheck_3852_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3791_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3852_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v_ref_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3850_; 
v_ref_3844_ = lean_ctor_get(v___y_3783_, 5);
v___x_3845_ = lean_io_error_to_string(v_a_3840_);
v___x_3846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
v___x_3847_ = l_Lean_MessageData_ofFormat(v___x_3846_);
lean_inc(v_ref_3844_);
v___x_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3848_, 0, v_ref_3844_);
lean_ctor_set(v___x_3848_, 1, v___x_3847_);
if (v_isShared_3843_ == 0)
{
lean_ctor_set(v___x_3842_, 0, v___x_3848_);
v___x_3850_ = v___x_3842_;
goto v_reusejp_3849_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3848_);
v___x_3850_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3849_;
}
v_reusejp_3849_:
{
return v___x_3850_;
}
}
}
}
v___jp_3853_:
{
uint8_t v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = 1;
lean_inc_ref(v___y_3854_);
v___x_3865_ = l_Lean_Environment_addConstAsync(v___y_3854_, v___y_3860_, v___y_3859_, v___y_3863_, v_hasTrace_3778_, v___x_3864_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v_mainEnv_3867_; lean_object* v_asyncEnv_3868_; lean_object* v___f_3869_; lean_object* v___f_3870_; lean_object* v___x_3871_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc_n(v_a_3866_, 3);
lean_dec_ref_known(v___x_3865_, 1);
v_mainEnv_3867_ = lean_ctor_get(v_a_3866_, 0);
lean_inc_ref(v_mainEnv_3867_);
v_asyncEnv_3868_ = lean_ctor_get(v_a_3866_, 1);
lean_inc_ref_n(v_asyncEnv_3868_, 2);
lean_inc_ref(v___y_3855_);
lean_inc(v___y_3856_);
v___f_3869_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3869_, 0, v___y_3856_);
lean_closure_set(v___f_3869_, 1, v_a_3866_);
lean_closure_set(v___f_3869_, 2, v___y_3855_);
lean_inc(v_decl_3719_);
v___f_3870_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3870_, 0, v_asyncEnv_3868_);
lean_closure_set(v___f_3870_, 1, v_a_3866_);
lean_closure_set(v___f_3870_, 2, v_decl_3719_);
v___x_3871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3871_, 0, v___y_3862_);
if (lean_obj_tag(v___y_3857_) == 0)
{
lean_inc_ref(v___x_3871_);
v___y_3780_ = v___y_3854_;
v___y_3781_ = v_a_3866_;
v___y_3782_ = v___f_3870_;
v___y_3783_ = v___y_3858_;
v___y_3784_ = v___x_3864_;
v___y_3785_ = v___x_3871_;
v___y_3786_ = v___y_3861_;
v___y_3787_ = v_mainEnv_3867_;
v___y_3788_ = v___f_3869_;
v___y_3789_ = v_asyncEnv_3868_;
v___y_3790_ = v___x_3871_;
goto v___jp_3779_;
}
else
{
v___y_3780_ = v___y_3854_;
v___y_3781_ = v_a_3866_;
v___y_3782_ = v___f_3870_;
v___y_3783_ = v___y_3858_;
v___y_3784_ = v___x_3864_;
v___y_3785_ = v___x_3871_;
v___y_3786_ = v___y_3861_;
v___y_3787_ = v_mainEnv_3867_;
v___y_3788_ = v___f_3869_;
v___y_3789_ = v_asyncEnv_3868_;
v___y_3790_ = v___y_3857_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3884_; 
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3854_);
lean_dec(v_decl_3719_);
v_a_3872_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3874_ = v___x_3865_;
v_isShared_3875_ = v_isSharedCheck_3884_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_dec(v___x_3865_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3884_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
lean_object* v_ref_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
v_ref_3876_ = lean_ctor_get(v___y_3858_, 5);
v___x_3877_ = lean_io_error_to_string(v_a_3872_);
v___x_3878_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
v___x_3879_ = l_Lean_MessageData_ofFormat(v___x_3878_);
lean_inc(v_ref_3876_);
v___x_3880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3880_, 0, v_ref_3876_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3880_);
v___x_3882_ = v___x_3874_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
return v___x_3882_;
}
}
}
}
v___jp_3885_:
{
lean_object* v___x_3892_; 
v___x_3892_ = lean_st_ref_get(v___y_3891_);
if (lean_obj_tag(v_exportedInfo_x3f_3889_) == 0)
{
lean_object* v_env_3893_; lean_object* v___x_3894_; 
v_env_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc_ref(v_env_3893_);
lean_dec(v___x_3892_);
v___x_3894_ = lean_box(0);
v___y_3854_ = v_env_3893_;
v___y_3855_ = v___y_3890_;
v___y_3856_ = v___y_3891_;
v___y_3857_ = v_exportedInfo_x3f_3889_;
v___y_3858_ = v___y_3890_;
v___y_3859_ = v___y_3886_;
v___y_3860_ = v___y_3887_;
v___y_3861_ = v___y_3891_;
v___y_3862_ = v___y_3888_;
v___y_3863_ = v___x_3894_;
goto v___jp_3853_;
}
else
{
lean_object* v_env_3895_; lean_object* v_val_3896_; uint8_t v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; 
v_env_3895_ = lean_ctor_get(v___x_3892_, 0);
lean_inc_ref(v_env_3895_);
lean_dec(v___x_3892_);
v_val_3896_ = lean_ctor_get(v_exportedInfo_x3f_3889_, 0);
v___x_3897_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3896_);
v___x_3898_ = lean_box(v___x_3897_);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3898_);
v___y_3854_ = v_env_3895_;
v___y_3855_ = v___y_3890_;
v___y_3856_ = v___y_3891_;
v___y_3857_ = v_exportedInfo_x3f_3889_;
v___y_3858_ = v___y_3890_;
v___y_3859_ = v___y_3886_;
v___y_3860_ = v___y_3887_;
v___y_3861_ = v___y_3891_;
v___y_3862_ = v___y_3888_;
v___y_3863_ = v___x_3899_;
goto v___jp_3853_;
}
}
v___jp_3900_:
{
lean_object* v___x_3906_; 
lean_inc_ref(v___y_3903_);
v___x_3906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___y_3903_);
v___y_3886_ = v___y_3901_;
v___y_3887_ = v___y_3902_;
v___y_3888_ = v___y_3903_;
v_exportedInfo_x3f_3889_ = v___x_3906_;
v___y_3890_ = v___y_3904_;
v___y_3891_ = v___y_3905_;
goto v___jp_3885_;
}
v___jp_3907_:
{
lean_object* v___x_3913_; 
lean_inc_ref(v___y_3910_);
v___x_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3913_, 0, v___y_3910_);
v___y_3886_ = v___y_3908_;
v___y_3887_ = v___y_3909_;
v___y_3888_ = v___y_3910_;
v_exportedInfo_x3f_3889_ = v___x_3913_;
v___y_3890_ = v___y_3911_;
v___y_3891_ = v___y_3912_;
goto v___jp_3885_;
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
lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
lean_dec_ref_known(v___x_4853_, 1);
v___x_4854_ = l_Lean_Declaration_getTopLevelNames(v_decl_4848_);
v___x_4855_ = lean_box(0);
v___x_4856_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4854_, v___x_4855_, v_a_4850_, v_a_4851_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4864_; 
v_isSharedCheck_4864_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4864_ == 0)
{
lean_object* v_unused_4865_; 
v_unused_4865_ = lean_ctor_get(v___x_4856_, 0);
lean_dec(v_unused_4865_);
v___x_4858_ = v___x_4856_;
v_isShared_4859_ = v_isSharedCheck_4864_;
goto v_resetjp_4857_;
}
else
{
lean_dec(v___x_4856_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4864_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4860_; lean_object* v___x_4862_; 
v___x_4860_ = lean_box(0);
if (v_isShared_4859_ == 0)
{
lean_ctor_set(v___x_4858_, 0, v___x_4860_);
v___x_4862_ = v___x_4858_;
goto v_reusejp_4861_;
}
else
{
lean_object* v_reuseFailAlloc_4863_; 
v_reuseFailAlloc_4863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4863_, 0, v___x_4860_);
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
v_a_4866_ = lean_ctor_get(v___x_4856_, 0);
v_isSharedCheck_4873_ = !lean_is_exclusive(v___x_4856_);
if (v_isSharedCheck_4873_ == 0)
{
v___x_4868_ = v___x_4856_;
v_isShared_4869_ = v_isSharedCheck_4873_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4856_);
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
lean_object* v_head_4886_; lean_object* v_tail_4887_; lean_object* v___x_4888_; lean_object* v_env_4889_; lean_object* v_nextMacroScope_4890_; lean_object* v_ngen_4891_; lean_object* v_auxDeclNGen_4892_; lean_object* v_traceState_4893_; lean_object* v_messages_4894_; lean_object* v_infoState_4895_; lean_object* v_snapshotTasks_4896_; lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4908_; 
v_head_4886_ = lean_ctor_get(v_as_x27_4881_, 0);
v_tail_4887_ = lean_ctor_get(v_as_x27_4881_, 1);
v___x_4888_ = lean_st_ref_take(v___y_4883_);
v_env_4889_ = lean_ctor_get(v___x_4888_, 0);
v_nextMacroScope_4890_ = lean_ctor_get(v___x_4888_, 1);
v_ngen_4891_ = lean_ctor_get(v___x_4888_, 2);
v_auxDeclNGen_4892_ = lean_ctor_get(v___x_4888_, 3);
v_traceState_4893_ = lean_ctor_get(v___x_4888_, 4);
v_messages_4894_ = lean_ctor_get(v___x_4888_, 6);
v_infoState_4895_ = lean_ctor_get(v___x_4888_, 7);
v_snapshotTasks_4896_ = lean_ctor_get(v___x_4888_, 8);
v_isSharedCheck_4908_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4908_ == 0)
{
lean_object* v_unused_4909_; 
v_unused_4909_ = lean_ctor_get(v___x_4888_, 5);
lean_dec(v_unused_4909_);
v___x_4898_ = v___x_4888_;
v_isShared_4899_ = v_isSharedCheck_4908_;
goto v_resetjp_4897_;
}
else
{
lean_inc(v_snapshotTasks_4896_);
lean_inc(v_infoState_4895_);
lean_inc(v_messages_4894_);
lean_inc(v_traceState_4893_);
lean_inc(v_auxDeclNGen_4892_);
lean_inc(v_ngen_4891_);
lean_inc(v_nextMacroScope_4890_);
lean_inc(v_env_4889_);
lean_dec(v___x_4888_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4908_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4903_; 
lean_inc(v_head_4886_);
v___x_4900_ = l_Lean_markMeta(v_env_4889_, v_head_4886_);
v___x_4901_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 5, v___x_4901_);
lean_ctor_set(v___x_4898_, 0, v___x_4900_);
v___x_4903_ = v___x_4898_;
goto v_reusejp_4902_;
}
else
{
lean_object* v_reuseFailAlloc_4907_; 
v_reuseFailAlloc_4907_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4907_, 0, v___x_4900_);
lean_ctor_set(v_reuseFailAlloc_4907_, 1, v_nextMacroScope_4890_);
lean_ctor_set(v_reuseFailAlloc_4907_, 2, v_ngen_4891_);
lean_ctor_set(v_reuseFailAlloc_4907_, 3, v_auxDeclNGen_4892_);
lean_ctor_set(v_reuseFailAlloc_4907_, 4, v_traceState_4893_);
lean_ctor_set(v_reuseFailAlloc_4907_, 5, v___x_4901_);
lean_ctor_set(v_reuseFailAlloc_4907_, 6, v_messages_4894_);
lean_ctor_set(v_reuseFailAlloc_4907_, 7, v_infoState_4895_);
lean_ctor_set(v_reuseFailAlloc_4907_, 8, v_snapshotTasks_4896_);
v___x_4903_ = v_reuseFailAlloc_4907_;
goto v_reusejp_4902_;
}
v_reusejp_4902_:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4904_ = lean_st_ref_set(v___y_4883_, v___x_4903_);
v___x_4905_ = lean_box(0);
v_as_x27_4881_ = v_tail_4887_;
v_b_4882_ = v___x_4905_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4910_, lean_object* v_b_4911_, lean_object* v___y_4912_, lean_object* v___y_4913_){
_start:
{
lean_object* v_res_4914_; 
v_res_4914_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4910_, v_b_4911_, v___y_4912_);
lean_dec(v___y_4912_);
lean_dec(v_as_x27_4910_);
return v_res_4914_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4915_, uint8_t v_logCompileErrors_4916_, uint8_t v_markMeta_4917_, lean_object* v_a_4918_, lean_object* v_a_4919_){
_start:
{
uint8_t v___x_4921_; lean_object* v___x_4922_; 
v___x_4921_ = 0;
lean_inc(v_decl_4915_);
v___x_4922_ = l_Lean_addDecl(v_decl_4915_, v___x_4921_, v_a_4918_, v_a_4919_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_dec_ref_known(v___x_4922_, 1);
if (v_markMeta_4917_ == 0)
{
lean_object* v___x_4923_; 
v___x_4923_ = l_Lean_compileDecl(v_decl_4915_, v_logCompileErrors_4916_, v_a_4918_, v_a_4919_);
return v___x_4923_;
}
else
{
lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
lean_inc(v_decl_4915_);
v___x_4924_ = l_Lean_Declaration_getNames(v_decl_4915_);
v___x_4925_ = lean_box(0);
v___x_4926_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4924_, v___x_4925_, v_a_4919_);
lean_dec(v___x_4924_);
lean_dec_ref(v___x_4926_);
v___x_4927_ = l_Lean_compileDecl(v_decl_4915_, v_logCompileErrors_4916_, v_a_4918_, v_a_4919_);
return v___x_4927_;
}
}
else
{
lean_dec(v_decl_4915_);
return v___x_4922_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4928_, lean_object* v_logCompileErrors_4929_, lean_object* v_markMeta_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_){
_start:
{
uint8_t v_logCompileErrors_boxed_4934_; uint8_t v_markMeta_boxed_4935_; lean_object* v_res_4936_; 
v_logCompileErrors_boxed_4934_ = lean_unbox(v_logCompileErrors_4929_);
v_markMeta_boxed_4935_ = lean_unbox(v_markMeta_4930_);
v_res_4936_ = l_Lean_addAndCompile(v_decl_4928_, v_logCompileErrors_boxed_4934_, v_markMeta_boxed_4935_, v_a_4931_, v_a_4932_);
lean_dec(v_a_4932_);
lean_dec_ref(v_a_4931_);
return v_res_4936_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4937_, lean_object* v_as_x27_4938_, lean_object* v_b_4939_, lean_object* v_a_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4938_, v_b_4939_, v___y_4942_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4945_, lean_object* v_as_x27_4946_, lean_object* v_b_4947_, lean_object* v_a_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_){
_start:
{
lean_object* v_res_4952_; 
v_res_4952_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4945_, v_as_x27_4946_, v_b_4947_, v_a_4948_, v___y_4949_, v___y_4950_);
lean_dec(v___y_4950_);
lean_dec_ref(v___y_4949_);
lean_dec(v_as_x27_4946_);
lean_dec(v_as_4945_);
return v_res_4952_;
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
