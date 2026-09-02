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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
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
v_options_117_ = lean_ctor_get(v___y_114_, 1);
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
v_options_334_ = lean_ctor_get(v___y_326_, 1);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v_suppressElabErrors_385_, uint8_t v___y_386_, lean_object* v_x_387_){
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
return v___x_395_;
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_397_ = lean_string_dec_eq(v_str_390_, v___x_396_);
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
return v_suppressElabErrors_385_;
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
return v___x_399_;
}
else
{
return v_suppressElabErrors_385_;
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
return v___x_405_;
}
else
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_407_ = lean_string_dec_eq(v_str_402_, v___x_406_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_409_ = lean_string_dec_eq(v_str_401_, v___x_408_);
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
return v_suppressElabErrors_385_;
}
}
}
}
else
{
return v___y_386_;
}
}
default: 
{
return v___y_386_;
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
return v___x_412_;
}
else
{
return v_suppressElabErrors_385_;
}
}
default: 
{
return v___y_386_;
}
}
}
else
{
return v___y_386_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_suppressElabErrors_413_, lean_object* v___y_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_suppressElabErrors_boxed_416_; uint8_t v___y_14934__boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v_suppressElabErrors_boxed_416_ = lean_unbox(v_suppressElabErrors_413_);
v___y_14934__boxed_417_ = lean_unbox(v___y_414_);
v_res_418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_416_, v___y_14934__boxed_417_, v_x_415_);
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
v_options_445_ = lean_ctor_get(v___y_440_, 1);
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
lean_object* v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; uint8_t v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_501_; lean_object* v___y_502_; uint8_t v___y_503_; uint8_t v___y_504_; uint8_t v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; lean_object* v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; uint8_t v___y_540_; uint8_t v___y_541_; uint8_t v___y_542_; uint8_t v___x_547_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; uint8_t v___y_553_; uint8_t v___y_554_; uint8_t v___y_556_; uint8_t v___x_570_; 
v___x_547_ = 2;
v___x_570_ = l_Lean_instBEqMessageSeverity_beq(v_severity_459_, v___x_547_);
if (v___x_570_ == 0)
{
v___y_556_ = v___x_570_;
goto v___jp_555_;
}
else
{
uint8_t v___x_571_; 
lean_inc_ref(v_msgData_458_);
v___x_571_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_458_);
v___y_556_ = v___x_571_;
goto v___jp_555_;
}
v___jp_464_:
{
lean_object* v___x_474_; lean_object* v_currNamespace_475_; lean_object* v_openDecls_476_; lean_object* v_env_477_; lean_object* v_nextMacroScope_478_; lean_object* v_ngen_479_; lean_object* v_auxDeclNGen_480_; lean_object* v_traceState_481_; lean_object* v_cache_482_; lean_object* v_messages_483_; lean_object* v_infoState_484_; lean_object* v_snapshotTasks_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_499_; 
v___x_474_ = lean_st_ref_take(v___y_473_);
v_currNamespace_475_ = lean_ctor_get(v___y_472_, 5);
v_openDecls_476_ = lean_ctor_get(v___y_472_, 6);
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
lean_inc_ref(v___y_466_);
lean_inc_ref(v___y_467_);
v___x_491_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_491_, 0, v___y_467_);
lean_ctor_set(v___x_491_, 1, v___y_470_);
lean_ctor_set(v___x_491_, 2, v___y_471_);
lean_ctor_set(v___x_491_, 3, v___y_466_);
lean_ctor_set(v___x_491_, 4, v___x_490_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5, v___y_468_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5 + 1, v___y_469_);
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
lean_object* v_fileName_508_; lean_object* v_fileMap_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_a_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_525_; 
v_fileName_508_ = lean_ctor_get(v___y_502_, 0);
v_fileMap_509_ = lean_ctor_get(v___y_502_, 1);
v___x_510_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_458_);
v___x_511_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_510_, v___y_461_, v___y_462_);
v_a_512_ = lean_ctor_get(v___x_511_, 0);
v_isSharedCheck_525_ = !lean_is_exclusive(v___x_511_);
if (v_isSharedCheck_525_ == 0)
{
v___x_514_ = v___x_511_;
v_isShared_515_ = v_isSharedCheck_525_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_a_512_);
lean_dec(v___x_511_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_525_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
lean_inc_ref_n(v_fileMap_509_, 2);
v___x_516_ = l_Lean_FileMap_toPosition(v_fileMap_509_, v___y_506_);
lean_dec(v___y_506_);
v___x_517_ = l_Lean_FileMap_toPosition(v_fileMap_509_, v___y_507_);
lean_dec(v___y_507_);
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_505_ == 0)
{
lean_del_object(v___x_514_);
lean_dec_ref(v___y_501_);
v___y_465_ = v_a_512_;
v___y_466_ = v___x_519_;
v___y_467_ = v_fileName_508_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___x_516_;
v___y_471_ = v___x_518_;
v___y_472_ = v___y_461_;
v___y_473_ = v___y_462_;
goto v___jp_464_;
}
else
{
uint8_t v___x_520_; 
lean_inc(v_a_512_);
v___x_520_ = l_Lean_MessageData_hasTag(v___y_501_, v_a_512_);
if (v___x_520_ == 0)
{
lean_object* v___x_521_; lean_object* v___x_523_; 
lean_dec_ref_known(v___x_518_, 1);
lean_dec_ref(v___x_516_);
lean_dec(v_a_512_);
v___x_521_ = lean_box(0);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_521_);
v___x_523_ = v___x_514_;
goto v_reusejp_522_;
}
else
{
lean_object* v_reuseFailAlloc_524_; 
v_reuseFailAlloc_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_524_, 0, v___x_521_);
v___x_523_ = v_reuseFailAlloc_524_;
goto v_reusejp_522_;
}
v_reusejp_522_:
{
return v___x_523_;
}
}
else
{
lean_del_object(v___x_514_);
v___y_465_ = v_a_512_;
v___y_466_ = v___x_519_;
v___y_467_ = v_fileName_508_;
v___y_468_ = v___y_503_;
v___y_469_ = v___y_504_;
v___y_470_ = v___x_516_;
v___y_471_ = v___x_518_;
v___y_472_ = v___y_461_;
v___y_473_ = v___y_462_;
goto v___jp_464_;
}
}
}
}
v___jp_526_:
{
lean_object* v___x_534_; 
v___x_534_ = l_Lean_Syntax_getTailPos_x3f(v___y_530_, v___y_529_);
lean_dec(v___y_530_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_inc(v___y_533_);
v___y_501_ = v___y_527_;
v___y_502_ = v___y_528_;
v___y_503_ = v___y_529_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_532_;
v___y_506_ = v___y_533_;
v___y_507_ = v___y_533_;
goto v___jp_500_;
}
else
{
lean_object* v_val_535_; 
v_val_535_ = lean_ctor_get(v___x_534_, 0);
lean_inc(v_val_535_);
lean_dec_ref_known(v___x_534_, 1);
v___y_501_ = v___y_527_;
v___y_502_ = v___y_528_;
v___y_503_ = v___y_529_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_532_;
v___y_506_ = v___y_533_;
v___y_507_ = v_val_535_;
goto v___jp_500_;
}
}
v___jp_536_:
{
lean_object* v_ref_543_; lean_object* v___x_544_; 
v_ref_543_ = l_Lean_replaceRef(v_ref_457_, v___y_538_);
v___x_544_ = l_Lean_Syntax_getPos_x3f(v_ref_543_, v___y_540_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
v___x_545_ = lean_unsigned_to_nat(0u);
v___y_527_ = v___y_537_;
v___y_528_ = v___y_539_;
v___y_529_ = v___y_540_;
v___y_530_ = v_ref_543_;
v___y_531_ = v___y_542_;
v___y_532_ = v___y_541_;
v___y_533_ = v___x_545_;
goto v___jp_526_;
}
else
{
lean_object* v_val_546_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_544_, 1);
v___y_527_ = v___y_537_;
v___y_528_ = v___y_539_;
v___y_529_ = v___y_540_;
v___y_530_ = v_ref_543_;
v___y_531_ = v___y_542_;
v___y_532_ = v___y_541_;
v___y_533_ = v_val_546_;
goto v___jp_526_;
}
}
v___jp_548_:
{
if (v___y_554_ == 0)
{
v___y_537_ = v___y_551_;
v___y_538_ = v___y_549_;
v___y_539_ = v___y_550_;
v___y_540_ = v___y_553_;
v___y_541_ = v___y_552_;
v___y_542_ = v_severity_459_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___y_551_;
v___y_538_ = v___y_549_;
v___y_539_ = v___y_550_;
v___y_540_ = v___y_553_;
v___y_541_ = v___y_552_;
v___y_542_ = v___x_547_;
goto v___jp_536_;
}
}
v___jp_555_:
{
if (v___y_556_ == 0)
{
lean_object* v_toCold_557_; lean_object* v_options_558_; lean_object* v_ref_559_; uint8_t v_suppressElabErrors_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___f_563_; uint8_t v___x_564_; uint8_t v___x_565_; 
v_toCold_557_ = lean_ctor_get(v___y_461_, 0);
v_options_558_ = lean_ctor_get(v___y_461_, 1);
v_ref_559_ = lean_ctor_get(v___y_461_, 4);
v_suppressElabErrors_560_ = lean_ctor_get_uint8(v___y_461_, sizeof(void*)*10 + 1);
v___x_561_ = lean_box(v_suppressElabErrors_560_);
v___x_562_ = lean_box(v___y_556_);
v___f_563_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_563_, 0, v___x_561_);
lean_closure_set(v___f_563_, 1, v___x_562_);
v___x_564_ = 1;
v___x_565_ = l_Lean_instBEqMessageSeverity_beq(v_severity_459_, v___x_564_);
if (v___x_565_ == 0)
{
v___y_549_ = v_ref_559_;
v___y_550_ = v_toCold_557_;
v___y_551_ = v___f_563_;
v___y_552_ = v_suppressElabErrors_560_;
v___y_553_ = v___y_556_;
v___y_554_ = v___x_565_;
goto v___jp_548_;
}
else
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = l_Lean_warningAsError;
v___x_567_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_558_, v___x_566_);
v___y_549_ = v_ref_559_;
v___y_550_ = v_toCold_557_;
v___y_551_ = v___f_563_;
v___y_552_ = v_suppressElabErrors_560_;
v___y_553_ = v___y_556_;
v___y_554_ = v___x_567_;
goto v___jp_548_;
}
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
lean_dec_ref(v_msgData_458_);
v___x_568_ = lean_box(0);
v___x_569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_569_, 0, v___x_568_);
return v___x_569_;
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
v_ref_588_ = lean_ctor_get(v___y_585_, 4);
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
lean_object* v_declName_778_; lean_object* v_type_779_; lean_object* v_value_780_; lean_object* v_body_781_; lean_object* v_d_782_; lean_object* v___x_783_; 
v_declName_778_ = lean_ctor_get(v_a_770_, 0);
lean_inc(v_declName_778_);
v_type_779_ = lean_ctor_get(v_a_770_, 1);
lean_inc_ref(v_type_779_);
v_value_780_ = lean_ctor_get(v_a_770_, 2);
lean_inc_ref(v_value_780_);
v_body_781_ = lean_ctor_get(v_a_770_, 3);
lean_inc_ref(v_body_781_);
lean_dec_ref_known(v_a_770_, 4);
v_d_782_ = lean_expr_instantiate_rev(v_type_779_, v_fvars_769_);
lean_dec_ref(v_type_779_);
lean_inc_ref(v_f_768_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v_d_782_);
v___x_783_ = lean_apply_8(v_f_768_, v_d_782_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, lean_box(0));
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v_v_784_; lean_object* v___x_785_; 
lean_dec_ref_known(v___x_783_, 1);
v_v_784_ = lean_expr_instantiate_rev(v_value_780_, v_fvars_769_);
lean_dec_ref(v_value_780_);
lean_inc_ref(v_f_768_);
lean_inc(v___y_776_);
lean_inc_ref(v___y_775_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc(v___y_771_);
lean_inc_ref(v_v_784_);
v___x_785_ = lean_apply_8(v_f_768_, v_v_784_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, lean_box(0));
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v___f_786_; uint8_t v___x_787_; uint8_t v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_785_, 1);
v___f_786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_786_, 0, v_fvars_769_);
lean_closure_set(v___f_786_, 1, v_f_768_);
lean_closure_set(v___f_786_, 2, v_body_781_);
v___x_787_ = 0;
v___x_788_ = 0;
v___x_789_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_778_, v_d_782_, v_v_784_, v___f_786_, v___x_787_, v___x_788_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
return v___x_789_;
}
else
{
lean_dec_ref(v_v_784_);
lean_dec_ref(v_d_782_);
lean_dec_ref(v_body_781_);
lean_dec(v_declName_778_);
lean_dec_ref(v_fvars_769_);
lean_dec_ref(v_f_768_);
return v___x_785_;
}
}
else
{
lean_dec_ref(v_d_782_);
lean_dec_ref(v_body_781_);
lean_dec_ref(v_value_780_);
lean_dec(v_declName_778_);
lean_dec_ref(v_fvars_769_);
lean_dec_ref(v_f_768_);
return v___x_783_;
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
lean_object* v_binderName_898_; lean_object* v_binderType_899_; lean_object* v_body_900_; uint8_t v_binderInfo_901_; lean_object* v_d_902_; lean_object* v___x_903_; 
v_binderName_898_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_binderName_898_);
v_binderType_899_ = lean_ctor_get(v_a_890_, 1);
lean_inc_ref(v_binderType_899_);
v_body_900_ = lean_ctor_get(v_a_890_, 2);
lean_inc_ref(v_body_900_);
v_binderInfo_901_ = lean_ctor_get_uint8(v_a_890_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_890_, 3);
v_d_902_ = lean_expr_instantiate_rev(v_binderType_899_, v_fvars_889_);
lean_dec_ref(v_binderType_899_);
lean_inc_ref(v_f_888_);
lean_inc(v___y_896_);
lean_inc_ref(v___y_895_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___y_892_);
lean_inc(v___y_891_);
lean_inc_ref(v_d_902_);
v___x_903_ = lean_apply_8(v_f_888_, v_d_902_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, lean_box(0));
if (lean_obj_tag(v___x_903_) == 0)
{
lean_object* v___f_904_; uint8_t v___x_905_; lean_object* v___x_906_; 
lean_dec_ref_known(v___x_903_, 1);
v___f_904_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_904_, 0, v_fvars_889_);
lean_closure_set(v___f_904_, 1, v_f_888_);
lean_closure_set(v___f_904_, 2, v_body_900_);
v___x_905_ = 0;
v___x_906_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_898_, v_binderInfo_901_, v_d_902_, v___f_904_, v___x_905_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_);
return v___x_906_;
}
else
{
lean_dec_ref(v_d_902_);
lean_dec_ref(v_body_900_);
lean_dec(v_binderName_898_);
lean_dec_ref(v_fvars_889_);
lean_dec_ref(v_f_888_);
return v___x_903_;
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
lean_object* v_binderName_976_; lean_object* v_binderType_977_; lean_object* v_body_978_; uint8_t v_binderInfo_979_; lean_object* v_d_980_; lean_object* v___x_981_; 
v_binderName_976_ = lean_ctor_get(v_a_968_, 0);
lean_inc(v_binderName_976_);
v_binderType_977_ = lean_ctor_get(v_a_968_, 1);
lean_inc_ref(v_binderType_977_);
v_body_978_ = lean_ctor_get(v_a_968_, 2);
lean_inc_ref(v_body_978_);
v_binderInfo_979_ = lean_ctor_get_uint8(v_a_968_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_968_, 3);
v_d_980_ = lean_expr_instantiate_rev(v_binderType_977_, v_fvars_967_);
lean_dec_ref(v_binderType_977_);
lean_inc_ref(v_f_966_);
lean_inc(v___y_974_);
lean_inc_ref(v___y_973_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc(v___y_969_);
lean_inc_ref(v_d_980_);
v___x_981_ = lean_apply_8(v_f_966_, v_d_980_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, lean_box(0));
if (lean_obj_tag(v___x_981_) == 0)
{
lean_object* v___f_982_; uint8_t v___x_983_; lean_object* v___x_984_; 
lean_dec_ref_known(v___x_981_, 1);
v___f_982_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_982_, 0, v_fvars_967_);
lean_closure_set(v___f_982_, 1, v_f_966_);
lean_closure_set(v___f_982_, 2, v_body_978_);
v___x_983_ = 0;
v___x_984_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_976_, v_binderInfo_979_, v_d_980_, v___f_982_, v___x_983_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_);
return v___x_984_;
}
else
{
lean_dec_ref(v_d_980_);
lean_dec_ref(v_body_978_);
lean_dec(v_binderName_976_);
lean_dec_ref(v_fvars_967_);
lean_dec_ref(v_f_966_);
return v___x_981_;
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
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v_nbuckets_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; 
v___x_1125_ = lean_array_get_size(v_data_1124_);
v___x_1126_ = lean_unsigned_to_nat(2u);
v_nbuckets_1127_ = lean_nat_mul(v___x_1125_, v___x_1126_);
v___x_1128_ = lean_unsigned_to_nat(0u);
v___x_1129_ = lean_box(0);
v___x_1130_ = lean_mk_array(v_nbuckets_1127_, v___x_1129_);
v___x_1131_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1128_, v_data_1124_, v___x_1130_);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1132_, lean_object* v_b_1133_, lean_object* v_x_1134_){
_start:
{
if (lean_obj_tag(v_x_1134_) == 0)
{
lean_dec(v_b_1133_);
lean_dec_ref(v_a_1132_);
return v_x_1134_;
}
else
{
lean_object* v_key_1135_; lean_object* v_value_1136_; lean_object* v_tail_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1149_; 
v_key_1135_ = lean_ctor_get(v_x_1134_, 0);
v_value_1136_ = lean_ctor_get(v_x_1134_, 1);
v_tail_1137_ = lean_ctor_get(v_x_1134_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_x_1134_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1139_ = v_x_1134_;
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_tail_1137_);
lean_inc(v_value_1136_);
lean_inc(v_key_1135_);
lean_dec(v_x_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1149_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
uint8_t v___x_1141_; 
v___x_1141_ = lean_expr_eqv(v_key_1135_, v_a_1132_);
if (v___x_1141_ == 0)
{
lean_object* v___x_1142_; lean_object* v___x_1144_; 
v___x_1142_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1132_, v_b_1133_, v_tail_1137_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 2, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_key_1135_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_value_1136_);
lean_ctor_set(v_reuseFailAlloc_1145_, 2, v___x_1142_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
else
{
lean_object* v___x_1147_; 
lean_dec(v_value_1136_);
lean_dec(v_key_1135_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v_b_1133_);
lean_ctor_set(v___x_1139_, 0, v_a_1132_);
v___x_1147_ = v___x_1139_;
goto v_reusejp_1146_;
}
else
{
lean_object* v_reuseFailAlloc_1148_; 
v_reuseFailAlloc_1148_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1148_, 0, v_a_1132_);
lean_ctor_set(v_reuseFailAlloc_1148_, 1, v_b_1133_);
lean_ctor_set(v_reuseFailAlloc_1148_, 2, v_tail_1137_);
v___x_1147_ = v_reuseFailAlloc_1148_;
goto v_reusejp_1146_;
}
v_reusejp_1146_:
{
return v___x_1147_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1150_, lean_object* v_x_1151_){
_start:
{
if (lean_obj_tag(v_x_1151_) == 0)
{
uint8_t v___x_1152_; 
v___x_1152_ = 0;
return v___x_1152_;
}
else
{
lean_object* v_key_1153_; lean_object* v_tail_1154_; uint8_t v___x_1155_; 
v_key_1153_ = lean_ctor_get(v_x_1151_, 0);
v_tail_1154_ = lean_ctor_get(v_x_1151_, 2);
v___x_1155_ = lean_expr_eqv(v_key_1153_, v_a_1150_);
if (v___x_1155_ == 0)
{
v_x_1151_ = v_tail_1154_;
goto _start;
}
else
{
return v___x_1155_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1157_, lean_object* v_x_1158_){
_start:
{
uint8_t v_res_1159_; lean_object* v_r_1160_; 
v_res_1159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1157_, v_x_1158_);
lean_dec(v_x_1158_);
lean_dec_ref(v_a_1157_);
v_r_1160_ = lean_box(v_res_1159_);
return v_r_1160_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1161_, lean_object* v_a_1162_, lean_object* v_b_1163_){
_start:
{
lean_object* v_size_1164_; lean_object* v_buckets_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1208_; 
v_size_1164_ = lean_ctor_get(v_m_1161_, 0);
v_buckets_1165_ = lean_ctor_get(v_m_1161_, 1);
v_isSharedCheck_1208_ = !lean_is_exclusive(v_m_1161_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1167_ = v_m_1161_;
v_isShared_1168_ = v_isSharedCheck_1208_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_buckets_1165_);
lean_inc(v_size_1164_);
lean_dec(v_m_1161_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1208_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v___x_1172_; uint64_t v_fold_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; uint64_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; size_t v___x_1181_; lean_object* v_bkt_1182_; uint8_t v___x_1183_; 
v___x_1169_ = lean_array_get_size(v_buckets_1165_);
v___x_1170_ = l_Lean_Expr_hash(v_a_1162_);
v___x_1171_ = 32ULL;
v___x_1172_ = lean_uint64_shift_right(v___x_1170_, v___x_1171_);
v_fold_1173_ = lean_uint64_xor(v___x_1170_, v___x_1172_);
v___x_1174_ = 16ULL;
v___x_1175_ = lean_uint64_shift_right(v_fold_1173_, v___x_1174_);
v___x_1176_ = lean_uint64_xor(v_fold_1173_, v___x_1175_);
v___x_1177_ = lean_uint64_to_usize(v___x_1176_);
v___x_1178_ = lean_usize_of_nat(v___x_1169_);
v___x_1179_ = ((size_t)1ULL);
v___x_1180_ = lean_usize_sub(v___x_1178_, v___x_1179_);
v___x_1181_ = lean_usize_land(v___x_1177_, v___x_1180_);
v_bkt_1182_ = lean_array_uget_borrowed(v_buckets_1165_, v___x_1181_);
v___x_1183_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1162_, v_bkt_1182_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; lean_object* v_size_x27_1185_; lean_object* v___x_1186_; lean_object* v_buckets_x27_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v___x_1184_ = lean_unsigned_to_nat(1u);
v_size_x27_1185_ = lean_nat_add(v_size_1164_, v___x_1184_);
lean_dec(v_size_1164_);
lean_inc(v_bkt_1182_);
v___x_1186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1186_, 0, v_a_1162_);
lean_ctor_set(v___x_1186_, 1, v_b_1163_);
lean_ctor_set(v___x_1186_, 2, v_bkt_1182_);
v_buckets_x27_1187_ = lean_array_uset(v_buckets_1165_, v___x_1181_, v___x_1186_);
v___x_1188_ = lean_unsigned_to_nat(4u);
v___x_1189_ = lean_nat_mul(v_size_x27_1185_, v___x_1188_);
v___x_1190_ = lean_unsigned_to_nat(3u);
v___x_1191_ = lean_nat_div(v___x_1189_, v___x_1190_);
lean_dec(v___x_1189_);
v___x_1192_ = lean_array_get_size(v_buckets_x27_1187_);
v___x_1193_ = lean_nat_dec_le(v___x_1191_, v___x_1192_);
lean_dec(v___x_1191_);
if (v___x_1193_ == 0)
{
lean_object* v_val_1194_; lean_object* v___x_1196_; 
v_val_1194_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1187_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_val_1194_);
lean_ctor_set(v___x_1167_, 0, v_size_x27_1185_);
v___x_1196_ = v___x_1167_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1197_; 
v_reuseFailAlloc_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1197_, 0, v_size_x27_1185_);
lean_ctor_set(v_reuseFailAlloc_1197_, 1, v_val_1194_);
v___x_1196_ = v_reuseFailAlloc_1197_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
return v___x_1196_;
}
}
else
{
lean_object* v___x_1199_; 
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v_buckets_x27_1187_);
lean_ctor_set(v___x_1167_, 0, v_size_x27_1185_);
v___x_1199_ = v___x_1167_;
goto v_reusejp_1198_;
}
else
{
lean_object* v_reuseFailAlloc_1200_; 
v_reuseFailAlloc_1200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1200_, 0, v_size_x27_1185_);
lean_ctor_set(v_reuseFailAlloc_1200_, 1, v_buckets_x27_1187_);
v___x_1199_ = v_reuseFailAlloc_1200_;
goto v_reusejp_1198_;
}
v_reusejp_1198_:
{
return v___x_1199_;
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v_buckets_x27_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1206_; 
lean_inc(v_bkt_1182_);
v___x_1201_ = lean_box(0);
v_buckets_x27_1202_ = lean_array_uset(v_buckets_1165_, v___x_1181_, v___x_1201_);
v___x_1203_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1162_, v_b_1163_, v_bkt_1182_);
v___x_1204_ = lean_array_uset(v_buckets_x27_1202_, v___x_1181_, v___x_1203_);
if (v_isShared_1168_ == 0)
{
lean_ctor_set(v___x_1167_, 1, v___x_1204_);
v___x_1206_ = v___x_1167_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_size_1164_);
lean_ctor_set(v_reuseFailAlloc_1207_, 1, v___x_1204_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1209_, lean_object* v_e_1210_, lean_object* v_a_1211_){
_start:
{
lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; 
v___x_1213_ = lean_st_ref_take(v_a_1209_);
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1213_, v_e_1210_, v_a_1211_);
v___x_1215_ = lean_st_ref_put(v_a_1209_, v___x_1214_);
v___x_1216_ = lean_box(0);
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1217_, lean_object* v_e_1218_, lean_object* v_a_1219_, lean_object* v___y_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1217_, v_e_1218_, v_a_1219_);
lean_dec(v_a_1217_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1222_, lean_object* v_e_1223_, lean_object* v_a_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1222_, v_e_1223_, v_a_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v_a_1224_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1232_, lean_object* v_e_1233_, lean_object* v_a_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_a_1242_; lean_object* v___y_1254_; lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_inc(v_a_1234_);
v___x_1256_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1256_, 0, lean_box(0));
lean_closure_set(v___x_1256_, 1, lean_box(0));
lean_closure_set(v___x_1256_, 2, v_a_1234_);
v___x_1257_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1256_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1257_) == 0)
{
lean_object* v_a_1258_; lean_object* v___x_1260_; uint8_t v_isShared_1261_; uint8_t v_isSharedCheck_1294_; 
v_a_1258_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1294_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1260_ = v___x_1257_;
v_isShared_1261_ = v_isSharedCheck_1294_;
goto v_resetjp_1259_;
}
else
{
lean_inc(v_a_1258_);
lean_dec(v___x_1257_);
v___x_1260_ = lean_box(0);
v_isShared_1261_ = v_isSharedCheck_1294_;
goto v_resetjp_1259_;
}
v_resetjp_1259_:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1258_, v_e_1233_);
lean_dec(v_a_1258_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v___x_1263_; 
lean_del_object(v___x_1260_);
lean_inc_ref(v_fn_1232_);
lean_inc(v___y_1239_);
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v_e_1233_);
v___x_1263_ = lean_apply_7(v_fn_1232_, v_e_1233_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_, lean_box(0));
if (lean_obj_tag(v___x_1263_) == 0)
{
lean_object* v_a_1264_; uint8_t v___x_1265_; 
v_a_1264_ = lean_ctor_get(v___x_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___x_1263_, 1);
v___x_1265_ = lean_unbox(v_a_1264_);
lean_dec(v_a_1264_);
if (v___x_1265_ == 0)
{
lean_object* v___x_1266_; 
lean_dec_ref(v_fn_1232_);
v___x_1266_ = lean_box(0);
v_a_1242_ = v___x_1266_;
goto v___jp_1241_;
}
else
{
switch(lean_obj_tag(v_e_1233_))
{
case 7:
{
lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1267_, 0, v_fn_1232_);
lean_inc_ref(v_e_1233_);
v___x_1268_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1267_, v_e_1233_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1268_;
goto v___jp_1253_;
}
case 6:
{
lean_object* v___x_1269_; lean_object* v___x_1270_; 
v___x_1269_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1269_, 0, v_fn_1232_);
lean_inc_ref(v_e_1233_);
v___x_1270_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1269_, v_e_1233_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1270_;
goto v___jp_1253_;
}
case 8:
{
lean_object* v___x_1271_; lean_object* v___x_1272_; 
v___x_1271_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1271_, 0, v_fn_1232_);
lean_inc_ref(v_e_1233_);
v___x_1272_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1271_, v_e_1233_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1272_;
goto v___jp_1253_;
}
case 5:
{
lean_object* v_fn_1273_; lean_object* v_arg_1274_; lean_object* v___x_1275_; 
v_fn_1273_ = lean_ctor_get(v_e_1233_, 0);
v_arg_1274_ = lean_ctor_get(v_e_1233_, 1);
lean_inc_ref(v_fn_1273_);
lean_inc_ref(v_fn_1232_);
v___x_1275_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1232_, v_fn_1273_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1275_) == 0)
{
lean_object* v___x_1276_; 
lean_dec_ref_known(v___x_1275_, 1);
lean_inc_ref(v_arg_1274_);
v___x_1276_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1232_, v_arg_1274_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1276_;
goto v___jp_1253_;
}
else
{
lean_dec_ref(v_fn_1232_);
v___y_1254_ = v___x_1275_;
goto v___jp_1253_;
}
}
case 10:
{
lean_object* v_expr_1277_; lean_object* v___x_1278_; 
v_expr_1277_ = lean_ctor_get(v_e_1233_, 1);
lean_inc_ref(v_expr_1277_);
v___x_1278_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1232_, v_expr_1277_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1278_;
goto v___jp_1253_;
}
case 11:
{
lean_object* v_struct_1279_; lean_object* v___x_1280_; 
v_struct_1279_ = lean_ctor_get(v_e_1233_, 2);
lean_inc_ref(v_struct_1279_);
v___x_1280_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1232_, v_struct_1279_, v_a_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
v___y_1254_ = v___x_1280_;
goto v___jp_1253_;
}
default: 
{
lean_object* v___x_1281_; 
lean_dec_ref(v_fn_1232_);
v___x_1281_ = lean_box(0);
v_a_1242_ = v___x_1281_;
goto v___jp_1241_;
}
}
}
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_fn_1232_);
v_a_1282_ = lean_ctor_get(v___x_1263_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1263_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1263_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1263_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
else
{
lean_object* v_val_1290_; lean_object* v___x_1292_; 
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_fn_1232_);
v_val_1290_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_val_1290_);
lean_dec_ref_known(v___x_1262_, 1);
if (v_isShared_1261_ == 0)
{
lean_ctor_set(v___x_1260_, 0, v_val_1290_);
v___x_1292_ = v___x_1260_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_val_1290_);
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
lean_object* v_a_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1302_; 
lean_dec_ref(v_e_1233_);
lean_dec_ref(v_fn_1232_);
v_a_1295_ = lean_ctor_get(v___x_1257_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1257_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1297_ = v___x_1257_;
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_a_1295_);
lean_dec(v___x_1257_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1302_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1300_; 
if (v_isShared_1298_ == 0)
{
v___x_1300_ = v___x_1297_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_a_1295_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
v___jp_1241_:
{
lean_object* v___f_1243_; lean_object* v___x_1244_; 
lean_inc(v_a_1234_);
v___f_1243_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1243_, 0, v_a_1234_);
lean_closure_set(v___f_1243_, 1, v_e_1233_);
lean_closure_set(v___f_1243_, 2, v_a_1242_);
v___x_1244_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1243_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, v___y_1239_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1251_; 
v_isSharedCheck_1251_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1251_ == 0)
{
lean_object* v_unused_1252_; 
v_unused_1252_ = lean_ctor_get(v___x_1244_, 0);
lean_dec(v_unused_1252_);
v___x_1246_ = v___x_1244_;
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
else
{
lean_dec(v___x_1244_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1251_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1249_; 
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_a_1242_);
v___x_1249_ = v___x_1246_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_a_1242_);
v___x_1249_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
return v___x_1249_;
}
}
}
else
{
return v___x_1244_;
}
}
v___jp_1253_:
{
if (lean_obj_tag(v___y_1254_) == 0)
{
lean_object* v_a_1255_; 
v_a_1255_ = lean_ctor_get(v___y_1254_, 0);
lean_inc(v_a_1255_);
lean_dec_ref_known(v___y_1254_, 1);
v_a_1242_ = v_a_1255_;
goto v___jp_1241_;
}
else
{
lean_dec_ref(v_e_1233_);
return v___y_1254_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1303_ = lean_box(0);
v___x_1304_ = lean_unsigned_to_nat(16u);
v___x_1305_ = lean_mk_array(v___x_1304_, v___x_1303_);
return v___x_1305_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1306_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1307_ = lean_unsigned_to_nat(0u);
v___x_1308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1308_, 0, v___x_1307_);
lean_ctor_set(v___x_1308_, 1, v___x_1306_);
return v___x_1308_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1309_; lean_object* v___x_1310_; 
v___x_1309_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1310_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, lean_box(0));
lean_closure_set(v___x_1310_, 2, v___x_1309_);
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1311_, lean_object* v_fn_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v_a_1321_; lean_object* v___x_1322_; 
v___x_1319_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1320_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1319_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
v_a_1321_ = lean_ctor_get(v___x_1320_, 0);
lean_inc(v_a_1321_);
lean_dec_ref(v___x_1320_);
v___x_1322_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1312_, v_input_1311_, v_a_1321_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_object* v_a_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1327_; uint8_t v_isShared_1328_; uint8_t v_isSharedCheck_1332_; 
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc(v_a_1323_);
lean_dec_ref_known(v___x_1322_, 1);
v___x_1324_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1324_, 0, lean_box(0));
lean_closure_set(v___x_1324_, 1, lean_box(0));
lean_closure_set(v___x_1324_, 2, v_a_1321_);
v___x_1325_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1324_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_, v___y_1317_);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1332_ == 0)
{
lean_object* v_unused_1333_; 
v_unused_1333_ = lean_ctor_get(v___x_1325_, 0);
lean_dec(v_unused_1333_);
v___x_1327_ = v___x_1325_;
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
else
{
lean_dec(v___x_1325_);
v___x_1327_ = lean_box(0);
v_isShared_1328_ = v_isSharedCheck_1332_;
goto v_resetjp_1326_;
}
v_resetjp_1326_:
{
lean_object* v___x_1330_; 
if (v_isShared_1328_ == 0)
{
lean_ctor_set(v___x_1327_, 0, v_a_1323_);
v___x_1330_ = v___x_1327_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v_a_1323_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
else
{
lean_dec(v_a_1321_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1334_, lean_object* v_fn_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_, lean_object* v___y_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1334_, v_fn_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, v___y_1340_);
lean_dec(v___y_1340_);
lean_dec_ref(v___y_1339_);
lean_dec(v___y_1338_);
lean_dec_ref(v___y_1337_);
lean_dec(v___y_1336_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1343_, lean_object* v_fn_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___f_1351_; lean_object* v___x_1352_; 
v___f_1351_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1351_, 0, v_fn_1344_);
v___x_1352_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1343_, v___f_1351_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1353_, lean_object* v_fn_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v_res_1361_; 
v_res_1361_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1353_, v_fn_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, v___y_1359_);
lean_dec(v___y_1359_);
lean_dec_ref(v___y_1358_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
return v_res_1361_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1362_, lean_object* v_x_1363_, lean_object* v_x_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
if (lean_obj_tag(v_x_1364_) == 0)
{
lean_object* v___x_1371_; 
lean_dec_ref(v_fn_1362_);
v___x_1371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1371_, 0, v_x_1363_);
return v___x_1371_;
}
else
{
lean_object* v_head_1372_; lean_object* v_tail_1373_; lean_object* v_type_1374_; lean_object* v___x_1375_; 
v_head_1372_ = lean_ctor_get(v_x_1364_, 0);
lean_inc(v_head_1372_);
v_tail_1373_ = lean_ctor_get(v_x_1364_, 1);
lean_inc(v_tail_1373_);
lean_dec_ref_known(v_x_1364_, 2);
v_type_1374_ = lean_ctor_get(v_head_1372_, 1);
lean_inc_ref(v_type_1374_);
lean_dec(v_head_1372_);
lean_inc_ref(v_fn_1362_);
v___x_1375_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1374_, v_fn_1362_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_, v___y_1369_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc(v_a_1376_);
lean_dec_ref_known(v___x_1375_, 1);
v_x_1363_ = v_a_1376_;
v_x_1364_ = v_tail_1373_;
goto _start;
}
else
{
lean_dec(v_tail_1373_);
lean_dec_ref(v_fn_1362_);
return v___x_1375_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1378_, v_x_1379_, v_x_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
lean_dec(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_dec(v___y_1383_);
lean_dec_ref(v___y_1382_);
lean_dec(v___y_1381_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1388_, lean_object* v_x_1389_, lean_object* v_x_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
if (lean_obj_tag(v_x_1390_) == 0)
{
lean_object* v___x_1397_; 
lean_dec_ref(v_fn_1388_);
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_x_1389_);
return v___x_1397_;
}
else
{
lean_object* v_head_1398_; lean_object* v_tail_1399_; lean_object* v___y_1401_; lean_object* v_type_1404_; lean_object* v_ctors_1405_; lean_object* v___x_1406_; 
v_head_1398_ = lean_ctor_get(v_x_1390_, 0);
lean_inc(v_head_1398_);
v_tail_1399_ = lean_ctor_get(v_x_1390_, 1);
lean_inc(v_tail_1399_);
lean_dec_ref_known(v_x_1390_, 2);
v_type_1404_ = lean_ctor_get(v_head_1398_, 1);
lean_inc_ref(v_type_1404_);
v_ctors_1405_ = lean_ctor_get(v_head_1398_, 2);
lean_inc(v_ctors_1405_);
lean_dec(v_head_1398_);
lean_inc_ref(v_fn_1388_);
v___x_1406_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1404_, v_fn_1388_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_object* v_a_1407_; lean_object* v___x_1408_; 
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
lean_inc(v_a_1407_);
lean_dec_ref_known(v___x_1406_, 1);
lean_inc_ref(v_fn_1388_);
v___x_1408_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1388_, v_a_1407_, v_ctors_1405_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
v___y_1401_ = v___x_1408_;
goto v___jp_1400_;
}
else
{
lean_dec(v_ctors_1405_);
v___y_1401_ = v___x_1406_;
goto v___jp_1400_;
}
v___jp_1400_:
{
if (lean_obj_tag(v___y_1401_) == 0)
{
lean_object* v_a_1402_; 
v_a_1402_ = lean_ctor_get(v___y_1401_, 0);
lean_inc(v_a_1402_);
lean_dec_ref_known(v___y_1401_, 1);
v_x_1389_ = v_a_1402_;
v_x_1390_ = v_tail_1399_;
goto _start;
}
else
{
lean_dec(v_tail_1399_);
lean_dec_ref(v_fn_1388_);
return v___y_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1409_, lean_object* v_x_1410_, lean_object* v_x_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
lean_object* v_res_1418_; 
v_res_1418_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1409_, v_x_1410_, v_x_1411_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1419_, lean_object* v_x_1420_, lean_object* v_x_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
if (lean_obj_tag(v_x_1421_) == 0)
{
lean_object* v___x_1428_; 
lean_dec_ref(v_fn_1419_);
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_x_1420_);
return v___x_1428_;
}
else
{
lean_object* v_head_1429_; lean_object* v_tail_1430_; lean_object* v___y_1432_; lean_object* v_toConstantVal_1435_; lean_object* v_value_1436_; lean_object* v_type_1437_; lean_object* v___x_1438_; 
v_head_1429_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_head_1429_);
v_tail_1430_ = lean_ctor_get(v_x_1421_, 1);
lean_inc(v_tail_1430_);
lean_dec_ref_known(v_x_1421_, 2);
v_toConstantVal_1435_ = lean_ctor_get(v_head_1429_, 0);
lean_inc_ref(v_toConstantVal_1435_);
v_value_1436_ = lean_ctor_get(v_head_1429_, 1);
lean_inc_ref(v_value_1436_);
lean_dec(v_head_1429_);
v_type_1437_ = lean_ctor_get(v_toConstantVal_1435_, 2);
lean_inc_ref(v_type_1437_);
lean_dec_ref(v_toConstantVal_1435_);
lean_inc_ref(v_fn_1419_);
v___x_1438_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1437_, v_fn_1419_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_object* v___x_1439_; 
lean_dec_ref_known(v___x_1438_, 1);
lean_inc_ref(v_fn_1419_);
v___x_1439_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1436_, v_fn_1419_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_);
v___y_1432_ = v___x_1439_;
goto v___jp_1431_;
}
else
{
lean_dec_ref(v_value_1436_);
v___y_1432_ = v___x_1438_;
goto v___jp_1431_;
}
v___jp_1431_:
{
if (lean_obj_tag(v___y_1432_) == 0)
{
lean_object* v_a_1433_; 
v_a_1433_ = lean_ctor_get(v___y_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref_known(v___y_1432_, 1);
v_x_1420_ = v_a_1433_;
v_x_1421_ = v_tail_1430_;
goto _start;
}
else
{
lean_dec(v_tail_1430_);
lean_dec_ref(v_fn_1419_);
return v___y_1432_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1440_, lean_object* v_x_1441_, lean_object* v_x_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1440_, v_x_1441_, v_x_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_);
lean_dec(v___y_1447_);
lean_dec_ref(v___y_1446_);
lean_dec(v___y_1445_);
lean_dec_ref(v___y_1444_);
lean_dec(v___y_1443_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1450_, lean_object* v_d_1451_, lean_object* v_a_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
switch(lean_obj_tag(v_d_1451_))
{
case 0:
{
lean_object* v_val_1459_; lean_object* v_toConstantVal_1460_; lean_object* v_type_1461_; lean_object* v___x_1462_; 
v_val_1459_ = lean_ctor_get(v_d_1451_, 0);
lean_inc_ref(v_val_1459_);
lean_dec_ref_known(v_d_1451_, 1);
v_toConstantVal_1460_ = lean_ctor_get(v_val_1459_, 0);
lean_inc_ref(v_toConstantVal_1460_);
lean_dec_ref(v_val_1459_);
v_type_1461_ = lean_ctor_get(v_toConstantVal_1460_, 2);
lean_inc_ref(v_type_1461_);
lean_dec_ref(v_toConstantVal_1460_);
v___x_1462_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1461_, v_fn_1450_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1462_;
}
case 4:
{
lean_object* v___x_1463_; 
lean_dec_ref(v_fn_1450_);
v___x_1463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1463_, 0, v_a_1452_);
return v___x_1463_;
}
case 5:
{
lean_object* v_defns_1464_; lean_object* v___x_1465_; 
v_defns_1464_ = lean_ctor_get(v_d_1451_, 0);
lean_inc(v_defns_1464_);
lean_dec_ref_known(v_d_1451_, 1);
v___x_1465_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1450_, v_a_1452_, v_defns_1464_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1465_;
}
case 6:
{
lean_object* v_types_1466_; lean_object* v___x_1467_; 
v_types_1466_ = lean_ctor_get(v_d_1451_, 2);
lean_inc(v_types_1466_);
lean_dec_ref_known(v_d_1451_, 3);
v___x_1467_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1450_, v_a_1452_, v_types_1466_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1467_;
}
default: 
{
lean_object* v_val_1468_; lean_object* v_toConstantVal_1469_; lean_object* v_value_1470_; lean_object* v_type_1471_; lean_object* v___x_1472_; 
v_val_1468_ = lean_ctor_get(v_d_1451_, 0);
lean_inc_ref(v_val_1468_);
lean_dec(v_d_1451_);
v_toConstantVal_1469_ = lean_ctor_get(v_val_1468_, 0);
lean_inc_ref(v_toConstantVal_1469_);
v_value_1470_ = lean_ctor_get(v_val_1468_, 1);
lean_inc_ref(v_value_1470_);
lean_dec_ref(v_val_1468_);
v_type_1471_ = lean_ctor_get(v_toConstantVal_1469_, 2);
lean_inc_ref(v_type_1471_);
lean_dec_ref(v_toConstantVal_1469_);
lean_inc_ref(v_fn_1450_);
v___x_1472_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1471_, v_fn_1450_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v___x_1473_; 
lean_dec_ref_known(v___x_1472_, 1);
v___x_1473_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1470_, v_fn_1450_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
return v___x_1473_;
}
else
{
lean_dec_ref(v_value_1470_);
lean_dec_ref(v_fn_1450_);
return v___x_1472_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1474_, lean_object* v_d_1475_, lean_object* v_a_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1474_, v_d_1475_, v_a_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_);
lean_dec(v___y_1481_);
lean_dec_ref(v___y_1480_);
lean_dec(v___y_1479_);
lean_dec_ref(v___y_1478_);
lean_dec(v___y_1477_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1484_, lean_object* v_fn_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1492_ = lean_box(0);
v___x_1493_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1485_, v_decl_1484_, v___x_1492_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1494_, lean_object* v_fn_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
lean_object* v_res_1502_; 
v_res_1502_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1494_, v_fn_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___y_1500_);
lean_dec_ref(v___y_1499_);
lean_dec(v___y_1498_);
lean_dec_ref(v___y_1497_);
lean_dec(v___y_1496_);
return v_res_1502_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1503_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1504_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1504_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1506_ = lean_box(1);
v___x_1507_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1508_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1509_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1509_, 0, v___x_1508_);
lean_ctor_set(v___x_1509_, 1, v___x_1507_);
lean_ctor_set(v___x_1509_, 2, v___x_1506_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1512_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1513_ = lean_unsigned_to_nat(0u);
v___x_1514_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
lean_ctor_set(v___x_1514_, 1, v___x_1513_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
lean_ctor_set(v___x_1514_, 3, v___x_1513_);
lean_ctor_set(v___x_1514_, 4, v___x_1512_);
lean_ctor_set(v___x_1514_, 5, v___x_1512_);
lean_ctor_set(v___x_1514_, 6, v___x_1512_);
lean_ctor_set(v___x_1514_, 7, v___x_1512_);
lean_ctor_set(v___x_1514_, 8, v___x_1512_);
lean_ctor_set(v___x_1514_, 9, v___x_1512_);
lean_ctor_set(v___x_1514_, 10, v___x_1512_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1516_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1516_, 0, v___x_1515_);
lean_ctor_set(v___x_1516_, 1, v___x_1515_);
lean_ctor_set(v___x_1516_, 2, v___x_1515_);
lean_ctor_set(v___x_1516_, 3, v___x_1515_);
lean_ctor_set(v___x_1516_, 4, v___x_1515_);
lean_ctor_set(v___x_1516_, 5, v___x_1515_);
return v___x_1516_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1517_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1518_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
lean_ctor_set(v___x_1518_, 2, v___x_1517_);
lean_ctor_set(v___x_1518_, 3, v___x_1517_);
lean_ctor_set(v___x_1518_, 4, v___x_1517_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1519_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1520_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1521_ = lean_box(1);
v___x_1522_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1523_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1524_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1522_);
lean_ctor_set(v___x_1524_, 2, v___x_1521_);
lean_ctor_set(v___x_1524_, 3, v___x_1520_);
lean_ctor_set(v___x_1524_, 4, v___x_1519_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1531_ = l_Lean_stringToMessageData(v___x_1530_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1534_ = l_Lean_stringToMessageData(v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1536_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1537_ = l_Lean_stringToMessageData(v___x_1536_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1538_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1539_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1540_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_){
_start:
{
lean_object* v_options_1548_; lean_object* v___x_1549_; uint8_t v___x_1550_; 
v_options_1548_ = lean_ctor_get(v_a_1545_, 1);
v___x_1549_ = l_Lean_warn_sorry;
v___x_1550_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
lean_dec(v_decl_1544_);
v___x_1551_ = lean_box(0);
v___x_1552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1552_, 0, v___x_1551_);
return v___x_1552_;
}
else
{
lean_object* v___x_1553_; lean_object* v_messages_1557_; uint8_t v___x_1558_; 
v___x_1553_ = lean_st_ref_get(v_a_1546_);
v_messages_1557_ = lean_ctor_get(v___x_1553_, 6);
lean_inc_ref(v_messages_1557_);
lean_dec(v___x_1553_);
v___x_1558_ = l_Lean_MessageLog_hasErrors(v_messages_1557_);
lean_dec_ref(v_messages_1557_);
if (v___x_1558_ == 0)
{
if (v___x_1550_ == 0)
{
lean_dec(v_decl_1544_);
goto v___jp_1554_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_Declaration_hasSorry(v_decl_1544_);
if (v___x_1559_ == 0)
{
lean_dec(v_decl_1544_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1560_; uint8_t v___x_1561_; uint8_t v___x_1562_; uint8_t v___x_1563_; lean_object* v___x_1564_; uint64_t v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___f_1575_; lean_object* v___x_1576_; 
v___x_1560_ = lean_box(1);
v___x_1561_ = 1;
v___x_1562_ = 0;
v___x_1563_ = 2;
v___x_1564_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1564_, 0, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 2, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 3, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 4, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 5, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 6, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 7, v___x_1558_);
lean_ctor_set_uint8(v___x_1564_, 8, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 9, v___x_1561_);
lean_ctor_set_uint8(v___x_1564_, 10, v___x_1562_);
lean_ctor_set_uint8(v___x_1564_, 11, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 12, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 13, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 14, v___x_1563_);
lean_ctor_set_uint8(v___x_1564_, 15, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 16, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 17, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 18, v___x_1559_);
lean_ctor_set_uint8(v___x_1564_, 19, v___x_1558_);
v___x_1565_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1564_);
v___x_1566_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1566_, 0, v___x_1564_);
lean_ctor_set_uint64(v___x_1566_, sizeof(void*)*1, v___x_1565_);
v___x_1567_ = lean_unsigned_to_nat(0u);
v___x_1568_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1569_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1570_ = lean_box(0);
v___x_1571_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1571_, 0, v___x_1566_);
lean_ctor_set(v___x_1571_, 1, v___x_1560_);
lean_ctor_set(v___x_1571_, 2, v___x_1568_);
lean_ctor_set(v___x_1571_, 3, v___x_1569_);
lean_ctor_set(v___x_1571_, 4, v___x_1570_);
lean_ctor_set(v___x_1571_, 5, v___x_1567_);
lean_ctor_set(v___x_1571_, 6, v___x_1570_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*7, v___x_1558_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*7 + 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*7 + 2, v___x_1558_);
lean_ctor_set_uint8(v___x_1571_, sizeof(void*)*7 + 3, v___x_1550_);
v___x_1572_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1573_ = lean_st_mk_ref(v___x_1572_);
v___x_1574_ = lean_st_mk_ref(v___x_1569_);
v___f_1575_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1576_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1544_, v___f_1575_, v___x_1574_, v___x_1571_, v___x_1573_, v_a_1545_, v_a_1546_);
lean_dec_ref_known(v___x_1571_, 7);
if (lean_obj_tag(v___x_1576_) == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v_val_1580_; lean_object* v___x_1602_; size_t v_sz_1603_; size_t v___x_1604_; lean_object* v___x_1605_; lean_object* v_fst_1606_; 
lean_dec_ref_known(v___x_1576_, 1);
v___x_1577_ = lean_st_ref_get(v___x_1574_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_st_ref_get(v___x_1573_);
lean_dec(v___x_1573_);
lean_dec(v___x_1578_);
v___x_1602_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1603_ = lean_array_size(v___x_1577_);
v___x_1604_ = ((size_t)0ULL);
v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1577_, v_sz_1603_, v___x_1604_, v___x_1602_);
v_fst_1606_ = lean_ctor_get(v___x_1605_, 0);
lean_inc(v_fst_1606_);
lean_dec_ref(v___x_1605_);
if (lean_obj_tag(v_fst_1606_) == 0)
{
goto v___jp_1596_;
}
else
{
lean_object* v_val_1607_; 
v_val_1607_ = lean_ctor_get(v_fst_1606_, 0);
lean_inc(v_val_1607_);
lean_dec_ref_known(v_fst_1606_, 1);
if (lean_obj_tag(v_val_1607_) == 0)
{
goto v___jp_1596_;
}
else
{
lean_object* v_val_1608_; 
lean_dec(v___x_1577_);
v_val_1608_ = lean_ctor_get(v_val_1607_, 0);
lean_inc(v_val_1608_);
lean_dec_ref_known(v_val_1607_, 1);
v_val_1580_ = v_val_1608_;
goto v___jp_1579_;
}
}
v___jp_1579_:
{
lean_object* v_snd_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1594_; 
v_snd_1581_ = lean_ctor_get(v_val_1580_, 1);
v_isSharedCheck_1594_ = !lean_is_exclusive(v_val_1580_);
if (v_isSharedCheck_1594_ == 0)
{
lean_object* v_unused_1595_; 
v_unused_1595_ = lean_ctor_get(v_val_1580_, 0);
lean_dec(v_unused_1595_);
v___x_1583_ = v_val_1580_;
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
else
{
lean_inc(v_snd_1581_);
lean_dec(v_val_1580_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1594_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1586_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1584_ == 0)
{
lean_ctor_set_tag(v___x_1583_, 7);
lean_ctor_set(v___x_1583_, 0, v___x_1586_);
v___x_1588_ = v___x_1583_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v___x_1586_);
lean_ctor_set(v_reuseFailAlloc_1593_, 1, v_snd_1581_);
v___x_1588_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1589_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1588_);
lean_ctor_set(v___x_1590_, 1, v___x_1589_);
v___x_1591_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1585_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v___x_1592_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1591_, v_a_1545_, v_a_1546_);
return v___x_1592_;
}
}
}
v___jp_1596_:
{
lean_object* v___x_1597_; uint8_t v___x_1598_; 
v___x_1597_ = lean_array_get_size(v___x_1577_);
v___x_1598_ = lean_nat_dec_lt(v___x_1567_, v___x_1597_);
if (v___x_1598_ == 0)
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
lean_dec(v___x_1577_);
v___x_1599_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1600_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1599_, v_a_1545_, v_a_1546_);
return v___x_1600_;
}
else
{
lean_object* v___x_1601_; 
v___x_1601_ = lean_array_fget(v___x_1577_, v___x_1567_);
lean_dec(v___x_1577_);
v_val_1580_ = v___x_1601_;
goto v___jp_1579_;
}
}
}
else
{
lean_dec(v___x_1574_);
lean_dec(v___x_1573_);
return v___x_1576_;
}
}
}
}
else
{
lean_dec(v_decl_1544_);
goto v___jp_1554_;
}
v___jp_1554_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_box(0);
v___x_1556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1556_, 0, v___x_1555_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1609_, lean_object* v_a_1610_, lean_object* v_a_1611_, lean_object* v_a_1612_){
_start:
{
lean_object* v_res_1613_; 
v_res_1613_ = l_Lean_warnIfUsesSorry(v_decl_1609_, v_a_1610_, v_a_1611_);
lean_dec(v_a_1611_);
lean_dec_ref(v_a_1610_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1614_, lean_object* v_m_1615_, lean_object* v_a_1616_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1615_, v_a_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1618_, lean_object* v_m_1619_, lean_object* v_a_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1618_, v_m_1619_, v_a_1620_);
lean_dec_ref(v_a_1620_);
lean_dec_ref(v_m_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1622_, lean_object* v_m_1623_, lean_object* v_a_1624_, lean_object* v_b_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1623_, v_a_1624_, v_b_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1627_, lean_object* v_a_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1631_, lean_object* v_a_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v_res_1634_; 
v_res_1634_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1631_, v_a_1632_, v_x_1633_);
lean_dec(v_x_1633_);
lean_dec_ref(v_a_1632_);
return v_res_1634_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1635_, lean_object* v_a_1636_, lean_object* v_x_1637_){
_start:
{
uint8_t v___x_1638_; 
v___x_1638_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1639_, lean_object* v_a_1640_, lean_object* v_x_1641_){
_start:
{
uint8_t v_res_1642_; lean_object* v_r_1643_; 
v_res_1642_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1639_, v_a_1640_, v_x_1641_);
lean_dec(v_x_1641_);
lean_dec_ref(v_a_1640_);
v_r_1643_ = lean_box(v_res_1642_);
return v_r_1643_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1644_, lean_object* v_data_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_b_1649_, lean_object* v_x_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1648_, v_b_1649_, v_x_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1652_, lean_object* v_name_1653_, uint8_t v_bi_1654_, lean_object* v_type_1655_, lean_object* v_k_1656_, uint8_t v_kind_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1653_, v_bi_1654_, v_type_1655_, v_k_1656_, v_kind_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1666_, lean_object* v_name_1667_, lean_object* v_bi_1668_, lean_object* v_type_1669_, lean_object* v_k_1670_, lean_object* v_kind_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_bi_boxed_1679_; uint8_t v_kind_boxed_1680_; lean_object* v_res_1681_; 
v_bi_boxed_1679_ = lean_unbox(v_bi_1668_);
v_kind_boxed_1680_ = lean_unbox(v_kind_1671_);
v_res_1681_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1666_, v_name_1667_, v_bi_boxed_1679_, v_type_1669_, v_k_1670_, v_kind_boxed_1680_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec(v___y_1672_);
return v_res_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1682_, lean_object* v_name_1683_, lean_object* v_type_1684_, lean_object* v_val_1685_, lean_object* v_k_1686_, uint8_t v_nondep_1687_, uint8_t v_kind_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1683_, v_type_1684_, v_val_1685_, v_k_1686_, v_nondep_1687_, v_kind_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_);
return v___x_1696_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1697_, lean_object* v_name_1698_, lean_object* v_type_1699_, lean_object* v_val_1700_, lean_object* v_k_1701_, lean_object* v_nondep_1702_, lean_object* v_kind_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
uint8_t v_nondep_boxed_1711_; uint8_t v_kind_boxed_1712_; lean_object* v_res_1713_; 
v_nondep_boxed_1711_ = lean_unbox(v_nondep_1702_);
v_kind_boxed_1712_ = lean_unbox(v_kind_1703_);
v_res_1713_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1697_, v_name_1698_, v_type_1699_, v_val_1700_, v_k_1701_, v_nondep_boxed_1711_, v_kind_boxed_1712_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_);
lean_dec(v___y_1709_);
lean_dec_ref(v___y_1708_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec(v___y_1704_);
return v_res_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1714_, lean_object* v_i_1715_, lean_object* v_source_1716_, lean_object* v_target_1717_){
_start:
{
lean_object* v___x_1718_; 
v___x_1718_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1715_, v_source_1716_, v_target_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1719_, lean_object* v_x_1720_, lean_object* v_x_1721_){
_start:
{
lean_object* v___x_1722_; 
v___x_1722_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1720_, v_x_1721_);
return v___x_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1772_; uint8_t v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1772_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1773_ = 0;
v___x_1774_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1775_ = l_Lean_registerTraceClass(v___x_1772_, v___x_1773_, v___x_1774_);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1776_){
_start:
{
lean_object* v_res_1777_; 
v_res_1777_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1777_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1778_, lean_object* v___y_1779_){
_start:
{
lean_object* v___x_1781_; lean_object* v_nextMacroScope_1782_; lean_object* v_ngen_1783_; lean_object* v_auxDeclNGen_1784_; lean_object* v_traceState_1785_; lean_object* v_messages_1786_; lean_object* v_infoState_1787_; lean_object* v_snapshotTasks_1788_; lean_object* v___x_1790_; uint8_t v_isShared_1791_; uint8_t v_isSharedCheck_1799_; 
v___x_1781_ = lean_st_ref_take(v___y_1779_);
v_nextMacroScope_1782_ = lean_ctor_get(v___x_1781_, 1);
v_ngen_1783_ = lean_ctor_get(v___x_1781_, 2);
v_auxDeclNGen_1784_ = lean_ctor_get(v___x_1781_, 3);
v_traceState_1785_ = lean_ctor_get(v___x_1781_, 4);
v_messages_1786_ = lean_ctor_get(v___x_1781_, 6);
v_infoState_1787_ = lean_ctor_get(v___x_1781_, 7);
v_snapshotTasks_1788_ = lean_ctor_get(v___x_1781_, 8);
v_isSharedCheck_1799_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1799_ == 0)
{
lean_object* v_unused_1800_; lean_object* v_unused_1801_; 
v_unused_1800_ = lean_ctor_get(v___x_1781_, 5);
lean_dec(v_unused_1800_);
v_unused_1801_ = lean_ctor_get(v___x_1781_, 0);
lean_dec(v_unused_1801_);
v___x_1790_ = v___x_1781_;
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
else
{
lean_inc(v_snapshotTasks_1788_);
lean_inc(v_infoState_1787_);
lean_inc(v_messages_1786_);
lean_inc(v_traceState_1785_);
lean_inc(v_auxDeclNGen_1784_);
lean_inc(v_ngen_1783_);
lean_inc(v_nextMacroScope_1782_);
lean_dec(v___x_1781_);
v___x_1790_ = lean_box(0);
v_isShared_1791_ = v_isSharedCheck_1799_;
goto v_resetjp_1789_;
}
v_resetjp_1789_:
{
lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1792_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1791_ == 0)
{
lean_ctor_set(v___x_1790_, 5, v___x_1792_);
lean_ctor_set(v___x_1790_, 0, v_env_1778_);
v___x_1794_ = v___x_1790_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1798_; 
v_reuseFailAlloc_1798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1798_, 0, v_env_1778_);
lean_ctor_set(v_reuseFailAlloc_1798_, 1, v_nextMacroScope_1782_);
lean_ctor_set(v_reuseFailAlloc_1798_, 2, v_ngen_1783_);
lean_ctor_set(v_reuseFailAlloc_1798_, 3, v_auxDeclNGen_1784_);
lean_ctor_set(v_reuseFailAlloc_1798_, 4, v_traceState_1785_);
lean_ctor_set(v_reuseFailAlloc_1798_, 5, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1798_, 6, v_messages_1786_);
lean_ctor_set(v_reuseFailAlloc_1798_, 7, v_infoState_1787_);
lean_ctor_set(v_reuseFailAlloc_1798_, 8, v_snapshotTasks_1788_);
v___x_1794_ = v_reuseFailAlloc_1798_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1795_ = lean_st_ref_put(v___y_1779_, v___x_1794_);
v___x_1796_ = lean_box(0);
v___x_1797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1796_);
return v___x_1797_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
lean_object* v_res_1805_; 
v_res_1805_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1802_, v___y_1803_);
lean_dec(v___y_1803_);
return v_res_1805_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1806_, lean_object* v___y_1807_, lean_object* v___y_1808_){
_start:
{
lean_object* v___x_1810_; 
v___x_1810_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1806_, v___y_1808_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v_res_1815_; 
v_res_1815_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1811_, v___y_1812_, v___y_1813_);
lean_dec(v___y_1813_);
lean_dec_ref(v___y_1812_);
return v_res_1815_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1816_ = lean_box(0);
v___x_1817_ = l_Lean_interruptExceptionId;
v___x_1818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1818_, 0, v___x_1817_);
lean_ctor_set(v___x_1818_, 1, v___x_1816_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1820_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1821_, 0, v___x_1820_);
return v___x_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1822_){
_start:
{
lean_object* v_res_1823_; 
v_res_1823_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_){
_start:
{
lean_object* v_ref_1828_; lean_object* v___x_1829_; lean_object* v_a_1830_; lean_object* v___x_1832_; uint8_t v_isShared_1833_; uint8_t v_isSharedCheck_1838_; 
v_ref_1828_ = lean_ctor_get(v___y_1825_, 4);
v___x_1829_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1824_, v___y_1825_, v___y_1826_);
v_a_1830_ = lean_ctor_get(v___x_1829_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1829_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1832_ = v___x_1829_;
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
else
{
lean_inc(v_a_1830_);
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v_isShared_1833_ = v_isSharedCheck_1838_;
goto v_resetjp_1831_;
}
v_resetjp_1831_:
{
lean_object* v___x_1834_; lean_object* v___x_1836_; 
lean_inc(v_ref_1828_);
v___x_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1834_, 0, v_ref_1828_);
lean_ctor_set(v___x_1834_, 1, v_a_1830_);
if (v_isShared_1833_ == 0)
{
lean_ctor_set_tag(v___x_1832_, 1);
lean_ctor_set(v___x_1832_, 0, v___x_1834_);
v___x_1836_ = v___x_1832_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v___x_1834_);
v___x_1836_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1835_;
}
v_reusejp_1835_:
{
return v___x_1836_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_res_1843_; 
v_res_1843_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1839_, v___y_1840_, v___y_1841_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
return v_res_1843_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
lean_object* v___y_1849_; lean_object* v___y_1850_; 
if (lean_obj_tag(v_ex_1844_) == 16)
{
lean_object* v___x_1854_; lean_object* v_a_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1862_; 
v___x_1854_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1862_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1862_ == 0)
{
v___x_1857_ = v___x_1854_;
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_a_1855_);
lean_dec(v___x_1854_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1862_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1860_; 
if (v_isShared_1858_ == 0)
{
v___x_1860_ = v___x_1857_;
goto v_reusejp_1859_;
}
else
{
lean_object* v_reuseFailAlloc_1861_; 
v_reuseFailAlloc_1861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1861_, 0, v_a_1855_);
v___x_1860_ = v_reuseFailAlloc_1861_;
goto v_reusejp_1859_;
}
v_reusejp_1859_:
{
return v___x_1860_;
}
}
}
else
{
v___y_1849_ = v___y_1845_;
v___y_1850_ = v___y_1846_;
goto v___jp_1848_;
}
v___jp_1848_:
{
lean_object* v_options_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_options_1851_ = lean_ctor_get(v___y_1849_, 1);
lean_inc_ref(v_options_1851_);
v___x_1852_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1844_, v_options_1851_);
v___x_1853_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1852_, v___y_1849_, v___y_1850_);
return v___x_1853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1863_, v___y_1864_, v___y_1865_);
lean_dec(v___y_1865_);
lean_dec_ref(v___y_1864_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_){
_start:
{
if (lean_obj_tag(v_x_1868_) == 0)
{
lean_object* v_a_1872_; lean_object* v___x_1873_; 
v_a_1872_ = lean_ctor_get(v_x_1868_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v_x_1868_, 1);
v___x_1873_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1872_, v___y_1869_, v___y_1870_);
return v___x_1873_;
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
v_a_1874_ = lean_ctor_get(v_x_1868_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v_x_1868_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v_x_1868_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v_x_1868_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
lean_ctor_set_tag(v___x_1876_, 0);
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_, lean_object* v___y_1885_){
_start:
{
lean_object* v_res_1886_; 
v_res_1886_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1882_, v___y_1883_, v___y_1884_);
lean_dec(v___y_1884_);
lean_dec_ref(v___y_1883_);
return v_res_1886_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(1u);
v___x_1888_ = l_Lean_Level_ofNat(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_box(0);
v___x_1890_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v___x_1889_);
return v___x_1891_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1899_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1900_ = l_Lean_mkConst(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Lean_Level_ofNat(v___x_1901_);
return v___x_1902_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1903_; lean_object* v___x_1904_; 
v___x_1903_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1904_ = l_Lean_mkSort(v___x_1903_);
return v___x_1904_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = lean_box(0);
v___x_1911_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1912_ = l_Lean_mkConst(v___x_1911_, v___x_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1913_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1914_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1915_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1916_ = l_Lean_mkAppB(v___x_1915_, v___x_1914_, v___x_1913_);
return v___x_1916_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1922_, lean_object* v_b_1923_, lean_object* v___y_1924_, lean_object* v___y_1925_){
_start:
{
if (lean_obj_tag(v_as_x27_1922_) == 0)
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1927_, 0, v_b_1923_);
return v___x_1927_;
}
else
{
lean_object* v_head_1928_; lean_object* v_tail_1929_; lean_object* v___x_1930_; lean_object* v_toCold_1931_; lean_object* v_env_1932_; lean_object* v_options_1933_; lean_object* v_cancelTk_x3f_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___y_1938_; uint8_t v___y_1939_; lean_object* v_a_1943_; lean_object* v___x_1946_; lean_object* v___x_1947_; uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec_ref(v_b_1923_);
v_head_1928_ = lean_ctor_get(v_as_x27_1922_, 0);
v_tail_1929_ = lean_ctor_get(v_as_x27_1922_, 1);
v___x_1930_ = lean_st_ref_get(v___y_1925_);
v_toCold_1931_ = lean_ctor_get(v___y_1924_, 0);
v_env_1932_ = lean_ctor_get(v___x_1930_, 0);
lean_inc_ref(v_env_1932_);
lean_dec(v___x_1930_);
v_options_1933_ = lean_ctor_get(v___y_1924_, 1);
v_cancelTk_x3f_1934_ = lean_ctor_get(v_toCold_1931_, 3);
v___x_1935_ = lean_box(0);
v___x_1936_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1946_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1928_);
v___x_1947_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1947_, 0, v_head_1928_);
lean_ctor_set(v___x_1947_, 1, v___x_1935_);
lean_ctor_set(v___x_1947_, 2, v___x_1946_);
v___x_1948_ = 0;
v___x_1949_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1949_, 0, v___x_1947_);
lean_ctor_set_uint8(v___x_1949_, sizeof(void*)*1, v___x_1948_);
v___x_1950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1932_, v_options_1933_, v___x_1950_, v_cancelTk_x3f_1934_);
lean_dec_ref_known(v___x_1950_, 1);
v___x_1952_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1951_, v___y_1924_, v___y_1925_);
if (lean_obj_tag(v___x_1952_) == 0)
{
lean_object* v_a_1953_; lean_object* v___x_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1962_; 
v_a_1953_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1953_);
lean_dec_ref_known(v___x_1952_, 1);
v___x_1954_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1953_, v___y_1925_);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1954_);
if (v_isSharedCheck_1962_ == 0)
{
lean_object* v_unused_1963_; 
v_unused_1963_ = lean_ctor_get(v___x_1954_, 0);
lean_dec(v_unused_1963_);
v___x_1956_ = v___x_1954_;
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
else
{
lean_dec(v___x_1954_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1962_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1958_; lean_object* v___x_1960_; 
v___x_1958_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1957_ == 0)
{
lean_ctor_set(v___x_1956_, 0, v___x_1958_);
v___x_1960_ = v___x_1956_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v___x_1958_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
else
{
lean_object* v_a_1964_; 
v_a_1964_ = lean_ctor_get(v___x_1952_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1952_, 1);
v_a_1943_ = v_a_1964_;
goto v___jp_1942_;
}
v___jp_1937_:
{
if (v___y_1939_ == 0)
{
lean_dec_ref(v___y_1938_);
v_as_x27_1922_ = v_tail_1929_;
v_b_1923_ = v___x_1936_;
goto _start;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1941_, 0, v___y_1938_);
return v___x_1941_;
}
}
v___jp_1942_:
{
uint8_t v___x_1944_; 
v___x_1944_ = l_Lean_Exception_isInterrupt(v_a_1943_);
if (v___x_1944_ == 0)
{
uint8_t v___x_1945_; 
lean_inc_ref(v_a_1943_);
v___x_1945_ = l_Lean_Exception_isRuntime(v_a_1943_);
v___y_1938_ = v_a_1943_;
v___y_1939_ = v___x_1945_;
goto v___jp_1937_;
}
else
{
v___y_1938_ = v_a_1943_;
v___y_1939_ = v___x_1944_;
goto v___jp_1937_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1965_, lean_object* v_b_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_res_1970_; 
v_res_1970_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1965_, v_b_1966_, v___y_1967_, v___y_1968_);
lean_dec(v___y_1968_);
lean_dec_ref(v___y_1967_);
lean_dec(v_as_x27_1965_);
return v_res_1970_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_2004_; uint8_t v___y_2005_; lean_object* v_a_2008_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v_a_2016_; 
switch(lean_obj_tag(v_decl_1971_))
{
case 1:
{
lean_object* v_val_2019_; lean_object* v___x_2020_; lean_object* v_toCold_2021_; lean_object* v_toConstantVal_2022_; lean_object* v_env_2023_; lean_object* v_options_2024_; lean_object* v_cancelTk_x3f_2025_; uint8_t v___x_2026_; lean_object* v___x_2027_; lean_object* v_fallbackDecl_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_val_2019_ = lean_ctor_get(v_decl_1971_, 0);
v___x_2020_ = lean_st_ref_get(v_a_1973_);
v_toCold_2021_ = lean_ctor_get(v_a_1972_, 0);
v_toConstantVal_2022_ = lean_ctor_get(v_val_2019_, 0);
v_env_2023_ = lean_ctor_get(v___x_2020_, 0);
lean_inc_ref(v_env_2023_);
lean_dec(v___x_2020_);
v_options_2024_ = lean_ctor_get(v_a_1972_, 1);
v_cancelTk_x3f_2025_ = lean_ctor_get(v_toCold_2021_, 3);
v___x_2026_ = 0;
lean_inc_ref(v_toConstantVal_2022_);
v___x_2027_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2027_, 0, v_toConstantVal_2022_);
lean_ctor_set_uint8(v___x_2027_, sizeof(void*)*1, v___x_2026_);
v_fallbackDecl_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2028_, 0, v___x_2027_);
v___x_2029_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2023_, v_options_2024_, v_fallbackDecl_2028_, v_cancelTk_x3f_2025_);
lean_dec_ref_known(v_fallbackDecl_2028_, 1);
v___x_2030_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2029_, v_a_1972_, v_a_1973_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2040_; 
lean_dec_ref_known(v_decl_1971_, 1);
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2031_, v_a_1973_);
v_isSharedCheck_2040_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2040_ == 0)
{
lean_object* v_unused_2041_; 
v_unused_2041_ = lean_ctor_get(v___x_2032_, 0);
lean_dec(v_unused_2041_);
v___x_2034_ = v___x_2032_;
v_isShared_2035_ = v_isSharedCheck_2040_;
goto v_resetjp_2033_;
}
else
{
lean_dec(v___x_2032_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2040_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
v___x_2036_ = lean_box(0);
if (v_isShared_2035_ == 0)
{
lean_ctor_set(v___x_2034_, 0, v___x_2036_);
v___x_2038_ = v___x_2034_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
return v___x_2038_;
}
}
}
else
{
lean_object* v_a_2042_; 
v_a_2042_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2030_, 1);
v_a_2008_ = v_a_2042_;
goto v___jp_2007_;
}
}
case 2:
{
lean_object* v_val_2043_; lean_object* v___x_2044_; lean_object* v_toCold_2045_; lean_object* v_toConstantVal_2046_; lean_object* v_env_2047_; lean_object* v_options_2048_; lean_object* v_cancelTk_x3f_2049_; uint8_t v___x_2050_; lean_object* v___x_2051_; lean_object* v_fallbackDecl_2052_; lean_object* v___x_2053_; lean_object* v___x_2054_; 
v_val_2043_ = lean_ctor_get(v_decl_1971_, 0);
v___x_2044_ = lean_st_ref_get(v_a_1973_);
v_toCold_2045_ = lean_ctor_get(v_a_1972_, 0);
v_toConstantVal_2046_ = lean_ctor_get(v_val_2043_, 0);
v_env_2047_ = lean_ctor_get(v___x_2044_, 0);
lean_inc_ref(v_env_2047_);
lean_dec(v___x_2044_);
v_options_2048_ = lean_ctor_get(v_a_1972_, 1);
v_cancelTk_x3f_2049_ = lean_ctor_get(v_toCold_2045_, 3);
v___x_2050_ = 0;
lean_inc_ref(v_toConstantVal_2046_);
v___x_2051_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2051_, 0, v_toConstantVal_2046_);
lean_ctor_set_uint8(v___x_2051_, sizeof(void*)*1, v___x_2050_);
v_fallbackDecl_2052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2052_, 0, v___x_2051_);
v___x_2053_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2047_, v_options_2048_, v_fallbackDecl_2052_, v_cancelTk_x3f_2049_);
lean_dec_ref_known(v_fallbackDecl_2052_, 1);
v___x_2054_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2053_, v_a_1972_, v_a_1973_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_object* v_a_2055_; lean_object* v___x_2056_; lean_object* v___x_2058_; uint8_t v_isShared_2059_; uint8_t v_isSharedCheck_2064_; 
lean_dec_ref_known(v_decl_1971_, 1);
v_a_2055_ = lean_ctor_get(v___x_2054_, 0);
lean_inc(v_a_2055_);
lean_dec_ref_known(v___x_2054_, 1);
v___x_2056_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2055_, v_a_1973_);
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
v_a_2016_ = v_a_2066_;
goto v___jp_2015_;
}
}
default: 
{
v___y_1976_ = v_a_1972_;
v___y_1977_ = v_a_1973_;
goto v___jp_1975_;
}
}
v___jp_1975_:
{
lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1978_ = l_Lean_Declaration_getNames(v_decl_1971_);
v___x_1979_ = lean_box(0);
v___x_1980_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1981_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1978_, v___x_1980_, v___y_1976_, v___y_1977_);
lean_dec(v___x_1978_);
if (lean_obj_tag(v___x_1981_) == 0)
{
lean_object* v_a_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_1994_; 
v_a_1982_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_1994_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_1994_ == 0)
{
v___x_1984_ = v___x_1981_;
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_a_1982_);
lean_dec(v___x_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_1994_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
lean_object* v_fst_1986_; 
v_fst_1986_ = lean_ctor_get(v_a_1982_, 0);
lean_inc(v_fst_1986_);
lean_dec(v_a_1982_);
if (lean_obj_tag(v_fst_1986_) == 0)
{
lean_object* v___x_1988_; 
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1979_);
v___x_1988_ = v___x_1984_;
goto v_reusejp_1987_;
}
else
{
lean_object* v_reuseFailAlloc_1989_; 
v_reuseFailAlloc_1989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1989_, 0, v___x_1979_);
v___x_1988_ = v_reuseFailAlloc_1989_;
goto v_reusejp_1987_;
}
v_reusejp_1987_:
{
return v___x_1988_;
}
}
else
{
lean_object* v_val_1990_; lean_object* v___x_1992_; 
v_val_1990_ = lean_ctor_get(v_fst_1986_, 0);
lean_inc(v_val_1990_);
lean_dec_ref_known(v_fst_1986_, 1);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v_val_1990_);
v___x_1992_ = v___x_1984_;
goto v_reusejp_1991_;
}
else
{
lean_object* v_reuseFailAlloc_1993_; 
v_reuseFailAlloc_1993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1993_, 0, v_val_1990_);
v___x_1992_ = v_reuseFailAlloc_1993_;
goto v_reusejp_1991_;
}
v_reusejp_1991_:
{
return v___x_1992_;
}
}
}
}
else
{
lean_object* v_a_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2002_; 
v_a_1995_ = lean_ctor_get(v___x_1981_, 0);
v_isSharedCheck_2002_ = !lean_is_exclusive(v___x_1981_);
if (v_isSharedCheck_2002_ == 0)
{
v___x_1997_ = v___x_1981_;
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_a_1995_);
lean_dec(v___x_1981_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2002_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v___x_2000_; 
if (v_isShared_1998_ == 0)
{
v___x_2000_ = v___x_1997_;
goto v_reusejp_1999_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_a_1995_);
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
v___jp_2003_:
{
if (v___y_2005_ == 0)
{
lean_dec_ref(v___y_2004_);
v___y_1976_ = v_a_1972_;
v___y_1977_ = v_a_1973_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2006_; 
lean_dec(v_decl_1971_);
v___x_2006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2006_, 0, v___y_2004_);
return v___x_2006_;
}
}
v___jp_2007_:
{
uint8_t v___x_2009_; 
v___x_2009_ = l_Lean_Exception_isInterrupt(v_a_2008_);
if (v___x_2009_ == 0)
{
uint8_t v___x_2010_; 
lean_inc_ref(v_a_2008_);
v___x_2010_ = l_Lean_Exception_isRuntime(v_a_2008_);
v___y_2004_ = v_a_2008_;
v___y_2005_ = v___x_2010_;
goto v___jp_2003_;
}
else
{
v___y_2004_ = v_a_2008_;
v___y_2005_ = v___x_2009_;
goto v___jp_2003_;
}
}
v___jp_2011_:
{
if (v___y_2013_ == 0)
{
lean_dec_ref(v___y_2012_);
v___y_1976_ = v_a_1972_;
v___y_1977_ = v_a_1973_;
goto v___jp_1975_;
}
else
{
lean_object* v___x_2014_; 
lean_dec(v_decl_1971_);
v___x_2014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2014_, 0, v___y_2012_);
return v___x_2014_;
}
}
v___jp_2015_:
{
uint8_t v___x_2017_; 
v___x_2017_ = l_Lean_Exception_isInterrupt(v_a_2016_);
if (v___x_2017_ == 0)
{
uint8_t v___x_2018_; 
lean_inc_ref(v_a_2016_);
v___x_2018_ = l_Lean_Exception_isRuntime(v_a_2016_);
v___y_2012_ = v_a_2016_;
v___y_2013_ = v___x_2018_;
goto v___jp_2011_;
}
else
{
v___y_2012_ = v_a_2016_;
v___y_2013_ = v___x_2017_;
goto v___jp_2011_;
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
v___x_2170_ = lean_st_ref_put(v___y_2143_, v___x_2169_);
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
lean_object* v_toCold_2283_; lean_object* v_options_2284_; lean_object* v_currRecDepth_2285_; lean_object* v_maxRecDepth_2286_; lean_object* v_ref_2287_; lean_object* v_currNamespace_2288_; lean_object* v_openDecls_2289_; lean_object* v_initHeartbeats_2290_; lean_object* v_maxHeartbeats_2291_; lean_object* v_currMacroScope_2292_; uint8_t v_diag_2293_; uint8_t v_suppressElabErrors_2294_; lean_object* v___x_2295_; lean_object* v_traceState_2296_; lean_object* v_traces_2297_; lean_object* v_ref_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; size_t v_sz_2301_; size_t v___x_2302_; lean_object* v___x_2303_; lean_object* v_msg_2304_; lean_object* v___x_2305_; lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2343_; 
v_toCold_2283_ = lean_ctor_get(v___y_2280_, 0);
v_options_2284_ = lean_ctor_get(v___y_2280_, 1);
v_currRecDepth_2285_ = lean_ctor_get(v___y_2280_, 2);
v_maxRecDepth_2286_ = lean_ctor_get(v___y_2280_, 3);
v_ref_2287_ = lean_ctor_get(v___y_2280_, 4);
v_currNamespace_2288_ = lean_ctor_get(v___y_2280_, 5);
v_openDecls_2289_ = lean_ctor_get(v___y_2280_, 6);
v_initHeartbeats_2290_ = lean_ctor_get(v___y_2280_, 7);
v_maxHeartbeats_2291_ = lean_ctor_get(v___y_2280_, 8);
v_currMacroScope_2292_ = lean_ctor_get(v___y_2280_, 9);
v_diag_2293_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*10);
v_suppressElabErrors_2294_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*10 + 1);
v___x_2295_ = lean_st_ref_get(v___y_2281_);
v_traceState_2296_ = lean_ctor_get(v___x_2295_, 4);
lean_inc_ref(v_traceState_2296_);
lean_dec(v___x_2295_);
v_traces_2297_ = lean_ctor_get(v_traceState_2296_, 0);
lean_inc_ref(v_traces_2297_);
lean_dec_ref(v_traceState_2296_);
v_ref_2298_ = l_Lean_replaceRef(v_ref_2278_, v_ref_2287_);
lean_inc(v_currMacroScope_2292_);
lean_inc(v_maxHeartbeats_2291_);
lean_inc(v_initHeartbeats_2290_);
lean_inc(v_openDecls_2289_);
lean_inc(v_currNamespace_2288_);
lean_inc(v_maxRecDepth_2286_);
lean_inc(v_currRecDepth_2285_);
lean_inc_ref(v_options_2284_);
lean_inc_ref(v_toCold_2283_);
v___x_2299_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_2299_, 0, v_toCold_2283_);
lean_ctor_set(v___x_2299_, 1, v_options_2284_);
lean_ctor_set(v___x_2299_, 2, v_currRecDepth_2285_);
lean_ctor_set(v___x_2299_, 3, v_maxRecDepth_2286_);
lean_ctor_set(v___x_2299_, 4, v_ref_2298_);
lean_ctor_set(v___x_2299_, 5, v_currNamespace_2288_);
lean_ctor_set(v___x_2299_, 6, v_openDecls_2289_);
lean_ctor_set(v___x_2299_, 7, v_initHeartbeats_2290_);
lean_ctor_set(v___x_2299_, 8, v_maxHeartbeats_2291_);
lean_ctor_set(v___x_2299_, 9, v_currMacroScope_2292_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*10, v_diag_2293_);
lean_ctor_set_uint8(v___x_2299_, sizeof(void*)*10 + 1, v_suppressElabErrors_2294_);
v___x_2300_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2297_);
lean_dec_ref(v_traces_2297_);
v_sz_2301_ = lean_array_size(v___x_2300_);
v___x_2302_ = ((size_t)0ULL);
v___x_2303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2301_, v___x_2302_, v___x_2300_);
v_msg_2304_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2304_, 0, v_data_2277_);
lean_ctor_set(v_msg_2304_, 1, v_msg_2279_);
lean_ctor_set(v_msg_2304_, 2, v___x_2303_);
v___x_2305_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2304_, v___x_2299_, v___y_2281_);
lean_dec_ref_known(v___x_2299_, 10);
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2343_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2343_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2343_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2343_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2310_; lean_object* v_traceState_2311_; lean_object* v_env_2312_; lean_object* v_nextMacroScope_2313_; lean_object* v_ngen_2314_; lean_object* v_auxDeclNGen_2315_; lean_object* v_cache_2316_; lean_object* v_messages_2317_; lean_object* v_infoState_2318_; lean_object* v_snapshotTasks_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2342_; 
v___x_2310_ = lean_st_ref_take(v___y_2281_);
v_traceState_2311_ = lean_ctor_get(v___x_2310_, 4);
v_env_2312_ = lean_ctor_get(v___x_2310_, 0);
v_nextMacroScope_2313_ = lean_ctor_get(v___x_2310_, 1);
v_ngen_2314_ = lean_ctor_get(v___x_2310_, 2);
v_auxDeclNGen_2315_ = lean_ctor_get(v___x_2310_, 3);
v_cache_2316_ = lean_ctor_get(v___x_2310_, 5);
v_messages_2317_ = lean_ctor_get(v___x_2310_, 6);
v_infoState_2318_ = lean_ctor_get(v___x_2310_, 7);
v_snapshotTasks_2319_ = lean_ctor_get(v___x_2310_, 8);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2310_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2321_ = v___x_2310_;
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_snapshotTasks_2319_);
lean_inc(v_infoState_2318_);
lean_inc(v_messages_2317_);
lean_inc(v_cache_2316_);
lean_inc(v_traceState_2311_);
lean_inc(v_auxDeclNGen_2315_);
lean_inc(v_ngen_2314_);
lean_inc(v_nextMacroScope_2313_);
lean_inc(v_env_2312_);
lean_dec(v___x_2310_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint64_t v_tid_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2340_; 
v_tid_2323_ = lean_ctor_get_uint64(v_traceState_2311_, sizeof(void*)*1);
v_isSharedCheck_2340_ = !lean_is_exclusive(v_traceState_2311_);
if (v_isSharedCheck_2340_ == 0)
{
lean_object* v_unused_2341_; 
v_unused_2341_ = lean_ctor_get(v_traceState_2311_, 0);
lean_dec(v_unused_2341_);
v___x_2325_ = v_traceState_2311_;
v_isShared_2326_ = v_isSharedCheck_2340_;
goto v_resetjp_2324_;
}
else
{
lean_dec(v_traceState_2311_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2340_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2330_; 
v___x_2327_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2327_, 0, v_ref_2278_);
lean_ctor_set(v___x_2327_, 1, v_a_2306_);
v___x_2328_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2276_, v___x_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 0, v___x_2328_);
v___x_2330_ = v___x_2325_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2328_);
lean_ctor_set_uint64(v_reuseFailAlloc_2339_, sizeof(void*)*1, v_tid_2323_);
v___x_2330_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
lean_object* v___x_2332_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 4, v___x_2330_);
v___x_2332_ = v___x_2321_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_env_2312_);
lean_ctor_set(v_reuseFailAlloc_2338_, 1, v_nextMacroScope_2313_);
lean_ctor_set(v_reuseFailAlloc_2338_, 2, v_ngen_2314_);
lean_ctor_set(v_reuseFailAlloc_2338_, 3, v_auxDeclNGen_2315_);
lean_ctor_set(v_reuseFailAlloc_2338_, 4, v___x_2330_);
lean_ctor_set(v_reuseFailAlloc_2338_, 5, v_cache_2316_);
lean_ctor_set(v_reuseFailAlloc_2338_, 6, v_messages_2317_);
lean_ctor_set(v_reuseFailAlloc_2338_, 7, v_infoState_2318_);
lean_ctor_set(v_reuseFailAlloc_2338_, 8, v_snapshotTasks_2319_);
v___x_2332_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
v___x_2333_ = lean_st_ref_put(v___y_2281_, v___x_2332_);
v___x_2334_ = lean_box(0);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v___x_2334_);
v___x_2336_ = v___x_2308_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
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
lean_object* v_fst_2397_; lean_object* v_snd_2398_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v_data_2402_; lean_object* v_fst_2405_; lean_object* v_snd_2406_; lean_object* v___x_2407_; uint8_t v___x_2408_; lean_object* v___y_2410_; lean_object* v_a_2411_; uint8_t v___y_2426_; double v___y_2457_; 
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
lean_object* v___x_2462_; uint8_t v___x_2463_; 
v___x_2462_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2463_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2389_, v___x_2462_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; lean_object* v___x_2465_; double v___x_2466_; double v___x_2467_; double v___x_2468_; 
v___x_2464_ = l_Lean_trace_profiler_threshold;
v___x_2465_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2389_, v___x_2464_);
v___x_2466_ = lean_float_of_nat(v___x_2465_);
v___x_2467_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2468_ = lean_float_div(v___x_2466_, v___x_2467_);
v___y_2457_ = v___x_2468_;
goto v___jp_2456_;
}
else
{
lean_object* v___x_2469_; lean_object* v___x_2470_; double v___x_2471_; 
v___x_2469_ = l_Lean_trace_profiler_threshold;
v___x_2470_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2389_, v___x_2469_);
v___x_2471_ = lean_float_of_nat(v___x_2470_);
v___y_2457_ = v___x_2471_;
goto v___jp_2456_;
}
}
v___jp_2399_:
{
lean_object* v___x_2403_; 
lean_inc(v___y_2401_);
v___x_2403_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2391_, v_data_2402_, v___y_2401_, v___y_2400_, v___y_2394_, v___y_2395_);
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
v___y_2400_ = v_a_2411_;
v___y_2401_ = v___y_2410_;
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
v___y_2400_ = v_a_2411_;
v___y_2401_ = v___y_2410_;
v_data_2402_ = v_data_2417_;
goto v___jp_2399_;
}
}
v___jp_2420_:
{
lean_object* v_ref_2421_; lean_object* v___x_2422_; 
v_ref_2421_ = lean_ctor_get(v___y_2394_, 4);
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
lean_object* v___x_2427_; lean_object* v_traceState_2428_; lean_object* v_env_2429_; lean_object* v_nextMacroScope_2430_; lean_object* v_ngen_2431_; lean_object* v_auxDeclNGen_2432_; lean_object* v_cache_2433_; lean_object* v_messages_2434_; lean_object* v_infoState_2435_; lean_object* v_snapshotTasks_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2455_; 
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
v_messages_2434_ = lean_ctor_get(v___x_2427_, 6);
v_infoState_2435_ = lean_ctor_get(v___x_2427_, 7);
v_snapshotTasks_2436_ = lean_ctor_get(v___x_2427_, 8);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2438_ = v___x_2427_;
v_isShared_2439_ = v_isSharedCheck_2455_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_snapshotTasks_2436_);
lean_inc(v_infoState_2435_);
lean_inc(v_messages_2434_);
lean_inc(v_cache_2433_);
lean_inc(v_traceState_2428_);
lean_inc(v_auxDeclNGen_2432_);
lean_inc(v_ngen_2431_);
lean_inc(v_nextMacroScope_2430_);
lean_inc(v_env_2429_);
lean_dec(v___x_2427_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2455_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
uint64_t v_tid_2440_; lean_object* v_traces_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2454_; 
v_tid_2440_ = lean_ctor_get_uint64(v_traceState_2428_, sizeof(void*)*1);
v_traces_2441_ = lean_ctor_get(v_traceState_2428_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_traceState_2428_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2443_ = v_traceState_2428_;
v_isShared_2444_ = v_isSharedCheck_2454_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_traces_2441_);
lean_dec(v_traceState_2428_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2454_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2445_; lean_object* v___x_2447_; 
v___x_2445_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2391_, v_traces_2441_);
lean_dec_ref(v_traces_2441_);
if (v_isShared_2444_ == 0)
{
lean_ctor_set(v___x_2443_, 0, v___x_2445_);
v___x_2447_ = v___x_2443_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2445_);
lean_ctor_set_uint64(v_reuseFailAlloc_2453_, sizeof(void*)*1, v_tid_2440_);
v___x_2447_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2449_; 
if (v_isShared_2439_ == 0)
{
lean_ctor_set(v___x_2438_, 4, v___x_2447_);
v___x_2449_ = v___x_2438_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_env_2429_);
lean_ctor_set(v_reuseFailAlloc_2452_, 1, v_nextMacroScope_2430_);
lean_ctor_set(v_reuseFailAlloc_2452_, 2, v_ngen_2431_);
lean_ctor_set(v_reuseFailAlloc_2452_, 3, v_auxDeclNGen_2432_);
lean_ctor_set(v_reuseFailAlloc_2452_, 4, v___x_2447_);
lean_ctor_set(v_reuseFailAlloc_2452_, 5, v_cache_2433_);
lean_ctor_set(v_reuseFailAlloc_2452_, 6, v_messages_2434_);
lean_ctor_set(v_reuseFailAlloc_2452_, 7, v_infoState_2435_);
lean_ctor_set(v_reuseFailAlloc_2452_, 8, v_snapshotTasks_2436_);
v___x_2449_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_st_ref_put(v___y_2395_, v___x_2449_);
v___x_2451_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2397_);
return v___x_2451_;
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
v___jp_2456_:
{
double v___x_2458_; double v___x_2459_; double v___x_2460_; uint8_t v___x_2461_; 
v___x_2458_ = lean_unbox_float(v_snd_2406_);
v___x_2459_ = lean_unbox_float(v_fst_2405_);
v___x_2460_ = lean_float_sub(v___x_2458_, v___x_2459_);
v___x_2461_ = lean_float_decLt(v___y_2457_, v___x_2460_);
v___y_2426_ = v___x_2461_;
goto v___jp_2425_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2472_, lean_object* v_collapsed_2473_, lean_object* v_tag_2474_, lean_object* v_opts_2475_, lean_object* v_clsEnabled_2476_, lean_object* v_oldTraces_2477_, lean_object* v_msg_2478_, lean_object* v_resStartStop_2479_, lean_object* v___y_2480_, lean_object* v___y_2481_, lean_object* v___y_2482_){
_start:
{
uint8_t v_collapsed_boxed_2483_; uint8_t v_clsEnabled_boxed_2484_; lean_object* v_res_2485_; 
v_collapsed_boxed_2483_ = lean_unbox(v_collapsed_2473_);
v_clsEnabled_boxed_2484_ = lean_unbox(v_clsEnabled_2476_);
v_res_2485_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2472_, v_collapsed_boxed_2483_, v_tag_2474_, v_opts_2475_, v_clsEnabled_boxed_2484_, v_oldTraces_2477_, v_msg_2478_, v_resStartStop_2479_, v___y_2480_, v___y_2481_);
lean_dec(v___y_2481_);
lean_dec_ref(v___y_2480_);
lean_dec_ref(v_opts_2475_);
return v_res_2485_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2488_; double v___x_2489_; 
v___x_2488_ = lean_unsigned_to_nat(1000000000u);
v___x_2489_ = lean_float_of_nat(v___x_2488_);
return v___x_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2490_, lean_object* v___x_2491_, uint8_t v___x_2492_, lean_object* v___x_2493_, lean_object* v___f_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
lean_object* v___y_2499_; lean_object* v___y_2500_; uint8_t v___y_2501_; lean_object* v___y_2512_; lean_object* v_a_2513_; lean_object* v___y_2517_; lean_object* v___y_2518_; uint8_t v___y_2519_; lean_object* v___y_2530_; lean_object* v_a_2531_; lean_object* v_options_2534_; uint8_t v_hasTrace_2535_; 
v_options_2534_ = lean_ctor_get(v___y_2495_, 1);
v_hasTrace_2535_ = lean_ctor_get_uint8(v_options_2534_, sizeof(void*)*1);
if (v_hasTrace_2535_ == 0)
{
lean_object* v_toCold_2536_; lean_object* v___x_2537_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec(v___x_2491_);
v_toCold_2536_ = lean_ctor_get(v___y_2495_, 0);
lean_inc(v_decl_2490_);
v___x_2537_ = l_Lean_warnIfUsesSorry(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2538_; lean_object* v_env_2539_; lean_object* v_cancelTk_x3f_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
lean_dec_ref_known(v___x_2537_, 1);
v___x_2538_ = lean_st_ref_get(v___y_2496_);
v_env_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc_ref(v_env_2539_);
lean_dec(v___x_2538_);
v_cancelTk_x3f_2540_ = lean_ctor_get(v_toCold_2536_, 3);
v___x_2541_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2539_, v_options_2534_, v_decl_2490_, v_cancelTk_x3f_2540_);
v___x_2542_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2541_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
lean_dec(v_decl_2490_);
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2543_, v___y_2496_);
return v___x_2544_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2542_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2542_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
lean_inc(v_a_2545_);
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
v___y_2530_ = v___x_2550_;
v_a_2531_ = v_a_2545_;
goto v___jp_2529_;
}
}
}
}
else
{
lean_dec(v_decl_2490_);
return v___x_2537_;
}
}
else
{
lean_object* v_toCold_2553_; lean_object* v_cancelTk_x3f_2554_; lean_object* v_inheritedTraceOptions_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; uint8_t v___x_2558_; lean_object* v___y_2560_; lean_object* v___y_2561_; lean_object* v_a_2562_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v_a_2577_; lean_object* v___y_2580_; lean_object* v___y_2581_; lean_object* v_a_2582_; lean_object* v___y_2585_; lean_object* v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; lean_object* v___y_2597_; lean_object* v___y_2598_; lean_object* v_a_2599_; lean_object* v___y_2603_; lean_object* v___y_2604_; lean_object* v_a_2605_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v_a_2617_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v_a_2622_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2634_; lean_object* v___y_2637_; lean_object* v___y_2638_; lean_object* v_a_2639_; 
v_toCold_2553_ = lean_ctor_get(v___y_2495_, 0);
v_cancelTk_x3f_2554_ = lean_ctor_get(v_toCold_2553_, 3);
v_inheritedTraceOptions_2555_ = lean_ctor_get(v_toCold_2553_, 4);
v___x_2556_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2491_);
v___x_2557_ = l_Lean_Name_append(v___x_2556_, v___x_2491_);
v___x_2558_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2555_, v_options_2534_, v___x_2557_);
lean_dec(v___x_2557_);
if (v___x_2558_ == 0)
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = l_Lean_trace_profiler;
v___x_2668_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2534_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v___f_2494_);
lean_dec_ref(v___x_2493_);
lean_dec(v___x_2491_);
lean_inc(v_decl_2490_);
v___x_2669_ = l_Lean_warnIfUsesSorry(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2670_; lean_object* v_env_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2669_, 1);
v___x_2670_ = lean_st_ref_get(v___y_2496_);
v_env_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref(v_env_2671_);
lean_dec(v___x_2670_);
v___x_2672_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2671_, v_options_2534_, v_decl_2490_, v_cancelTk_x3f_2554_);
v___x_2673_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2672_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
lean_dec(v_decl_2490_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2674_, v___y_2496_);
return v___x_2675_;
}
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_a_2676_ = lean_ctor_get(v___x_2673_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2673_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2673_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2673_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
lean_inc(v_a_2676_);
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
v___y_2512_ = v___x_2681_;
v_a_2513_ = v_a_2676_;
goto v___jp_2511_;
}
}
}
}
else
{
lean_dec(v_decl_2490_);
return v___x_2669_;
}
}
else
{
goto v___jp_2642_;
}
}
else
{
goto v___jp_2642_;
}
v___jp_2559_:
{
lean_object* v___x_2563_; double v___x_2564_; double v___x_2565_; double v___x_2566_; double v___x_2567_; double v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2563_ = lean_io_mono_nanos_now();
v___x_2564_ = lean_float_of_nat(v___y_2561_);
v___x_2565_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2566_ = lean_float_div(v___x_2564_, v___x_2565_);
v___x_2567_ = lean_float_of_nat(v___x_2563_);
v___x_2568_ = lean_float_div(v___x_2567_, v___x_2565_);
v___x_2569_ = lean_box_float(v___x_2566_);
v___x_2570_ = lean_box_float(v___x_2568_);
v___x_2571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2571_, 0, v___x_2569_);
lean_ctor_set(v___x_2571_, 1, v___x_2570_);
v___x_2572_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2572_, 0, v_a_2562_);
lean_ctor_set(v___x_2572_, 1, v___x_2571_);
v___x_2573_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2491_, v___x_2492_, v___x_2493_, v_options_2534_, v___x_2558_, v___y_2560_, v___f_2494_, v___x_2572_, v___y_2495_, v___y_2496_);
return v___x_2573_;
}
v___jp_2574_:
{
lean_object* v___x_2578_; 
v___x_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2578_, 0, v_a_2577_);
v___y_2560_ = v___y_2575_;
v___y_2561_ = v___y_2576_;
v_a_2562_ = v___x_2578_;
goto v___jp_2559_;
}
v___jp_2579_:
{
lean_object* v___x_2583_; 
v___x_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2583_, 0, v_a_2582_);
v___y_2560_ = v___y_2580_;
v___y_2561_ = v___y_2581_;
v_a_2562_ = v___x_2583_;
goto v___jp_2559_;
}
v___jp_2584_:
{
if (lean_obj_tag(v___y_2587_) == 0)
{
lean_object* v_a_2588_; 
v_a_2588_ = lean_ctor_get(v___y_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___y_2587_, 1);
v___y_2580_ = v___y_2585_;
v___y_2581_ = v___y_2586_;
v_a_2582_ = v_a_2588_;
goto v___jp_2579_;
}
else
{
lean_object* v_a_2589_; 
v_a_2589_ = lean_ctor_get(v___y_2587_, 0);
lean_inc(v_a_2589_);
lean_dec_ref_known(v___y_2587_, 1);
v___y_2575_ = v___y_2585_;
v___y_2576_ = v___y_2586_;
v_a_2577_ = v_a_2589_;
goto v___jp_2574_;
}
}
v___jp_2590_:
{
if (v___y_2594_ == 0)
{
lean_object* v___x_2595_; 
v___x_2595_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_dec_ref_known(v___x_2595_, 1);
v___y_2575_ = v___y_2592_;
v___y_2576_ = v___y_2593_;
v_a_2577_ = v___y_2591_;
goto v___jp_2574_;
}
else
{
lean_dec_ref(v___y_2591_);
v___y_2585_ = v___y_2592_;
v___y_2586_ = v___y_2593_;
v___y_2587_ = v___x_2595_;
goto v___jp_2584_;
}
}
else
{
lean_dec(v_decl_2490_);
v___y_2575_ = v___y_2592_;
v___y_2576_ = v___y_2593_;
v_a_2577_ = v___y_2591_;
goto v___jp_2574_;
}
}
v___jp_2596_:
{
uint8_t v___x_2600_; 
v___x_2600_ = l_Lean_Exception_isInterrupt(v_a_2599_);
if (v___x_2600_ == 0)
{
uint8_t v___x_2601_; 
lean_inc_ref(v_a_2599_);
v___x_2601_ = l_Lean_Exception_isRuntime(v_a_2599_);
v___y_2591_ = v_a_2599_;
v___y_2592_ = v___y_2597_;
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___x_2601_;
goto v___jp_2590_;
}
else
{
v___y_2591_ = v_a_2599_;
v___y_2592_ = v___y_2597_;
v___y_2593_ = v___y_2598_;
v___y_2594_ = v___x_2600_;
goto v___jp_2590_;
}
}
v___jp_2602_:
{
lean_object* v___x_2606_; double v___x_2607_; double v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2606_ = lean_io_get_num_heartbeats();
v___x_2607_ = lean_float_of_nat(v___y_2604_);
v___x_2608_ = lean_float_of_nat(v___x_2606_);
v___x_2609_ = lean_box_float(v___x_2607_);
v___x_2610_ = lean_box_float(v___x_2608_);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2612_, 0, v_a_2605_);
lean_ctor_set(v___x_2612_, 1, v___x_2611_);
v___x_2613_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2491_, v___x_2492_, v___x_2493_, v_options_2534_, v___x_2558_, v___y_2603_, v___f_2494_, v___x_2612_, v___y_2495_, v___y_2496_);
return v___x_2613_;
}
v___jp_2614_:
{
lean_object* v___x_2618_; 
v___x_2618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2618_, 0, v_a_2617_);
v___y_2603_ = v___y_2615_;
v___y_2604_ = v___y_2616_;
v_a_2605_ = v___x_2618_;
goto v___jp_2602_;
}
v___jp_2619_:
{
lean_object* v___x_2623_; 
v___x_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2623_, 0, v_a_2622_);
v___y_2603_ = v___y_2620_;
v___y_2604_ = v___y_2621_;
v_a_2605_ = v___x_2623_;
goto v___jp_2602_;
}
v___jp_2624_:
{
if (lean_obj_tag(v___y_2627_) == 0)
{
lean_object* v_a_2628_; 
v_a_2628_ = lean_ctor_get(v___y_2627_, 0);
lean_inc(v_a_2628_);
lean_dec_ref_known(v___y_2627_, 1);
v___y_2620_ = v___y_2625_;
v___y_2621_ = v___y_2626_;
v_a_2622_ = v_a_2628_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2629_; 
v_a_2629_ = lean_ctor_get(v___y_2627_, 0);
lean_inc(v_a_2629_);
lean_dec_ref_known(v___y_2627_, 1);
v___y_2615_ = v___y_2625_;
v___y_2616_ = v___y_2626_;
v_a_2617_ = v_a_2629_;
goto v___jp_2614_;
}
}
v___jp_2630_:
{
if (v___y_2634_ == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref_known(v___x_2635_, 1);
v___y_2615_ = v___y_2632_;
v___y_2616_ = v___y_2633_;
v_a_2617_ = v___y_2631_;
goto v___jp_2614_;
}
else
{
lean_dec_ref(v___y_2631_);
v___y_2625_ = v___y_2632_;
v___y_2626_ = v___y_2633_;
v___y_2627_ = v___x_2635_;
goto v___jp_2624_;
}
}
else
{
lean_dec(v_decl_2490_);
v___y_2615_ = v___y_2632_;
v___y_2616_ = v___y_2633_;
v_a_2617_ = v___y_2631_;
goto v___jp_2614_;
}
}
v___jp_2636_:
{
uint8_t v___x_2640_; 
v___x_2640_ = l_Lean_Exception_isInterrupt(v_a_2639_);
if (v___x_2640_ == 0)
{
uint8_t v___x_2641_; 
lean_inc_ref(v_a_2639_);
v___x_2641_ = l_Lean_Exception_isRuntime(v_a_2639_);
v___y_2631_ = v_a_2639_;
v___y_2632_ = v___y_2637_;
v___y_2633_ = v___y_2638_;
v___y_2634_ = v___x_2641_;
goto v___jp_2630_;
}
else
{
v___y_2631_ = v_a_2639_;
v___y_2632_ = v___y_2637_;
v___y_2633_ = v___y_2638_;
v___y_2634_ = v___x_2640_;
goto v___jp_2630_;
}
}
v___jp_2642_:
{
lean_object* v___x_2643_; lean_object* v_a_2644_; lean_object* v___x_2645_; uint8_t v___x_2646_; 
v___x_2643_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2496_);
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref(v___x_2643_);
v___x_2645_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2646_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2534_, v___x_2645_);
if (v___x_2646_ == 0)
{
lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2647_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2490_);
v___x_2648_ = l_Lean_warnIfUsesSorry(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v___x_2649_; lean_object* v_env_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
lean_dec_ref_known(v___x_2648_, 1);
v___x_2649_ = lean_st_ref_get(v___y_2496_);
v_env_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc_ref(v_env_2650_);
lean_dec(v___x_2649_);
v___x_2651_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2650_, v_options_2534_, v_decl_2490_, v_cancelTk_x3f_2554_);
v___x_2652_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2651_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2652_) == 0)
{
lean_object* v_a_2653_; lean_object* v___x_2654_; lean_object* v_a_2655_; 
lean_dec(v_decl_2490_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2652_, 1);
v___x_2654_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2653_, v___y_2496_);
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref(v___x_2654_);
v___y_2580_ = v_a_2644_;
v___y_2581_ = v___x_2647_;
v_a_2582_ = v_a_2655_;
goto v___jp_2579_;
}
else
{
lean_object* v_a_2656_; 
v_a_2656_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2652_, 1);
v___y_2597_ = v_a_2644_;
v___y_2598_ = v___x_2647_;
v_a_2599_ = v_a_2656_;
goto v___jp_2596_;
}
}
else
{
lean_dec(v_decl_2490_);
v___y_2585_ = v_a_2644_;
v___y_2586_ = v___x_2647_;
v___y_2587_ = v___x_2648_;
goto v___jp_2584_;
}
}
else
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2490_);
v___x_2658_ = l_Lean_warnIfUsesSorry(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v___x_2659_; lean_object* v_env_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; 
lean_dec_ref_known(v___x_2658_, 1);
v___x_2659_ = lean_st_ref_get(v___y_2496_);
v_env_2660_ = lean_ctor_get(v___x_2659_, 0);
lean_inc_ref(v_env_2660_);
lean_dec(v___x_2659_);
v___x_2661_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2660_, v_options_2534_, v_decl_2490_, v_cancelTk_x3f_2554_);
v___x_2662_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2661_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v_a_2663_; lean_object* v___x_2664_; lean_object* v_a_2665_; 
lean_dec(v_decl_2490_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref_known(v___x_2662_, 1);
v___x_2664_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2663_, v___y_2496_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref(v___x_2664_);
v___y_2620_ = v_a_2644_;
v___y_2621_ = v___x_2657_;
v_a_2622_ = v_a_2665_;
goto v___jp_2619_;
}
else
{
lean_object* v_a_2666_; 
v_a_2666_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2662_, 1);
v___y_2637_ = v_a_2644_;
v___y_2638_ = v___x_2657_;
v_a_2639_ = v_a_2666_;
goto v___jp_2636_;
}
}
else
{
lean_dec(v_decl_2490_);
v___y_2625_ = v_a_2644_;
v___y_2626_ = v___x_2657_;
v___y_2627_ = v___x_2658_;
goto v___jp_2624_;
}
}
}
}
v___jp_2498_:
{
if (v___y_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_dec_ref(v___y_2499_);
v___x_2502_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2502_) == 0)
{
lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2509_ == 0)
{
lean_object* v_unused_2510_; 
v_unused_2510_ = lean_ctor_get(v___x_2502_, 0);
lean_dec(v_unused_2510_);
v___x_2504_ = v___x_2502_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_dec(v___x_2502_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
lean_ctor_set_tag(v___x_2504_, 1);
lean_ctor_set(v___x_2504_, 0, v___y_2500_);
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v___y_2500_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
else
{
lean_dec_ref(v___y_2500_);
return v___x_2502_;
}
}
else
{
lean_dec_ref(v___y_2500_);
lean_dec(v_decl_2490_);
return v___y_2499_;
}
}
v___jp_2511_:
{
uint8_t v___x_2514_; 
v___x_2514_ = l_Lean_Exception_isInterrupt(v_a_2513_);
if (v___x_2514_ == 0)
{
uint8_t v___x_2515_; 
lean_inc_ref(v_a_2513_);
v___x_2515_ = l_Lean_Exception_isRuntime(v_a_2513_);
v___y_2499_ = v___y_2512_;
v___y_2500_ = v_a_2513_;
v___y_2501_ = v___x_2515_;
goto v___jp_2498_;
}
else
{
v___y_2499_ = v___y_2512_;
v___y_2500_ = v_a_2513_;
v___y_2501_ = v___x_2514_;
goto v___jp_2498_;
}
}
v___jp_2516_:
{
if (v___y_2519_ == 0)
{
lean_object* v___x_2520_; 
lean_dec_ref(v___y_2518_);
v___x_2520_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2490_, v___y_2495_, v___y_2496_);
if (lean_obj_tag(v___x_2520_) == 0)
{
lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2520_);
if (v_isSharedCheck_2527_ == 0)
{
lean_object* v_unused_2528_; 
v_unused_2528_ = lean_ctor_get(v___x_2520_, 0);
lean_dec(v_unused_2528_);
v___x_2522_ = v___x_2520_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_dec(v___x_2520_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
lean_ctor_set_tag(v___x_2522_, 1);
lean_ctor_set(v___x_2522_, 0, v___y_2517_);
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v___y_2517_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
else
{
lean_dec_ref(v___y_2517_);
return v___x_2520_;
}
}
else
{
lean_dec_ref(v___y_2517_);
lean_dec(v_decl_2490_);
return v___y_2518_;
}
}
v___jp_2529_:
{
uint8_t v___x_2532_; 
v___x_2532_ = l_Lean_Exception_isInterrupt(v_a_2531_);
if (v___x_2532_ == 0)
{
uint8_t v___x_2533_; 
lean_inc_ref(v_a_2531_);
v___x_2533_ = l_Lean_Exception_isRuntime(v_a_2531_);
v___y_2517_ = v_a_2531_;
v___y_2518_ = v___y_2530_;
v___y_2519_ = v___x_2533_;
goto v___jp_2516_;
}
else
{
v___y_2517_ = v_a_2531_;
v___y_2518_ = v___y_2530_;
v___y_2519_ = v___x_2532_;
goto v___jp_2516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v___x_2687_, lean_object* v___f_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v___x_7927__boxed_2692_; lean_object* v_res_2693_; 
v___x_7927__boxed_2692_ = lean_unbox(v___x_2686_);
v_res_2693_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2684_, v___x_2685_, v___x_7927__boxed_2692_, v___x_2687_, v___f_2688_, v___y_2689_, v___y_2690_);
lean_dec(v___y_2690_);
lean_dec_ref(v___y_2689_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v_options_2702_; lean_object* v___f_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; uint8_t v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; 
v_options_2702_ = lean_ctor_get(v_a_2699_, 1);
lean_inc(v_decl_2698_);
v___f_2703_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2703_, 0, v_decl_2698_);
v___x_2704_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2705_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2706_ = 1;
v___x_2707_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2708_ = lean_box(v___x_2706_);
v___f_2709_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2709_, 0, v_decl_2698_);
lean_closure_set(v___f_2709_, 1, v___x_2705_);
lean_closure_set(v___f_2709_, 2, v___x_2708_);
lean_closure_set(v___f_2709_, 3, v___x_2707_);
lean_closure_set(v___f_2709_, 4, v___f_2703_);
v___x_2710_ = lean_box(0);
v___x_2711_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2704_, v_options_2702_, v___f_2709_, v___x_2710_, v_a_2699_, v_a_2700_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2712_, v_a_2713_, v_a_2714_);
lean_dec(v_a_2714_);
lean_dec_ref(v_a_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2717_, lean_object* v_x_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v___x_2722_; 
v___x_2722_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2718_);
return v___x_2722_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2723_, lean_object* v_x_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2723_, v_x_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2729_, lean_object* v_a_2730_, lean_object* v___y_2731_, lean_object* v_a_x3f_2732_){
_start:
{
lean_object* v___x_2734_; lean_object* v_env_2735_; lean_object* v___x_2736_; 
v___x_2734_ = lean_st_ref_get(v___y_2729_);
v_env_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc_ref(v_env_2735_);
lean_dec(v___x_2734_);
v___x_2736_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2730_, v_env_2735_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2736_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2736_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
else
{
lean_object* v_a_2745_; lean_object* v___x_2747_; uint8_t v_isShared_2748_; uint8_t v_isSharedCheck_2757_; 
v_a_2745_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2757_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2757_ == 0)
{
v___x_2747_ = v___x_2736_;
v_isShared_2748_ = v_isSharedCheck_2757_;
goto v_resetjp_2746_;
}
else
{
lean_inc(v_a_2745_);
lean_dec(v___x_2736_);
v___x_2747_ = lean_box(0);
v_isShared_2748_ = v_isSharedCheck_2757_;
goto v_resetjp_2746_;
}
v_resetjp_2746_:
{
lean_object* v_ref_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
v_ref_2749_ = lean_ctor_get(v___y_2731_, 4);
v___x_2750_ = lean_io_error_to_string(v_a_2745_);
v___x_2751_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
v___x_2752_ = l_Lean_MessageData_ofFormat(v___x_2751_);
lean_inc(v_ref_2749_);
v___x_2753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2753_, 0, v_ref_2749_);
lean_ctor_set(v___x_2753_, 1, v___x_2752_);
if (v_isShared_2748_ == 0)
{
lean_ctor_set(v___x_2747_, 0, v___x_2753_);
v___x_2755_ = v___x_2747_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2756_; 
v_reuseFailAlloc_2756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2756_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2756_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
return v___x_2755_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2758_, lean_object* v_a_2759_, lean_object* v___y_2760_, lean_object* v_a_x3f_2761_, lean_object* v___y_2762_){
_start:
{
lean_object* v_res_2763_; 
v_res_2763_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2758_, v_a_2759_, v___y_2760_, v_a_x3f_2761_);
lean_dec(v_a_x3f_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v___y_2758_);
return v_res_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2764_, lean_object* v_a_2765_, lean_object* v_decl_2766_, lean_object* v_x_2767_, lean_object* v___y_2768_, lean_object* v___y_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v_r_2772_; 
v___x_2771_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2764_, v___y_2769_);
lean_dec_ref(v___x_2771_);
v_r_2772_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2766_, v___y_2768_, v___y_2769_);
if (lean_obj_tag(v_r_2772_) == 0)
{
lean_object* v_a_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2789_; 
v_a_2773_ = lean_ctor_get(v_r_2772_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v_r_2772_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2775_ = v_r_2772_;
v_isShared_2776_ = v_isSharedCheck_2789_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_a_2773_);
lean_dec(v_r_2772_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2789_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
lean_object* v___x_2778_; 
lean_inc(v_a_2773_);
if (v_isShared_2776_ == 0)
{
lean_ctor_set_tag(v___x_2775_, 1);
v___x_2778_ = v___x_2775_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2773_);
v___x_2778_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; 
v___x_2779_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2769_, v_a_2765_, v___y_2768_, v___x_2778_);
lean_dec_ref(v___x_2778_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2786_; 
v_isSharedCheck_2786_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2786_ == 0)
{
lean_object* v_unused_2787_; 
v_unused_2787_ = lean_ctor_get(v___x_2779_, 0);
lean_dec(v_unused_2787_);
v___x_2781_ = v___x_2779_;
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
else
{
lean_dec(v___x_2779_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2786_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2784_; 
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v_a_2773_);
v___x_2784_ = v___x_2781_;
goto v_reusejp_2783_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2773_);
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
lean_dec(v_a_2773_);
return v___x_2779_;
}
}
}
}
else
{
lean_object* v_a_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; 
v_a_2790_ = lean_ctor_get(v_r_2772_, 0);
lean_inc(v_a_2790_);
lean_dec_ref_known(v_r_2772_, 1);
v___x_2791_ = lean_box(0);
v___x_2792_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2769_, v_a_2765_, v___y_2768_, v___x_2791_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_2799_ == 0)
{
lean_object* v_unused_2800_; 
v_unused_2800_ = lean_ctor_get(v___x_2792_, 0);
lean_dec(v_unused_2800_);
v___x_2794_ = v___x_2792_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v___x_2792_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set_tag(v___x_2794_, 1);
lean_ctor_set(v___x_2794_, 0, v_a_2790_);
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2790_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
else
{
lean_dec(v_a_2790_);
return v___x_2792_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2801_, lean_object* v_a_2802_, lean_object* v_decl_2803_, lean_object* v_x_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2801_, v_a_2802_, v_decl_2803_, v_x_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec_ref(v_x_2804_);
return v_res_2808_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2811_ = l_Lean_stringToMessageData(v___x_2810_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2812_, lean_object* v_x_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_){
_start:
{
lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2817_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2818_ = l_Lean_Declaration_getNames(v_decl_2812_);
v___x_2819_ = lean_box(0);
v___x_2820_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2818_, v___x_2819_);
v___x_2821_ = l_Lean_MessageData_ofList(v___x_2820_);
v___x_2822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2822_, 0, v___x_2817_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
return v___x_2823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2824_, lean_object* v_x_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2824_, v_x_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v_x_2825_);
return v_res_2829_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2832_, lean_object* v_msg_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_ref_2837_; lean_object* v___x_2838_; lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2883_; 
v_ref_2837_ = lean_ctor_get(v___y_2834_, 4);
v___x_2838_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2833_, v___y_2834_, v___y_2835_);
v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2838_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2841_ = v___x_2838_;
v_isShared_2842_ = v_isSharedCheck_2883_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2838_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2883_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; lean_object* v_traceState_2844_; lean_object* v_env_2845_; lean_object* v_nextMacroScope_2846_; lean_object* v_ngen_2847_; lean_object* v_auxDeclNGen_2848_; lean_object* v_cache_2849_; lean_object* v_messages_2850_; lean_object* v_infoState_2851_; lean_object* v_snapshotTasks_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2882_; 
v___x_2843_ = lean_st_ref_take(v___y_2835_);
v_traceState_2844_ = lean_ctor_get(v___x_2843_, 4);
v_env_2845_ = lean_ctor_get(v___x_2843_, 0);
v_nextMacroScope_2846_ = lean_ctor_get(v___x_2843_, 1);
v_ngen_2847_ = lean_ctor_get(v___x_2843_, 2);
v_auxDeclNGen_2848_ = lean_ctor_get(v___x_2843_, 3);
v_cache_2849_ = lean_ctor_get(v___x_2843_, 5);
v_messages_2850_ = lean_ctor_get(v___x_2843_, 6);
v_infoState_2851_ = lean_ctor_get(v___x_2843_, 7);
v_snapshotTasks_2852_ = lean_ctor_get(v___x_2843_, 8);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2854_ = v___x_2843_;
v_isShared_2855_ = v_isSharedCheck_2882_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_snapshotTasks_2852_);
lean_inc(v_infoState_2851_);
lean_inc(v_messages_2850_);
lean_inc(v_cache_2849_);
lean_inc(v_traceState_2844_);
lean_inc(v_auxDeclNGen_2848_);
lean_inc(v_ngen_2847_);
lean_inc(v_nextMacroScope_2846_);
lean_inc(v_env_2845_);
lean_dec(v___x_2843_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2882_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
uint64_t v_tid_2856_; lean_object* v_traces_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2881_; 
v_tid_2856_ = lean_ctor_get_uint64(v_traceState_2844_, sizeof(void*)*1);
v_traces_2857_ = lean_ctor_get(v_traceState_2844_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v_traceState_2844_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2859_ = v_traceState_2844_;
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_traces_2857_);
lean_dec(v_traceState_2844_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2881_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; double v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2871_; 
v___x_2861_ = lean_box(0);
v___x_2862_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2863_ = 0;
v___x_2864_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2865_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2865_, 0, v_cls_2832_);
lean_ctor_set(v___x_2865_, 1, v___x_2861_);
lean_ctor_set(v___x_2865_, 2, v___x_2864_);
lean_ctor_set_float(v___x_2865_, sizeof(void*)*3, v___x_2862_);
lean_ctor_set_float(v___x_2865_, sizeof(void*)*3 + 8, v___x_2862_);
lean_ctor_set_uint8(v___x_2865_, sizeof(void*)*3 + 16, v___x_2863_);
v___x_2866_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2867_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2865_);
lean_ctor_set(v___x_2867_, 1, v_a_2839_);
lean_ctor_set(v___x_2867_, 2, v___x_2866_);
lean_inc(v_ref_2837_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_ref_2837_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = l_Lean_PersistentArray_push___redArg(v_traces_2857_, v___x_2868_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 0, v___x_2869_);
v___x_2871_ = v___x_2859_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v___x_2869_);
lean_ctor_set_uint64(v_reuseFailAlloc_2880_, sizeof(void*)*1, v_tid_2856_);
v___x_2871_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
lean_object* v___x_2873_; 
if (v_isShared_2855_ == 0)
{
lean_ctor_set(v___x_2854_, 4, v___x_2871_);
v___x_2873_ = v___x_2854_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v_env_2845_);
lean_ctor_set(v_reuseFailAlloc_2879_, 1, v_nextMacroScope_2846_);
lean_ctor_set(v_reuseFailAlloc_2879_, 2, v_ngen_2847_);
lean_ctor_set(v_reuseFailAlloc_2879_, 3, v_auxDeclNGen_2848_);
lean_ctor_set(v_reuseFailAlloc_2879_, 4, v___x_2871_);
lean_ctor_set(v_reuseFailAlloc_2879_, 5, v_cache_2849_);
lean_ctor_set(v_reuseFailAlloc_2879_, 6, v_messages_2850_);
lean_ctor_set(v_reuseFailAlloc_2879_, 7, v_infoState_2851_);
lean_ctor_set(v_reuseFailAlloc_2879_, 8, v_snapshotTasks_2852_);
v___x_2873_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2874_ = lean_st_ref_put(v___y_2835_, v___x_2873_);
v___x_2875_ = lean_box(0);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2875_);
v___x_2877_ = v___x_2841_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2884_, lean_object* v_msg_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2884_, v_msg_2885_, v___y_2886_, v___y_2887_);
lean_dec(v___y_2887_);
lean_dec_ref(v___y_2886_);
return v_res_2889_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; 
v___x_2891_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2892_ = l_Lean_stringToMessageData(v___x_2891_);
return v___x_2892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2893_, lean_object* v_cls_2894_, lean_object* v_x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v_options_2899_; uint8_t v_hasTrace_2900_; 
v_options_2899_ = lean_ctor_get(v___y_2896_, 1);
v_hasTrace_2900_ = lean_ctor_get_uint8(v_options_2899_, sizeof(void*)*1);
if (v_hasTrace_2900_ == 0)
{
lean_object* v___x_2901_; 
lean_dec(v_cls_2894_);
v___x_2901_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2893_, v___y_2896_, v___y_2897_);
return v___x_2901_;
}
else
{
lean_object* v_toCold_2902_; lean_object* v_inheritedTraceOptions_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v_toCold_2902_ = lean_ctor_get(v___y_2896_, 0);
v_inheritedTraceOptions_2903_ = lean_ctor_get(v_toCold_2902_, 4);
v___x_2904_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2894_);
v___x_2905_ = l_Lean_Name_append(v___x_2904_, v_cls_2894_);
v___x_2906_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2903_, v_options_2899_, v___x_2905_);
lean_dec(v___x_2905_);
if (v___x_2906_ == 0)
{
lean_object* v___x_2907_; 
lean_dec(v_cls_2894_);
v___x_2907_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2893_, v___y_2896_, v___y_2897_);
return v___x_2907_;
}
else
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2908_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2909_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2894_, v___x_2908_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v___x_2910_; 
lean_dec_ref_known(v___x_2909_, 1);
v___x_2910_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2893_, v___y_2896_, v___y_2897_);
return v___x_2910_;
}
else
{
lean_dec(v_decl_2893_);
return v___x_2909_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2911_, lean_object* v_cls_2912_, lean_object* v_x_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_, lean_object* v___y_2916_){
_start:
{
lean_object* v_res_2917_; 
v_res_2917_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2911_, v_cls_2912_, v_x_2913_, v___y_2914_, v___y_2915_);
lean_dec(v___y_2915_);
lean_dec_ref(v___y_2914_);
lean_dec(v_x_2913_);
return v_res_2917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_options_2921_; uint8_t v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; 
v_options_2921_ = lean_ctor_get(v___y_2919_, 1);
v___x_2922_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2921_, v_opt_2918_);
v___x_2923_ = lean_box(v___x_2922_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2925_, lean_object* v___y_2926_, lean_object* v___y_2927_){
_start:
{
lean_object* v_res_2928_; 
v_res_2928_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2925_, v___y_2926_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v_opt_2925_);
return v_res_2928_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2929_){
_start:
{
if (lean_obj_tag(v_x_2929_) == 0)
{
uint8_t v___x_2930_; 
v___x_2930_ = 1;
return v___x_2930_;
}
else
{
lean_object* v_head_2931_; lean_object* v_tail_2932_; uint8_t v___x_2933_; 
v_head_2931_ = lean_ctor_get(v_x_2929_, 0);
v_tail_2932_ = lean_ctor_get(v_x_2929_, 1);
v___x_2933_ = l_Lean_isPrivateName(v_head_2931_);
if (v___x_2933_ == 0)
{
return v___x_2933_;
}
else
{
v_x_2929_ = v_tail_2932_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2935_){
_start:
{
uint8_t v_res_2936_; lean_object* v_r_2937_; 
v_res_2936_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2935_);
lean_dec(v_x_2935_);
v_r_2937_ = lean_box(v_res_2936_);
return v_r_2937_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2943_; lean_object* v___x_2944_; 
v___x_2943_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2944_ = l_Lean_stringToMessageData(v___x_2943_);
return v___x_2944_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2947_ = l_Lean_stringToMessageData(v___x_2946_);
return v___x_2947_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2949_; lean_object* v___x_2950_; 
v___x_2949_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2950_ = l_Lean_stringToMessageData(v___x_2949_);
return v___x_2950_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2951_, uint8_t v_hasTrace_2952_, uint8_t v___x_2953_, lean_object* v___x_2954_, lean_object* v_cls_2955_, lean_object* v___x_2956_, lean_object* v_____x_2957_, lean_object* v_exportedInfo_x3f_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v_a_2965_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v_a_2978_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v_snd_3061_; lean_object* v_fst_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3192_; 
v_snd_3061_ = lean_ctor_get(v_____x_2957_, 1);
v_fst_3062_ = lean_ctor_get(v_____x_2957_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v_____x_2957_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3064_ = v_____x_2957_;
v_isShared_3065_ = v_isSharedCheck_3192_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_snd_3061_);
lean_inc(v_fst_3062_);
lean_dec(v_____x_2957_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3192_;
goto v_resetjp_3063_;
}
v___jp_2962_:
{
lean_object* v___x_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v___x_2966_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2963_, v___y_2964_);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_2973_ == 0)
{
lean_object* v_unused_2974_; 
v_unused_2974_ = lean_ctor_get(v___x_2966_, 0);
lean_dec(v_unused_2974_);
v___x_2968_ = v___x_2966_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_dec(v___x_2966_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
lean_ctor_set_tag(v___x_2968_, 1);
lean_ctor_set(v___x_2968_, 0, v_a_2965_);
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2965_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
v___jp_2975_:
{
lean_object* v___x_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
v___x_2979_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2976_, v___y_2977_);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2986_ == 0)
{
lean_object* v_unused_2987_; 
v_unused_2987_ = lean_ctor_get(v___x_2979_, 0);
lean_dec(v_unused_2987_);
v___x_2981_ = v___x_2979_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_dec(v___x_2979_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
lean_ctor_set(v___x_2981_, 0, v_a_2978_);
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2978_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
v___jp_2988_:
{
lean_object* v___x_2999_; 
lean_inc_ref(v___y_2995_);
v___x_2999_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2993_, v___y_2995_, v___y_2990_, v___y_2998_);
if (lean_obj_tag(v___x_2999_) == 0)
{
lean_object* v___x_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref_known(v___x_2999_, 1);
lean_inc_ref(v___y_2989_);
v___x_3000_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2989_, v___y_2994_);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3046_ == 0)
{
lean_object* v_unused_3047_; 
v_unused_3047_ = lean_ctor_get(v___x_3000_, 0);
lean_dec(v_unused_3047_);
v___x_3002_ = v___x_3000_;
v_isShared_3003_ = v_isSharedCheck_3046_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v___x_3000_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3046_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v_options_3004_; lean_object* v___x_3005_; uint8_t v___x_3006_; 
v_options_3004_ = lean_ctor_get(v___y_2997_, 1);
v___x_3005_ = l_Lean_Elab_async;
v___x_3006_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3004_, v___x_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v_r_3008_; 
lean_del_object(v___x_3002_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2991_);
v___x_3007_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2995_, v___y_2994_);
lean_dec_ref(v___x_3007_);
v_r_3008_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2951_, v___y_2997_, v___y_2994_);
if (lean_obj_tag(v_r_3008_) == 0)
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3018_; 
v_a_3009_ = lean_ctor_get(v_r_3008_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v_r_3008_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3011_ = v_r_3008_;
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v_r_3008_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3018_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
lean_inc(v_a_3009_);
if (v_isShared_3012_ == 0)
{
lean_ctor_set_tag(v___x_3011_, 1);
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
lean_object* v___x_3015_; 
v___x_3015_ = lean_apply_2(v___y_2992_, v___x_3014_, lean_box(0));
if (lean_obj_tag(v___x_3015_) == 0)
{
lean_dec_ref_known(v___x_3015_, 1);
v___y_2976_ = v___y_2989_;
v___y_2977_ = v___y_2994_;
v_a_2978_ = v_a_3009_;
goto v___jp_2975_;
}
else
{
lean_object* v_a_3016_; 
lean_dec(v_a_3009_);
v_a_3016_ = lean_ctor_get(v___x_3015_, 0);
lean_inc(v_a_3016_);
lean_dec_ref_known(v___x_3015_, 1);
v___y_2963_ = v___y_2989_;
v___y_2964_ = v___y_2994_;
v_a_2965_ = v_a_3016_;
goto v___jp_2962_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3019_ = lean_ctor_get(v_r_3008_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v_r_3008_, 1);
v___x_3020_ = lean_box(0);
v___x_3021_ = lean_apply_2(v___y_2992_, v___x_3020_, lean_box(0));
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec_ref_known(v___x_3021_, 1);
v___y_2963_ = v___y_2989_;
v___y_2964_ = v___y_2994_;
v_a_2965_ = v_a_3019_;
goto v___jp_2962_;
}
else
{
lean_object* v_a_3022_; 
lean_dec(v_a_3019_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___y_2963_ = v___y_2989_;
v___y_2964_ = v___y_2994_;
v_a_2965_ = v_a_3022_;
goto v___jp_2962_;
}
}
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3025_; 
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2989_);
lean_dec(v_decl_2951_);
v___x_3023_ = l_IO_CancelToken_new();
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 1);
lean_ctor_set(v___x_3002_, 0, v___x_3023_);
v___x_3025_ = v___x_3002_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v___x_3023_);
v___x_3025_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3024_;
}
v_reusejp_3024_:
{
lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; 
v___x_3026_ = lean_unsigned_to_nat(0u);
v___x_3027_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3028_ = l_Lean_Name_toString(v___x_3027_, v_hasTrace_2952_);
lean_inc_ref(v___x_3025_);
v___x_3029_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2991_, v___x_3025_, v___x_3028_, v___y_2997_, v___y_2994_);
if (lean_obj_tag(v___x_3029_) == 0)
{
lean_object* v_a_3030_; lean_object* v_checked_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; 
v_a_3030_ = lean_ctor_get(v___x_3029_, 0);
lean_inc(v_a_3030_);
lean_dec_ref_known(v___x_3029_, 1);
v_checked_3031_ = lean_ctor_get(v___y_2996_, 2);
lean_inc_ref(v_checked_3031_);
lean_dec_ref(v___y_2996_);
v___x_3032_ = lean_io_map_task(v_a_3030_, v_checked_3031_, v___x_3026_, v___x_2953_);
v___x_3033_ = lean_box(0);
v___x_3034_ = lean_box(2);
v___x_3035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3033_);
lean_ctor_set(v___x_3035_, 1, v___x_3034_);
lean_ctor_set(v___x_3035_, 2, v___x_3025_);
lean_ctor_set(v___x_3035_, 3, v___x_3032_);
v___x_3036_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3035_, v___y_2994_);
return v___x_3036_;
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v___x_3025_);
lean_dec_ref(v___y_2996_);
v_a_3037_ = lean_ctor_get(v___x_3029_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3029_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3029_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3029_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3060_; 
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2992_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v___y_2989_);
lean_dec(v_decl_2951_);
v_a_3048_ = lean_ctor_get(v___x_2999_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___x_2999_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3050_ = v___x_2999_;
v_isShared_3051_ = v_isSharedCheck_3060_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2999_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3060_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v_ref_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3058_; 
v_ref_3052_ = lean_ctor_get(v___y_2997_, 4);
v___x_3053_ = lean_io_error_to_string(v_a_3048_);
v___x_3054_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3053_);
v___x_3055_ = l_Lean_MessageData_ofFormat(v___x_3054_);
lean_inc(v_ref_3052_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v_ref_3052_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
if (v_isShared_3051_ == 0)
{
lean_ctor_set(v___x_3050_, 0, v___x_3056_);
v___x_3058_ = v___x_3050_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v___x_3056_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
}
v_resetjp_3063_:
{
lean_object* v_fst_3066_; lean_object* v_snd_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3191_; 
v_fst_3066_ = lean_ctor_get(v_snd_3061_, 0);
v_snd_3067_ = lean_ctor_get(v_snd_3061_, 1);
v_isSharedCheck_3191_ = !lean_is_exclusive(v_snd_3061_);
if (v_isSharedCheck_3191_ == 0)
{
v___x_3069_ = v_snd_3061_;
v_isShared_3070_ = v_isSharedCheck_3191_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_snd_3067_);
lean_inc(v_fst_3066_);
lean_dec(v_snd_3061_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3191_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v___y_3074_; lean_object* v___y_3075_; lean_object* v___y_3076_; lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v_exportedInfo_x3f_3103_; lean_object* v___y_3104_; lean_object* v___y_3105_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3146_; lean_object* v___y_3147_; lean_object* v___x_3181_; lean_object* v_env_3182_; uint8_t v___x_3183_; 
v___x_3181_ = lean_st_ref_get(v___y_2960_);
v_env_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc_ref(v_env_3182_);
lean_dec(v___x_3181_);
v___x_3183_ = l_Lean_Environment_containsOnBranch(v_env_3182_, v_fst_3062_);
lean_dec_ref(v_env_3182_);
if (v___x_3183_ == 0)
{
lean_del_object(v___x_3064_);
v___y_3146_ = v___y_2959_;
v___y_3147_ = v___y_2960_;
goto v___jp_3145_;
}
else
{
lean_object* v___x_3184_; lean_object* v_env_3185_; lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_del_object(v___x_3069_);
lean_dec(v_snd_3067_);
lean_dec(v_fst_3066_);
lean_dec(v_exportedInfo_x3f_2958_);
lean_dec(v___x_2956_);
lean_dec(v_cls_2955_);
lean_dec_ref(v___x_2954_);
lean_dec(v_decl_2951_);
v___x_3184_ = lean_st_ref_get(v___y_2960_);
v_env_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc_ref(v_env_3185_);
lean_dec(v___x_3184_);
v___x_3186_ = lean_elab_environment_to_kernel_env(v_env_3185_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set_tag(v___x_3064_, 1);
lean_ctor_set(v___x_3064_, 1, v_fst_3062_);
lean_ctor_set(v___x_3064_, 0, v___x_3186_);
v___x_3188_ = v___x_3064_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3186_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_fst_3062_);
v___x_3188_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; 
v___x_3189_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3188_, v___y_2959_, v___y_2960_);
return v___x_3189_;
}
}
v___jp_3071_:
{
uint8_t v___x_3079_; lean_object* v___x_3080_; 
v___x_3079_ = lean_unbox(v_snd_3067_);
lean_dec(v_snd_3067_);
lean_inc_ref(v___y_3074_);
v___x_3080_ = l_Lean_Environment_addConstAsync(v___y_3074_, v_fst_3062_, v___x_3079_, v___y_3078_, v___x_2953_, v_hasTrace_2952_);
if (lean_obj_tag(v___x_3080_) == 0)
{
lean_object* v_a_3081_; lean_object* v_mainEnv_3082_; lean_object* v_asyncEnv_3083_; lean_object* v___f_3084_; lean_object* v___f_3085_; lean_object* v___x_3086_; 
lean_del_object(v___x_3069_);
v_a_3081_ = lean_ctor_get(v___x_3080_, 0);
lean_inc_n(v_a_3081_, 3);
lean_dec_ref_known(v___x_3080_, 1);
v_mainEnv_3082_ = lean_ctor_get(v_a_3081_, 0);
lean_inc_ref(v_mainEnv_3082_);
v_asyncEnv_3083_ = lean_ctor_get(v_a_3081_, 1);
lean_inc_ref_n(v_asyncEnv_3083_, 2);
lean_inc_ref(v___y_3073_);
lean_inc(v___y_3072_);
v___f_3084_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3084_, 0, v___y_3072_);
lean_closure_set(v___f_3084_, 1, v_a_3081_);
lean_closure_set(v___f_3084_, 2, v___y_3073_);
lean_inc(v_decl_2951_);
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3085_, 0, v_asyncEnv_3083_);
lean_closure_set(v___f_3085_, 1, v_a_3081_);
lean_closure_set(v___f_3085_, 2, v_decl_2951_);
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v_fst_3066_);
if (lean_obj_tag(v___y_3075_) == 0)
{
lean_inc_ref(v___x_3086_);
v___y_2989_ = v_mainEnv_3082_;
v___y_2990_ = v___x_3086_;
v___y_2991_ = v___f_3085_;
v___y_2992_ = v___f_3084_;
v___y_2993_ = v_a_3081_;
v___y_2994_ = v___y_3076_;
v___y_2995_ = v_asyncEnv_3083_;
v___y_2996_ = v___y_3074_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___x_3086_;
goto v___jp_2988_;
}
else
{
v___y_2989_ = v_mainEnv_3082_;
v___y_2990_ = v___x_3086_;
v___y_2991_ = v___f_3085_;
v___y_2992_ = v___f_3084_;
v___y_2993_ = v_a_3081_;
v___y_2994_ = v___y_3076_;
v___y_2995_ = v_asyncEnv_3083_;
v___y_2996_ = v___y_3074_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___y_3075_;
goto v___jp_2988_;
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3101_; 
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
lean_dec(v_fst_3066_);
lean_dec(v_decl_2951_);
v_a_3087_ = lean_ctor_get(v___x_3080_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3080_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3089_ = v___x_3080_;
v_isShared_3090_ = v_isSharedCheck_3101_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3080_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3101_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v_ref_3091_; lean_object* v___x_3092_; lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3096_; 
v_ref_3091_ = lean_ctor_get(v___y_3077_, 4);
v___x_3092_ = lean_io_error_to_string(v_a_3087_);
v___x_3093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3093_, 0, v___x_3092_);
v___x_3094_ = l_Lean_MessageData_ofFormat(v___x_3093_);
lean_inc(v_ref_3091_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 1, v___x_3094_);
lean_ctor_set(v___x_3069_, 0, v_ref_3091_);
v___x_3096_ = v___x_3069_;
goto v_reusejp_3095_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_ref_3091_);
lean_ctor_set(v_reuseFailAlloc_3100_, 1, v___x_3094_);
v___x_3096_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3095_;
}
v_reusejp_3095_:
{
lean_object* v___x_3098_; 
if (v_isShared_3090_ == 0)
{
lean_ctor_set(v___x_3089_, 0, v___x_3096_);
v___x_3098_ = v___x_3089_;
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
}
v___jp_3102_:
{
lean_object* v___x_3106_; 
v___x_3106_ = lean_st_ref_get(v___y_3105_);
if (lean_obj_tag(v_exportedInfo_x3f_3103_) == 0)
{
lean_object* v_env_3107_; lean_object* v___x_3108_; 
v_env_3107_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_ref(v_env_3107_);
lean_dec(v___x_3106_);
v___x_3108_ = lean_box(0);
v___y_3072_ = v___y_3105_;
v___y_3073_ = v___y_3104_;
v___y_3074_ = v_env_3107_;
v___y_3075_ = v_exportedInfo_x3f_3103_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3104_;
v___y_3078_ = v___x_3108_;
goto v___jp_3071_;
}
else
{
lean_object* v_env_3109_; lean_object* v_val_3110_; uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v_env_3109_ = lean_ctor_get(v___x_3106_, 0);
lean_inc_ref(v_env_3109_);
lean_dec(v___x_3106_);
v_val_3110_ = lean_ctor_get(v_exportedInfo_x3f_3103_, 0);
v___x_3111_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3110_);
v___x_3112_ = lean_box(v___x_3111_);
v___x_3113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3112_);
v___y_3072_ = v___y_3105_;
v___y_3073_ = v___y_3104_;
v___y_3074_ = v_env_3109_;
v___y_3075_ = v_exportedInfo_x3f_3103_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3104_;
v___y_3078_ = v___x_3113_;
goto v___jp_3071_;
}
}
v___jp_3114_:
{
lean_object* v___x_3117_; 
lean_inc(v_fst_3066_);
v___x_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3117_, 0, v_fst_3066_);
v_exportedInfo_x3f_3103_ = v___x_3117_;
v___y_3104_ = v___y_3115_;
v___y_3105_ = v___y_3116_;
goto v___jp_3102_;
}
v___jp_3118_:
{
lean_object* v___x_3121_; 
lean_inc(v_fst_3066_);
v___x_3121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3121_, 0, v_fst_3066_);
v_exportedInfo_x3f_3103_ = v___x_3121_;
v___y_3104_ = v___y_3119_;
v___y_3105_ = v___y_3120_;
goto v___jp_3102_;
}
v___jp_3122_:
{
lean_object* v___x_3125_; lean_object* v_env_3126_; lean_object* v_nextMacroScope_3127_; lean_object* v_ngen_3128_; lean_object* v_auxDeclNGen_3129_; lean_object* v_traceState_3130_; lean_object* v_messages_3131_; lean_object* v_infoState_3132_; lean_object* v_snapshotTasks_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3143_; 
v___x_3125_ = lean_st_ref_take(v___y_3123_);
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
v_nextMacroScope_3127_ = lean_ctor_get(v___x_3125_, 1);
v_ngen_3128_ = lean_ctor_get(v___x_3125_, 2);
v_auxDeclNGen_3129_ = lean_ctor_get(v___x_3125_, 3);
v_traceState_3130_ = lean_ctor_get(v___x_3125_, 4);
v_messages_3131_ = lean_ctor_get(v___x_3125_, 6);
v_infoState_3132_ = lean_ctor_get(v___x_3125_, 7);
v_snapshotTasks_3133_ = lean_ctor_get(v___x_3125_, 8);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3143_ == 0)
{
lean_object* v_unused_3144_; 
v_unused_3144_ = lean_ctor_get(v___x_3125_, 5);
lean_dec(v_unused_3144_);
v___x_3135_ = v___x_3125_;
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_snapshotTasks_3133_);
lean_inc(v_infoState_3132_);
lean_inc(v_messages_3131_);
lean_inc(v_traceState_3130_);
lean_inc(v_auxDeclNGen_3129_);
lean_inc(v_ngen_3128_);
lean_inc(v_nextMacroScope_3127_);
lean_inc(v_env_3126_);
lean_dec(v___x_3125_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3143_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3140_; 
v___x_3137_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3067_);
lean_inc(v_fst_3062_);
v___x_3138_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3137_, v_env_3126_, v_fst_3062_, v_snd_3067_);
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 5, v___x_2954_);
lean_ctor_set(v___x_3135_, 0, v___x_3138_);
v___x_3140_ = v___x_3135_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v___x_3138_);
lean_ctor_set(v_reuseFailAlloc_3142_, 1, v_nextMacroScope_3127_);
lean_ctor_set(v_reuseFailAlloc_3142_, 2, v_ngen_3128_);
lean_ctor_set(v_reuseFailAlloc_3142_, 3, v_auxDeclNGen_3129_);
lean_ctor_set(v_reuseFailAlloc_3142_, 4, v_traceState_3130_);
lean_ctor_set(v_reuseFailAlloc_3142_, 5, v___x_2954_);
lean_ctor_set(v_reuseFailAlloc_3142_, 6, v_messages_3131_);
lean_ctor_set(v_reuseFailAlloc_3142_, 7, v_infoState_3132_);
lean_ctor_set(v_reuseFailAlloc_3142_, 8, v_snapshotTasks_3133_);
v___x_3140_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
lean_object* v___x_3141_; 
v___x_3141_ = lean_st_ref_put(v___y_3123_, v___x_3140_);
v_exportedInfo_x3f_3103_ = v_exportedInfo_x3f_2958_;
v___y_3104_ = v___y_3124_;
v___y_3105_ = v___y_3123_;
goto v___jp_3102_;
}
}
}
v___jp_3145_:
{
lean_object* v___x_3148_; uint8_t v___x_3149_; 
lean_inc(v_decl_2951_);
v___x_3148_ = l_Lean_Declaration_getTopLevelNames(v_decl_2951_);
v___x_3149_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3148_);
lean_dec(v___x_3148_);
if (v___x_3149_ == 0)
{
lean_dec(v___x_2956_);
if (lean_obj_tag(v_exportedInfo_x3f_2958_) == 0)
{
if (v___x_3149_ == 0)
{
lean_object* v_options_3150_; uint8_t v_hasTrace_3151_; 
lean_dec_ref(v___x_2954_);
v_options_3150_ = lean_ctor_get(v___y_3146_, 1);
v_hasTrace_3151_ = lean_ctor_get_uint8(v_options_3150_, sizeof(void*)*1);
if (v_hasTrace_3151_ == 0)
{
lean_dec(v_cls_2955_);
v___y_3115_ = v___y_3146_;
v___y_3116_ = v___y_3147_;
goto v___jp_3114_;
}
else
{
lean_object* v_toCold_3152_; lean_object* v_inheritedTraceOptions_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; uint8_t v___x_3156_; 
v_toCold_3152_ = lean_ctor_get(v___y_3146_, 0);
v_inheritedTraceOptions_3153_ = lean_ctor_get(v_toCold_3152_, 4);
v___x_3154_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2955_);
v___x_3155_ = l_Lean_Name_append(v___x_3154_, v_cls_2955_);
v___x_3156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3153_, v_options_3150_, v___x_3155_);
lean_dec(v___x_3155_);
if (v___x_3156_ == 0)
{
lean_dec(v_cls_2955_);
v___y_3115_ = v___y_3146_;
v___y_3116_ = v___y_3147_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3157_; lean_object* v___x_3158_; 
v___x_3157_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3158_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2955_, v___x_3157_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_dec_ref_known(v___x_3158_, 1);
v___y_3115_ = v___y_3146_;
v___y_3116_ = v___y_3147_;
goto v___jp_3114_;
}
else
{
lean_del_object(v___x_3069_);
lean_dec(v_snd_3067_);
lean_dec(v_fst_3066_);
lean_dec(v_fst_3062_);
lean_dec(v_decl_2951_);
return v___x_3158_;
}
}
}
}
else
{
lean_dec(v_cls_2955_);
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3146_;
goto v___jp_3122_;
}
}
else
{
lean_dec(v_cls_2955_);
v___y_3123_ = v___y_3147_;
v___y_3124_ = v___y_3146_;
goto v___jp_3122_;
}
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v_a_3161_; uint8_t v___x_3162_; 
lean_dec(v_exportedInfo_x3f_2958_);
lean_dec_ref(v___x_2954_);
v___x_3159_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3160_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3159_, v___y_3146_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_a_3161_);
lean_dec_ref(v___x_3160_);
v___x_3162_ = lean_unbox(v_a_3161_);
lean_dec(v_a_3161_);
if (v___x_3162_ == 0)
{
lean_object* v_options_3163_; uint8_t v_hasTrace_3164_; 
v_options_3163_ = lean_ctor_get(v___y_3146_, 1);
v_hasTrace_3164_ = lean_ctor_get_uint8(v_options_3163_, sizeof(void*)*1);
if (v_hasTrace_3164_ == 0)
{
lean_dec(v_cls_2955_);
v_exportedInfo_x3f_3103_ = v___x_2956_;
v___y_3104_ = v___y_3146_;
v___y_3105_ = v___y_3147_;
goto v___jp_3102_;
}
else
{
lean_object* v_toCold_3165_; lean_object* v_inheritedTraceOptions_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; uint8_t v___x_3169_; 
v_toCold_3165_ = lean_ctor_get(v___y_3146_, 0);
v_inheritedTraceOptions_3166_ = lean_ctor_get(v_toCold_3165_, 4);
v___x_3167_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2955_);
v___x_3168_ = l_Lean_Name_append(v___x_3167_, v_cls_2955_);
v___x_3169_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3166_, v_options_3163_, v___x_3168_);
lean_dec(v___x_3168_);
if (v___x_3169_ == 0)
{
lean_dec(v_cls_2955_);
v_exportedInfo_x3f_3103_ = v___x_2956_;
v___y_3104_ = v___y_3146_;
v___y_3105_ = v___y_3147_;
goto v___jp_3102_;
}
else
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3171_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2955_, v___x_3170_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3171_) == 0)
{
lean_dec_ref_known(v___x_3171_, 1);
v_exportedInfo_x3f_3103_ = v___x_2956_;
v___y_3104_ = v___y_3146_;
v___y_3105_ = v___y_3147_;
goto v___jp_3102_;
}
else
{
lean_del_object(v___x_3069_);
lean_dec(v_snd_3067_);
lean_dec(v_fst_3066_);
lean_dec(v_fst_3062_);
lean_dec(v___x_2956_);
lean_dec(v_decl_2951_);
return v___x_3171_;
}
}
}
}
else
{
lean_object* v_options_3172_; uint8_t v_hasTrace_3173_; 
lean_dec(v___x_2956_);
v_options_3172_ = lean_ctor_get(v___y_3146_, 1);
v_hasTrace_3173_ = lean_ctor_get_uint8(v_options_3172_, sizeof(void*)*1);
if (v_hasTrace_3173_ == 0)
{
lean_dec(v_cls_2955_);
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
goto v___jp_3118_;
}
else
{
lean_object* v_toCold_3174_; lean_object* v_inheritedTraceOptions_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; uint8_t v___x_3178_; 
v_toCold_3174_ = lean_ctor_get(v___y_3146_, 0);
v_inheritedTraceOptions_3175_ = lean_ctor_get(v_toCold_3174_, 4);
v___x_3176_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2955_);
v___x_3177_ = l_Lean_Name_append(v___x_3176_, v_cls_2955_);
v___x_3178_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3175_, v_options_3172_, v___x_3177_);
lean_dec(v___x_3177_);
if (v___x_3178_ == 0)
{
lean_dec(v_cls_2955_);
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
goto v___jp_3118_;
}
else
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3180_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2955_, v___x_3179_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_dec_ref_known(v___x_3180_, 1);
v___y_3119_ = v___y_3146_;
v___y_3120_ = v___y_3147_;
goto v___jp_3118_;
}
else
{
lean_del_object(v___x_3069_);
lean_dec(v_snd_3067_);
lean_dec(v_fst_3066_);
lean_dec(v_fst_3062_);
lean_dec(v_decl_2951_);
return v___x_3180_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3193_, lean_object* v_hasTrace_3194_, lean_object* v___x_3195_, lean_object* v___x_3196_, lean_object* v_cls_3197_, lean_object* v___x_3198_, lean_object* v_____x_3199_, lean_object* v_exportedInfo_x3f_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
uint8_t v_hasTrace_boxed_3204_; uint8_t v___x_52585__boxed_3205_; lean_object* v_res_3206_; 
v_hasTrace_boxed_3204_ = lean_unbox(v_hasTrace_3194_);
v___x_52585__boxed_3205_ = lean_unbox(v___x_3195_);
v_res_3206_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3193_, v_hasTrace_boxed_3204_, v___x_52585__boxed_3205_, v___x_3196_, v_cls_3197_, v___x_3198_, v_____x_3199_, v_exportedInfo_x3f_3200_, v___y_3201_, v___y_3202_);
lean_dec(v___y_3202_);
lean_dec_ref(v___y_3201_);
return v_res_3206_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3209_ = l_Lean_stringToMessageData(v___x_3208_);
return v___x_3209_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; 
v___x_3211_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3212_ = l_Lean_stringToMessageData(v___x_3211_);
return v___x_3212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3213_, uint8_t v___x_3214_, lean_object* v_cls_3215_, lean_object* v___x_3216_, uint8_t v_forceExpose_3217_, lean_object* v_defn_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_){
_start:
{
lean_object* v_exportedInfo_x3f_3223_; lean_object* v___y_3224_; lean_object* v___y_3225_; lean_object* v___y_3235_; lean_object* v___y_3236_; lean_object* v___y_3237_; uint8_t v___y_3238_; uint8_t v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; lean_object* v___x_3250_; lean_object* v___x_3251_; uint8_t v___y_3253_; lean_object* v_env_3269_; lean_object* v_env_3270_; 
v___x_3250_ = lean_st_ref_get(v___y_3220_);
v___x_3251_ = lean_st_ref_get(v___y_3220_);
v_env_3269_ = lean_ctor_get(v___x_3250_, 0);
lean_inc_ref(v_env_3269_);
lean_dec(v___x_3250_);
v_env_3270_ = lean_ctor_get(v___x_3251_, 0);
lean_inc_ref(v_env_3270_);
lean_dec(v___x_3251_);
if (v_forceExpose_3217_ == 0)
{
goto v___jp_3271_;
}
else
{
if (v___x_3214_ == 0)
{
lean_dec_ref(v_env_3270_);
lean_dec_ref(v_env_3269_);
lean_dec(v_cls_3215_);
v_exportedInfo_x3f_3223_ = v___x_3216_;
v___y_3224_ = v___y_3219_;
v___y_3225_ = v___y_3220_;
goto v___jp_3222_;
}
else
{
goto v___jp_3271_;
}
}
v___jp_3222_:
{
lean_object* v_toConstantVal_3226_; lean_object* v_name_3227_; lean_object* v___x_3228_; uint8_t v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; 
v_toConstantVal_3226_ = lean_ctor_get(v_defn_3218_, 0);
v_name_3227_ = lean_ctor_get(v_toConstantVal_3226_, 0);
lean_inc(v_name_3227_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v_defn_3218_);
v___x_3229_ = 0;
v___x_3230_ = lean_box(v___x_3229_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3228_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
v___x_3232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3232_, 0, v_name_3227_);
lean_ctor_set(v___x_3232_, 1, v___x_3231_);
lean_inc(v___y_3225_);
lean_inc_ref(v___y_3224_);
v___x_3233_ = lean_apply_5(v___f_3213_, v___x_3232_, v_exportedInfo_x3f_3223_, v___y_3224_, v___y_3225_, lean_box(0));
return v___x_3233_;
}
v___jp_3234_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3239_, 0, v___y_3237_);
lean_ctor_set_uint8(v___x_3239_, sizeof(void*)*1, v___y_3238_);
v___x_3240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
v___x_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
v_exportedInfo_x3f_3223_ = v___x_3241_;
v___y_3224_ = v___y_3235_;
v___y_3225_ = v___y_3236_;
goto v___jp_3222_;
}
v___jp_3242_:
{
lean_object* v_toConstantVal_3246_; uint8_t v_safety_3247_; uint8_t v___x_3248_; uint8_t v___x_3249_; 
v_toConstantVal_3246_ = lean_ctor_get(v_defn_3218_, 0);
v_safety_3247_ = lean_ctor_get_uint8(v_defn_3218_, sizeof(void*)*4);
v___x_3248_ = 1;
v___x_3249_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3247_, v___x_3248_);
if (v___x_3249_ == 0)
{
lean_inc_ref(v_toConstantVal_3246_);
v___y_3235_ = v___y_3244_;
v___y_3236_ = v___y_3245_;
v___y_3237_ = v_toConstantVal_3246_;
v___y_3238_ = v___y_3243_;
goto v___jp_3234_;
}
else
{
lean_inc_ref(v_toConstantVal_3246_);
v___y_3235_ = v___y_3244_;
v___y_3236_ = v___y_3245_;
v___y_3237_ = v_toConstantVal_3246_;
v___y_3238_ = v___x_3214_;
goto v___jp_3234_;
}
}
v___jp_3252_:
{
lean_object* v_options_3254_; uint8_t v_hasTrace_3255_; 
v_options_3254_ = lean_ctor_get(v___y_3219_, 1);
v_hasTrace_3255_ = lean_ctor_get_uint8(v_options_3254_, sizeof(void*)*1);
if (v_hasTrace_3255_ == 0)
{
lean_dec(v_cls_3215_);
v___y_3243_ = v___y_3253_;
v___y_3244_ = v___y_3219_;
v___y_3245_ = v___y_3220_;
goto v___jp_3242_;
}
else
{
lean_object* v_toCold_3256_; lean_object* v_inheritedTraceOptions_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v_toCold_3256_ = lean_ctor_get(v___y_3219_, 0);
v_inheritedTraceOptions_3257_ = lean_ctor_get(v_toCold_3256_, 4);
v___x_3258_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3215_);
v___x_3259_ = l_Lean_Name_append(v___x_3258_, v_cls_3215_);
v___x_3260_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3257_, v_options_3254_, v___x_3259_);
lean_dec(v___x_3259_);
if (v___x_3260_ == 0)
{
lean_dec(v_cls_3215_);
v___y_3243_ = v___y_3253_;
v___y_3244_ = v___y_3219_;
v___y_3245_ = v___y_3220_;
goto v___jp_3242_;
}
else
{
lean_object* v_toConstantVal_3261_; lean_object* v_name_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_toConstantVal_3261_ = lean_ctor_get(v_defn_3218_, 0);
v_name_3262_ = lean_ctor_get(v_toConstantVal_3261_, 0);
v___x_3263_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3262_);
v___x_3264_ = l_Lean_MessageData_ofName(v_name_3262_);
v___x_3265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3263_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
v___x_3266_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3267_, 0, v___x_3265_);
lean_ctor_set(v___x_3267_, 1, v___x_3266_);
v___x_3268_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3215_, v___x_3267_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec_ref_known(v___x_3268_, 1);
v___y_3243_ = v___y_3253_;
v___y_3244_ = v___y_3219_;
v___y_3245_ = v___y_3220_;
goto v___jp_3242_;
}
else
{
lean_dec_ref(v_defn_3218_);
lean_dec_ref(v___f_3213_);
return v___x_3268_;
}
}
}
}
v___jp_3271_:
{
lean_object* v___x_3272_; uint8_t v_isModule_3273_; 
v___x_3272_ = l_Lean_Environment_header(v_env_3269_);
lean_dec_ref(v_env_3269_);
v_isModule_3273_ = lean_ctor_get_uint8(v___x_3272_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3272_);
if (v_isModule_3273_ == 0)
{
lean_dec_ref(v_env_3270_);
lean_dec(v_cls_3215_);
v_exportedInfo_x3f_3223_ = v___x_3216_;
v___y_3224_ = v___y_3219_;
v___y_3225_ = v___y_3220_;
goto v___jp_3222_;
}
else
{
uint8_t v_isExporting_3274_; 
v_isExporting_3274_ = lean_ctor_get_uint8(v_env_3270_, sizeof(void*)*8);
lean_dec_ref(v_env_3270_);
if (v_isExporting_3274_ == 0)
{
lean_dec(v___x_3216_);
v___y_3253_ = v_isModule_3273_;
goto v___jp_3252_;
}
else
{
if (v___x_3214_ == 0)
{
lean_dec(v_cls_3215_);
v_exportedInfo_x3f_3223_ = v___x_3216_;
v___y_3224_ = v___y_3219_;
v___y_3225_ = v___y_3220_;
goto v___jp_3222_;
}
else
{
lean_dec(v___x_3216_);
v___y_3253_ = v___x_3214_;
goto v___jp_3252_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3275_, lean_object* v___x_3276_, lean_object* v_cls_3277_, lean_object* v___x_3278_, lean_object* v_forceExpose_3279_, lean_object* v_defn_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
uint8_t v___x_53057__boxed_3284_; uint8_t v_forceExpose_boxed_3285_; lean_object* v_res_3286_; 
v___x_53057__boxed_3284_ = lean_unbox(v___x_3276_);
v_forceExpose_boxed_3285_ = lean_unbox(v_forceExpose_3279_);
v_res_3286_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3275_, v___x_53057__boxed_3284_, v_cls_3277_, v___x_3278_, v_forceExpose_boxed_3285_, v_defn_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
return v_res_3286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3287_, lean_object* v___f_3288_, lean_object* v_____r_3289_, lean_object* v_exportedInfo_x3f_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_toConstantVal_3294_; lean_object* v_name_3295_; lean_object* v___x_3296_; uint8_t v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; 
v_toConstantVal_3294_ = lean_ctor_get(v_val_3287_, 0);
v_name_3295_ = lean_ctor_get(v_toConstantVal_3294_, 0);
lean_inc(v_name_3295_);
v___x_3296_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3296_, 0, v_val_3287_);
v___x_3297_ = 1;
v___x_3298_ = lean_box(v___x_3297_);
v___x_3299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3296_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3300_, 0, v_name_3295_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
lean_inc(v___y_3292_);
lean_inc_ref(v___y_3291_);
v___x_3301_ = lean_apply_5(v___f_3288_, v___x_3300_, v_exportedInfo_x3f_3290_, v___y_3291_, v___y_3292_, lean_box(0));
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3302_, lean_object* v___f_3303_, lean_object* v_____r_3304_, lean_object* v_exportedInfo_x3f_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
lean_object* v_res_3309_; 
v_res_3309_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3302_, v___f_3303_, v_____r_3304_, v_exportedInfo_x3f_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3310_, uint8_t v___x_3311_, lean_object* v___f_3312_, lean_object* v_____r_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_toConstantVal_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v_toConstantVal_3317_ = lean_ctor_get(v_val_3310_, 0);
lean_inc_ref(v_toConstantVal_3317_);
v___x_3318_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3318_, 0, v_toConstantVal_3317_);
lean_ctor_set_uint8(v___x_3318_, sizeof(void*)*1, v___x_3311_);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
v___x_3320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3319_);
v___x_3321_ = lean_box(0);
lean_inc(v___y_3315_);
lean_inc_ref(v___y_3314_);
v___x_3322_ = lean_apply_5(v___f_3312_, v___x_3321_, v___x_3320_, v___y_3314_, v___y_3315_, lean_box(0));
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3323_, lean_object* v___x_3324_, lean_object* v___f_3325_, lean_object* v_____r_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v___x_53192__boxed_3330_; lean_object* v_res_3331_; 
v___x_53192__boxed_3330_ = lean_unbox(v___x_3324_);
v_res_3331_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3323_, v___x_53192__boxed_3330_, v___f_3325_, v_____r_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec_ref(v_val_3323_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3332_, lean_object* v___f_3333_, lean_object* v_____r_3334_, lean_object* v_exportedInfo_x3f_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_toConstantVal_3339_; lean_object* v_name_3340_; lean_object* v___x_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_toConstantVal_3339_ = lean_ctor_get(v_val_3332_, 0);
v_name_3340_ = lean_ctor_get(v_toConstantVal_3339_, 0);
lean_inc(v_name_3340_);
v___x_3341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_val_3332_);
v___x_3342_ = 3;
v___x_3343_ = lean_box(v___x_3342_);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3341_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3345_, 0, v_name_3340_);
lean_ctor_set(v___x_3345_, 1, v___x_3344_);
lean_inc(v___y_3337_);
lean_inc_ref(v___y_3336_);
v___x_3346_ = lean_apply_5(v___f_3333_, v___x_3345_, v_exportedInfo_x3f_3335_, v___y_3336_, v___y_3337_, lean_box(0));
return v___x_3346_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3347_, lean_object* v___f_3348_, lean_object* v_____r_3349_, lean_object* v_exportedInfo_x3f_3350_, lean_object* v___y_3351_, lean_object* v___y_3352_, lean_object* v___y_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3347_, v___f_3348_, v_____r_3349_, v_exportedInfo_x3f_3350_, v___y_3351_, v___y_3352_);
lean_dec(v___y_3352_);
lean_dec_ref(v___y_3351_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3355_, lean_object* v___f_3356_, lean_object* v_____r_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_toConstantVal_3361_; uint8_t v_isUnsafe_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; 
v_toConstantVal_3361_ = lean_ctor_get(v_val_3355_, 0);
v_isUnsafe_3362_ = lean_ctor_get_uint8(v_val_3355_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3361_);
v___x_3363_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3363_, 0, v_toConstantVal_3361_);
lean_ctor_set_uint8(v___x_3363_, sizeof(void*)*1, v_isUnsafe_3362_);
v___x_3364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
v___x_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3364_);
v___x_3366_ = lean_box(0);
lean_inc(v___y_3359_);
lean_inc_ref(v___y_3358_);
v___x_3367_ = lean_apply_5(v___f_3356_, v___x_3366_, v___x_3365_, v___y_3358_, v___y_3359_, lean_box(0));
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3368_, lean_object* v___f_3369_, lean_object* v_____r_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3368_, v___f_3369_, v_____r_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec_ref(v_val_3368_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3375_, uint8_t v___x_3376_, lean_object* v_cls_3377_, lean_object* v___x_3378_, lean_object* v___x_3379_, lean_object* v_____x_3380_, lean_object* v_exportedInfo_x3f_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_){
_start:
{
lean_object* v___y_3386_; lean_object* v___y_3387_; lean_object* v_a_3388_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v_a_3401_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; uint8_t v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v_snd_3485_; lean_object* v_fst_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3618_; 
v_snd_3485_ = lean_ctor_get(v_____x_3380_, 1);
v_fst_3486_ = lean_ctor_get(v_____x_3380_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v_____x_3380_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3488_ = v_____x_3380_;
v_isShared_3489_ = v_isSharedCheck_3618_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_snd_3485_);
lean_inc(v_fst_3486_);
lean_dec(v_____x_3380_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3618_;
goto v_resetjp_3487_;
}
v___jp_3385_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
v___x_3389_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3387_, v___y_3386_);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3389_);
if (v_isSharedCheck_3396_ == 0)
{
lean_object* v_unused_3397_; 
v_unused_3397_ = lean_ctor_get(v___x_3389_, 0);
lean_dec(v_unused_3397_);
v___x_3391_ = v___x_3389_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_dec(v___x_3389_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
lean_ctor_set_tag(v___x_3391_, 1);
lean_ctor_set(v___x_3391_, 0, v_a_3388_);
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3388_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
v___jp_3398_:
{
lean_object* v___x_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
v___x_3402_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3400_, v___y_3399_);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3402_);
if (v_isSharedCheck_3409_ == 0)
{
lean_object* v_unused_3410_; 
v_unused_3410_ = lean_ctor_get(v___x_3402_, 0);
lean_dec(v_unused_3410_);
v___x_3404_ = v___x_3402_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_dec(v___x_3402_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
lean_ctor_set(v___x_3404_, 0, v_a_3401_);
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3401_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
v___jp_3411_:
{
lean_object* v___x_3423_; 
lean_inc_ref(v___y_3412_);
v___x_3423_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3413_, v___y_3412_, v___y_3420_, v___y_3422_);
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_object* v___x_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref_known(v___x_3423_, 1);
lean_inc_ref(v___y_3417_);
v___x_3424_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3417_, v___y_3414_);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3424_);
if (v_isSharedCheck_3470_ == 0)
{
lean_object* v_unused_3471_; 
v_unused_3471_ = lean_ctor_get(v___x_3424_, 0);
lean_dec(v_unused_3471_);
v___x_3426_ = v___x_3424_;
v_isShared_3427_ = v_isSharedCheck_3470_;
goto v_resetjp_3425_;
}
else
{
lean_dec(v___x_3424_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3470_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v_options_3428_; lean_object* v___x_3429_; uint8_t v___x_3430_; 
v_options_3428_ = lean_ctor_get(v___y_3416_, 1);
v___x_3429_ = l_Lean_Elab_async;
v___x_3430_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3428_, v___x_3429_);
if (v___x_3430_ == 0)
{
lean_object* v___x_3431_; lean_object* v_r_3432_; 
lean_del_object(v___x_3426_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
v___x_3431_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3412_, v___y_3414_);
lean_dec_ref(v___x_3431_);
v_r_3432_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3375_, v___y_3416_, v___y_3414_);
if (lean_obj_tag(v_r_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3442_; 
v_a_3433_ = lean_ctor_get(v_r_3432_, 0);
v_isSharedCheck_3442_ = !lean_is_exclusive(v_r_3432_);
if (v_isSharedCheck_3442_ == 0)
{
v___x_3435_ = v_r_3432_;
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v_r_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3442_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
lean_inc(v_a_3433_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set_tag(v___x_3435_, 1);
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3441_; 
v_reuseFailAlloc_3441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3441_, 0, v_a_3433_);
v___x_3438_ = v_reuseFailAlloc_3441_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
lean_object* v___x_3439_; 
v___x_3439_ = lean_apply_2(v___y_3421_, v___x_3438_, lean_box(0));
if (lean_obj_tag(v___x_3439_) == 0)
{
lean_dec_ref_known(v___x_3439_, 1);
v___y_3399_ = v___y_3414_;
v___y_3400_ = v___y_3417_;
v_a_3401_ = v_a_3433_;
goto v___jp_3398_;
}
else
{
lean_object* v_a_3440_; 
lean_dec(v_a_3433_);
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc(v_a_3440_);
lean_dec_ref_known(v___x_3439_, 1);
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3417_;
v_a_3388_ = v_a_3440_;
goto v___jp_3385_;
}
}
}
}
else
{
lean_object* v_a_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; 
v_a_3443_ = lean_ctor_get(v_r_3432_, 0);
lean_inc(v_a_3443_);
lean_dec_ref_known(v_r_3432_, 1);
v___x_3444_ = lean_box(0);
v___x_3445_ = lean_apply_2(v___y_3421_, v___x_3444_, lean_box(0));
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_dec_ref_known(v___x_3445_, 1);
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3417_;
v_a_3388_ = v_a_3443_;
goto v___jp_3385_;
}
else
{
lean_object* v_a_3446_; 
lean_dec(v_a_3443_);
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___y_3386_ = v___y_3414_;
v___y_3387_ = v___y_3417_;
v_a_3388_ = v_a_3446_;
goto v___jp_3385_;
}
}
}
else
{
lean_object* v___x_3447_; lean_object* v___x_3449_; 
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3412_);
lean_dec(v_decl_3375_);
v___x_3447_ = l_IO_CancelToken_new();
if (v_isShared_3427_ == 0)
{
lean_ctor_set_tag(v___x_3426_, 1);
lean_ctor_set(v___x_3426_, 0, v___x_3447_);
v___x_3449_ = v___x_3426_;
goto v_reusejp_3448_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v___x_3447_);
v___x_3449_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3448_;
}
v_reusejp_3448_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3450_ = lean_unsigned_to_nat(0u);
v___x_3451_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3452_ = l_Lean_Name_toString(v___x_3451_, v___x_3376_);
lean_inc_ref(v___x_3449_);
v___x_3453_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3419_, v___x_3449_, v___x_3452_, v___y_3416_, v___y_3414_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v_checked_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v_checked_3455_ = lean_ctor_get(v___y_3418_, 2);
lean_inc_ref(v_checked_3455_);
lean_dec_ref(v___y_3418_);
v___x_3456_ = lean_io_map_task(v_a_3454_, v_checked_3455_, v___x_3450_, v___y_3415_);
v___x_3457_ = lean_box(0);
v___x_3458_ = lean_box(2);
v___x_3459_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3459_, 0, v___x_3457_);
lean_ctor_set(v___x_3459_, 1, v___x_3458_);
lean_ctor_set(v___x_3459_, 2, v___x_3449_);
lean_ctor_set(v___x_3459_, 3, v___x_3456_);
v___x_3460_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3459_, v___y_3414_);
return v___x_3460_;
}
else
{
lean_object* v_a_3461_; lean_object* v___x_3463_; uint8_t v_isShared_3464_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___x_3449_);
lean_dec_ref(v___y_3418_);
v_a_3461_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3463_ = v___x_3453_;
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
else
{
lean_inc(v_a_3461_);
lean_dec(v___x_3453_);
v___x_3463_ = lean_box(0);
v_isShared_3464_ = v_isSharedCheck_3468_;
goto v_resetjp_3462_;
}
v_resetjp_3462_:
{
lean_object* v___x_3466_; 
if (v_isShared_3464_ == 0)
{
v___x_3466_ = v___x_3463_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v_a_3461_);
v___x_3466_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3465_;
}
v_reusejp_3465_:
{
return v___x_3466_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3484_; 
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3412_);
lean_dec(v_decl_3375_);
v_a_3472_ = lean_ctor_get(v___x_3423_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3423_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3474_ = v___x_3423_;
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3423_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3484_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v_ref_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v___x_3480_; lean_object* v___x_3482_; 
v_ref_3476_ = lean_ctor_get(v___y_3416_, 4);
v___x_3477_ = lean_io_error_to_string(v_a_3472_);
v___x_3478_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3478_, 0, v___x_3477_);
v___x_3479_ = l_Lean_MessageData_ofFormat(v___x_3478_);
lean_inc(v_ref_3476_);
v___x_3480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3480_, 0, v_ref_3476_);
lean_ctor_set(v___x_3480_, 1, v___x_3479_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3480_);
v___x_3482_ = v___x_3474_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v___x_3480_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
v_resetjp_3487_:
{
lean_object* v_fst_3490_; lean_object* v_snd_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3617_; 
v_fst_3490_ = lean_ctor_get(v_snd_3485_, 0);
v_snd_3491_ = lean_ctor_get(v_snd_3485_, 1);
v_isSharedCheck_3617_ = !lean_is_exclusive(v_snd_3485_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3493_ = v_snd_3485_;
v_isShared_3494_ = v_isSharedCheck_3617_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_snd_3491_);
lean_inc(v_fst_3490_);
lean_dec(v_snd_3485_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3617_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v_exportedInfo_x3f_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___y_3548_; lean_object* v___y_3549_; uint8_t v___y_3550_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___x_3607_; lean_object* v_env_3608_; uint8_t v___x_3609_; 
v___x_3607_ = lean_st_ref_get(v___y_3383_);
v_env_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc_ref(v_env_3608_);
lean_dec(v___x_3607_);
v___x_3609_ = l_Lean_Environment_containsOnBranch(v_env_3608_, v_fst_3486_);
lean_dec_ref(v_env_3608_);
if (v___x_3609_ == 0)
{
lean_del_object(v___x_3488_);
v___y_3581_ = v___y_3382_;
v___y_3582_ = v___y_3383_;
goto v___jp_3580_;
}
else
{
lean_object* v___x_3610_; lean_object* v_env_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_exportedInfo_x3f_3381_);
lean_dec(v___x_3379_);
lean_dec_ref(v___x_3378_);
lean_dec(v_cls_3377_);
lean_dec(v_decl_3375_);
v___x_3610_ = lean_st_ref_get(v___y_3383_);
v_env_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_ref(v_env_3611_);
lean_dec(v___x_3610_);
v___x_3612_ = lean_elab_environment_to_kernel_env(v_env_3611_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set_tag(v___x_3488_, 1);
lean_ctor_set(v___x_3488_, 1, v_fst_3486_);
lean_ctor_set(v___x_3488_, 0, v___x_3612_);
v___x_3614_ = v___x_3488_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3612_);
lean_ctor_set(v_reuseFailAlloc_3616_, 1, v_fst_3486_);
v___x_3614_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
lean_object* v___x_3615_; 
v___x_3615_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3614_, v___y_3382_, v___y_3383_);
return v___x_3615_;
}
}
v___jp_3495_:
{
uint8_t v___x_3503_; uint8_t v___x_3504_; lean_object* v___x_3505_; 
v___x_3503_ = 0;
v___x_3504_ = lean_unbox(v_snd_3491_);
lean_dec(v_snd_3491_);
lean_inc_ref(v___y_3497_);
v___x_3505_ = l_Lean_Environment_addConstAsync(v___y_3497_, v_fst_3486_, v___x_3504_, v___y_3502_, v___x_3503_, v___x_3376_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v_mainEnv_3507_; lean_object* v_asyncEnv_3508_; lean_object* v___f_3509_; lean_object* v___f_3510_; lean_object* v___x_3511_; 
lean_del_object(v___x_3493_);
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc_n(v_a_3506_, 3);
lean_dec_ref_known(v___x_3505_, 1);
v_mainEnv_3507_ = lean_ctor_get(v_a_3506_, 0);
lean_inc_ref(v_mainEnv_3507_);
v_asyncEnv_3508_ = lean_ctor_get(v_a_3506_, 1);
lean_inc_ref_n(v_asyncEnv_3508_, 2);
lean_inc_ref(v___y_3498_);
lean_inc(v___y_3496_);
v___f_3509_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3509_, 0, v___y_3496_);
lean_closure_set(v___f_3509_, 1, v_a_3506_);
lean_closure_set(v___f_3509_, 2, v___y_3498_);
lean_inc(v_decl_3375_);
v___f_3510_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3510_, 0, v_asyncEnv_3508_);
lean_closure_set(v___f_3510_, 1, v_a_3506_);
lean_closure_set(v___f_3510_, 2, v_decl_3375_);
v___x_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3511_, 0, v_fst_3490_);
if (lean_obj_tag(v___y_3501_) == 0)
{
lean_inc_ref(v___x_3511_);
v___y_3412_ = v_asyncEnv_3508_;
v___y_3413_ = v_a_3506_;
v___y_3414_ = v___y_3499_;
v___y_3415_ = v___x_3503_;
v___y_3416_ = v___y_3500_;
v___y_3417_ = v_mainEnv_3507_;
v___y_3418_ = v___y_3497_;
v___y_3419_ = v___f_3510_;
v___y_3420_ = v___x_3511_;
v___y_3421_ = v___f_3509_;
v___y_3422_ = v___x_3511_;
goto v___jp_3411_;
}
else
{
v___y_3412_ = v_asyncEnv_3508_;
v___y_3413_ = v_a_3506_;
v___y_3414_ = v___y_3499_;
v___y_3415_ = v___x_3503_;
v___y_3416_ = v___y_3500_;
v___y_3417_ = v_mainEnv_3507_;
v___y_3418_ = v___y_3497_;
v___y_3419_ = v___f_3510_;
v___y_3420_ = v___x_3511_;
v___y_3421_ = v___f_3509_;
v___y_3422_ = v___y_3501_;
goto v___jp_3411_;
}
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3526_; 
lean_dec(v___y_3501_);
lean_dec_ref(v___y_3497_);
lean_dec(v_fst_3490_);
lean_dec(v_decl_3375_);
v_a_3512_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3514_ = v___x_3505_;
v_isShared_3515_ = v_isSharedCheck_3526_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3505_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3526_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v_ref_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3521_; 
v_ref_3516_ = lean_ctor_get(v___y_3500_, 4);
v___x_3517_ = lean_io_error_to_string(v_a_3512_);
v___x_3518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = l_Lean_MessageData_ofFormat(v___x_3518_);
lean_inc(v_ref_3516_);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 1, v___x_3519_);
lean_ctor_set(v___x_3493_, 0, v_ref_3516_);
v___x_3521_ = v___x_3493_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_ref_3516_);
lean_ctor_set(v_reuseFailAlloc_3525_, 1, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3523_; 
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3521_);
v___x_3523_ = v___x_3514_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
}
}
v___jp_3527_:
{
lean_object* v___x_3531_; 
v___x_3531_ = lean_st_ref_get(v___y_3530_);
if (lean_obj_tag(v_exportedInfo_x3f_3528_) == 0)
{
lean_object* v_env_3532_; lean_object* v___x_3533_; 
v_env_3532_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref(v_env_3532_);
lean_dec(v___x_3531_);
v___x_3533_ = lean_box(0);
v___y_3496_ = v___y_3530_;
v___y_3497_ = v_env_3532_;
v___y_3498_ = v___y_3529_;
v___y_3499_ = v___y_3530_;
v___y_3500_ = v___y_3529_;
v___y_3501_ = v_exportedInfo_x3f_3528_;
v___y_3502_ = v___x_3533_;
goto v___jp_3495_;
}
else
{
lean_object* v_env_3534_; lean_object* v_val_3535_; uint8_t v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3538_; 
v_env_3534_ = lean_ctor_get(v___x_3531_, 0);
lean_inc_ref(v_env_3534_);
lean_dec(v___x_3531_);
v_val_3535_ = lean_ctor_get(v_exportedInfo_x3f_3528_, 0);
v___x_3536_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3535_);
v___x_3537_ = lean_box(v___x_3536_);
v___x_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3538_, 0, v___x_3537_);
v___y_3496_ = v___y_3530_;
v___y_3497_ = v_env_3534_;
v___y_3498_ = v___y_3529_;
v___y_3499_ = v___y_3530_;
v___y_3500_ = v___y_3529_;
v___y_3501_ = v_exportedInfo_x3f_3528_;
v___y_3502_ = v___x_3538_;
goto v___jp_3495_;
}
}
v___jp_3539_:
{
lean_object* v___x_3542_; 
lean_inc(v_fst_3490_);
v___x_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3542_, 0, v_fst_3490_);
v_exportedInfo_x3f_3528_ = v___x_3542_;
v___y_3529_ = v___y_3540_;
v___y_3530_ = v___y_3541_;
goto v___jp_3527_;
}
v___jp_3543_:
{
lean_object* v___x_3546_; 
lean_inc(v_fst_3490_);
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_fst_3490_);
v_exportedInfo_x3f_3528_ = v___x_3546_;
v___y_3529_ = v___y_3544_;
v___y_3530_ = v___y_3545_;
goto v___jp_3527_;
}
v___jp_3547_:
{
if (v___y_3550_ == 0)
{
lean_object* v_options_3551_; uint8_t v_hasTrace_3552_; 
lean_dec(v_exportedInfo_x3f_3381_);
lean_dec_ref(v___x_3378_);
v_options_3551_ = lean_ctor_get(v___y_3549_, 1);
v_hasTrace_3552_ = lean_ctor_get_uint8(v_options_3551_, sizeof(void*)*1);
if (v_hasTrace_3552_ == 0)
{
lean_dec(v_cls_3377_);
v___y_3540_ = v___y_3549_;
v___y_3541_ = v___y_3548_;
goto v___jp_3539_;
}
else
{
lean_object* v_toCold_3553_; lean_object* v_inheritedTraceOptions_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; uint8_t v___x_3557_; 
v_toCold_3553_ = lean_ctor_get(v___y_3549_, 0);
v_inheritedTraceOptions_3554_ = lean_ctor_get(v_toCold_3553_, 4);
v___x_3555_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3377_);
v___x_3556_ = l_Lean_Name_append(v___x_3555_, v_cls_3377_);
v___x_3557_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3554_, v_options_3551_, v___x_3556_);
lean_dec(v___x_3556_);
if (v___x_3557_ == 0)
{
lean_dec(v_cls_3377_);
v___y_3540_ = v___y_3549_;
v___y_3541_ = v___y_3548_;
goto v___jp_3539_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; 
v___x_3558_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3559_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3377_, v___x_3558_, v___y_3549_, v___y_3548_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_dec_ref_known(v___x_3559_, 1);
v___y_3540_ = v___y_3549_;
v___y_3541_ = v___y_3548_;
goto v___jp_3539_;
}
else
{
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_fst_3486_);
lean_dec(v_decl_3375_);
return v___x_3559_;
}
}
}
}
else
{
lean_object* v___x_3560_; lean_object* v_env_3561_; lean_object* v_nextMacroScope_3562_; lean_object* v_ngen_3563_; lean_object* v_auxDeclNGen_3564_; lean_object* v_traceState_3565_; lean_object* v_messages_3566_; lean_object* v_infoState_3567_; lean_object* v_snapshotTasks_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3578_; 
lean_dec(v_cls_3377_);
v___x_3560_ = lean_st_ref_take(v___y_3548_);
v_env_3561_ = lean_ctor_get(v___x_3560_, 0);
v_nextMacroScope_3562_ = lean_ctor_get(v___x_3560_, 1);
v_ngen_3563_ = lean_ctor_get(v___x_3560_, 2);
v_auxDeclNGen_3564_ = lean_ctor_get(v___x_3560_, 3);
v_traceState_3565_ = lean_ctor_get(v___x_3560_, 4);
v_messages_3566_ = lean_ctor_get(v___x_3560_, 6);
v_infoState_3567_ = lean_ctor_get(v___x_3560_, 7);
v_snapshotTasks_3568_ = lean_ctor_get(v___x_3560_, 8);
v_isSharedCheck_3578_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3578_ == 0)
{
lean_object* v_unused_3579_; 
v_unused_3579_ = lean_ctor_get(v___x_3560_, 5);
lean_dec(v_unused_3579_);
v___x_3570_ = v___x_3560_;
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_snapshotTasks_3568_);
lean_inc(v_infoState_3567_);
lean_inc(v_messages_3566_);
lean_inc(v_traceState_3565_);
lean_inc(v_auxDeclNGen_3564_);
lean_inc(v_ngen_3563_);
lean_inc(v_nextMacroScope_3562_);
lean_inc(v_env_3561_);
lean_dec(v___x_3560_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3578_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3575_; 
v___x_3572_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3491_);
lean_inc(v_fst_3486_);
v___x_3573_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3572_, v_env_3561_, v_fst_3486_, v_snd_3491_);
if (v_isShared_3571_ == 0)
{
lean_ctor_set(v___x_3570_, 5, v___x_3378_);
lean_ctor_set(v___x_3570_, 0, v___x_3573_);
v___x_3575_ = v___x_3570_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v___x_3573_);
lean_ctor_set(v_reuseFailAlloc_3577_, 1, v_nextMacroScope_3562_);
lean_ctor_set(v_reuseFailAlloc_3577_, 2, v_ngen_3563_);
lean_ctor_set(v_reuseFailAlloc_3577_, 3, v_auxDeclNGen_3564_);
lean_ctor_set(v_reuseFailAlloc_3577_, 4, v_traceState_3565_);
lean_ctor_set(v_reuseFailAlloc_3577_, 5, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3577_, 6, v_messages_3566_);
lean_ctor_set(v_reuseFailAlloc_3577_, 7, v_infoState_3567_);
lean_ctor_set(v_reuseFailAlloc_3577_, 8, v_snapshotTasks_3568_);
v___x_3575_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
lean_object* v___x_3576_; 
v___x_3576_ = lean_st_ref_put(v___y_3548_, v___x_3575_);
v_exportedInfo_x3f_3528_ = v_exportedInfo_x3f_3381_;
v___y_3529_ = v___y_3549_;
v___y_3530_ = v___y_3548_;
goto v___jp_3527_;
}
}
}
}
v___jp_3580_:
{
lean_object* v___x_3583_; uint8_t v___x_3584_; 
lean_inc(v_decl_3375_);
v___x_3583_ = l_Lean_Declaration_getTopLevelNames(v_decl_3375_);
v___x_3584_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3583_);
lean_dec(v___x_3583_);
if (v___x_3584_ == 0)
{
lean_dec(v___x_3379_);
if (lean_obj_tag(v_exportedInfo_x3f_3381_) == 0)
{
v___y_3548_ = v___y_3582_;
v___y_3549_ = v___y_3581_;
v___y_3550_ = v___x_3584_;
goto v___jp_3547_;
}
else
{
v___y_3548_ = v___y_3582_;
v___y_3549_ = v___y_3581_;
v___y_3550_ = v___x_3376_;
goto v___jp_3547_;
}
}
else
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v_a_3587_; uint8_t v___x_3588_; 
lean_dec(v_exportedInfo_x3f_3381_);
lean_dec_ref(v___x_3378_);
v___x_3585_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3586_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3585_, v___y_3581_);
v_a_3587_ = lean_ctor_get(v___x_3586_, 0);
lean_inc(v_a_3587_);
lean_dec_ref(v___x_3586_);
v___x_3588_ = lean_unbox(v_a_3587_);
lean_dec(v_a_3587_);
if (v___x_3588_ == 0)
{
lean_object* v_options_3589_; uint8_t v_hasTrace_3590_; 
v_options_3589_ = lean_ctor_get(v___y_3581_, 1);
v_hasTrace_3590_ = lean_ctor_get_uint8(v_options_3589_, sizeof(void*)*1);
if (v_hasTrace_3590_ == 0)
{
lean_dec(v_cls_3377_);
v_exportedInfo_x3f_3528_ = v___x_3379_;
v___y_3529_ = v___y_3581_;
v___y_3530_ = v___y_3582_;
goto v___jp_3527_;
}
else
{
lean_object* v_toCold_3591_; lean_object* v_inheritedTraceOptions_3592_; lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v_toCold_3591_ = lean_ctor_get(v___y_3581_, 0);
v_inheritedTraceOptions_3592_ = lean_ctor_get(v_toCold_3591_, 4);
v___x_3593_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3377_);
v___x_3594_ = l_Lean_Name_append(v___x_3593_, v_cls_3377_);
v___x_3595_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3592_, v_options_3589_, v___x_3594_);
lean_dec(v___x_3594_);
if (v___x_3595_ == 0)
{
lean_dec(v_cls_3377_);
v_exportedInfo_x3f_3528_ = v___x_3379_;
v___y_3529_ = v___y_3581_;
v___y_3530_ = v___y_3582_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3597_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3377_, v___x_3596_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_dec_ref_known(v___x_3597_, 1);
v_exportedInfo_x3f_3528_ = v___x_3379_;
v___y_3529_ = v___y_3581_;
v___y_3530_ = v___y_3582_;
goto v___jp_3527_;
}
else
{
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_fst_3486_);
lean_dec(v___x_3379_);
lean_dec(v_decl_3375_);
return v___x_3597_;
}
}
}
}
else
{
lean_object* v_options_3598_; uint8_t v_hasTrace_3599_; 
lean_dec(v___x_3379_);
v_options_3598_ = lean_ctor_get(v___y_3581_, 1);
v_hasTrace_3599_ = lean_ctor_get_uint8(v_options_3598_, sizeof(void*)*1);
if (v_hasTrace_3599_ == 0)
{
lean_dec(v_cls_3377_);
v___y_3544_ = v___y_3581_;
v___y_3545_ = v___y_3582_;
goto v___jp_3543_;
}
else
{
lean_object* v_toCold_3600_; lean_object* v_inheritedTraceOptions_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; uint8_t v___x_3604_; 
v_toCold_3600_ = lean_ctor_get(v___y_3581_, 0);
v_inheritedTraceOptions_3601_ = lean_ctor_get(v_toCold_3600_, 4);
v___x_3602_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3377_);
v___x_3603_ = l_Lean_Name_append(v___x_3602_, v_cls_3377_);
v___x_3604_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3601_, v_options_3598_, v___x_3603_);
lean_dec(v___x_3603_);
if (v___x_3604_ == 0)
{
lean_dec(v_cls_3377_);
v___y_3544_ = v___y_3581_;
v___y_3545_ = v___y_3582_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3605_; lean_object* v___x_3606_; 
v___x_3605_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3606_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3377_, v___x_3605_, v___y_3581_, v___y_3582_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_dec_ref_known(v___x_3606_, 1);
v___y_3544_ = v___y_3581_;
v___y_3545_ = v___y_3582_;
goto v___jp_3543_;
}
else
{
lean_del_object(v___x_3493_);
lean_dec(v_snd_3491_);
lean_dec(v_fst_3490_);
lean_dec(v_fst_3486_);
lean_dec(v_decl_3375_);
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
uint8_t v___x_53323__boxed_3629_; lean_object* v_res_3630_; 
v___x_53323__boxed_3629_ = lean_unbox(v___x_3620_);
v_res_3630_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3619_, v___x_53323__boxed_3629_, v_cls_3621_, v___x_3622_, v___x_3623_, v_____x_3624_, v_exportedInfo_x3f_3625_, v___y_3626_, v___y_3627_);
lean_dec(v___y_3627_);
lean_dec_ref(v___y_3626_);
return v_res_3630_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3631_, uint8_t v_forceExpose_3632_, uint8_t v___x_3633_, lean_object* v___x_3634_, lean_object* v_cls_3635_, lean_object* v_defn_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
lean_object* v_exportedInfo_x3f_3641_; lean_object* v___y_3642_; lean_object* v___y_3643_; lean_object* v___y_3653_; lean_object* v___y_3654_; lean_object* v___y_3655_; uint8_t v___y_3656_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v___x_3660_ = lean_st_ref_get(v___y_3638_);
v___x_3661_ = lean_st_ref_get(v___y_3638_);
if (v_forceExpose_3632_ == 0)
{
if (v___x_3633_ == 0)
{
lean_dec(v___x_3661_);
lean_dec(v___x_3660_);
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
else
{
lean_object* v_env_3662_; lean_object* v_env_3663_; lean_object* v___x_3664_; uint8_t v_isModule_3665_; 
v_env_3662_ = lean_ctor_get(v___x_3660_, 0);
lean_inc_ref(v_env_3662_);
lean_dec(v___x_3660_);
v_env_3663_ = lean_ctor_get(v___x_3661_, 0);
lean_inc_ref(v_env_3663_);
lean_dec(v___x_3661_);
v___x_3664_ = l_Lean_Environment_header(v_env_3662_);
lean_dec_ref(v_env_3662_);
v_isModule_3665_ = lean_ctor_get_uint8(v___x_3664_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3664_);
if (v_isModule_3665_ == 0)
{
lean_dec_ref(v_env_3663_);
lean_dec(v_cls_3635_);
v_exportedInfo_x3f_3641_ = v___x_3634_;
v___y_3642_ = v___y_3637_;
v___y_3643_ = v___y_3638_;
goto v___jp_3640_;
}
else
{
uint8_t v_isExporting_3666_; lean_object* v___y_3668_; lean_object* v___y_3669_; 
v_isExporting_3666_ = lean_ctor_get_uint8(v_env_3663_, sizeof(void*)*8);
lean_dec_ref(v_env_3663_);
if (v_isExporting_3666_ == 0)
{
lean_object* v_options_3674_; uint8_t v_hasTrace_3675_; 
lean_dec(v___x_3634_);
v_options_3674_ = lean_ctor_get(v___y_3637_, 1);
v_hasTrace_3675_ = lean_ctor_get_uint8(v_options_3674_, sizeof(void*)*1);
if (v_hasTrace_3675_ == 0)
{
lean_dec(v_cls_3635_);
v___y_3668_ = v___y_3637_;
v___y_3669_ = v___y_3638_;
goto v___jp_3667_;
}
else
{
lean_object* v_toCold_3676_; lean_object* v_inheritedTraceOptions_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; uint8_t v___x_3680_; 
v_toCold_3676_ = lean_ctor_get(v___y_3637_, 0);
v_inheritedTraceOptions_3677_ = lean_ctor_get(v_toCold_3676_, 4);
v___x_3678_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3635_);
v___x_3679_ = l_Lean_Name_append(v___x_3678_, v_cls_3635_);
v___x_3680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3677_, v_options_3674_, v___x_3679_);
lean_dec(v___x_3679_);
if (v___x_3680_ == 0)
{
lean_dec(v_cls_3635_);
v___y_3668_ = v___y_3637_;
v___y_3669_ = v___y_3638_;
goto v___jp_3667_;
}
else
{
lean_object* v_toConstantVal_3681_; lean_object* v_name_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v_toConstantVal_3681_ = lean_ctor_get(v_defn_3636_, 0);
v_name_3682_ = lean_ctor_get(v_toConstantVal_3681_, 0);
v___x_3683_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3682_);
v___x_3684_ = l_Lean_MessageData_ofName(v_name_3682_);
v___x_3685_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3683_);
lean_ctor_set(v___x_3685_, 1, v___x_3684_);
v___x_3686_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3687_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3685_);
lean_ctor_set(v___x_3687_, 1, v___x_3686_);
v___x_3688_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3635_, v___x_3687_, v___y_3637_, v___y_3638_);
if (lean_obj_tag(v___x_3688_) == 0)
{
lean_dec_ref_known(v___x_3688_, 1);
v___y_3668_ = v___y_3637_;
v___y_3669_ = v___y_3638_;
goto v___jp_3667_;
}
else
{
lean_dec_ref(v_defn_3636_);
lean_dec_ref(v___f_3631_);
return v___x_3688_;
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
v___jp_3667_:
{
lean_object* v_toConstantVal_3670_; uint8_t v_safety_3671_; uint8_t v___x_3672_; uint8_t v___x_3673_; 
v_toConstantVal_3670_ = lean_ctor_get(v_defn_3636_, 0);
v_safety_3671_ = lean_ctor_get_uint8(v_defn_3636_, sizeof(void*)*4);
v___x_3672_ = 1;
v___x_3673_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3671_, v___x_3672_);
if (v___x_3673_ == 0)
{
lean_inc_ref(v_toConstantVal_3670_);
v___y_3653_ = v___y_3669_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v_toConstantVal_3670_;
v___y_3656_ = v_isModule_3665_;
goto v___jp_3652_;
}
else
{
lean_inc_ref(v_toConstantVal_3670_);
v___y_3653_ = v___y_3669_;
v___y_3654_ = v___y_3668_;
v___y_3655_ = v_toConstantVal_3670_;
v___y_3656_ = v_isExporting_3666_;
goto v___jp_3652_;
}
}
}
}
}
else
{
lean_dec(v___x_3661_);
lean_dec(v___x_3660_);
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
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
v___x_3657_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3657_, 0, v___y_3655_);
lean_ctor_set_uint8(v___x_3657_, sizeof(void*)*1, v___y_3656_);
v___x_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
v_exportedInfo_x3f_3641_ = v___x_3659_;
v___y_3642_ = v___y_3654_;
v___y_3643_ = v___y_3653_;
goto v___jp_3640_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3689_, lean_object* v_forceExpose_3690_, lean_object* v___x_3691_, lean_object* v___x_3692_, lean_object* v_cls_3693_, lean_object* v_defn_3694_, lean_object* v___y_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_){
_start:
{
uint8_t v_forceExpose_boxed_3698_; uint8_t v___x_53798__boxed_3699_; lean_object* v_res_3700_; 
v_forceExpose_boxed_3698_ = lean_unbox(v_forceExpose_3690_);
v___x_53798__boxed_3699_ = lean_unbox(v___x_3691_);
v_res_3700_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3689_, v_forceExpose_boxed_3698_, v___x_53798__boxed_3699_, v___x_3692_, v_cls_3693_, v_defn_3694_, v___y_3695_, v___y_3696_);
lean_dec(v___y_3696_);
lean_dec_ref(v___y_3695_);
return v_res_3700_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3701_, uint8_t v_forceExpose_3702_, lean_object* v___f_3703_, lean_object* v_____r_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_){
_start:
{
lean_object* v_toConstantVal_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; 
v_toConstantVal_3708_ = lean_ctor_get(v_val_3701_, 0);
lean_inc_ref(v_toConstantVal_3708_);
v___x_3709_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3709_, 0, v_toConstantVal_3708_);
lean_ctor_set_uint8(v___x_3709_, sizeof(void*)*1, v_forceExpose_3702_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
v___x_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3711_, 0, v___x_3710_);
v___x_3712_ = lean_box(0);
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3705_);
v___x_3713_ = lean_apply_5(v___f_3703_, v___x_3712_, v___x_3711_, v___y_3705_, v___y_3706_, lean_box(0));
return v___x_3713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3714_, lean_object* v_forceExpose_3715_, lean_object* v___f_3716_, lean_object* v_____r_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
uint8_t v_forceExpose_boxed_3721_; lean_object* v_res_3722_; 
v_forceExpose_boxed_3721_ = lean_unbox(v_forceExpose_3715_);
v_res_3722_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3714_, v_forceExpose_boxed_3721_, v___f_3716_, v_____r_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_val_3714_);
return v_res_3722_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3723_, lean_object* v_x_3724_){
_start:
{
if (lean_obj_tag(v_x_3724_) == 0)
{
return v_x_3723_;
}
else
{
lean_object* v_head_3725_; lean_object* v_tail_3726_; lean_object* v___x_3727_; 
v_head_3725_ = lean_ctor_get(v_x_3724_, 0);
lean_inc(v_head_3725_);
v_tail_3726_ = lean_ctor_get(v_x_3724_, 1);
lean_inc(v_tail_3726_);
lean_dec_ref_known(v_x_3724_, 2);
v___x_3727_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3723_, v_head_3725_);
v_x_3723_ = v___x_3727_;
v_x_3724_ = v_tail_3726_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_cls_3729_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3730_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3731_ = l_Lean_Name_append(v___x_3730_, v_cls_3729_);
return v___x_3731_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3733_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3734_ = l_Lean_stringToMessageData(v___x_3733_);
return v___x_3734_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3736_; lean_object* v___x_3737_; 
v___x_3736_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3737_ = l_Lean_stringToMessageData(v___x_3736_);
return v___x_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3738_, uint8_t v_forceExpose_3739_, lean_object* v_a_3740_, lean_object* v_a_3741_){
_start:
{
lean_object* v___y_3744_; lean_object* v___y_3745_; lean_object* v_a_3746_; lean_object* v___y_3757_; lean_object* v___y_3758_; lean_object* v_a_3759_; lean_object* v___y_3770_; lean_object* v___y_3771_; lean_object* v_a_3772_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v_a_3785_; lean_object* v_options_3795_; lean_object* v_toCold_3796_; uint8_t v_hasTrace_3797_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3804_; lean_object* v___y_3805_; uint8_t v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3878_; lean_object* v___y_3879_; lean_object* v___y_3880_; uint8_t v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3905_; lean_object* v___y_3906_; uint8_t v___y_3907_; lean_object* v_exportedInfo_x3f_3908_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3920_; lean_object* v___y_3921_; uint8_t v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3927_; lean_object* v___y_3928_; uint8_t v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v_cls_3933_; 
v_options_3795_ = lean_ctor_get(v_a_3740_, 1);
v_toCold_3796_ = lean_ctor_get(v_a_3740_, 0);
v_hasTrace_3797_ = lean_ctor_get_uint8(v_options_3795_, sizeof(void*)*1);
v_cls_3933_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3797_ == 0)
{
lean_object* v___x_3934_; lean_object* v_env_3935_; lean_object* v_nextMacroScope_3936_; lean_object* v_ngen_3937_; lean_object* v_auxDeclNGen_3938_; lean_object* v_traceState_3939_; lean_object* v_messages_3940_; lean_object* v_infoState_3941_; lean_object* v_snapshotTasks_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_4144_; 
v___x_3934_ = lean_st_ref_take(v_a_3741_);
v_env_3935_ = lean_ctor_get(v___x_3934_, 0);
v_nextMacroScope_3936_ = lean_ctor_get(v___x_3934_, 1);
v_ngen_3937_ = lean_ctor_get(v___x_3934_, 2);
v_auxDeclNGen_3938_ = lean_ctor_get(v___x_3934_, 3);
v_traceState_3939_ = lean_ctor_get(v___x_3934_, 4);
v_messages_3940_ = lean_ctor_get(v___x_3934_, 6);
v_infoState_3941_ = lean_ctor_get(v___x_3934_, 7);
v_snapshotTasks_3942_ = lean_ctor_get(v___x_3934_, 8);
v_isSharedCheck_4144_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_4144_ == 0)
{
lean_object* v_unused_4145_; 
v_unused_4145_ = lean_ctor_get(v___x_3934_, 5);
lean_dec(v_unused_4145_);
v___x_3944_ = v___x_3934_;
v_isShared_3945_ = v_isSharedCheck_4144_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_snapshotTasks_3942_);
lean_inc(v_infoState_3941_);
lean_inc(v_messages_3940_);
lean_inc(v_traceState_3939_);
lean_inc(v_auxDeclNGen_3938_);
lean_inc(v_ngen_3937_);
lean_inc(v_nextMacroScope_3936_);
lean_inc(v_env_3935_);
lean_dec(v___x_3934_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_4144_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; uint8_t v___y_3955_; lean_object* v___x_3978_; 
lean_inc(v_decl_3738_);
v___x_3946_ = l_Lean_Declaration_getNames(v_decl_3738_);
v___x_3947_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3935_, v___x_3946_);
v___x_3948_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 5, v___x_3948_);
lean_ctor_set(v___x_3944_, 0, v___x_3947_);
v___x_3978_ = v___x_3944_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_4143_; 
v_reuseFailAlloc_4143_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4143_, 0, v___x_3947_);
lean_ctor_set(v_reuseFailAlloc_4143_, 1, v_nextMacroScope_3936_);
lean_ctor_set(v_reuseFailAlloc_4143_, 2, v_ngen_3937_);
lean_ctor_set(v_reuseFailAlloc_4143_, 3, v_auxDeclNGen_3938_);
lean_ctor_set(v_reuseFailAlloc_4143_, 4, v_traceState_3939_);
lean_ctor_set(v_reuseFailAlloc_4143_, 5, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_4143_, 6, v_messages_3940_);
lean_ctor_set(v_reuseFailAlloc_4143_, 7, v_infoState_3941_);
lean_ctor_set(v_reuseFailAlloc_4143_, 8, v_snapshotTasks_3942_);
v___x_3978_ = v_reuseFailAlloc_4143_;
goto v_reusejp_3977_;
}
v___jp_3949_:
{
lean_object* v___x_3956_; lean_object* v_env_3957_; lean_object* v_nextMacroScope_3958_; lean_object* v_ngen_3959_; lean_object* v_auxDeclNGen_3960_; lean_object* v_traceState_3961_; lean_object* v_messages_3962_; lean_object* v_infoState_3963_; lean_object* v_snapshotTasks_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3975_; 
v___x_3956_ = lean_st_ref_take(v___y_3952_);
v_env_3957_ = lean_ctor_get(v___x_3956_, 0);
v_nextMacroScope_3958_ = lean_ctor_get(v___x_3956_, 1);
v_ngen_3959_ = lean_ctor_get(v___x_3956_, 2);
v_auxDeclNGen_3960_ = lean_ctor_get(v___x_3956_, 3);
v_traceState_3961_ = lean_ctor_get(v___x_3956_, 4);
v_messages_3962_ = lean_ctor_get(v___x_3956_, 6);
v_infoState_3963_ = lean_ctor_get(v___x_3956_, 7);
v_snapshotTasks_3964_ = lean_ctor_get(v___x_3956_, 8);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3975_ == 0)
{
lean_object* v_unused_3976_; 
v_unused_3976_ = lean_ctor_get(v___x_3956_, 5);
lean_dec(v_unused_3976_);
v___x_3966_ = v___x_3956_;
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_snapshotTasks_3964_);
lean_inc(v_infoState_3963_);
lean_inc(v_messages_3962_);
lean_inc(v_traceState_3961_);
lean_inc(v_auxDeclNGen_3960_);
lean_inc(v_ngen_3959_);
lean_inc(v_nextMacroScope_3958_);
lean_inc(v_env_3957_);
lean_dec(v___x_3956_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3975_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3972_; 
v___x_3968_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3969_ = lean_box(v___y_3955_);
lean_inc(v___y_3950_);
v___x_3970_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3968_, v_env_3957_, v___y_3950_, v___x_3969_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 5, v___x_3948_);
lean_ctor_set(v___x_3966_, 0, v___x_3970_);
v___x_3972_ = v___x_3966_;
goto v_reusejp_3971_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v___x_3970_);
lean_ctor_set(v_reuseFailAlloc_3974_, 1, v_nextMacroScope_3958_);
lean_ctor_set(v_reuseFailAlloc_3974_, 2, v_ngen_3959_);
lean_ctor_set(v_reuseFailAlloc_3974_, 3, v_auxDeclNGen_3960_);
lean_ctor_set(v_reuseFailAlloc_3974_, 4, v_traceState_3961_);
lean_ctor_set(v_reuseFailAlloc_3974_, 5, v___x_3948_);
lean_ctor_set(v_reuseFailAlloc_3974_, 6, v_messages_3962_);
lean_ctor_set(v_reuseFailAlloc_3974_, 7, v_infoState_3963_);
lean_ctor_set(v_reuseFailAlloc_3974_, 8, v_snapshotTasks_3964_);
v___x_3972_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3971_;
}
v_reusejp_3971_:
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_st_ref_put(v___y_3952_, v___x_3972_);
v___y_3905_ = v___y_3950_;
v___y_3906_ = v___y_3953_;
v___y_3907_ = v___y_3955_;
v_exportedInfo_x3f_3908_ = v___y_3954_;
v___y_3909_ = v___y_3951_;
v___y_3910_ = v___y_3952_;
goto v___jp_3904_;
}
}
}
v_reusejp_3977_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___y_3982_; lean_object* v___y_3983_; uint8_t v___y_3984_; lean_object* v___y_3985_; lean_object* v___y_3986_; lean_object* v___y_3987_; lean_object* v_fst_4019_; lean_object* v_fst_4020_; uint8_t v_snd_4021_; lean_object* v_exportedInfo_x3f_4022_; lean_object* v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4034_; lean_object* v_exportedInfo_x3f_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; uint8_t v___y_4047_; lean_object* v___y_4052_; lean_object* v_toConstantVal_4053_; uint8_t v_safety_4054_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4061_; uint8_t v___y_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v_defn_4068_; lean_object* v___y_4069_; lean_object* v___y_4070_; 
v___x_3979_ = lean_st_ref_put(v_a_3741_, v___x_3978_);
v___x_3980_ = lean_box(0);
switch(lean_obj_tag(v_decl_3738_))
{
case 2:
{
lean_object* v_val_4093_; lean_object* v_exportedInfo_x3f_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___x_4102_; 
v_val_4093_ = lean_ctor_get(v_decl_3738_, 0);
v___x_4102_ = lean_st_ref_get(v_a_3741_);
if (v_forceExpose_3739_ == 0)
{
lean_object* v_env_4103_; lean_object* v___x_4104_; uint8_t v_isModule_4105_; 
v_env_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc_ref(v_env_4103_);
lean_dec(v___x_4102_);
v___x_4104_ = l_Lean_Environment_header(v_env_4103_);
lean_dec_ref(v_env_4103_);
v_isModule_4105_ = lean_ctor_get_uint8(v___x_4104_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4104_);
if (v_isModule_4105_ == 0)
{
v_exportedInfo_x3f_4095_ = v___x_3980_;
v___y_4096_ = v_a_3740_;
v___y_4097_ = v_a_3741_;
goto v___jp_4094_;
}
else
{
lean_object* v_toConstantVal_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_toConstantVal_4106_ = lean_ctor_get(v_val_4093_, 0);
lean_inc_ref(v_toConstantVal_4106_);
v___x_4107_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4107_, 0, v_toConstantVal_4106_);
lean_ctor_set_uint8(v___x_4107_, sizeof(void*)*1, v_hasTrace_3797_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
v___x_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
v_exportedInfo_x3f_4095_ = v___x_4109_;
v___y_4096_ = v_a_3740_;
v___y_4097_ = v_a_3741_;
goto v___jp_4094_;
}
}
else
{
lean_dec(v___x_4102_);
v_exportedInfo_x3f_4095_ = v___x_3980_;
v___y_4096_ = v_a_3740_;
v___y_4097_ = v_a_3741_;
goto v___jp_4094_;
}
v___jp_4094_:
{
lean_object* v_toConstantVal_4098_; lean_object* v_name_4099_; lean_object* v___x_4100_; uint8_t v___x_4101_; 
v_toConstantVal_4098_ = lean_ctor_get(v_val_4093_, 0);
v_name_4099_ = lean_ctor_get(v_toConstantVal_4098_, 0);
lean_inc_ref(v_val_4093_);
v___x_4100_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4100_, 0, v_val_4093_);
v___x_4101_ = 1;
lean_inc(v_name_4099_);
v_fst_4019_ = v_name_4099_;
v_fst_4020_ = v___x_4100_;
v_snd_4021_ = v___x_4101_;
v_exportedInfo_x3f_4022_ = v_exportedInfo_x3f_4095_;
v___y_4023_ = v___y_4096_;
v___y_4024_ = v___y_4097_;
goto v___jp_4018_;
}
}
case 1:
{
lean_object* v_val_4110_; 
v_val_4110_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref(v_val_4110_);
v_defn_4068_ = v_val_4110_;
v___y_4069_ = v_a_3740_;
v___y_4070_ = v_a_3741_;
goto v___jp_4067_;
}
case 5:
{
lean_object* v_defns_4111_; 
v_defns_4111_ = lean_ctor_get(v_decl_3738_, 0);
if (lean_obj_tag(v_defns_4111_) == 1)
{
lean_object* v_tail_4112_; 
v_tail_4112_ = lean_ctor_get(v_defns_4111_, 1);
if (lean_obj_tag(v_tail_4112_) == 0)
{
lean_object* v_head_4113_; 
v_head_4113_ = lean_ctor_get(v_defns_4111_, 0);
lean_inc(v_head_4113_);
v_defn_4068_ = v_head_4113_;
v___y_4069_ = v_a_3740_;
v___y_4070_ = v_a_3741_;
goto v___jp_4067_;
}
else
{
lean_object* v___x_4114_; 
v___x_4114_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v_a_3740_, v_a_3741_);
return v___x_4114_;
}
}
else
{
lean_object* v___x_4115_; 
v___x_4115_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v_a_3740_, v_a_3741_);
return v___x_4115_;
}
}
case 3:
{
lean_object* v_val_4116_; lean_object* v_exportedInfo_x3f_4118_; lean_object* v___y_4119_; lean_object* v___y_4120_; lean_object* v___x_4125_; lean_object* v___x_4126_; 
v_val_4116_ = lean_ctor_get(v_decl_3738_, 0);
v___x_4125_ = lean_st_ref_get(v_a_3741_);
v___x_4126_ = lean_st_ref_get(v_a_3741_);
if (v_forceExpose_3739_ == 0)
{
lean_object* v_env_4127_; lean_object* v_env_4128_; lean_object* v___x_4129_; uint8_t v_isModule_4130_; 
v_env_4127_ = lean_ctor_get(v___x_4125_, 0);
lean_inc_ref(v_env_4127_);
lean_dec(v___x_4125_);
v_env_4128_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_ref(v_env_4128_);
lean_dec(v___x_4126_);
v___x_4129_ = l_Lean_Environment_header(v_env_4127_);
lean_dec_ref(v_env_4127_);
v_isModule_4130_ = lean_ctor_get_uint8(v___x_4129_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4129_);
if (v_isModule_4130_ == 0)
{
lean_dec_ref(v_env_4128_);
v_exportedInfo_x3f_4118_ = v___x_3980_;
v___y_4119_ = v_a_3740_;
v___y_4120_ = v_a_3741_;
goto v___jp_4117_;
}
else
{
uint8_t v_isExporting_4131_; 
v_isExporting_4131_ = lean_ctor_get_uint8(v_env_4128_, sizeof(void*)*8);
lean_dec_ref(v_env_4128_);
if (v_isExporting_4131_ == 0)
{
lean_object* v_toConstantVal_4132_; uint8_t v_isUnsafe_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; 
v_toConstantVal_4132_ = lean_ctor_get(v_val_4116_, 0);
v_isUnsafe_4133_ = lean_ctor_get_uint8(v_val_4116_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4132_);
v___x_4134_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4134_, 0, v_toConstantVal_4132_);
lean_ctor_set_uint8(v___x_4134_, sizeof(void*)*1, v_isUnsafe_4133_);
v___x_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
v___x_4136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
v_exportedInfo_x3f_4118_ = v___x_4136_;
v___y_4119_ = v_a_3740_;
v___y_4120_ = v_a_3741_;
goto v___jp_4117_;
}
else
{
v_exportedInfo_x3f_4118_ = v___x_3980_;
v___y_4119_ = v_a_3740_;
v___y_4120_ = v_a_3741_;
goto v___jp_4117_;
}
}
}
else
{
lean_dec(v___x_4126_);
lean_dec(v___x_4125_);
v_exportedInfo_x3f_4118_ = v___x_3980_;
v___y_4119_ = v_a_3740_;
v___y_4120_ = v_a_3741_;
goto v___jp_4117_;
}
v___jp_4117_:
{
lean_object* v_toConstantVal_4121_; lean_object* v_name_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
v_toConstantVal_4121_ = lean_ctor_get(v_val_4116_, 0);
v_name_4122_ = lean_ctor_get(v_toConstantVal_4121_, 0);
lean_inc_ref(v_val_4116_);
v___x_4123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_val_4116_);
v___x_4124_ = 3;
lean_inc(v_name_4122_);
v_fst_4019_ = v_name_4122_;
v_fst_4020_ = v___x_4123_;
v_snd_4021_ = v___x_4124_;
v_exportedInfo_x3f_4022_ = v_exportedInfo_x3f_4118_;
v___y_4023_ = v___y_4119_;
v___y_4024_ = v___y_4120_;
goto v___jp_4018_;
}
}
case 0:
{
lean_object* v_val_4137_; lean_object* v_toConstantVal_4138_; lean_object* v_name_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v_val_4137_ = lean_ctor_get(v_decl_3738_, 0);
v_toConstantVal_4138_ = lean_ctor_get(v_val_4137_, 0);
v_name_4139_ = lean_ctor_get(v_toConstantVal_4138_, 0);
lean_inc_ref(v_val_4137_);
v___x_4140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4140_, 0, v_val_4137_);
v___x_4141_ = 2;
lean_inc(v_name_4139_);
v_fst_4019_ = v_name_4139_;
v_fst_4020_ = v___x_4140_;
v_snd_4021_ = v___x_4141_;
v_exportedInfo_x3f_4022_ = v___x_3980_;
v___y_4023_ = v_a_3740_;
v___y_4024_ = v_a_3741_;
goto v___jp_4018_;
}
default: 
{
lean_object* v___x_4142_; 
v___x_4142_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v_a_3740_, v_a_3741_);
return v___x_4142_;
}
}
v___jp_3981_:
{
lean_object* v___x_3988_; uint8_t v___x_3989_; 
lean_inc(v_decl_3738_);
v___x_3988_ = l_Lean_Declaration_getTopLevelNames(v_decl_3738_);
v___x_3989_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3988_);
lean_dec(v___x_3988_);
if (v___x_3989_ == 0)
{
if (lean_obj_tag(v___y_3985_) == 0)
{
if (v___x_3989_ == 0)
{
lean_object* v_options_3990_; uint8_t v_hasTrace_3991_; 
v_options_3990_ = lean_ctor_get(v___y_3986_, 1);
v_hasTrace_3991_ = lean_ctor_get_uint8(v_options_3990_, sizeof(void*)*1);
if (v_hasTrace_3991_ == 0)
{
v___y_3927_ = v___y_3982_;
v___y_3928_ = v___y_3983_;
v___y_3929_ = v___y_3984_;
v___y_3930_ = v___y_3986_;
v___y_3931_ = v___y_3987_;
goto v___jp_3926_;
}
else
{
lean_object* v_toCold_3992_; lean_object* v_inheritedTraceOptions_3993_; lean_object* v___x_3994_; uint8_t v___x_3995_; 
v_toCold_3992_ = lean_ctor_get(v___y_3986_, 0);
v_inheritedTraceOptions_3993_ = lean_ctor_get(v_toCold_3992_, 4);
v___x_3994_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3995_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3993_, v_options_3990_, v___x_3994_);
if (v___x_3995_ == 0)
{
v___y_3927_ = v___y_3982_;
v___y_3928_ = v___y_3983_;
v___y_3929_ = v___y_3984_;
v___y_3930_ = v___y_3986_;
v___y_3931_ = v___y_3987_;
goto v___jp_3926_;
}
else
{
lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3996_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3997_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_3996_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_3997_) == 0)
{
lean_dec_ref_known(v___x_3997_, 1);
v___y_3927_ = v___y_3982_;
v___y_3928_ = v___y_3983_;
v___y_3929_ = v___y_3984_;
v___y_3930_ = v___y_3986_;
v___y_3931_ = v___y_3987_;
goto v___jp_3926_;
}
else
{
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec(v_decl_3738_);
return v___x_3997_;
}
}
}
}
else
{
v___y_3950_ = v___y_3982_;
v___y_3951_ = v___y_3986_;
v___y_3952_ = v___y_3987_;
v___y_3953_ = v___y_3983_;
v___y_3954_ = v___y_3985_;
v___y_3955_ = v___y_3984_;
goto v___jp_3949_;
}
}
else
{
v___y_3950_ = v___y_3982_;
v___y_3951_ = v___y_3986_;
v___y_3952_ = v___y_3987_;
v___y_3953_ = v___y_3983_;
v___y_3954_ = v___y_3985_;
v___y_3955_ = v___y_3984_;
goto v___jp_3949_;
}
}
else
{
lean_object* v___x_3998_; lean_object* v___x_3999_; lean_object* v_a_4000_; uint8_t v___x_4001_; 
lean_dec(v___y_3985_);
v___x_3998_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3999_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3998_, v___y_3986_);
v_a_4000_ = lean_ctor_get(v___x_3999_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v___x_3999_);
v___x_4001_ = lean_unbox(v_a_4000_);
lean_dec(v_a_4000_);
if (v___x_4001_ == 0)
{
lean_object* v_options_4002_; uint8_t v_hasTrace_4003_; 
v_options_4002_ = lean_ctor_get(v___y_3986_, 1);
v_hasTrace_4003_ = lean_ctor_get_uint8(v_options_4002_, sizeof(void*)*1);
if (v_hasTrace_4003_ == 0)
{
v___y_3905_ = v___y_3982_;
v___y_3906_ = v___y_3983_;
v___y_3907_ = v___y_3984_;
v_exportedInfo_x3f_3908_ = v___x_3980_;
v___y_3909_ = v___y_3986_;
v___y_3910_ = v___y_3987_;
goto v___jp_3904_;
}
else
{
lean_object* v_toCold_4004_; lean_object* v_inheritedTraceOptions_4005_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v_toCold_4004_ = lean_ctor_get(v___y_3986_, 0);
v_inheritedTraceOptions_4005_ = lean_ctor_get(v_toCold_4004_, 4);
v___x_4006_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4007_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4005_, v_options_4002_, v___x_4006_);
if (v___x_4007_ == 0)
{
v___y_3905_ = v___y_3982_;
v___y_3906_ = v___y_3983_;
v___y_3907_ = v___y_3984_;
v_exportedInfo_x3f_3908_ = v___x_3980_;
v___y_3909_ = v___y_3986_;
v___y_3910_ = v___y_3987_;
goto v___jp_3904_;
}
else
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
v___x_4008_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4009_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4008_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_dec_ref_known(v___x_4009_, 1);
v___y_3905_ = v___y_3982_;
v___y_3906_ = v___y_3983_;
v___y_3907_ = v___y_3984_;
v_exportedInfo_x3f_3908_ = v___x_3980_;
v___y_3909_ = v___y_3986_;
v___y_3910_ = v___y_3987_;
goto v___jp_3904_;
}
else
{
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec(v_decl_3738_);
return v___x_4009_;
}
}
}
}
else
{
lean_object* v_options_4010_; uint8_t v_hasTrace_4011_; 
v_options_4010_ = lean_ctor_get(v___y_3986_, 1);
v_hasTrace_4011_ = lean_ctor_get_uint8(v_options_4010_, sizeof(void*)*1);
if (v_hasTrace_4011_ == 0)
{
v___y_3920_ = v___y_3982_;
v___y_3921_ = v___y_3983_;
v___y_3922_ = v___y_3984_;
v___y_3923_ = v___y_3986_;
v___y_3924_ = v___y_3987_;
goto v___jp_3919_;
}
else
{
lean_object* v_toCold_4012_; lean_object* v_inheritedTraceOptions_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; 
v_toCold_4012_ = lean_ctor_get(v___y_3986_, 0);
v_inheritedTraceOptions_4013_ = lean_ctor_get(v_toCold_4012_, 4);
v___x_4014_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4013_, v_options_4010_, v___x_4014_);
if (v___x_4015_ == 0)
{
v___y_3920_ = v___y_3982_;
v___y_3921_ = v___y_3983_;
v___y_3922_ = v___y_3984_;
v___y_3923_ = v___y_3986_;
v___y_3924_ = v___y_3987_;
goto v___jp_3919_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4017_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4016_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_dec_ref_known(v___x_4017_, 1);
v___y_3920_ = v___y_3982_;
v___y_3921_ = v___y_3983_;
v___y_3922_ = v___y_3984_;
v___y_3923_ = v___y_3986_;
v___y_3924_ = v___y_3987_;
goto v___jp_3919_;
}
else
{
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec(v_decl_3738_);
return v___x_4017_;
}
}
}
}
}
}
v___jp_4018_:
{
lean_object* v___x_4025_; lean_object* v_env_4026_; uint8_t v___x_4027_; 
v___x_4025_ = lean_st_ref_get(v___y_4024_);
v_env_4026_ = lean_ctor_get(v___x_4025_, 0);
lean_inc_ref(v_env_4026_);
lean_dec(v___x_4025_);
v___x_4027_ = l_Lean_Environment_containsOnBranch(v_env_4026_, v_fst_4019_);
lean_dec_ref(v_env_4026_);
if (v___x_4027_ == 0)
{
v___y_3982_ = v_fst_4019_;
v___y_3983_ = v_fst_4020_;
v___y_3984_ = v_snd_4021_;
v___y_3985_ = v_exportedInfo_x3f_4022_;
v___y_3986_ = v___y_4023_;
v___y_3987_ = v___y_4024_;
goto v___jp_3981_;
}
else
{
lean_object* v___x_4028_; lean_object* v_env_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; 
lean_dec(v_exportedInfo_x3f_4022_);
lean_dec_ref(v_fst_4020_);
lean_dec(v_decl_3738_);
v___x_4028_ = lean_st_ref_get(v___y_4024_);
v_env_4029_ = lean_ctor_get(v___x_4028_, 0);
lean_inc_ref(v_env_4029_);
lean_dec(v___x_4028_);
v___x_4030_ = lean_elab_environment_to_kernel_env(v_env_4029_);
v___x_4031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
lean_ctor_set(v___x_4031_, 1, v_fst_4019_);
v___x_4032_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4031_, v___y_4023_, v___y_4024_);
return v___x_4032_;
}
}
v___jp_4033_:
{
lean_object* v_toConstantVal_4038_; lean_object* v_name_4039_; lean_object* v___x_4040_; uint8_t v___x_4041_; 
v_toConstantVal_4038_ = lean_ctor_get(v___y_4034_, 0);
v_name_4039_ = lean_ctor_get(v_toConstantVal_4038_, 0);
lean_inc(v_name_4039_);
v___x_4040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4040_, 0, v___y_4034_);
v___x_4041_ = 0;
v_fst_4019_ = v_name_4039_;
v_fst_4020_ = v___x_4040_;
v_snd_4021_ = v___x_4041_;
v_exportedInfo_x3f_4022_ = v_exportedInfo_x3f_4035_;
v___y_4023_ = v___y_4036_;
v___y_4024_ = v___y_4037_;
goto v___jp_4018_;
}
v___jp_4042_:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4048_, 0, v___y_4044_);
lean_ctor_set_uint8(v___x_4048_, sizeof(void*)*1, v___y_4047_);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
v___x_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
v___y_4034_ = v___y_4043_;
v_exportedInfo_x3f_4035_ = v___x_4050_;
v___y_4036_ = v___y_4046_;
v___y_4037_ = v___y_4045_;
goto v___jp_4033_;
}
v___jp_4051_:
{
uint8_t v___x_4058_; uint8_t v___x_4059_; 
v___x_4058_ = 1;
v___x_4059_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4054_, v___x_4058_);
if (v___x_4059_ == 0)
{
v___y_4043_ = v___y_4052_;
v___y_4044_ = v_toConstantVal_4053_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4055_;
goto v___jp_4042_;
}
else
{
v___y_4043_ = v___y_4052_;
v___y_4044_ = v_toConstantVal_4053_;
v___y_4045_ = v___y_4057_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v_hasTrace_3797_;
goto v___jp_4042_;
}
}
v___jp_4060_:
{
lean_object* v_toConstantVal_4065_; uint8_t v_safety_4066_; 
v_toConstantVal_4065_ = lean_ctor_get(v___y_4061_, 0);
lean_inc_ref(v_toConstantVal_4065_);
v_safety_4066_ = lean_ctor_get_uint8(v___y_4061_, sizeof(void*)*4);
v___y_4052_ = v___y_4061_;
v_toConstantVal_4053_ = v_toConstantVal_4065_;
v_safety_4054_ = v_safety_4066_;
v___y_4055_ = v___y_4062_;
v___y_4056_ = v___y_4063_;
v___y_4057_ = v___y_4064_;
goto v___jp_4051_;
}
v___jp_4067_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = lean_st_ref_get(v___y_4070_);
v___x_4072_ = lean_st_ref_get(v___y_4070_);
if (v_forceExpose_3739_ == 0)
{
lean_object* v_env_4073_; lean_object* v_env_4074_; lean_object* v___x_4075_; uint8_t v_isModule_4076_; 
v_env_4073_ = lean_ctor_get(v___x_4071_, 0);
lean_inc_ref(v_env_4073_);
lean_dec(v___x_4071_);
v_env_4074_ = lean_ctor_get(v___x_4072_, 0);
lean_inc_ref(v_env_4074_);
lean_dec(v___x_4072_);
v___x_4075_ = l_Lean_Environment_header(v_env_4073_);
lean_dec_ref(v_env_4073_);
v_isModule_4076_ = lean_ctor_get_uint8(v___x_4075_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4075_);
if (v_isModule_4076_ == 0)
{
lean_dec_ref(v_env_4074_);
v___y_4034_ = v_defn_4068_;
v_exportedInfo_x3f_4035_ = v___x_3980_;
v___y_4036_ = v___y_4069_;
v___y_4037_ = v___y_4070_;
goto v___jp_4033_;
}
else
{
uint8_t v_isExporting_4077_; 
v_isExporting_4077_ = lean_ctor_get_uint8(v_env_4074_, sizeof(void*)*8);
lean_dec_ref(v_env_4074_);
if (v_isExporting_4077_ == 0)
{
lean_object* v_options_4078_; uint8_t v_hasTrace_4079_; 
v_options_4078_ = lean_ctor_get(v___y_4069_, 1);
v_hasTrace_4079_ = lean_ctor_get_uint8(v_options_4078_, sizeof(void*)*1);
if (v_hasTrace_4079_ == 0)
{
v___y_4061_ = v_defn_4068_;
v___y_4062_ = v_isModule_4076_;
v___y_4063_ = v___y_4069_;
v___y_4064_ = v___y_4070_;
goto v___jp_4060_;
}
else
{
lean_object* v_toCold_4080_; lean_object* v_inheritedTraceOptions_4081_; lean_object* v___x_4082_; uint8_t v___x_4083_; 
v_toCold_4080_ = lean_ctor_get(v___y_4069_, 0);
v_inheritedTraceOptions_4081_ = lean_ctor_get(v_toCold_4080_, 4);
v___x_4082_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4083_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4081_, v_options_4078_, v___x_4082_);
if (v___x_4083_ == 0)
{
v___y_4061_ = v_defn_4068_;
v___y_4062_ = v_isModule_4076_;
v___y_4063_ = v___y_4069_;
v___y_4064_ = v___y_4070_;
goto v___jp_4060_;
}
else
{
lean_object* v_toConstantVal_4084_; uint8_t v_safety_4085_; lean_object* v_name_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v_toConstantVal_4084_ = lean_ctor_get(v_defn_4068_, 0);
lean_inc_ref(v_toConstantVal_4084_);
v_safety_4085_ = lean_ctor_get_uint8(v_defn_4068_, sizeof(void*)*4);
v_name_4086_ = lean_ctor_get(v_toConstantVal_4084_, 0);
v___x_4087_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4086_);
v___x_4088_ = l_Lean_MessageData_ofName(v_name_4086_);
v___x_4089_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4087_);
lean_ctor_set(v___x_4089_, 1, v___x_4088_);
v___x_4090_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4089_);
lean_ctor_set(v___x_4091_, 1, v___x_4090_);
v___x_4092_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4091_, v___y_4069_, v___y_4070_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_dec_ref_known(v___x_4092_, 1);
v___y_4052_ = v_defn_4068_;
v_toConstantVal_4053_ = v_toConstantVal_4084_;
v_safety_4054_ = v_safety_4085_;
v___y_4055_ = v_isModule_4076_;
v___y_4056_ = v___y_4069_;
v___y_4057_ = v___y_4070_;
goto v___jp_4051_;
}
else
{
lean_dec_ref(v_toConstantVal_4084_);
lean_dec_ref(v_defn_4068_);
lean_dec(v_decl_3738_);
return v___x_4092_;
}
}
}
}
else
{
v___y_4034_ = v_defn_4068_;
v_exportedInfo_x3f_4035_ = v___x_3980_;
v___y_4036_ = v___y_4069_;
v___y_4037_ = v___y_4070_;
goto v___jp_4033_;
}
}
}
else
{
lean_dec(v___x_4072_);
lean_dec(v___x_4071_);
v___y_4034_ = v_defn_4068_;
v_exportedInfo_x3f_4035_ = v___x_3980_;
v___y_4036_ = v___y_4069_;
v___y_4037_ = v___y_4070_;
goto v___jp_4033_;
}
}
}
}
}
else
{
lean_object* v_inheritedTraceOptions_4146_; lean_object* v___f_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v_a_4154_; lean_object* v___y_4164_; lean_object* v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4186_; lean_object* v___y_4187_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v_a_4200_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v___y_4215_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; uint8_t v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; 
v_inheritedTraceOptions_4146_ = lean_ctor_get(v_toCold_3796_, 4);
lean_inc(v_decl_3738_);
v___f_4147_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4147_, 0, v_decl_3738_);
v___x_4148_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4149_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4146_, v_options_3795_, v___x_4149_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4450_; uint8_t v___x_4451_; lean_object* v___y_4453_; lean_object* v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4457_; lean_object* v___y_4458_; lean_object* v___y_4459_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4526_; lean_object* v___y_4527_; lean_object* v___y_4528_; lean_object* v___y_4529_; lean_object* v___y_4530_; lean_object* v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; uint8_t v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4557_; lean_object* v___y_4558_; uint8_t v___y_4559_; lean_object* v_exportedInfo_x3f_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4572_; lean_object* v___y_4573_; uint8_t v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; lean_object* v___y_4579_; lean_object* v___y_4580_; uint8_t v___y_4581_; lean_object* v___y_4582_; lean_object* v___y_4583_; 
v___x_4450_ = l_Lean_trace_profiler;
v___x_4451_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3795_, v___x_4450_);
if (v___x_4451_ == 0)
{
lean_object* v___x_4585_; lean_object* v_env_4586_; lean_object* v_nextMacroScope_4587_; lean_object* v_ngen_4588_; lean_object* v_auxDeclNGen_4589_; lean_object* v_traceState_4590_; lean_object* v_messages_4591_; lean_object* v_infoState_4592_; lean_object* v_snapshotTasks_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v___f_4147_);
v___x_4585_ = lean_st_ref_take(v_a_3741_);
v_env_4586_ = lean_ctor_get(v___x_4585_, 0);
v_nextMacroScope_4587_ = lean_ctor_get(v___x_4585_, 1);
v_ngen_4588_ = lean_ctor_get(v___x_4585_, 2);
v_auxDeclNGen_4589_ = lean_ctor_get(v___x_4585_, 3);
v_traceState_4590_ = lean_ctor_get(v___x_4585_, 4);
v_messages_4591_ = lean_ctor_get(v___x_4585_, 6);
v_infoState_4592_ = lean_ctor_get(v___x_4585_, 7);
v_snapshotTasks_4593_ = lean_ctor_get(v___x_4585_, 8);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4836_ == 0)
{
lean_object* v_unused_4837_; 
v_unused_4837_ = lean_ctor_get(v___x_4585_, 5);
lean_dec(v_unused_4837_);
v___x_4595_ = v___x_4585_;
v_isShared_4596_ = v_isSharedCheck_4836_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_snapshotTasks_4593_);
lean_inc(v_infoState_4592_);
lean_inc(v_messages_4591_);
lean_inc(v_traceState_4590_);
lean_inc(v_auxDeclNGen_4589_);
lean_inc(v_ngen_4588_);
lean_inc(v_nextMacroScope_4587_);
lean_inc(v_env_4586_);
lean_dec(v___x_4585_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4836_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v___x_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___y_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; lean_object* v___y_4604_; uint8_t v___y_4605_; lean_object* v___y_4606_; lean_object* v___x_4629_; 
lean_inc(v_decl_3738_);
v___x_4597_ = l_Lean_Declaration_getNames(v_decl_3738_);
v___x_4598_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4586_, v___x_4597_);
v___x_4599_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 5, v___x_4599_);
lean_ctor_set(v___x_4595_, 0, v___x_4598_);
v___x_4629_ = v___x_4595_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v___x_4598_);
lean_ctor_set(v_reuseFailAlloc_4835_, 1, v_nextMacroScope_4587_);
lean_ctor_set(v_reuseFailAlloc_4835_, 2, v_ngen_4588_);
lean_ctor_set(v_reuseFailAlloc_4835_, 3, v_auxDeclNGen_4589_);
lean_ctor_set(v_reuseFailAlloc_4835_, 4, v_traceState_4590_);
lean_ctor_set(v_reuseFailAlloc_4835_, 5, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4835_, 6, v_messages_4591_);
lean_ctor_set(v_reuseFailAlloc_4835_, 7, v_infoState_4592_);
lean_ctor_set(v_reuseFailAlloc_4835_, 8, v_snapshotTasks_4593_);
v___x_4629_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4628_;
}
v___jp_4600_:
{
lean_object* v___x_4607_; lean_object* v_env_4608_; lean_object* v_nextMacroScope_4609_; lean_object* v_ngen_4610_; lean_object* v_auxDeclNGen_4611_; lean_object* v_traceState_4612_; lean_object* v_messages_4613_; lean_object* v_infoState_4614_; lean_object* v_snapshotTasks_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4626_; 
v___x_4607_ = lean_st_ref_take(v___y_4606_);
v_env_4608_ = lean_ctor_get(v___x_4607_, 0);
v_nextMacroScope_4609_ = lean_ctor_get(v___x_4607_, 1);
v_ngen_4610_ = lean_ctor_get(v___x_4607_, 2);
v_auxDeclNGen_4611_ = lean_ctor_get(v___x_4607_, 3);
v_traceState_4612_ = lean_ctor_get(v___x_4607_, 4);
v_messages_4613_ = lean_ctor_get(v___x_4607_, 6);
v_infoState_4614_ = lean_ctor_get(v___x_4607_, 7);
v_snapshotTasks_4615_ = lean_ctor_get(v___x_4607_, 8);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4607_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4607_, 5);
lean_dec(v_unused_4627_);
v___x_4617_ = v___x_4607_;
v_isShared_4618_ = v_isSharedCheck_4626_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_snapshotTasks_4615_);
lean_inc(v_infoState_4614_);
lean_inc(v_messages_4613_);
lean_inc(v_traceState_4612_);
lean_inc(v_auxDeclNGen_4611_);
lean_inc(v_ngen_4610_);
lean_inc(v_nextMacroScope_4609_);
lean_inc(v_env_4608_);
lean_dec(v___x_4607_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4626_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v___x_4619_; lean_object* v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4619_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4620_ = lean_box(v___y_4605_);
lean_inc(v___y_4604_);
v___x_4621_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4619_, v_env_4608_, v___y_4604_, v___x_4620_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 5, v___x_4599_);
lean_ctor_set(v___x_4617_, 0, v___x_4621_);
v___x_4623_ = v___x_4617_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_nextMacroScope_4609_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_ngen_4610_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_auxDeclNGen_4611_);
lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_traceState_4612_);
lean_ctor_set(v_reuseFailAlloc_4625_, 5, v___x_4599_);
lean_ctor_set(v_reuseFailAlloc_4625_, 6, v_messages_4613_);
lean_ctor_set(v_reuseFailAlloc_4625_, 7, v_infoState_4614_);
lean_ctor_set(v_reuseFailAlloc_4625_, 8, v_snapshotTasks_4615_);
v___x_4623_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_st_ref_put(v___y_4606_, v___x_4623_);
v___y_4557_ = v___y_4601_;
v___y_4558_ = v___y_4604_;
v___y_4559_ = v___y_4605_;
v_exportedInfo_x3f_4560_ = v___y_4602_;
v___y_4561_ = v___y_4603_;
v___y_4562_ = v___y_4606_;
goto v___jp_4556_;
}
}
}
v_reusejp_4628_:
{
lean_object* v___x_4630_; lean_object* v___y_4632_; lean_object* v_inheritedTraceOptions_4633_; lean_object* v_options_4634_; lean_object* v___y_4635_; lean_object* v___x_4641_; lean_object* v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; uint8_t v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v_fst_4677_; lean_object* v_fst_4678_; uint8_t v_snd_4679_; lean_object* v_exportedInfo_x3f_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4692_; lean_object* v_exportedInfo_x3f_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; uint8_t v___y_4705_; uint8_t v___y_4710_; lean_object* v___y_4711_; lean_object* v_toConstantVal_4712_; uint8_t v_safety_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; uint8_t v___y_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; uint8_t v___y_4729_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v_defn_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; 
v___x_4630_ = lean_st_ref_put(v_a_3741_, v___x_4629_);
v___x_4641_ = lean_box(0);
switch(lean_obj_tag(v_decl_3738_))
{
case 2:
{
lean_object* v_val_4763_; lean_object* v_exportedInfo_x3f_4765_; lean_object* v___y_4766_; lean_object* v___y_4767_; lean_object* v___y_4773_; lean_object* v___y_4774_; lean_object* v___x_4779_; lean_object* v_env_4780_; 
v_val_4763_ = lean_ctor_get(v_decl_3738_, 0);
v___x_4779_ = lean_st_ref_get(v_a_3741_);
v_env_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_ref(v_env_4780_);
lean_dec(v___x_4779_);
if (v_forceExpose_3739_ == 0)
{
goto v___jp_4781_;
}
else
{
if (v___x_4451_ == 0)
{
lean_dec_ref(v_env_4780_);
v_exportedInfo_x3f_4765_ = v___x_4641_;
v___y_4766_ = v_a_3740_;
v___y_4767_ = v_a_3741_;
goto v___jp_4764_;
}
else
{
goto v___jp_4781_;
}
}
v___jp_4764_:
{
lean_object* v_toConstantVal_4768_; lean_object* v_name_4769_; lean_object* v___x_4770_; uint8_t v___x_4771_; 
v_toConstantVal_4768_ = lean_ctor_get(v_val_4763_, 0);
v_name_4769_ = lean_ctor_get(v_toConstantVal_4768_, 0);
lean_inc_ref(v_val_4763_);
v___x_4770_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4770_, 0, v_val_4763_);
v___x_4771_ = 1;
lean_inc(v_name_4769_);
v_fst_4677_ = v_name_4769_;
v_fst_4678_ = v___x_4770_;
v_snd_4679_ = v___x_4771_;
v_exportedInfo_x3f_4680_ = v_exportedInfo_x3f_4765_;
v___y_4681_ = v___y_4766_;
v___y_4682_ = v___y_4767_;
goto v___jp_4676_;
}
v___jp_4772_:
{
lean_object* v_toConstantVal_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; lean_object* v___x_4778_; 
v_toConstantVal_4775_ = lean_ctor_get(v_val_4763_, 0);
lean_inc_ref(v_toConstantVal_4775_);
v___x_4776_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4776_, 0, v_toConstantVal_4775_);
lean_ctor_set_uint8(v___x_4776_, sizeof(void*)*1, v___x_4451_);
v___x_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4777_, 0, v___x_4776_);
v___x_4778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4778_, 0, v___x_4777_);
v_exportedInfo_x3f_4765_ = v___x_4778_;
v___y_4766_ = v___y_4773_;
v___y_4767_ = v___y_4774_;
goto v___jp_4764_;
}
v___jp_4781_:
{
lean_object* v___x_4782_; uint8_t v_isModule_4783_; 
v___x_4782_ = l_Lean_Environment_header(v_env_4780_);
lean_dec_ref(v_env_4780_);
v_isModule_4783_ = lean_ctor_get_uint8(v___x_4782_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4782_);
if (v_isModule_4783_ == 0)
{
v_exportedInfo_x3f_4765_ = v___x_4641_;
v___y_4766_ = v_a_3740_;
v___y_4767_ = v_a_3741_;
goto v___jp_4764_;
}
else
{
if (v___x_4150_ == 0)
{
v___y_4773_ = v_a_3740_;
v___y_4774_ = v_a_3741_;
goto v___jp_4772_;
}
else
{
lean_object* v_toConstantVal_4784_; lean_object* v_name_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v_toConstantVal_4784_ = lean_ctor_get(v_val_4763_, 0);
v_name_4785_ = lean_ctor_get(v_toConstantVal_4784_, 0);
v___x_4786_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4785_);
v___x_4787_ = l_Lean_MessageData_ofName(v_name_4785_);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4790_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4788_);
lean_ctor_set(v___x_4790_, 1, v___x_4789_);
v___x_4791_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4790_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_dec_ref_known(v___x_4791_, 1);
v___y_4773_ = v_a_3740_;
v___y_4774_ = v_a_3741_;
goto v___jp_4772_;
}
else
{
lean_dec_ref_known(v_decl_3738_, 1);
return v___x_4791_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4792_; 
v_val_4792_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref(v_val_4792_);
v_defn_4754_ = v_val_4792_;
v___y_4755_ = v_a_3740_;
v___y_4756_ = v_a_3741_;
goto v___jp_4753_;
}
case 5:
{
lean_object* v_defns_4793_; 
v_defns_4793_ = lean_ctor_get(v_decl_3738_, 0);
if (lean_obj_tag(v_defns_4793_) == 1)
{
lean_object* v_tail_4794_; 
v_tail_4794_ = lean_ctor_get(v_defns_4793_, 1);
if (lean_obj_tag(v_tail_4794_) == 0)
{
lean_object* v_head_4795_; 
v_head_4795_ = lean_ctor_get(v_defns_4793_, 0);
lean_inc(v_head_4795_);
v_defn_4754_ = v_head_4795_;
v___y_4755_ = v_a_3740_;
v___y_4756_ = v_a_3741_;
goto v___jp_4753_;
}
else
{
v___y_4632_ = v_a_3740_;
v_inheritedTraceOptions_4633_ = v_inheritedTraceOptions_4146_;
v_options_4634_ = v_options_3795_;
v___y_4635_ = v_a_3741_;
goto v___jp_4631_;
}
}
else
{
v___y_4632_ = v_a_3740_;
v_inheritedTraceOptions_4633_ = v_inheritedTraceOptions_4146_;
v_options_4634_ = v_options_3795_;
v___y_4635_ = v_a_3741_;
goto v___jp_4631_;
}
}
case 3:
{
lean_object* v_val_4796_; lean_object* v_exportedInfo_x3f_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; lean_object* v___y_4806_; lean_object* v___y_4807_; lean_object* v___x_4813_; lean_object* v___x_4814_; lean_object* v_env_4824_; lean_object* v_env_4825_; 
v_val_4796_ = lean_ctor_get(v_decl_3738_, 0);
v___x_4813_ = lean_st_ref_get(v_a_3741_);
v___x_4814_ = lean_st_ref_get(v_a_3741_);
v_env_4824_ = lean_ctor_get(v___x_4813_, 0);
lean_inc_ref(v_env_4824_);
lean_dec(v___x_4813_);
v_env_4825_ = lean_ctor_get(v___x_4814_, 0);
lean_inc_ref(v_env_4825_);
lean_dec(v___x_4814_);
if (v_forceExpose_3739_ == 0)
{
goto v___jp_4826_;
}
else
{
if (v___x_4451_ == 0)
{
lean_dec_ref(v_env_4825_);
lean_dec_ref(v_env_4824_);
v_exportedInfo_x3f_4798_ = v___x_4641_;
v___y_4799_ = v_a_3740_;
v___y_4800_ = v_a_3741_;
goto v___jp_4797_;
}
else
{
goto v___jp_4826_;
}
}
v___jp_4797_:
{
lean_object* v_toConstantVal_4801_; lean_object* v_name_4802_; lean_object* v___x_4803_; uint8_t v___x_4804_; 
v_toConstantVal_4801_ = lean_ctor_get(v_val_4796_, 0);
v_name_4802_ = lean_ctor_get(v_toConstantVal_4801_, 0);
lean_inc_ref(v_val_4796_);
v___x_4803_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4803_, 0, v_val_4796_);
v___x_4804_ = 3;
lean_inc(v_name_4802_);
v_fst_4677_ = v_name_4802_;
v_fst_4678_ = v___x_4803_;
v_snd_4679_ = v___x_4804_;
v_exportedInfo_x3f_4680_ = v_exportedInfo_x3f_4798_;
v___y_4681_ = v___y_4799_;
v___y_4682_ = v___y_4800_;
goto v___jp_4676_;
}
v___jp_4805_:
{
lean_object* v_toConstantVal_4808_; uint8_t v_isUnsafe_4809_; lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4812_; 
v_toConstantVal_4808_ = lean_ctor_get(v_val_4796_, 0);
v_isUnsafe_4809_ = lean_ctor_get_uint8(v_val_4796_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4808_);
v___x_4810_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4810_, 0, v_toConstantVal_4808_);
lean_ctor_set_uint8(v___x_4810_, sizeof(void*)*1, v_isUnsafe_4809_);
v___x_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4811_, 0, v___x_4810_);
v___x_4812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4812_, 0, v___x_4811_);
v_exportedInfo_x3f_4798_ = v___x_4812_;
v___y_4799_ = v___y_4806_;
v___y_4800_ = v___y_4807_;
goto v___jp_4797_;
}
v___jp_4815_:
{
if (v___x_4150_ == 0)
{
v___y_4806_ = v_a_3740_;
v___y_4807_ = v_a_3741_;
goto v___jp_4805_;
}
else
{
lean_object* v_toConstantVal_4816_; lean_object* v_name_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v_toConstantVal_4816_ = lean_ctor_get(v_val_4796_, 0);
v_name_4817_ = lean_ctor_get(v_toConstantVal_4816_, 0);
v___x_4818_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4817_);
v___x_4819_ = l_Lean_MessageData_ofName(v_name_4817_);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4822_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_dec_ref_known(v___x_4823_, 1);
v___y_4806_ = v_a_3740_;
v___y_4807_ = v_a_3741_;
goto v___jp_4805_;
}
else
{
lean_dec_ref_known(v_decl_3738_, 1);
return v___x_4823_;
}
}
}
v___jp_4826_:
{
lean_object* v___x_4827_; uint8_t v_isModule_4828_; 
v___x_4827_ = l_Lean_Environment_header(v_env_4824_);
lean_dec_ref(v_env_4824_);
v_isModule_4828_ = lean_ctor_get_uint8(v___x_4827_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4827_);
if (v_isModule_4828_ == 0)
{
lean_dec_ref(v_env_4825_);
v_exportedInfo_x3f_4798_ = v___x_4641_;
v___y_4799_ = v_a_3740_;
v___y_4800_ = v_a_3741_;
goto v___jp_4797_;
}
else
{
uint8_t v_isExporting_4829_; 
v_isExporting_4829_ = lean_ctor_get_uint8(v_env_4825_, sizeof(void*)*8);
lean_dec_ref(v_env_4825_);
if (v_isExporting_4829_ == 0)
{
goto v___jp_4815_;
}
else
{
if (v___x_4451_ == 0)
{
v_exportedInfo_x3f_4798_ = v___x_4641_;
v___y_4799_ = v_a_3740_;
v___y_4800_ = v_a_3741_;
goto v___jp_4797_;
}
else
{
goto v___jp_4815_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4830_; lean_object* v_toConstantVal_4831_; lean_object* v_name_4832_; lean_object* v___x_4833_; uint8_t v___x_4834_; 
v_val_4830_ = lean_ctor_get(v_decl_3738_, 0);
v_toConstantVal_4831_ = lean_ctor_get(v_val_4830_, 0);
v_name_4832_ = lean_ctor_get(v_toConstantVal_4831_, 0);
lean_inc_ref(v_val_4830_);
v___x_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4833_, 0, v_val_4830_);
v___x_4834_ = 2;
lean_inc(v_name_4832_);
v_fst_4677_ = v_name_4832_;
v_fst_4678_ = v___x_4833_;
v_snd_4679_ = v___x_4834_;
v_exportedInfo_x3f_4680_ = v___x_4641_;
v___y_4681_ = v_a_3740_;
v___y_4682_ = v_a_3741_;
goto v___jp_4676_;
}
default: 
{
v___y_4632_ = v_a_3740_;
v_inheritedTraceOptions_4633_ = v_inheritedTraceOptions_4146_;
v_options_4634_ = v_options_3795_;
v___y_4635_ = v_a_3741_;
goto v___jp_4631_;
}
}
v___jp_4631_:
{
uint8_t v___x_4636_; 
v___x_4636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4633_, v_options_4634_, v___x_4149_);
if (v___x_4636_ == 0)
{
lean_object* v___x_4637_; 
v___x_4637_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v___y_4632_, v___y_4635_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4638_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4639_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4638_, v___y_4632_, v___y_4635_);
if (lean_obj_tag(v___x_4639_) == 0)
{
lean_object* v___x_4640_; 
lean_dec_ref_known(v___x_4639_, 1);
v___x_4640_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v___y_4632_, v___y_4635_);
return v___x_4640_;
}
else
{
lean_dec(v_decl_3738_);
return v___x_4639_;
}
}
}
v___jp_4642_:
{
lean_object* v___x_4649_; uint8_t v___x_4650_; 
lean_inc(v_decl_3738_);
v___x_4649_ = l_Lean_Declaration_getTopLevelNames(v_decl_3738_);
v___x_4650_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4649_);
lean_dec(v___x_4649_);
if (v___x_4650_ == 0)
{
if (lean_obj_tag(v___y_4644_) == 0)
{
if (v___x_4650_ == 0)
{
lean_object* v_options_4651_; uint8_t v_hasTrace_4652_; 
v_options_4651_ = lean_ctor_get(v___y_4647_, 1);
v_hasTrace_4652_ = lean_ctor_get_uint8(v_options_4651_, sizeof(void*)*1);
if (v_hasTrace_4652_ == 0)
{
v___y_4572_ = v___y_4643_;
v___y_4573_ = v___y_4645_;
v___y_4574_ = v___y_4646_;
v___y_4575_ = v___y_4647_;
v___y_4576_ = v___y_4648_;
goto v___jp_4571_;
}
else
{
lean_object* v_toCold_4653_; lean_object* v_inheritedTraceOptions_4654_; uint8_t v___x_4655_; 
v_toCold_4653_ = lean_ctor_get(v___y_4647_, 0);
v_inheritedTraceOptions_4654_ = lean_ctor_get(v_toCold_4653_, 4);
v___x_4655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4654_, v_options_4651_, v___x_4149_);
if (v___x_4655_ == 0)
{
v___y_4572_ = v___y_4643_;
v___y_4573_ = v___y_4645_;
v___y_4574_ = v___y_4646_;
v___y_4575_ = v___y_4647_;
v___y_4576_ = v___y_4648_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4656_; lean_object* v___x_4657_; 
v___x_4656_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4657_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4656_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4657_) == 0)
{
lean_dec_ref_known(v___x_4657_, 1);
v___y_4572_ = v___y_4643_;
v___y_4573_ = v___y_4645_;
v___y_4574_ = v___y_4646_;
v___y_4575_ = v___y_4647_;
v___y_4576_ = v___y_4648_;
goto v___jp_4571_;
}
else
{
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4643_);
lean_dec(v_decl_3738_);
return v___x_4657_;
}
}
}
}
else
{
v___y_4601_ = v___y_4643_;
v___y_4602_ = v___y_4644_;
v___y_4603_ = v___y_4647_;
v___y_4604_ = v___y_4645_;
v___y_4605_ = v___y_4646_;
v___y_4606_ = v___y_4648_;
goto v___jp_4600_;
}
}
else
{
v___y_4601_ = v___y_4643_;
v___y_4602_ = v___y_4644_;
v___y_4603_ = v___y_4647_;
v___y_4604_ = v___y_4645_;
v___y_4605_ = v___y_4646_;
v___y_4606_ = v___y_4648_;
goto v___jp_4600_;
}
}
else
{
lean_object* v___x_4658_; lean_object* v___x_4659_; lean_object* v_a_4660_; uint8_t v___x_4661_; 
lean_dec(v___y_4644_);
v___x_4658_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4659_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4658_, v___y_4647_);
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc(v_a_4660_);
lean_dec_ref(v___x_4659_);
v___x_4661_ = lean_unbox(v_a_4660_);
lean_dec(v_a_4660_);
if (v___x_4661_ == 0)
{
lean_object* v_options_4662_; uint8_t v_hasTrace_4663_; 
v_options_4662_ = lean_ctor_get(v___y_4647_, 1);
v_hasTrace_4663_ = lean_ctor_get_uint8(v_options_4662_, sizeof(void*)*1);
if (v_hasTrace_4663_ == 0)
{
v___y_4557_ = v___y_4643_;
v___y_4558_ = v___y_4645_;
v___y_4559_ = v___y_4646_;
v_exportedInfo_x3f_4560_ = v___x_4641_;
v___y_4561_ = v___y_4647_;
v___y_4562_ = v___y_4648_;
goto v___jp_4556_;
}
else
{
lean_object* v_toCold_4664_; lean_object* v_inheritedTraceOptions_4665_; uint8_t v___x_4666_; 
v_toCold_4664_ = lean_ctor_get(v___y_4647_, 0);
v_inheritedTraceOptions_4665_ = lean_ctor_get(v_toCold_4664_, 4);
v___x_4666_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4665_, v_options_4662_, v___x_4149_);
if (v___x_4666_ == 0)
{
v___y_4557_ = v___y_4643_;
v___y_4558_ = v___y_4645_;
v___y_4559_ = v___y_4646_;
v_exportedInfo_x3f_4560_ = v___x_4641_;
v___y_4561_ = v___y_4647_;
v___y_4562_ = v___y_4648_;
goto v___jp_4556_;
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4667_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4668_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4667_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_dec_ref_known(v___x_4668_, 1);
v___y_4557_ = v___y_4643_;
v___y_4558_ = v___y_4645_;
v___y_4559_ = v___y_4646_;
v_exportedInfo_x3f_4560_ = v___x_4641_;
v___y_4561_ = v___y_4647_;
v___y_4562_ = v___y_4648_;
goto v___jp_4556_;
}
else
{
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4643_);
lean_dec(v_decl_3738_);
return v___x_4668_;
}
}
}
}
else
{
lean_object* v_options_4669_; uint8_t v_hasTrace_4670_; 
v_options_4669_ = lean_ctor_get(v___y_4647_, 1);
v_hasTrace_4670_ = lean_ctor_get_uint8(v_options_4669_, sizeof(void*)*1);
if (v_hasTrace_4670_ == 0)
{
v___y_4579_ = v___y_4643_;
v___y_4580_ = v___y_4645_;
v___y_4581_ = v___y_4646_;
v___y_4582_ = v___y_4647_;
v___y_4583_ = v___y_4648_;
goto v___jp_4578_;
}
else
{
lean_object* v_toCold_4671_; lean_object* v_inheritedTraceOptions_4672_; uint8_t v___x_4673_; 
v_toCold_4671_ = lean_ctor_get(v___y_4647_, 0);
v_inheritedTraceOptions_4672_ = lean_ctor_get(v_toCold_4671_, 4);
v___x_4673_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4672_, v_options_4669_, v___x_4149_);
if (v___x_4673_ == 0)
{
v___y_4579_ = v___y_4643_;
v___y_4580_ = v___y_4645_;
v___y_4581_ = v___y_4646_;
v___y_4582_ = v___y_4647_;
v___y_4583_ = v___y_4648_;
goto v___jp_4578_;
}
else
{
lean_object* v___x_4674_; lean_object* v___x_4675_; 
v___x_4674_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4675_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4674_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_dec_ref_known(v___x_4675_, 1);
v___y_4579_ = v___y_4643_;
v___y_4580_ = v___y_4645_;
v___y_4581_ = v___y_4646_;
v___y_4582_ = v___y_4647_;
v___y_4583_ = v___y_4648_;
goto v___jp_4578_;
}
else
{
lean_dec(v___y_4645_);
lean_dec_ref(v___y_4643_);
lean_dec(v_decl_3738_);
return v___x_4675_;
}
}
}
}
}
}
v___jp_4676_:
{
lean_object* v___x_4683_; lean_object* v_env_4684_; uint8_t v___x_4685_; 
v___x_4683_ = lean_st_ref_get(v___y_4682_);
v_env_4684_ = lean_ctor_get(v___x_4683_, 0);
lean_inc_ref(v_env_4684_);
lean_dec(v___x_4683_);
v___x_4685_ = l_Lean_Environment_containsOnBranch(v_env_4684_, v_fst_4677_);
lean_dec_ref(v_env_4684_);
if (v___x_4685_ == 0)
{
v___y_4643_ = v_fst_4678_;
v___y_4644_ = v_exportedInfo_x3f_4680_;
v___y_4645_ = v_fst_4677_;
v___y_4646_ = v_snd_4679_;
v___y_4647_ = v___y_4681_;
v___y_4648_ = v___y_4682_;
goto v___jp_4642_;
}
else
{
lean_object* v___x_4686_; lean_object* v_env_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_dec(v_exportedInfo_x3f_4680_);
lean_dec_ref(v_fst_4678_);
lean_dec(v_decl_3738_);
v___x_4686_ = lean_st_ref_get(v___y_4682_);
v_env_4687_ = lean_ctor_get(v___x_4686_, 0);
lean_inc_ref(v_env_4687_);
lean_dec(v___x_4686_);
v___x_4688_ = lean_elab_environment_to_kernel_env(v_env_4687_);
v___x_4689_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4689_, 0, v___x_4688_);
lean_ctor_set(v___x_4689_, 1, v_fst_4677_);
v___x_4690_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4689_, v___y_4681_, v___y_4682_);
return v___x_4690_;
}
}
v___jp_4691_:
{
lean_object* v_toConstantVal_4696_; lean_object* v_name_4697_; lean_object* v___x_4698_; uint8_t v___x_4699_; 
v_toConstantVal_4696_ = lean_ctor_get(v___y_4692_, 0);
v_name_4697_ = lean_ctor_get(v_toConstantVal_4696_, 0);
lean_inc(v_name_4697_);
v___x_4698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4698_, 0, v___y_4692_);
v___x_4699_ = 0;
v_fst_4677_ = v_name_4697_;
v_fst_4678_ = v___x_4698_;
v_snd_4679_ = v___x_4699_;
v_exportedInfo_x3f_4680_ = v_exportedInfo_x3f_4693_;
v___y_4681_ = v___y_4694_;
v___y_4682_ = v___y_4695_;
goto v___jp_4676_;
}
v___jp_4700_:
{
lean_object* v___x_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4706_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4706_, 0, v___y_4704_);
lean_ctor_set_uint8(v___x_4706_, sizeof(void*)*1, v___y_4705_);
v___x_4707_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___x_4706_);
v___x_4708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4708_, 0, v___x_4707_);
v___y_4692_ = v___y_4703_;
v_exportedInfo_x3f_4693_ = v___x_4708_;
v___y_4694_ = v___y_4701_;
v___y_4695_ = v___y_4702_;
goto v___jp_4691_;
}
v___jp_4709_:
{
uint8_t v___x_4716_; uint8_t v___x_4717_; 
v___x_4716_ = 1;
v___x_4717_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4713_, v___x_4716_);
if (v___x_4717_ == 0)
{
v___y_4701_ = v___y_4714_;
v___y_4702_ = v___y_4715_;
v___y_4703_ = v___y_4711_;
v___y_4704_ = v_toConstantVal_4712_;
v___y_4705_ = v___y_4710_;
goto v___jp_4700_;
}
else
{
v___y_4701_ = v___y_4714_;
v___y_4702_ = v___y_4715_;
v___y_4703_ = v___y_4711_;
v___y_4704_ = v_toConstantVal_4712_;
v___y_4705_ = v___x_4451_;
goto v___jp_4700_;
}
}
v___jp_4718_:
{
lean_object* v_toConstantVal_4723_; uint8_t v_safety_4724_; 
v_toConstantVal_4723_ = lean_ctor_get(v___y_4720_, 0);
lean_inc_ref(v_toConstantVal_4723_);
v_safety_4724_ = lean_ctor_get_uint8(v___y_4720_, sizeof(void*)*4);
v___y_4710_ = v___y_4719_;
v___y_4711_ = v___y_4720_;
v_toConstantVal_4712_ = v_toConstantVal_4723_;
v_safety_4713_ = v_safety_4724_;
v___y_4714_ = v___y_4721_;
v___y_4715_ = v___y_4722_;
goto v___jp_4709_;
}
v___jp_4725_:
{
lean_object* v_options_4730_; uint8_t v_hasTrace_4731_; 
v_options_4730_ = lean_ctor_get(v___y_4726_, 1);
v_hasTrace_4731_ = lean_ctor_get_uint8(v_options_4730_, sizeof(void*)*1);
if (v_hasTrace_4731_ == 0)
{
v___y_4719_ = v___y_4729_;
v___y_4720_ = v___y_4728_;
v___y_4721_ = v___y_4726_;
v___y_4722_ = v___y_4727_;
goto v___jp_4718_;
}
else
{
lean_object* v_toCold_4732_; lean_object* v_inheritedTraceOptions_4733_; uint8_t v___x_4734_; 
v_toCold_4732_ = lean_ctor_get(v___y_4726_, 0);
v_inheritedTraceOptions_4733_ = lean_ctor_get(v_toCold_4732_, 4);
v___x_4734_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4733_, v_options_4730_, v___x_4149_);
if (v___x_4734_ == 0)
{
v___y_4719_ = v___y_4729_;
v___y_4720_ = v___y_4728_;
v___y_4721_ = v___y_4726_;
v___y_4722_ = v___y_4727_;
goto v___jp_4718_;
}
else
{
lean_object* v_toConstantVal_4735_; uint8_t v_safety_4736_; lean_object* v_name_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v_toConstantVal_4735_ = lean_ctor_get(v___y_4728_, 0);
lean_inc_ref(v_toConstantVal_4735_);
v_safety_4736_ = lean_ctor_get_uint8(v___y_4728_, sizeof(void*)*4);
v_name_4737_ = lean_ctor_get(v_toConstantVal_4735_, 0);
v___x_4738_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4737_);
v___x_4739_ = l_Lean_MessageData_ofName(v_name_4737_);
v___x_4740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4738_);
lean_ctor_set(v___x_4740_, 1, v___x_4739_);
v___x_4741_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4742_, v___y_4726_, v___y_4727_);
if (lean_obj_tag(v___x_4743_) == 0)
{
lean_dec_ref_known(v___x_4743_, 1);
v___y_4710_ = v___y_4729_;
v___y_4711_ = v___y_4728_;
v_toConstantVal_4712_ = v_toConstantVal_4735_;
v_safety_4713_ = v_safety_4736_;
v___y_4714_ = v___y_4726_;
v___y_4715_ = v___y_4727_;
goto v___jp_4709_;
}
else
{
lean_dec_ref(v_toConstantVal_4735_);
lean_dec_ref(v___y_4728_);
lean_dec(v_decl_3738_);
return v___x_4743_;
}
}
}
}
v___jp_4744_:
{
lean_object* v___x_4750_; uint8_t v_isModule_4751_; 
v___x_4750_ = l_Lean_Environment_header(v___y_4747_);
lean_dec_ref(v___y_4747_);
v_isModule_4751_ = lean_ctor_get_uint8(v___x_4750_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4750_);
if (v_isModule_4751_ == 0)
{
lean_dec_ref(v___y_4748_);
v___y_4692_ = v___y_4749_;
v_exportedInfo_x3f_4693_ = v___x_4641_;
v___y_4694_ = v___y_4745_;
v___y_4695_ = v___y_4746_;
goto v___jp_4691_;
}
else
{
uint8_t v_isExporting_4752_; 
v_isExporting_4752_ = lean_ctor_get_uint8(v___y_4748_, sizeof(void*)*8);
lean_dec_ref(v___y_4748_);
if (v_isExporting_4752_ == 0)
{
v___y_4726_ = v___y_4745_;
v___y_4727_ = v___y_4746_;
v___y_4728_ = v___y_4749_;
v___y_4729_ = v_isModule_4751_;
goto v___jp_4725_;
}
else
{
if (v___x_4451_ == 0)
{
v___y_4692_ = v___y_4749_;
v_exportedInfo_x3f_4693_ = v___x_4641_;
v___y_4694_ = v___y_4745_;
v___y_4695_ = v___y_4746_;
goto v___jp_4691_;
}
else
{
v___y_4726_ = v___y_4745_;
v___y_4727_ = v___y_4746_;
v___y_4728_ = v___y_4749_;
v___y_4729_ = v___x_4451_;
goto v___jp_4725_;
}
}
}
}
v___jp_4753_:
{
lean_object* v___x_4757_; lean_object* v___x_4758_; 
v___x_4757_ = lean_st_ref_get(v___y_4756_);
v___x_4758_ = lean_st_ref_get(v___y_4756_);
if (v_forceExpose_3739_ == 0)
{
lean_object* v_env_4759_; lean_object* v_env_4760_; 
v_env_4759_ = lean_ctor_get(v___x_4757_, 0);
lean_inc_ref(v_env_4759_);
lean_dec(v___x_4757_);
v_env_4760_ = lean_ctor_get(v___x_4758_, 0);
lean_inc_ref(v_env_4760_);
lean_dec(v___x_4758_);
v___y_4745_ = v___y_4755_;
v___y_4746_ = v___y_4756_;
v___y_4747_ = v_env_4759_;
v___y_4748_ = v_env_4760_;
v___y_4749_ = v_defn_4754_;
goto v___jp_4744_;
}
else
{
if (v___x_4451_ == 0)
{
lean_dec(v___x_4758_);
lean_dec(v___x_4757_);
v___y_4692_ = v_defn_4754_;
v_exportedInfo_x3f_4693_ = v___x_4641_;
v___y_4694_ = v___y_4755_;
v___y_4695_ = v___y_4756_;
goto v___jp_4691_;
}
else
{
lean_object* v_env_4761_; lean_object* v_env_4762_; 
v_env_4761_ = lean_ctor_get(v___x_4757_, 0);
lean_inc_ref(v_env_4761_);
lean_dec(v___x_4757_);
v_env_4762_ = lean_ctor_get(v___x_4758_, 0);
lean_inc_ref(v_env_4762_);
lean_dec(v___x_4758_);
v___y_4745_ = v___y_4755_;
v___y_4746_ = v___y_4756_;
v___y_4747_ = v_env_4761_;
v___y_4748_ = v_env_4762_;
v___y_4749_ = v_defn_4754_;
goto v___jp_4744_;
}
}
}
}
}
}
else
{
goto v___jp_4298_;
}
v___jp_4452_:
{
lean_object* v___x_4463_; 
lean_inc_ref(v___y_4460_);
v___x_4463_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4454_, v___y_4460_, v___y_4453_, v___y_4462_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_object* v___x_4464_; lean_object* v___x_4466_; uint8_t v_isShared_4467_; uint8_t v_isSharedCheck_4510_; 
lean_dec_ref_known(v___x_4463_, 1);
lean_inc_ref(v___y_4457_);
v___x_4464_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4457_, v___y_4461_);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4464_);
if (v_isSharedCheck_4510_ == 0)
{
lean_object* v_unused_4511_; 
v_unused_4511_ = lean_ctor_get(v___x_4464_, 0);
lean_dec(v_unused_4511_);
v___x_4466_ = v___x_4464_;
v_isShared_4467_ = v_isSharedCheck_4510_;
goto v_resetjp_4465_;
}
else
{
lean_dec(v___x_4464_);
v___x_4466_ = lean_box(0);
v_isShared_4467_ = v_isSharedCheck_4510_;
goto v_resetjp_4465_;
}
v_resetjp_4465_:
{
lean_object* v_options_4468_; lean_object* v___x_4469_; uint8_t v___x_4470_; 
v_options_4468_ = lean_ctor_get(v___y_4455_, 1);
v___x_4469_ = l_Lean_Elab_async;
v___x_4470_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4468_, v___x_4469_);
if (v___x_4470_ == 0)
{
lean_object* v___x_4471_; lean_object* v_r_4472_; 
lean_del_object(v___x_4466_);
lean_dec_ref(v___y_4458_);
lean_dec_ref(v___y_4456_);
v___x_4471_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4460_, v___y_4461_);
lean_dec_ref(v___x_4471_);
v_r_4472_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v___y_4455_, v___y_4461_);
if (lean_obj_tag(v_r_4472_) == 0)
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4482_; 
v_a_4473_ = lean_ctor_get(v_r_4472_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v_r_4472_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4475_ = v_r_4472_;
v_isShared_4476_ = v_isSharedCheck_4482_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v_r_4472_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4482_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v___x_4478_; 
lean_inc(v_a_4473_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set_tag(v___x_4475_, 1);
v___x_4478_ = v___x_4475_;
goto v_reusejp_4477_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4473_);
v___x_4478_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4477_;
}
v_reusejp_4477_:
{
lean_object* v___x_4479_; 
v___x_4479_ = lean_apply_2(v___y_4459_, v___x_4478_, lean_box(0));
if (lean_obj_tag(v___x_4479_) == 0)
{
lean_dec_ref_known(v___x_4479_, 1);
v___y_3744_ = v___y_4457_;
v___y_3745_ = v___y_4461_;
v_a_3746_ = v_a_4473_;
goto v___jp_3743_;
}
else
{
lean_object* v_a_4480_; 
lean_dec(v_a_4473_);
v_a_4480_ = lean_ctor_get(v___x_4479_, 0);
lean_inc(v_a_4480_);
lean_dec_ref_known(v___x_4479_, 1);
v___y_3757_ = v___y_4457_;
v___y_3758_ = v___y_4461_;
v_a_3759_ = v_a_4480_;
goto v___jp_3756_;
}
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_a_4483_ = lean_ctor_get(v_r_4472_, 0);
lean_inc(v_a_4483_);
lean_dec_ref_known(v_r_4472_, 1);
v___x_4484_ = lean_box(0);
v___x_4485_ = lean_apply_2(v___y_4459_, v___x_4484_, lean_box(0));
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_dec_ref_known(v___x_4485_, 1);
v___y_3757_ = v___y_4457_;
v___y_3758_ = v___y_4461_;
v_a_3759_ = v_a_4483_;
goto v___jp_3756_;
}
else
{
lean_object* v_a_4486_; 
lean_dec(v_a_4483_);
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___y_3757_ = v___y_4457_;
v___y_3758_ = v___y_4461_;
v_a_3759_ = v_a_4486_;
goto v___jp_3756_;
}
}
}
else
{
lean_object* v___x_4487_; lean_object* v___x_4489_; 
lean_dec_ref(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec_ref(v___y_4457_);
lean_dec(v_decl_3738_);
v___x_4487_ = l_IO_CancelToken_new();
if (v_isShared_4467_ == 0)
{
lean_ctor_set_tag(v___x_4466_, 1);
lean_ctor_set(v___x_4466_, 0, v___x_4487_);
v___x_4489_ = v___x_4466_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4487_);
v___x_4489_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
lean_object* v___x_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v___x_4490_ = lean_unsigned_to_nat(0u);
v___x_4491_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4492_ = l_Lean_Name_toString(v___x_4491_, v_hasTrace_3797_);
lean_inc_ref(v___x_4489_);
v___x_4493_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4458_, v___x_4489_, v___x_4492_, v___y_4455_, v___y_4461_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v_checked_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v_checked_4495_ = lean_ctor_get(v___y_4456_, 2);
lean_inc_ref(v_checked_4495_);
lean_dec_ref(v___y_4456_);
v___x_4496_ = lean_io_map_task(v_a_4494_, v_checked_4495_, v___x_4490_, v___x_4451_);
v___x_4497_ = lean_box(0);
v___x_4498_ = lean_box(2);
v___x_4499_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4499_, 0, v___x_4497_);
lean_ctor_set(v___x_4499_, 1, v___x_4498_);
lean_ctor_set(v___x_4499_, 2, v___x_4489_);
lean_ctor_set(v___x_4499_, 3, v___x_4496_);
v___x_4500_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4499_, v___y_4461_);
return v___x_4500_;
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec_ref(v___x_4489_);
lean_dec_ref(v___y_4456_);
v_a_4501_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4493_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4493_);
v___x_4503_ = lean_box(0);
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
v_resetjp_4502_:
{
lean_object* v___x_4506_; 
if (v_isShared_4504_ == 0)
{
v___x_4506_ = v___x_4503_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4507_; 
v_reuseFailAlloc_4507_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4507_, 0, v_a_4501_);
v___x_4506_ = v_reuseFailAlloc_4507_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
return v___x_4506_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4524_; 
lean_dec_ref(v___y_4460_);
lean_dec_ref(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec_ref(v___y_4456_);
lean_dec(v_decl_3738_);
v_a_4512_ = lean_ctor_get(v___x_4463_, 0);
v_isSharedCheck_4524_ = !lean_is_exclusive(v___x_4463_);
if (v_isSharedCheck_4524_ == 0)
{
v___x_4514_ = v___x_4463_;
v_isShared_4515_ = v_isSharedCheck_4524_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4463_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4524_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v_ref_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4522_; 
v_ref_4516_ = lean_ctor_get(v___y_4455_, 4);
v___x_4517_ = lean_io_error_to_string(v_a_4512_);
v___x_4518_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4518_, 0, v___x_4517_);
v___x_4519_ = l_Lean_MessageData_ofFormat(v___x_4518_);
lean_inc(v_ref_4516_);
v___x_4520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4520_, 0, v_ref_4516_);
lean_ctor_set(v___x_4520_, 1, v___x_4519_);
if (v_isShared_4515_ == 0)
{
lean_ctor_set(v___x_4514_, 0, v___x_4520_);
v___x_4522_ = v___x_4514_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4523_; 
v_reuseFailAlloc_4523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4523_, 0, v___x_4520_);
v___x_4522_ = v_reuseFailAlloc_4523_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
return v___x_4522_;
}
}
}
}
v___jp_4525_:
{
lean_object* v___x_4536_; 
lean_inc_ref(v___y_4527_);
v___x_4536_ = l_Lean_Environment_addConstAsync(v___y_4527_, v___y_4531_, v___y_4534_, v___y_4535_, v___x_4451_, v_hasTrace_3797_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v_a_4537_; lean_object* v_mainEnv_4538_; lean_object* v_asyncEnv_4539_; lean_object* v___f_4540_; lean_object* v___f_4541_; lean_object* v___x_4542_; 
v_a_4537_ = lean_ctor_get(v___x_4536_, 0);
lean_inc_n(v_a_4537_, 3);
lean_dec_ref_known(v___x_4536_, 1);
v_mainEnv_4538_ = lean_ctor_get(v_a_4537_, 0);
lean_inc_ref(v_mainEnv_4538_);
v_asyncEnv_4539_ = lean_ctor_get(v_a_4537_, 1);
lean_inc_ref_n(v_asyncEnv_4539_, 2);
lean_inc_ref(v___y_4526_);
lean_inc(v___y_4528_);
v___f_4540_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4540_, 0, v___y_4528_);
lean_closure_set(v___f_4540_, 1, v_a_4537_);
lean_closure_set(v___f_4540_, 2, v___y_4526_);
lean_inc(v_decl_3738_);
v___f_4541_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4541_, 0, v_asyncEnv_4539_);
lean_closure_set(v___f_4541_, 1, v_a_4537_);
lean_closure_set(v___f_4541_, 2, v_decl_3738_);
v___x_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4542_, 0, v___y_4529_);
if (lean_obj_tag(v___y_4533_) == 0)
{
lean_inc_ref(v___x_4542_);
v___y_4453_ = v___x_4542_;
v___y_4454_ = v_a_4537_;
v___y_4455_ = v___y_4530_;
v___y_4456_ = v___y_4527_;
v___y_4457_ = v_mainEnv_4538_;
v___y_4458_ = v___f_4541_;
v___y_4459_ = v___f_4540_;
v___y_4460_ = v_asyncEnv_4539_;
v___y_4461_ = v___y_4532_;
v___y_4462_ = v___x_4542_;
goto v___jp_4452_;
}
else
{
v___y_4453_ = v___x_4542_;
v___y_4454_ = v_a_4537_;
v___y_4455_ = v___y_4530_;
v___y_4456_ = v___y_4527_;
v___y_4457_ = v_mainEnv_4538_;
v___y_4458_ = v___f_4541_;
v___y_4459_ = v___f_4540_;
v___y_4460_ = v_asyncEnv_4539_;
v___y_4461_ = v___y_4532_;
v___y_4462_ = v___y_4533_;
goto v___jp_4452_;
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4555_; 
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4529_);
lean_dec_ref(v___y_4527_);
lean_dec(v_decl_3738_);
v_a_4543_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4555_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4555_ == 0)
{
v___x_4545_ = v___x_4536_;
v_isShared_4546_ = v_isSharedCheck_4555_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4536_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4555_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v_ref_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4553_; 
v_ref_4547_ = lean_ctor_get(v___y_4530_, 4);
v___x_4548_ = lean_io_error_to_string(v_a_4543_);
v___x_4549_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4549_, 0, v___x_4548_);
v___x_4550_ = l_Lean_MessageData_ofFormat(v___x_4549_);
lean_inc(v_ref_4547_);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v_ref_4547_);
lean_ctor_set(v___x_4551_, 1, v___x_4550_);
if (v_isShared_4546_ == 0)
{
lean_ctor_set(v___x_4545_, 0, v___x_4551_);
v___x_4553_ = v___x_4545_;
goto v_reusejp_4552_;
}
else
{
lean_object* v_reuseFailAlloc_4554_; 
v_reuseFailAlloc_4554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4554_, 0, v___x_4551_);
v___x_4553_ = v_reuseFailAlloc_4554_;
goto v_reusejp_4552_;
}
v_reusejp_4552_:
{
return v___x_4553_;
}
}
}
}
v___jp_4556_:
{
lean_object* v___x_4563_; 
v___x_4563_ = lean_st_ref_get(v___y_4562_);
if (lean_obj_tag(v_exportedInfo_x3f_4560_) == 0)
{
lean_object* v_env_4564_; lean_object* v___x_4565_; 
v_env_4564_ = lean_ctor_get(v___x_4563_, 0);
lean_inc_ref(v_env_4564_);
lean_dec(v___x_4563_);
v___x_4565_ = lean_box(0);
v___y_4526_ = v___y_4561_;
v___y_4527_ = v_env_4564_;
v___y_4528_ = v___y_4562_;
v___y_4529_ = v___y_4557_;
v___y_4530_ = v___y_4561_;
v___y_4531_ = v___y_4558_;
v___y_4532_ = v___y_4562_;
v___y_4533_ = v_exportedInfo_x3f_4560_;
v___y_4534_ = v___y_4559_;
v___y_4535_ = v___x_4565_;
goto v___jp_4525_;
}
else
{
lean_object* v_env_4566_; lean_object* v_val_4567_; uint8_t v___x_4568_; lean_object* v___x_4569_; lean_object* v___x_4570_; 
v_env_4566_ = lean_ctor_get(v___x_4563_, 0);
lean_inc_ref(v_env_4566_);
lean_dec(v___x_4563_);
v_val_4567_ = lean_ctor_get(v_exportedInfo_x3f_4560_, 0);
v___x_4568_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4567_);
v___x_4569_ = lean_box(v___x_4568_);
v___x_4570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4570_, 0, v___x_4569_);
v___y_4526_ = v___y_4561_;
v___y_4527_ = v_env_4566_;
v___y_4528_ = v___y_4562_;
v___y_4529_ = v___y_4557_;
v___y_4530_ = v___y_4561_;
v___y_4531_ = v___y_4558_;
v___y_4532_ = v___y_4562_;
v___y_4533_ = v_exportedInfo_x3f_4560_;
v___y_4534_ = v___y_4559_;
v___y_4535_ = v___x_4570_;
goto v___jp_4525_;
}
}
v___jp_4571_:
{
lean_object* v___x_4577_; 
lean_inc_ref(v___y_4572_);
v___x_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4577_, 0, v___y_4572_);
v___y_4557_ = v___y_4572_;
v___y_4558_ = v___y_4573_;
v___y_4559_ = v___y_4574_;
v_exportedInfo_x3f_4560_ = v___x_4577_;
v___y_4561_ = v___y_4575_;
v___y_4562_ = v___y_4576_;
goto v___jp_4556_;
}
v___jp_4578_:
{
lean_object* v___x_4584_; 
lean_inc_ref(v___y_4579_);
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___y_4579_);
v___y_4557_ = v___y_4579_;
v___y_4558_ = v___y_4580_;
v___y_4559_ = v___y_4581_;
v_exportedInfo_x3f_4560_ = v___x_4584_;
v___y_4561_ = v___y_4582_;
v___y_4562_ = v___y_4583_;
goto v___jp_4556_;
}
}
else
{
goto v___jp_4298_;
}
v___jp_4151_:
{
lean_object* v___x_4155_; double v___x_4156_; double v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v___x_4155_ = lean_io_get_num_heartbeats();
v___x_4156_ = lean_float_of_nat(v___y_4153_);
v___x_4157_ = lean_float_of_nat(v___x_4155_);
v___x_4158_ = lean_box_float(v___x_4156_);
v___x_4159_ = lean_box_float(v___x_4157_);
v___x_4160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4160_, 0, v___x_4158_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
v___x_4161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4161_, 0, v_a_4154_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3933_, v_hasTrace_3797_, v___x_4148_, v_options_3795_, v___x_4150_, v___y_4152_, v___f_4147_, v___x_4161_, v_a_3740_, v_a_3741_);
return v___x_4162_;
}
v___jp_4163_:
{
if (lean_obj_tag(v___y_4166_) == 0)
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
v_a_4167_ = lean_ctor_get(v___y_4166_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___y_4166_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___y_4166_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___y_4166_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
lean_ctor_set_tag(v___x_4169_, 1);
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
v___y_4152_ = v___y_4164_;
v___y_4153_ = v___y_4165_;
v_a_4154_ = v___x_4172_;
goto v___jp_4151_;
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___y_4166_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4166_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___y_4166_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___y_4166_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set_tag(v___x_4177_, 0);
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
v___y_4152_ = v___y_4164_;
v___y_4153_ = v___y_4165_;
v_a_4154_ = v___x_4180_;
goto v___jp_4151_;
}
}
}
}
v___jp_4183_:
{
lean_object* v___x_4188_; lean_object* v___x_4189_; 
v___x_4188_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4189_ = lean_apply_5(v___y_4186_, v___x_4188_, v___y_4185_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4164_ = v___y_4184_;
v___y_4165_ = v___y_4187_;
v___y_4166_ = v___x_4189_;
goto v___jp_4163_;
}
v___jp_4190_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4196_ = lean_apply_5(v___y_4192_, v___x_4195_, v___y_4193_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4164_ = v___y_4191_;
v___y_4165_ = v___y_4194_;
v___y_4166_ = v___x_4196_;
goto v___jp_4163_;
}
v___jp_4197_:
{
lean_object* v___x_4201_; double v___x_4202_; double v___x_4203_; double v___x_4204_; double v___x_4205_; double v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4201_ = lean_io_mono_nanos_now();
v___x_4202_ = lean_float_of_nat(v___y_4198_);
v___x_4203_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4204_ = lean_float_div(v___x_4202_, v___x_4203_);
v___x_4205_ = lean_float_of_nat(v___x_4201_);
v___x_4206_ = lean_float_div(v___x_4205_, v___x_4203_);
v___x_4207_ = lean_box_float(v___x_4204_);
v___x_4208_ = lean_box_float(v___x_4206_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4207_);
lean_ctor_set(v___x_4209_, 1, v___x_4208_);
v___x_4210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4210_, 0, v_a_4200_);
lean_ctor_set(v___x_4210_, 1, v___x_4209_);
v___x_4211_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3933_, v_hasTrace_3797_, v___x_4148_, v_options_3795_, v___x_4150_, v___y_4199_, v___f_4147_, v___x_4210_, v_a_3740_, v_a_3741_);
return v___x_4211_;
}
v___jp_4212_:
{
if (lean_obj_tag(v___y_4215_) == 0)
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
v_a_4216_ = lean_ctor_get(v___y_4215_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___y_4215_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___y_4215_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
lean_ctor_set_tag(v___x_4218_, 1);
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
v___y_4198_ = v___y_4213_;
v___y_4199_ = v___y_4214_;
v_a_4200_ = v___x_4221_;
goto v___jp_4197_;
}
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___y_4215_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___y_4215_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___y_4215_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___y_4215_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
lean_ctor_set_tag(v___x_4226_, 0);
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
v___y_4198_ = v___y_4213_;
v___y_4199_ = v___y_4214_;
v_a_4200_ = v___x_4229_;
goto v___jp_4197_;
}
}
}
}
v___jp_4232_:
{
lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4237_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4238_ = lean_apply_5(v___y_4234_, v___x_4237_, v___y_4236_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4233_;
v___y_4214_ = v___y_4235_;
v___y_4215_ = v___x_4238_;
goto v___jp_4212_;
}
v___jp_4239_:
{
if (v___x_4150_ == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
lean_dec_ref(v___y_4243_);
v___x_4244_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4245_ = lean_apply_4(v___y_4241_, v___x_4244_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4245_;
goto v___jp_4212_;
}
else
{
lean_object* v_toConstantVal_4246_; lean_object* v_name_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; 
v_toConstantVal_4246_ = lean_ctor_get(v___y_4243_, 0);
lean_inc_ref(v_toConstantVal_4246_);
lean_dec_ref(v___y_4243_);
v_name_4247_ = lean_ctor_get(v_toConstantVal_4246_, 0);
lean_inc(v_name_4247_);
lean_dec_ref(v_toConstantVal_4246_);
v___x_4248_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4249_ = l_Lean_MessageData_ofName(v_name_4247_);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4252_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; lean_object* v___x_4255_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4255_ = lean_apply_4(v___y_4241_, v_a_4254_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4255_;
goto v___jp_4212_;
}
else
{
lean_dec_ref(v___y_4241_);
v___y_4213_ = v___y_4240_;
v___y_4214_ = v___y_4242_;
v___y_4215_ = v___x_4253_;
goto v___jp_4212_;
}
}
}
v___jp_4256_:
{
lean_object* v___x_4266_; uint8_t v_isModule_4267_; 
v___x_4266_ = l_Lean_Environment_header(v___y_4258_);
lean_dec_ref(v___y_4258_);
v_isModule_4267_ = lean_ctor_get_uint8(v___x_4266_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4266_);
if (v_isModule_4267_ == 0)
{
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4260_);
v___y_4233_ = v___y_4257_;
v___y_4234_ = v___y_4259_;
v___y_4235_ = v___y_4261_;
v___y_4236_ = v___y_4265_;
goto v___jp_4232_;
}
else
{
uint8_t v_isExporting_4268_; 
v_isExporting_4268_ = lean_ctor_get_uint8(v___y_4263_, sizeof(void*)*8);
lean_dec_ref(v___y_4263_);
if (v_isExporting_4268_ == 0)
{
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4259_);
v___y_4240_ = v___y_4257_;
v___y_4241_ = v___y_4260_;
v___y_4242_ = v___y_4261_;
v___y_4243_ = v___y_4264_;
goto v___jp_4239_;
}
else
{
if (v___y_4262_ == 0)
{
lean_dec_ref(v___y_4264_);
lean_dec_ref(v___y_4260_);
v___y_4233_ = v___y_4257_;
v___y_4234_ = v___y_4259_;
v___y_4235_ = v___y_4261_;
v___y_4236_ = v___y_4265_;
goto v___jp_4232_;
}
else
{
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4259_);
v___y_4240_ = v___y_4257_;
v___y_4241_ = v___y_4260_;
v___y_4242_ = v___y_4261_;
v___y_4243_ = v___y_4264_;
goto v___jp_4239_;
}
}
}
}
v___jp_4269_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; 
v___x_4274_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4275_ = lean_apply_5(v___y_4272_, v___x_4274_, v___y_4273_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4270_;
v___y_4214_ = v___y_4271_;
v___y_4215_ = v___x_4275_;
goto v___jp_4212_;
}
v___jp_4276_:
{
lean_object* v___x_4284_; uint8_t v_isModule_4285_; 
v___x_4284_ = l_Lean_Environment_header(v___y_4283_);
lean_dec_ref(v___y_4283_);
v_isModule_4285_ = lean_ctor_get_uint8(v___x_4284_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4284_);
if (v_isModule_4285_ == 0)
{
lean_dec_ref(v___y_4281_);
lean_dec_ref(v___y_4280_);
v___y_4270_ = v___y_4277_;
v___y_4271_ = v___y_4278_;
v___y_4272_ = v___y_4279_;
v___y_4273_ = v___y_4282_;
goto v___jp_4269_;
}
else
{
lean_dec(v___y_4282_);
lean_dec_ref(v___y_4279_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4286_; lean_object* v___x_4287_; 
lean_dec_ref(v___y_4281_);
v___x_4286_ = lean_box(0);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4287_ = lean_apply_4(v___y_4280_, v___x_4286_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4277_;
v___y_4214_ = v___y_4278_;
v___y_4215_ = v___x_4287_;
goto v___jp_4212_;
}
else
{
lean_object* v_toConstantVal_4288_; lean_object* v_name_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; lean_object* v___x_4295_; 
v_toConstantVal_4288_ = lean_ctor_get(v___y_4281_, 0);
lean_inc_ref(v_toConstantVal_4288_);
lean_dec_ref(v___y_4281_);
v_name_4289_ = lean_ctor_get(v_toConstantVal_4288_, 0);
lean_inc(v_name_4289_);
lean_dec_ref(v_toConstantVal_4288_);
v___x_4290_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4291_ = l_Lean_MessageData_ofName(v_name_4289_);
v___x_4292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4294_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4294_, 0, v___x_4292_);
lean_ctor_set(v___x_4294_, 1, v___x_4293_);
v___x_4295_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4294_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref_known(v___x_4295_, 1);
lean_inc(v_a_3741_);
lean_inc_ref(v_a_3740_);
v___x_4297_ = lean_apply_4(v___y_4280_, v_a_4296_, v_a_3740_, v_a_3741_, lean_box(0));
v___y_4213_ = v___y_4277_;
v___y_4214_ = v___y_4278_;
v___y_4215_ = v___x_4297_;
goto v___jp_4212_;
}
else
{
lean_dec_ref(v___y_4280_);
v___y_4213_ = v___y_4277_;
v___y_4214_ = v___y_4278_;
v___y_4215_ = v___x_4295_;
goto v___jp_4212_;
}
}
}
}
v___jp_4298_:
{
lean_object* v___x_4299_; lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4449_; 
v___x_4299_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3741_);
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4302_ = v___x_4299_;
v_isShared_4303_ = v_isSharedCheck_4449_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4449_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4304_; uint8_t v___x_4305_; 
v___x_4304_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4305_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3795_, v___x_4304_);
if (v___x_4305_ == 0)
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v_env_4308_; lean_object* v_nextMacroScope_4309_; lean_object* v_ngen_4310_; lean_object* v_auxDeclNGen_4311_; lean_object* v_traceState_4312_; lean_object* v_messages_4313_; lean_object* v_infoState_4314_; lean_object* v_snapshotTasks_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4363_; 
v___x_4306_ = lean_io_mono_nanos_now();
v___x_4307_ = lean_st_ref_take(v_a_3741_);
v_env_4308_ = lean_ctor_get(v___x_4307_, 0);
v_nextMacroScope_4309_ = lean_ctor_get(v___x_4307_, 1);
v_ngen_4310_ = lean_ctor_get(v___x_4307_, 2);
v_auxDeclNGen_4311_ = lean_ctor_get(v___x_4307_, 3);
v_traceState_4312_ = lean_ctor_get(v___x_4307_, 4);
v_messages_4313_ = lean_ctor_get(v___x_4307_, 6);
v_infoState_4314_ = lean_ctor_get(v___x_4307_, 7);
v_snapshotTasks_4315_ = lean_ctor_get(v___x_4307_, 8);
v_isSharedCheck_4363_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4363_ == 0)
{
lean_object* v_unused_4364_; 
v_unused_4364_ = lean_ctor_get(v___x_4307_, 5);
lean_dec(v_unused_4364_);
v___x_4317_ = v___x_4307_;
v_isShared_4318_ = v_isSharedCheck_4363_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_snapshotTasks_4315_);
lean_inc(v_infoState_4314_);
lean_inc(v_messages_4313_);
lean_inc(v_traceState_4312_);
lean_inc(v_auxDeclNGen_4311_);
lean_inc(v_ngen_4310_);
lean_inc(v_nextMacroScope_4309_);
lean_inc(v_env_4308_);
lean_dec(v___x_4307_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4363_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
lean_inc(v_decl_3738_);
v___x_4319_ = l_Lean_Declaration_getNames(v_decl_3738_);
v___x_4320_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4308_, v___x_4319_);
v___x_4321_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 5, v___x_4321_);
lean_ctor_set(v___x_4317_, 0, v___x_4320_);
v___x_4323_ = v___x_4317_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4362_; 
v_reuseFailAlloc_4362_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4362_, 0, v___x_4320_);
lean_ctor_set(v_reuseFailAlloc_4362_, 1, v_nextMacroScope_4309_);
lean_ctor_set(v_reuseFailAlloc_4362_, 2, v_ngen_4310_);
lean_ctor_set(v_reuseFailAlloc_4362_, 3, v_auxDeclNGen_4311_);
lean_ctor_set(v_reuseFailAlloc_4362_, 4, v_traceState_4312_);
lean_ctor_set(v_reuseFailAlloc_4362_, 5, v___x_4321_);
lean_ctor_set(v_reuseFailAlloc_4362_, 6, v_messages_4313_);
lean_ctor_set(v_reuseFailAlloc_4362_, 7, v_infoState_4314_);
lean_ctor_set(v_reuseFailAlloc_4362_, 8, v_snapshotTasks_4315_);
v___x_4323_ = v_reuseFailAlloc_4362_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
lean_object* v___x_4324_; lean_object* v___x_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___f_4328_; 
v___x_4324_ = lean_st_ref_put(v_a_3741_, v___x_4323_);
v___x_4325_ = lean_box(0);
v___x_4326_ = lean_box(v_hasTrace_3797_);
v___x_4327_ = lean_box(v___x_4305_);
lean_inc(v_decl_3738_);
v___f_4328_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4328_, 0, v_decl_3738_);
lean_closure_set(v___f_4328_, 1, v___x_4326_);
lean_closure_set(v___f_4328_, 2, v___x_4327_);
lean_closure_set(v___f_4328_, 3, v___x_4321_);
lean_closure_set(v___f_4328_, 4, v_cls_3933_);
lean_closure_set(v___f_4328_, 5, v___x_4325_);
switch(lean_obj_tag(v_decl_3738_))
{
case 2:
{
lean_object* v_val_4329_; lean_object* v___x_4330_; lean_object* v_env_4331_; lean_object* v___f_4332_; lean_object* v___x_4333_; lean_object* v___f_4334_; 
lean_del_object(v___x_4302_);
v_val_4329_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref_n(v_val_4329_, 3);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4330_ = lean_st_ref_get(v_a_3741_);
v_env_4331_ = lean_ctor_get(v___x_4330_, 0);
lean_inc_ref(v_env_4331_);
lean_dec(v___x_4330_);
v___f_4332_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4332_, 0, v_val_4329_);
lean_closure_set(v___f_4332_, 1, v___f_4328_);
v___x_4333_ = lean_box(v___x_4305_);
lean_inc_ref(v___f_4332_);
v___f_4334_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4334_, 0, v_val_4329_);
lean_closure_set(v___f_4334_, 1, v___x_4333_);
lean_closure_set(v___f_4334_, 2, v___f_4332_);
if (v_forceExpose_3739_ == 0)
{
v___y_4277_ = v___x_4306_;
v___y_4278_ = v_a_4300_;
v___y_4279_ = v___f_4332_;
v___y_4280_ = v___f_4334_;
v___y_4281_ = v_val_4329_;
v___y_4282_ = v___x_4325_;
v___y_4283_ = v_env_4331_;
goto v___jp_4276_;
}
else
{
if (v___x_4305_ == 0)
{
lean_dec_ref(v___f_4334_);
lean_dec_ref(v_env_4331_);
lean_dec_ref(v_val_4329_);
v___y_4270_ = v___x_4306_;
v___y_4271_ = v_a_4300_;
v___y_4272_ = v___f_4332_;
v___y_4273_ = v___x_4325_;
goto v___jp_4269_;
}
else
{
v___y_4277_ = v___x_4306_;
v___y_4278_ = v_a_4300_;
v___y_4279_ = v___f_4332_;
v___y_4280_ = v___f_4334_;
v___y_4281_ = v_val_4329_;
v___y_4282_ = v___x_4325_;
v___y_4283_ = v_env_4331_;
goto v___jp_4276_;
}
}
}
case 1:
{
lean_object* v_val_4335_; lean_object* v___x_4336_; 
lean_del_object(v___x_4302_);
v_val_4335_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref(v_val_4335_);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4336_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4328_, v___x_4305_, v_cls_3933_, v___x_4325_, v_forceExpose_3739_, v_val_4335_, v_a_3740_, v_a_3741_);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4336_;
goto v___jp_4212_;
}
case 5:
{
lean_object* v_defns_4337_; 
lean_del_object(v___x_4302_);
v_defns_4337_ = lean_ctor_get(v_decl_3738_, 0);
if (lean_obj_tag(v_defns_4337_) == 1)
{
lean_object* v_tail_4338_; 
v_tail_4338_ = lean_ctor_get(v_defns_4337_, 1);
if (lean_obj_tag(v_tail_4338_) == 0)
{
lean_object* v_head_4339_; lean_object* v___x_4340_; 
lean_inc_ref(v_defns_4337_);
lean_dec_ref_known(v_decl_3738_, 1);
v_head_4339_ = lean_ctor_get(v_defns_4337_, 0);
lean_inc(v_head_4339_);
lean_dec_ref_known(v_defns_4337_, 2);
v___x_4340_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4328_, v___x_4305_, v_cls_3933_, v___x_4325_, v_forceExpose_3739_, v_head_4339_, v_a_3740_, v_a_3741_);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4340_;
goto v___jp_4212_;
}
else
{
lean_object* v___x_4341_; 
lean_dec_ref(v___f_4328_);
lean_inc_ref(v_decl_3738_);
v___x_4341_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec_ref_known(v_decl_3738_, 1);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4341_;
goto v___jp_4212_;
}
}
else
{
lean_object* v___x_4342_; 
lean_dec_ref(v___f_4328_);
lean_inc_ref(v_decl_3738_);
v___x_4342_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec_ref_known(v_decl_3738_, 1);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4342_;
goto v___jp_4212_;
}
}
case 3:
{
lean_object* v_val_4343_; lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v_env_4346_; lean_object* v_env_4347_; lean_object* v___f_4348_; lean_object* v___f_4349_; 
lean_del_object(v___x_4302_);
v_val_4343_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref_n(v_val_4343_, 3);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4344_ = lean_st_ref_get(v_a_3741_);
v___x_4345_ = lean_st_ref_get(v_a_3741_);
v_env_4346_ = lean_ctor_get(v___x_4344_, 0);
lean_inc_ref(v_env_4346_);
lean_dec(v___x_4344_);
v_env_4347_ = lean_ctor_get(v___x_4345_, 0);
lean_inc_ref(v_env_4347_);
lean_dec(v___x_4345_);
v___f_4348_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4348_, 0, v_val_4343_);
lean_closure_set(v___f_4348_, 1, v___f_4328_);
lean_inc_ref(v___f_4348_);
v___f_4349_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4349_, 0, v_val_4343_);
lean_closure_set(v___f_4349_, 1, v___f_4348_);
if (v_forceExpose_3739_ == 0)
{
v___y_4257_ = v___x_4306_;
v___y_4258_ = v_env_4346_;
v___y_4259_ = v___f_4348_;
v___y_4260_ = v___f_4349_;
v___y_4261_ = v_a_4300_;
v___y_4262_ = v___x_4305_;
v___y_4263_ = v_env_4347_;
v___y_4264_ = v_val_4343_;
v___y_4265_ = v___x_4325_;
goto v___jp_4256_;
}
else
{
if (v___x_4305_ == 0)
{
lean_dec_ref(v___f_4349_);
lean_dec_ref(v_env_4347_);
lean_dec_ref(v_env_4346_);
lean_dec_ref(v_val_4343_);
v___y_4233_ = v___x_4306_;
v___y_4234_ = v___f_4348_;
v___y_4235_ = v_a_4300_;
v___y_4236_ = v___x_4325_;
goto v___jp_4232_;
}
else
{
v___y_4257_ = v___x_4306_;
v___y_4258_ = v_env_4346_;
v___y_4259_ = v___f_4348_;
v___y_4260_ = v___f_4349_;
v___y_4261_ = v_a_4300_;
v___y_4262_ = v___x_4305_;
v___y_4263_ = v_env_4347_;
v___y_4264_ = v_val_4343_;
v___y_4265_ = v___x_4325_;
goto v___jp_4256_;
}
}
}
case 0:
{
lean_object* v_val_4350_; lean_object* v_toConstantVal_4351_; lean_object* v_name_4352_; lean_object* v___x_4354_; 
lean_dec_ref(v___f_4328_);
v_val_4350_ = lean_ctor_get(v_decl_3738_, 0);
v_toConstantVal_4351_ = lean_ctor_get(v_val_4350_, 0);
v_name_4352_ = lean_ctor_get(v_toConstantVal_4351_, 0);
lean_inc_ref(v_val_4350_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v_val_4350_);
v___x_4354_ = v___x_4302_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_val_4350_);
v___x_4354_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
uint8_t v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
v___x_4355_ = 2;
v___x_4356_ = lean_box(v___x_4355_);
v___x_4357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4354_);
lean_ctor_set(v___x_4357_, 1, v___x_4356_);
lean_inc(v_name_4352_);
v___x_4358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4358_, 0, v_name_4352_);
lean_ctor_set(v___x_4358_, 1, v___x_4357_);
v___x_4359_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3738_, v_hasTrace_3797_, v___x_4305_, v___x_4321_, v_cls_3933_, v___x_4325_, v___x_4358_, v___x_4325_, v_a_3740_, v_a_3741_);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4359_;
goto v___jp_4212_;
}
}
default: 
{
lean_object* v___x_4361_; 
lean_dec_ref(v___f_4328_);
lean_del_object(v___x_4302_);
lean_inc(v_decl_3738_);
v___x_4361_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec(v_decl_3738_);
v___y_4213_ = v___x_4306_;
v___y_4214_ = v_a_4300_;
v___y_4215_ = v___x_4361_;
goto v___jp_4212_;
}
}
}
}
}
else
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v_env_4367_; lean_object* v_nextMacroScope_4368_; lean_object* v_ngen_4369_; lean_object* v_auxDeclNGen_4370_; lean_object* v_traceState_4371_; lean_object* v_messages_4372_; lean_object* v_infoState_4373_; lean_object* v_snapshotTasks_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4447_; 
v___x_4365_ = lean_io_get_num_heartbeats();
v___x_4366_ = lean_st_ref_take(v_a_3741_);
v_env_4367_ = lean_ctor_get(v___x_4366_, 0);
v_nextMacroScope_4368_ = lean_ctor_get(v___x_4366_, 1);
v_ngen_4369_ = lean_ctor_get(v___x_4366_, 2);
v_auxDeclNGen_4370_ = lean_ctor_get(v___x_4366_, 3);
v_traceState_4371_ = lean_ctor_get(v___x_4366_, 4);
v_messages_4372_ = lean_ctor_get(v___x_4366_, 6);
v_infoState_4373_ = lean_ctor_get(v___x_4366_, 7);
v_snapshotTasks_4374_ = lean_ctor_get(v___x_4366_, 8);
v_isSharedCheck_4447_ = !lean_is_exclusive(v___x_4366_);
if (v_isSharedCheck_4447_ == 0)
{
lean_object* v_unused_4448_; 
v_unused_4448_ = lean_ctor_get(v___x_4366_, 5);
lean_dec(v_unused_4448_);
v___x_4376_ = v___x_4366_;
v_isShared_4377_ = v_isSharedCheck_4447_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_snapshotTasks_4374_);
lean_inc(v_infoState_4373_);
lean_inc(v_messages_4372_);
lean_inc(v_traceState_4371_);
lean_inc(v_auxDeclNGen_4370_);
lean_inc(v_ngen_4369_);
lean_inc(v_nextMacroScope_4368_);
lean_inc(v_env_4367_);
lean_dec(v___x_4366_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4447_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4382_; 
lean_inc(v_decl_3738_);
v___x_4378_ = l_Lean_Declaration_getNames(v_decl_3738_);
v___x_4379_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4367_, v___x_4378_);
v___x_4380_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4377_ == 0)
{
lean_ctor_set(v___x_4376_, 5, v___x_4380_);
lean_ctor_set(v___x_4376_, 0, v___x_4379_);
v___x_4382_ = v___x_4376_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4446_; 
v_reuseFailAlloc_4446_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4446_, 0, v___x_4379_);
lean_ctor_set(v_reuseFailAlloc_4446_, 1, v_nextMacroScope_4368_);
lean_ctor_set(v_reuseFailAlloc_4446_, 2, v_ngen_4369_);
lean_ctor_set(v_reuseFailAlloc_4446_, 3, v_auxDeclNGen_4370_);
lean_ctor_set(v_reuseFailAlloc_4446_, 4, v_traceState_4371_);
lean_ctor_set(v_reuseFailAlloc_4446_, 5, v___x_4380_);
lean_ctor_set(v_reuseFailAlloc_4446_, 6, v_messages_4372_);
lean_ctor_set(v_reuseFailAlloc_4446_, 7, v_infoState_4373_);
lean_ctor_set(v_reuseFailAlloc_4446_, 8, v_snapshotTasks_4374_);
v___x_4382_ = v_reuseFailAlloc_4446_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___f_4386_; 
v___x_4383_ = lean_st_ref_put(v_a_3741_, v___x_4382_);
v___x_4384_ = lean_box(0);
v___x_4385_ = lean_box(v___x_4305_);
lean_inc(v_decl_3738_);
v___f_4386_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4386_, 0, v_decl_3738_);
lean_closure_set(v___f_4386_, 1, v___x_4385_);
lean_closure_set(v___f_4386_, 2, v_cls_3933_);
lean_closure_set(v___f_4386_, 3, v___x_4380_);
lean_closure_set(v___f_4386_, 4, v___x_4384_);
switch(lean_obj_tag(v_decl_3738_))
{
case 2:
{
lean_object* v_val_4387_; lean_object* v___x_4388_; lean_object* v_env_4389_; lean_object* v___f_4390_; 
lean_del_object(v___x_4302_);
v_val_4387_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref_n(v_val_4387_, 2);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4388_ = lean_st_ref_get(v_a_3741_);
v_env_4389_ = lean_ctor_get(v___x_4388_, 0);
lean_inc_ref(v_env_4389_);
lean_dec(v___x_4388_);
v___f_4390_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4390_, 0, v_val_4387_);
lean_closure_set(v___f_4390_, 1, v___f_4386_);
if (v_forceExpose_3739_ == 0)
{
if (v___x_4305_ == 0)
{
lean_dec_ref(v_env_4389_);
lean_dec_ref(v_val_4387_);
v___y_4191_ = v_a_4300_;
v___y_4192_ = v___f_4390_;
v___y_4193_ = v___x_4384_;
v___y_4194_ = v___x_4365_;
goto v___jp_4190_;
}
else
{
lean_object* v___x_4391_; uint8_t v_isModule_4392_; 
v___x_4391_ = l_Lean_Environment_header(v_env_4389_);
lean_dec_ref(v_env_4389_);
v_isModule_4392_ = lean_ctor_get_uint8(v___x_4391_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4391_);
if (v_isModule_4392_ == 0)
{
lean_dec_ref(v_val_4387_);
v___y_4191_ = v_a_4300_;
v___y_4192_ = v___f_4390_;
v___y_4193_ = v___x_4384_;
v___y_4194_ = v___x_4365_;
goto v___jp_4190_;
}
else
{
if (v___x_4150_ == 0)
{
lean_object* v___x_4393_; lean_object* v___x_4394_; 
v___x_4393_ = lean_box(0);
v___x_4394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4387_, v_forceExpose_3739_, v___f_4390_, v___x_4393_, v_a_3740_, v_a_3741_);
lean_dec_ref(v_val_4387_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4394_;
goto v___jp_4163_;
}
else
{
lean_object* v_toConstantVal_4395_; lean_object* v_name_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; 
v_toConstantVal_4395_ = lean_ctor_get(v_val_4387_, 0);
v_name_4396_ = lean_ctor_get(v_toConstantVal_4395_, 0);
v___x_4397_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4396_);
v___x_4398_ = l_Lean_MessageData_ofName(v_name_4396_);
v___x_4399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4397_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4399_);
lean_ctor_set(v___x_4401_, 1, v___x_4400_);
v___x_4402_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4401_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; lean_object* v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4387_, v_forceExpose_3739_, v___f_4390_, v_a_4403_, v_a_3740_, v_a_3741_);
lean_dec_ref(v_val_4387_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4404_;
goto v___jp_4163_;
}
else
{
lean_dec_ref(v___f_4390_);
lean_dec_ref(v_val_4387_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4402_;
goto v___jp_4163_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4389_);
lean_dec_ref(v_val_4387_);
v___y_4191_ = v_a_4300_;
v___y_4192_ = v___f_4390_;
v___y_4193_ = v___x_4384_;
v___y_4194_ = v___x_4365_;
goto v___jp_4190_;
}
}
case 1:
{
lean_object* v_val_4405_; lean_object* v___x_4406_; 
lean_del_object(v___x_4302_);
v_val_4405_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref(v_val_4405_);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4406_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4386_, v_forceExpose_3739_, v___x_4305_, v___x_4384_, v_cls_3933_, v_val_4405_, v_a_3740_, v_a_3741_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4406_;
goto v___jp_4163_;
}
case 5:
{
lean_object* v_defns_4407_; 
lean_del_object(v___x_4302_);
v_defns_4407_ = lean_ctor_get(v_decl_3738_, 0);
if (lean_obj_tag(v_defns_4407_) == 1)
{
lean_object* v_tail_4408_; 
v_tail_4408_ = lean_ctor_get(v_defns_4407_, 1);
if (lean_obj_tag(v_tail_4408_) == 0)
{
lean_object* v_head_4409_; lean_object* v___x_4410_; 
lean_inc_ref(v_defns_4407_);
lean_dec_ref_known(v_decl_3738_, 1);
v_head_4409_ = lean_ctor_get(v_defns_4407_, 0);
lean_inc(v_head_4409_);
lean_dec_ref_known(v_defns_4407_, 2);
v___x_4410_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4386_, v_forceExpose_3739_, v___x_4305_, v___x_4384_, v_cls_3933_, v_head_4409_, v_a_3740_, v_a_3741_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4410_;
goto v___jp_4163_;
}
else
{
lean_object* v___x_4411_; 
lean_dec_ref(v___f_4386_);
lean_inc_ref(v_decl_3738_);
v___x_4411_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec_ref_known(v_decl_3738_, 1);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4411_;
goto v___jp_4163_;
}
}
else
{
lean_object* v___x_4412_; 
lean_dec_ref(v___f_4386_);
lean_inc_ref(v_decl_3738_);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec_ref_known(v_decl_3738_, 1);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4412_;
goto v___jp_4163_;
}
}
case 3:
{
lean_object* v_val_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; lean_object* v_env_4416_; lean_object* v_env_4417_; lean_object* v___f_4418_; 
lean_del_object(v___x_4302_);
v_val_4413_ = lean_ctor_get(v_decl_3738_, 0);
lean_inc_ref_n(v_val_4413_, 2);
lean_dec_ref_known(v_decl_3738_, 1);
v___x_4414_ = lean_st_ref_get(v_a_3741_);
v___x_4415_ = lean_st_ref_get(v_a_3741_);
v_env_4416_ = lean_ctor_get(v___x_4414_, 0);
lean_inc_ref(v_env_4416_);
lean_dec(v___x_4414_);
v_env_4417_ = lean_ctor_get(v___x_4415_, 0);
lean_inc_ref(v_env_4417_);
lean_dec(v___x_4415_);
v___f_4418_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4418_, 0, v_val_4413_);
lean_closure_set(v___f_4418_, 1, v___f_4386_);
if (v_forceExpose_3739_ == 0)
{
if (v___x_4305_ == 0)
{
lean_dec_ref(v_env_4417_);
lean_dec_ref(v_env_4416_);
lean_dec_ref(v_val_4413_);
v___y_4184_ = v_a_4300_;
v___y_4185_ = v___x_4384_;
v___y_4186_ = v___f_4418_;
v___y_4187_ = v___x_4365_;
goto v___jp_4183_;
}
else
{
lean_object* v___x_4419_; uint8_t v_isModule_4420_; 
v___x_4419_ = l_Lean_Environment_header(v_env_4416_);
lean_dec_ref(v_env_4416_);
v_isModule_4420_ = lean_ctor_get_uint8(v___x_4419_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4419_);
if (v_isModule_4420_ == 0)
{
lean_dec_ref(v_env_4417_);
lean_dec_ref(v_val_4413_);
v___y_4184_ = v_a_4300_;
v___y_4185_ = v___x_4384_;
v___y_4186_ = v___f_4418_;
v___y_4187_ = v___x_4365_;
goto v___jp_4183_;
}
else
{
uint8_t v_isExporting_4421_; 
v_isExporting_4421_ = lean_ctor_get_uint8(v_env_4417_, sizeof(void*)*8);
lean_dec_ref(v_env_4417_);
if (v_isExporting_4421_ == 0)
{
if (v___x_4150_ == 0)
{
lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4422_ = lean_box(0);
v___x_4423_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4413_, v___f_4418_, v___x_4422_, v_a_3740_, v_a_3741_);
lean_dec_ref(v_val_4413_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4423_;
goto v___jp_4163_;
}
else
{
lean_object* v_toConstantVal_4424_; lean_object* v_name_4425_; lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v_toConstantVal_4424_ = lean_ctor_get(v_val_4413_, 0);
v_name_4425_ = lean_ctor_get(v_toConstantVal_4424_, 0);
v___x_4426_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4425_);
v___x_4427_ = l_Lean_MessageData_ofName(v_name_4425_);
v___x_4428_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4426_);
lean_ctor_set(v___x_4428_, 1, v___x_4427_);
v___x_4429_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3933_, v___x_4430_, v_a_3740_, v_a_3741_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4433_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref_known(v___x_4431_, 1);
v___x_4433_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4413_, v___f_4418_, v_a_4432_, v_a_3740_, v_a_3741_);
lean_dec_ref(v_val_4413_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4433_;
goto v___jp_4163_;
}
else
{
lean_dec_ref(v___f_4418_);
lean_dec_ref(v_val_4413_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4431_;
goto v___jp_4163_;
}
}
}
else
{
lean_dec_ref(v_val_4413_);
v___y_4184_ = v_a_4300_;
v___y_4185_ = v___x_4384_;
v___y_4186_ = v___f_4418_;
v___y_4187_ = v___x_4365_;
goto v___jp_4183_;
}
}
}
}
else
{
lean_dec_ref(v_env_4417_);
lean_dec_ref(v_env_4416_);
lean_dec_ref(v_val_4413_);
v___y_4184_ = v_a_4300_;
v___y_4185_ = v___x_4384_;
v___y_4186_ = v___f_4418_;
v___y_4187_ = v___x_4365_;
goto v___jp_4183_;
}
}
case 0:
{
lean_object* v_val_4434_; lean_object* v_toConstantVal_4435_; lean_object* v_name_4436_; lean_object* v___x_4438_; 
lean_dec_ref(v___f_4386_);
v_val_4434_ = lean_ctor_get(v_decl_3738_, 0);
v_toConstantVal_4435_ = lean_ctor_get(v_val_4434_, 0);
v_name_4436_ = lean_ctor_get(v_toConstantVal_4435_, 0);
lean_inc_ref(v_val_4434_);
if (v_isShared_4303_ == 0)
{
lean_ctor_set(v___x_4302_, 0, v_val_4434_);
v___x_4438_ = v___x_4302_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v_val_4434_);
v___x_4438_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
uint8_t v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4439_ = 2;
v___x_4440_ = lean_box(v___x_4439_);
v___x_4441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4441_, 0, v___x_4438_);
lean_ctor_set(v___x_4441_, 1, v___x_4440_);
lean_inc(v_name_4436_);
v___x_4442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4442_, 0, v_name_4436_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3738_, v___x_4305_, v_cls_3933_, v___x_4380_, v___x_4384_, v___x_4442_, v___x_4384_, v_a_3740_, v_a_3741_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4443_;
goto v___jp_4163_;
}
}
default: 
{
lean_object* v___x_4445_; 
lean_dec_ref(v___f_4386_);
lean_del_object(v___x_4302_);
lean_inc(v_decl_3738_);
v___x_4445_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3738_, v_cls_3933_, v_decl_3738_, v_a_3740_, v_a_3741_);
lean_dec(v_decl_3738_);
v___y_4164_ = v_a_4300_;
v___y_4165_ = v___x_4365_;
v___y_4166_ = v___x_4445_;
goto v___jp_4163_;
}
}
}
}
}
}
}
}
v___jp_3743_:
{
lean_object* v___x_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3754_; 
v___x_3747_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3744_, v___y_3745_);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3754_ == 0)
{
lean_object* v_unused_3755_; 
v_unused_3755_ = lean_ctor_get(v___x_3747_, 0);
lean_dec(v_unused_3755_);
v___x_3749_ = v___x_3747_;
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
else
{
lean_dec(v___x_3747_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3754_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3752_; 
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v_a_3746_);
v___x_3752_ = v___x_3749_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3746_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
v___jp_3756_:
{
lean_object* v___x_3760_; lean_object* v___x_3762_; uint8_t v_isShared_3763_; uint8_t v_isSharedCheck_3767_; 
v___x_3760_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3757_, v___y_3758_);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3760_);
if (v_isSharedCheck_3767_ == 0)
{
lean_object* v_unused_3768_; 
v_unused_3768_ = lean_ctor_get(v___x_3760_, 0);
lean_dec(v_unused_3768_);
v___x_3762_ = v___x_3760_;
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
else
{
lean_dec(v___x_3760_);
v___x_3762_ = lean_box(0);
v_isShared_3763_ = v_isSharedCheck_3767_;
goto v_resetjp_3761_;
}
v_resetjp_3761_:
{
lean_object* v___x_3765_; 
if (v_isShared_3763_ == 0)
{
lean_ctor_set_tag(v___x_3762_, 1);
lean_ctor_set(v___x_3762_, 0, v_a_3759_);
v___x_3765_ = v___x_3762_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_a_3759_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
v___jp_3769_:
{
lean_object* v___x_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
v___x_3773_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3771_, v___y_3770_);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3773_);
if (v_isSharedCheck_3780_ == 0)
{
lean_object* v_unused_3781_; 
v_unused_3781_ = lean_ctor_get(v___x_3773_, 0);
lean_dec(v_unused_3781_);
v___x_3775_ = v___x_3773_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_dec(v___x_3773_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
lean_ctor_set(v___x_3775_, 0, v_a_3772_);
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3772_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
v___jp_3782_:
{
lean_object* v___x_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3793_; 
v___x_3786_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3784_, v___y_3783_);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3793_ == 0)
{
lean_object* v_unused_3794_; 
v_unused_3794_ = lean_ctor_get(v___x_3786_, 0);
lean_dec(v_unused_3794_);
v___x_3788_ = v___x_3786_;
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v___x_3786_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3793_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 1);
lean_ctor_set(v___x_3788_, 0, v_a_3785_);
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_a_3785_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
v___jp_3798_:
{
lean_object* v___x_3810_; 
lean_inc_ref(v___y_3803_);
v___x_3810_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3808_, v___y_3803_, v___y_3799_, v___y_3809_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v___x_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref_known(v___x_3810_, 1);
lean_inc_ref(v___y_3801_);
v___x_3811_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3801_, v___y_3802_);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3857_ == 0)
{
lean_object* v_unused_3858_; 
v_unused_3858_ = lean_ctor_get(v___x_3811_, 0);
lean_dec(v_unused_3858_);
v___x_3813_ = v___x_3811_;
v_isShared_3814_ = v_isSharedCheck_3857_;
goto v_resetjp_3812_;
}
else
{
lean_dec(v___x_3811_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3857_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
lean_object* v_options_3815_; lean_object* v___x_3816_; uint8_t v___x_3817_; 
v_options_3815_ = lean_ctor_get(v___y_3800_, 1);
v___x_3816_ = l_Lean_Elab_async;
v___x_3817_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3815_, v___x_3816_);
if (v___x_3817_ == 0)
{
lean_object* v___x_3818_; lean_object* v_r_3819_; 
lean_del_object(v___x_3813_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v___y_3804_);
v___x_3818_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3803_, v___y_3802_);
lean_dec_ref(v___x_3818_);
v_r_3819_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3738_, v___y_3800_, v___y_3802_);
if (lean_obj_tag(v_r_3819_) == 0)
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3829_; 
v_a_3820_ = lean_ctor_get(v_r_3819_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v_r_3819_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3822_ = v_r_3819_;
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v_r_3819_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3829_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
lean_inc(v_a_3820_);
if (v_isShared_3823_ == 0)
{
lean_ctor_set_tag(v___x_3822_, 1);
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
lean_object* v___x_3826_; 
v___x_3826_ = lean_apply_2(v___y_3807_, v___x_3825_, lean_box(0));
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_dec_ref_known(v___x_3826_, 1);
v___y_3770_ = v___y_3802_;
v___y_3771_ = v___y_3801_;
v_a_3772_ = v_a_3820_;
goto v___jp_3769_;
}
else
{
lean_object* v_a_3827_; 
lean_dec(v_a_3820_);
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3783_ = v___y_3802_;
v___y_3784_ = v___y_3801_;
v_a_3785_ = v_a_3827_;
goto v___jp_3782_;
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; 
v_a_3830_ = lean_ctor_get(v_r_3819_, 0);
lean_inc(v_a_3830_);
lean_dec_ref_known(v_r_3819_, 1);
v___x_3831_ = lean_box(0);
v___x_3832_ = lean_apply_2(v___y_3807_, v___x_3831_, lean_box(0));
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_dec_ref_known(v___x_3832_, 1);
v___y_3783_ = v___y_3802_;
v___y_3784_ = v___y_3801_;
v_a_3785_ = v_a_3830_;
goto v___jp_3782_;
}
else
{
lean_object* v_a_3833_; 
lean_dec(v_a_3830_);
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v___y_3783_ = v___y_3802_;
v___y_3784_ = v___y_3801_;
v_a_3785_ = v_a_3833_;
goto v___jp_3782_;
}
}
}
else
{
lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_dec_ref(v___y_3807_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v___y_3801_);
lean_dec(v_decl_3738_);
v___x_3834_ = l_IO_CancelToken_new();
if (v_isShared_3814_ == 0)
{
lean_ctor_set_tag(v___x_3813_, 1);
lean_ctor_set(v___x_3813_, 0, v___x_3834_);
v___x_3836_ = v___x_3813_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3834_);
v___x_3836_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v___x_3837_ = lean_unsigned_to_nat(0u);
v___x_3838_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3839_ = l_Lean_Name_toString(v___x_3838_, v___y_3806_);
lean_inc_ref(v___x_3836_);
v___x_3840_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3805_, v___x_3836_, v___x_3839_, v___y_3800_, v___y_3802_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v_a_3841_; lean_object* v_checked_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; 
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v_checked_3842_ = lean_ctor_get(v___y_3804_, 2);
lean_inc_ref(v_checked_3842_);
lean_dec_ref(v___y_3804_);
v___x_3843_ = lean_io_map_task(v_a_3841_, v_checked_3842_, v___x_3837_, v_hasTrace_3797_);
v___x_3844_ = lean_box(0);
v___x_3845_ = lean_box(2);
v___x_3846_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3844_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
lean_ctor_set(v___x_3846_, 2, v___x_3836_);
lean_ctor_set(v___x_3846_, 3, v___x_3843_);
v___x_3847_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3846_, v___y_3802_);
return v___x_3847_;
}
else
{
lean_object* v_a_3848_; lean_object* v___x_3850_; uint8_t v_isShared_3851_; uint8_t v_isSharedCheck_3855_; 
lean_dec_ref(v___x_3836_);
lean_dec_ref(v___y_3804_);
v_a_3848_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3850_ = v___x_3840_;
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
else
{
lean_inc(v_a_3848_);
lean_dec(v___x_3840_);
v___x_3850_ = lean_box(0);
v_isShared_3851_ = v_isSharedCheck_3855_;
goto v_resetjp_3849_;
}
v_resetjp_3849_:
{
lean_object* v___x_3853_; 
if (v_isShared_3851_ == 0)
{
v___x_3853_ = v___x_3850_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v_a_3848_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3871_; 
lean_dec_ref(v___y_3807_);
lean_dec_ref(v___y_3805_);
lean_dec_ref(v___y_3804_);
lean_dec_ref(v___y_3803_);
lean_dec_ref(v___y_3801_);
lean_dec(v_decl_3738_);
v_a_3859_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3871_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3871_ == 0)
{
v___x_3861_ = v___x_3810_;
v_isShared_3862_ = v_isSharedCheck_3871_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3810_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3871_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v_ref_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3869_; 
v_ref_3863_ = lean_ctor_get(v___y_3800_, 4);
v___x_3864_ = lean_io_error_to_string(v_a_3859_);
v___x_3865_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
v___x_3866_ = l_Lean_MessageData_ofFormat(v___x_3865_);
lean_inc(v_ref_3863_);
v___x_3867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3867_, 0, v_ref_3863_);
lean_ctor_set(v___x_3867_, 1, v___x_3866_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3867_);
v___x_3869_ = v___x_3861_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3870_; 
v_reuseFailAlloc_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3870_, 0, v___x_3867_);
v___x_3869_ = v_reuseFailAlloc_3870_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
return v___x_3869_;
}
}
}
}
v___jp_3872_:
{
uint8_t v___x_3883_; lean_object* v___x_3884_; 
v___x_3883_ = 1;
lean_inc_ref(v___y_3875_);
v___x_3884_ = l_Lean_Environment_addConstAsync(v___y_3875_, v___y_3876_, v___y_3881_, v___y_3882_, v_hasTrace_3797_, v___x_3883_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v_mainEnv_3886_; lean_object* v_asyncEnv_3887_; lean_object* v___f_3888_; lean_object* v___f_3889_; lean_object* v___x_3890_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc_n(v_a_3885_, 3);
lean_dec_ref_known(v___x_3884_, 1);
v_mainEnv_3886_ = lean_ctor_get(v_a_3885_, 0);
lean_inc_ref(v_mainEnv_3886_);
v_asyncEnv_3887_ = lean_ctor_get(v_a_3885_, 1);
lean_inc_ref_n(v_asyncEnv_3887_, 2);
lean_inc_ref(v___y_3873_);
lean_inc(v___y_3874_);
v___f_3888_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3888_, 0, v___y_3874_);
lean_closure_set(v___f_3888_, 1, v_a_3885_);
lean_closure_set(v___f_3888_, 2, v___y_3873_);
lean_inc(v_decl_3738_);
v___f_3889_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3889_, 0, v_asyncEnv_3887_);
lean_closure_set(v___f_3889_, 1, v_a_3885_);
lean_closure_set(v___f_3889_, 2, v_decl_3738_);
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v___y_3879_);
if (lean_obj_tag(v___y_3880_) == 0)
{
lean_inc_ref(v___x_3890_);
v___y_3799_ = v___x_3890_;
v___y_3800_ = v___y_3878_;
v___y_3801_ = v_mainEnv_3886_;
v___y_3802_ = v___y_3877_;
v___y_3803_ = v_asyncEnv_3887_;
v___y_3804_ = v___y_3875_;
v___y_3805_ = v___f_3889_;
v___y_3806_ = v___x_3883_;
v___y_3807_ = v___f_3888_;
v___y_3808_ = v_a_3885_;
v___y_3809_ = v___x_3890_;
goto v___jp_3798_;
}
else
{
v___y_3799_ = v___x_3890_;
v___y_3800_ = v___y_3878_;
v___y_3801_ = v_mainEnv_3886_;
v___y_3802_ = v___y_3877_;
v___y_3803_ = v_asyncEnv_3887_;
v___y_3804_ = v___y_3875_;
v___y_3805_ = v___f_3889_;
v___y_3806_ = v___x_3883_;
v___y_3807_ = v___f_3888_;
v___y_3808_ = v_a_3885_;
v___y_3809_ = v___y_3880_;
goto v___jp_3798_;
}
}
else
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3903_; 
lean_dec(v___y_3880_);
lean_dec_ref(v___y_3879_);
lean_dec_ref(v___y_3875_);
lean_dec(v_decl_3738_);
v_a_3891_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3893_ = v___x_3884_;
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3884_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3903_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v_ref_3895_; lean_object* v___x_3896_; lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3901_; 
v_ref_3895_ = lean_ctor_get(v___y_3878_, 4);
v___x_3896_ = lean_io_error_to_string(v_a_3891_);
v___x_3897_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3897_, 0, v___x_3896_);
v___x_3898_ = l_Lean_MessageData_ofFormat(v___x_3897_);
lean_inc(v_ref_3895_);
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v_ref_3895_);
lean_ctor_set(v___x_3899_, 1, v___x_3898_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3899_);
v___x_3901_ = v___x_3893_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v___x_3899_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
v___jp_3904_:
{
lean_object* v___x_3911_; 
v___x_3911_ = lean_st_ref_get(v___y_3910_);
if (lean_obj_tag(v_exportedInfo_x3f_3908_) == 0)
{
lean_object* v_env_3912_; lean_object* v___x_3913_; 
v_env_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc_ref(v_env_3912_);
lean_dec(v___x_3911_);
v___x_3913_ = lean_box(0);
v___y_3873_ = v___y_3909_;
v___y_3874_ = v___y_3910_;
v___y_3875_ = v_env_3912_;
v___y_3876_ = v___y_3905_;
v___y_3877_ = v___y_3910_;
v___y_3878_ = v___y_3909_;
v___y_3879_ = v___y_3906_;
v___y_3880_ = v_exportedInfo_x3f_3908_;
v___y_3881_ = v___y_3907_;
v___y_3882_ = v___x_3913_;
goto v___jp_3872_;
}
else
{
lean_object* v_env_3914_; lean_object* v_val_3915_; uint8_t v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v_env_3914_ = lean_ctor_get(v___x_3911_, 0);
lean_inc_ref(v_env_3914_);
lean_dec(v___x_3911_);
v_val_3915_ = lean_ctor_get(v_exportedInfo_x3f_3908_, 0);
v___x_3916_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3915_);
v___x_3917_ = lean_box(v___x_3916_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v___y_3873_ = v___y_3909_;
v___y_3874_ = v___y_3910_;
v___y_3875_ = v_env_3914_;
v___y_3876_ = v___y_3905_;
v___y_3877_ = v___y_3910_;
v___y_3878_ = v___y_3909_;
v___y_3879_ = v___y_3906_;
v___y_3880_ = v_exportedInfo_x3f_3908_;
v___y_3881_ = v___y_3907_;
v___y_3882_ = v___x_3918_;
goto v___jp_3872_;
}
}
v___jp_3919_:
{
lean_object* v___x_3925_; 
lean_inc_ref(v___y_3921_);
v___x_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3925_, 0, v___y_3921_);
v___y_3905_ = v___y_3920_;
v___y_3906_ = v___y_3921_;
v___y_3907_ = v___y_3922_;
v_exportedInfo_x3f_3908_ = v___x_3925_;
v___y_3909_ = v___y_3923_;
v___y_3910_ = v___y_3924_;
goto v___jp_3904_;
}
v___jp_3926_:
{
lean_object* v___x_3932_; 
lean_inc_ref(v___y_3928_);
v___x_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___y_3928_);
v___y_3905_ = v___y_3927_;
v___y_3906_ = v___y_3928_;
v___y_3907_ = v___y_3929_;
v_exportedInfo_x3f_3908_ = v___x_3932_;
v___y_3909_ = v___y_3930_;
v___y_3910_ = v___y_3931_;
goto v___jp_3904_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4838_, lean_object* v_forceExpose_4839_, lean_object* v_a_4840_, lean_object* v_a_4841_, lean_object* v_a_4842_){
_start:
{
uint8_t v_forceExpose_boxed_4843_; lean_object* v_res_4844_; 
v_forceExpose_boxed_4843_ = lean_unbox(v_forceExpose_4839_);
v_res_4844_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4838_, v_forceExpose_boxed_4843_, v_a_4840_, v_a_4841_);
lean_dec(v_a_4841_);
lean_dec_ref(v_a_4840_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_){
_start:
{
lean_object* v___x_4849_; 
v___x_4849_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4845_, v___y_4846_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4850_, lean_object* v___y_4851_, lean_object* v___y_4852_, lean_object* v___y_4853_){
_start:
{
lean_object* v_res_4854_; 
v_res_4854_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4850_, v___y_4851_, v___y_4852_);
lean_dec(v___y_4852_);
lean_dec_ref(v___y_4851_);
lean_dec_ref(v_opt_4850_);
return v_res_4854_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4855_, lean_object* v_x_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_){
_start:
{
if (lean_obj_tag(v_x_4855_) == 0)
{
lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4860_ = l_List_reverse___redArg(v_x_4856_);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v___x_4860_);
return v___x_4861_;
}
else
{
lean_object* v_head_4862_; lean_object* v_tail_4863_; lean_object* v___x_4865_; uint8_t v_isShared_4866_; uint8_t v_isSharedCheck_4881_; 
v_head_4862_ = lean_ctor_get(v_x_4855_, 0);
v_tail_4863_ = lean_ctor_get(v_x_4855_, 1);
v_isSharedCheck_4881_ = !lean_is_exclusive(v_x_4855_);
if (v_isSharedCheck_4881_ == 0)
{
v___x_4865_ = v_x_4855_;
v_isShared_4866_ = v_isSharedCheck_4881_;
goto v_resetjp_4864_;
}
else
{
lean_inc(v_tail_4863_);
lean_inc(v_head_4862_);
lean_dec(v_x_4855_);
v___x_4865_ = lean_box(0);
v_isShared_4866_ = v_isSharedCheck_4881_;
goto v_resetjp_4864_;
}
v_resetjp_4864_:
{
lean_object* v___x_4867_; 
v___x_4867_ = l_Lean_snapshotEnvLinterOptions(v_head_4862_, v___y_4857_, v___y_4858_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_object* v_a_4868_; lean_object* v___x_4870_; 
v_a_4868_ = lean_ctor_get(v___x_4867_, 0);
lean_inc(v_a_4868_);
lean_dec_ref_known(v___x_4867_, 1);
if (v_isShared_4866_ == 0)
{
lean_ctor_set(v___x_4865_, 1, v_x_4856_);
lean_ctor_set(v___x_4865_, 0, v_a_4868_);
v___x_4870_ = v___x_4865_;
goto v_reusejp_4869_;
}
else
{
lean_object* v_reuseFailAlloc_4872_; 
v_reuseFailAlloc_4872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4872_, 0, v_a_4868_);
lean_ctor_set(v_reuseFailAlloc_4872_, 1, v_x_4856_);
v___x_4870_ = v_reuseFailAlloc_4872_;
goto v_reusejp_4869_;
}
v_reusejp_4869_:
{
v_x_4855_ = v_tail_4863_;
v_x_4856_ = v___x_4870_;
goto _start;
}
}
else
{
lean_object* v_a_4873_; lean_object* v___x_4875_; uint8_t v_isShared_4876_; uint8_t v_isSharedCheck_4880_; 
lean_del_object(v___x_4865_);
lean_dec(v_tail_4863_);
lean_dec(v_x_4856_);
v_a_4873_ = lean_ctor_get(v___x_4867_, 0);
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4867_);
if (v_isSharedCheck_4880_ == 0)
{
v___x_4875_ = v___x_4867_;
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
else
{
lean_inc(v_a_4873_);
lean_dec(v___x_4867_);
v___x_4875_ = lean_box(0);
v_isShared_4876_ = v_isSharedCheck_4880_;
goto v_resetjp_4874_;
}
v_resetjp_4874_:
{
lean_object* v___x_4878_; 
if (v_isShared_4876_ == 0)
{
v___x_4878_ = v___x_4875_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4879_; 
v_reuseFailAlloc_4879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4879_, 0, v_a_4873_);
v___x_4878_ = v_reuseFailAlloc_4879_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
return v___x_4878_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4882_, lean_object* v_x_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_, lean_object* v___y_4886_){
_start:
{
lean_object* v_res_4887_; 
v_res_4887_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4882_, v_x_4883_, v___y_4884_, v___y_4885_);
lean_dec(v___y_4885_);
lean_dec_ref(v___y_4884_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4888_, uint8_t v_forceExpose_4889_, lean_object* v_a_4890_, lean_object* v_a_4891_){
_start:
{
lean_object* v___x_4893_; 
lean_inc(v_decl_4888_);
v___x_4893_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4888_, v_forceExpose_4889_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4893_) == 0)
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; 
lean_dec_ref_known(v___x_4893_, 1);
v___x_4894_ = l_Lean_Declaration_getTopLevelNames(v_decl_4888_);
v___x_4895_ = lean_box(0);
v___x_4896_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4894_, v___x_4895_, v_a_4890_, v_a_4891_);
if (lean_obj_tag(v___x_4896_) == 0)
{
lean_object* v___x_4898_; uint8_t v_isShared_4899_; uint8_t v_isSharedCheck_4904_; 
v_isSharedCheck_4904_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4904_ == 0)
{
lean_object* v_unused_4905_; 
v_unused_4905_ = lean_ctor_get(v___x_4896_, 0);
lean_dec(v_unused_4905_);
v___x_4898_ = v___x_4896_;
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
else
{
lean_dec(v___x_4896_);
v___x_4898_ = lean_box(0);
v_isShared_4899_ = v_isSharedCheck_4904_;
goto v_resetjp_4897_;
}
v_resetjp_4897_:
{
lean_object* v___x_4900_; lean_object* v___x_4902_; 
v___x_4900_ = lean_box(0);
if (v_isShared_4899_ == 0)
{
lean_ctor_set(v___x_4898_, 0, v___x_4900_);
v___x_4902_ = v___x_4898_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4903_; 
v_reuseFailAlloc_4903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4903_, 0, v___x_4900_);
v___x_4902_ = v_reuseFailAlloc_4903_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
return v___x_4902_;
}
}
}
else
{
lean_object* v_a_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4913_; 
v_a_4906_ = lean_ctor_get(v___x_4896_, 0);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4908_ = v___x_4896_;
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_a_4906_);
lean_dec(v___x_4896_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4913_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4911_; 
if (v_isShared_4909_ == 0)
{
v___x_4911_ = v___x_4908_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v_a_4906_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
}
else
{
lean_dec(v_decl_4888_);
return v___x_4893_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4914_, lean_object* v_forceExpose_4915_, lean_object* v_a_4916_, lean_object* v_a_4917_, lean_object* v_a_4918_){
_start:
{
uint8_t v_forceExpose_boxed_4919_; lean_object* v_res_4920_; 
v_forceExpose_boxed_4919_ = lean_unbox(v_forceExpose_4915_);
v_res_4920_ = l_Lean_addDecl(v_decl_4914_, v_forceExpose_boxed_4919_, v_a_4916_, v_a_4917_);
lean_dec(v_a_4917_);
lean_dec_ref(v_a_4916_);
return v_res_4920_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4921_, lean_object* v_b_4922_, lean_object* v___y_4923_){
_start:
{
if (lean_obj_tag(v_as_x27_4921_) == 0)
{
lean_object* v___x_4925_; 
v___x_4925_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4925_, 0, v_b_4922_);
return v___x_4925_;
}
else
{
lean_object* v_head_4926_; lean_object* v_tail_4927_; lean_object* v___x_4928_; lean_object* v_env_4929_; lean_object* v_nextMacroScope_4930_; lean_object* v_ngen_4931_; lean_object* v_auxDeclNGen_4932_; lean_object* v_traceState_4933_; lean_object* v_messages_4934_; lean_object* v_infoState_4935_; lean_object* v_snapshotTasks_4936_; lean_object* v___x_4938_; uint8_t v_isShared_4939_; uint8_t v_isSharedCheck_4948_; 
v_head_4926_ = lean_ctor_get(v_as_x27_4921_, 0);
v_tail_4927_ = lean_ctor_get(v_as_x27_4921_, 1);
v___x_4928_ = lean_st_ref_take(v___y_4923_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
v_nextMacroScope_4930_ = lean_ctor_get(v___x_4928_, 1);
v_ngen_4931_ = lean_ctor_get(v___x_4928_, 2);
v_auxDeclNGen_4932_ = lean_ctor_get(v___x_4928_, 3);
v_traceState_4933_ = lean_ctor_get(v___x_4928_, 4);
v_messages_4934_ = lean_ctor_get(v___x_4928_, 6);
v_infoState_4935_ = lean_ctor_get(v___x_4928_, 7);
v_snapshotTasks_4936_ = lean_ctor_get(v___x_4928_, 8);
v_isSharedCheck_4948_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4948_ == 0)
{
lean_object* v_unused_4949_; 
v_unused_4949_ = lean_ctor_get(v___x_4928_, 5);
lean_dec(v_unused_4949_);
v___x_4938_ = v___x_4928_;
v_isShared_4939_ = v_isSharedCheck_4948_;
goto v_resetjp_4937_;
}
else
{
lean_inc(v_snapshotTasks_4936_);
lean_inc(v_infoState_4935_);
lean_inc(v_messages_4934_);
lean_inc(v_traceState_4933_);
lean_inc(v_auxDeclNGen_4932_);
lean_inc(v_ngen_4931_);
lean_inc(v_nextMacroScope_4930_);
lean_inc(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4938_ = lean_box(0);
v_isShared_4939_ = v_isSharedCheck_4948_;
goto v_resetjp_4937_;
}
v_resetjp_4937_:
{
lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4943_; 
lean_inc(v_head_4926_);
v___x_4940_ = l_Lean_markMeta(v_env_4929_, v_head_4926_);
v___x_4941_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4939_ == 0)
{
lean_ctor_set(v___x_4938_, 5, v___x_4941_);
lean_ctor_set(v___x_4938_, 0, v___x_4940_);
v___x_4943_ = v___x_4938_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4947_; 
v_reuseFailAlloc_4947_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4947_, 0, v___x_4940_);
lean_ctor_set(v_reuseFailAlloc_4947_, 1, v_nextMacroScope_4930_);
lean_ctor_set(v_reuseFailAlloc_4947_, 2, v_ngen_4931_);
lean_ctor_set(v_reuseFailAlloc_4947_, 3, v_auxDeclNGen_4932_);
lean_ctor_set(v_reuseFailAlloc_4947_, 4, v_traceState_4933_);
lean_ctor_set(v_reuseFailAlloc_4947_, 5, v___x_4941_);
lean_ctor_set(v_reuseFailAlloc_4947_, 6, v_messages_4934_);
lean_ctor_set(v_reuseFailAlloc_4947_, 7, v_infoState_4935_);
lean_ctor_set(v_reuseFailAlloc_4947_, 8, v_snapshotTasks_4936_);
v___x_4943_ = v_reuseFailAlloc_4947_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
lean_object* v___x_4944_; lean_object* v___x_4945_; 
v___x_4944_ = lean_st_ref_put(v___y_4923_, v___x_4943_);
v___x_4945_ = lean_box(0);
v_as_x27_4921_ = v_tail_4927_;
v_b_4922_ = v___x_4945_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4950_, lean_object* v_b_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
lean_object* v_res_4954_; 
v_res_4954_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4950_, v_b_4951_, v___y_4952_);
lean_dec(v___y_4952_);
lean_dec(v_as_x27_4950_);
return v_res_4954_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4955_, uint8_t v_logCompileErrors_4956_, uint8_t v_markMeta_4957_, lean_object* v_a_4958_, lean_object* v_a_4959_){
_start:
{
uint8_t v___x_4961_; lean_object* v___x_4962_; 
v___x_4961_ = 0;
lean_inc(v_decl_4955_);
v___x_4962_ = l_Lean_addDecl(v_decl_4955_, v___x_4961_, v_a_4958_, v_a_4959_);
if (lean_obj_tag(v___x_4962_) == 0)
{
lean_dec_ref_known(v___x_4962_, 1);
if (v_markMeta_4957_ == 0)
{
lean_object* v___x_4963_; 
v___x_4963_ = l_Lean_compileDecl(v_decl_4955_, v_logCompileErrors_4956_, v_a_4958_, v_a_4959_);
return v___x_4963_;
}
else
{
lean_object* v___x_4964_; lean_object* v___x_4965_; lean_object* v___x_4966_; lean_object* v___x_4967_; 
lean_inc(v_decl_4955_);
v___x_4964_ = l_Lean_Declaration_getNames(v_decl_4955_);
v___x_4965_ = lean_box(0);
v___x_4966_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4964_, v___x_4965_, v_a_4959_);
lean_dec(v___x_4964_);
lean_dec_ref(v___x_4966_);
v___x_4967_ = l_Lean_compileDecl(v_decl_4955_, v_logCompileErrors_4956_, v_a_4958_, v_a_4959_);
return v___x_4967_;
}
}
else
{
lean_dec(v_decl_4955_);
return v___x_4962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4968_, lean_object* v_logCompileErrors_4969_, lean_object* v_markMeta_4970_, lean_object* v_a_4971_, lean_object* v_a_4972_, lean_object* v_a_4973_){
_start:
{
uint8_t v_logCompileErrors_boxed_4974_; uint8_t v_markMeta_boxed_4975_; lean_object* v_res_4976_; 
v_logCompileErrors_boxed_4974_ = lean_unbox(v_logCompileErrors_4969_);
v_markMeta_boxed_4975_ = lean_unbox(v_markMeta_4970_);
v_res_4976_ = l_Lean_addAndCompile(v_decl_4968_, v_logCompileErrors_boxed_4974_, v_markMeta_boxed_4975_, v_a_4971_, v_a_4972_);
lean_dec(v_a_4972_);
lean_dec_ref(v_a_4971_);
return v_res_4976_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4977_, lean_object* v_as_x27_4978_, lean_object* v_b_4979_, lean_object* v_a_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
lean_object* v___x_4984_; 
v___x_4984_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4978_, v_b_4979_, v___y_4982_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4985_, lean_object* v_as_x27_4986_, lean_object* v_b_4987_, lean_object* v_a_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v_res_4992_; 
v_res_4992_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4985_, v_as_x27_4986_, v_b_4987_, v_a_4988_, v___y_4989_, v___y_4990_);
lean_dec(v___y_4990_);
lean_dec_ref(v___y_4989_);
lean_dec(v_as_x27_4986_);
lean_dec(v_as_4985_);
return v_res_4992_;
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
