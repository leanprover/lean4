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
lean_object* v_toCold_117_; lean_object* v_options_118_; lean_object* v___x_119_; 
v_toCold_117_ = lean_ctor_get(v___y_114_, 0);
v_options_118_ = lean_ctor_get(v_toCold_117_, 2);
lean_inc_ref(v_options_118_);
v___x_119_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_options_118_, v___y_115_);
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
v___x_124_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
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
lean_object* v_a_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_192_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_192_ == 0)
{
v___x_143_ = v___x_140_;
v_isShared_144_ = v_isSharedCheck_192_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_a_141_);
lean_dec(v___x_140_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_192_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
uint8_t v___x_145_; 
v___x_145_ = lean_unbox(v_a_141_);
lean_dec(v_a_141_);
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
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_179_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_179_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_179_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_179_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v_env_155_; lean_object* v_nextMacroScope_156_; lean_object* v_ngen_157_; lean_object* v_auxDeclNGen_158_; lean_object* v_traceState_159_; lean_object* v_messages_160_; lean_object* v_infoState_161_; lean_object* v_snapshotTasks_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_177_; 
v___x_154_ = lean_st_ref_take(v_a_131_);
v_env_155_ = lean_ctor_get(v___x_154_, 0);
v_nextMacroScope_156_ = lean_ctor_get(v___x_154_, 1);
v_ngen_157_ = lean_ctor_get(v___x_154_, 2);
v_auxDeclNGen_158_ = lean_ctor_get(v___x_154_, 3);
v_traceState_159_ = lean_ctor_get(v___x_154_, 4);
v_messages_160_ = lean_ctor_get(v___x_154_, 6);
v_infoState_161_ = lean_ctor_get(v___x_154_, 7);
v_snapshotTasks_162_ = lean_ctor_get(v___x_154_, 8);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___x_154_, 5);
lean_dec(v_unused_178_);
v___x_164_ = v___x_154_;
v_isShared_165_ = v_isSharedCheck_177_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snapshotTasks_162_);
lean_inc(v_infoState_161_);
lean_inc(v_messages_160_);
lean_inc(v_traceState_159_);
lean_inc(v_auxDeclNGen_158_);
lean_inc(v_ngen_157_);
lean_inc(v_nextMacroScope_156_);
lean_inc(v_env_155_);
lean_dec(v___x_154_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_177_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_170_; 
v___x_166_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_167_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_166_, v_env_155_, v_declName_129_, v_a_150_);
v___x_168_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 5, v___x_168_);
lean_ctor_set(v___x_164_, 0, v___x_167_);
v___x_170_ = v___x_164_;
goto v_reusejp_169_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_167_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_nextMacroScope_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_ngen_157_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_auxDeclNGen_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_traceState_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_messages_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_infoState_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_snapshotTasks_162_);
v___x_170_ = v_reuseFailAlloc_176_;
goto v_reusejp_169_;
}
v_reusejp_169_:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_st_ref_put(v_a_131_, v___x_170_);
v___x_172_ = lean_box(0);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_172_);
v___x_174_ = v___x_152_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_declName_129_);
v_a_180_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_149_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_149_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v___x_188_; lean_object* v___x_190_; 
lean_dec(v_a_139_);
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v___x_188_ = lean_box(0);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 0, v___x_188_);
v___x_190_ = v___x_143_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v___x_188_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_a_139_);
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v_a_193_ = lean_ctor_get(v___x_140_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_140_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_140_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_140_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v___x_134_);
lean_dec(v_declName_129_);
v___x_201_ = lean_box(0);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_snapshotEnvLinterOptions(v_declName_203_, v_a_204_, v_a_205_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_208_, lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_208_, v___y_210_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_218_, lean_object* v_as_219_, size_t v_sz_220_, size_t v_i_221_, lean_object* v_b_222_, lean_object* v___y_223_, lean_object* v___y_224_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_218_, v_as_219_, v_sz_220_, v_i_221_, v_b_222_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_227_, lean_object* v_as_228_, lean_object* v_sz_229_, lean_object* v_i_230_, lean_object* v_b_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
size_t v_sz_boxed_235_; size_t v_i_boxed_236_; lean_object* v_res_237_; 
v_sz_boxed_235_ = lean_unbox_usize(v_sz_229_);
lean_dec(v_sz_229_);
v_i_boxed_236_ = lean_unbox_usize(v_i_230_);
lean_dec(v_i_230_);
v_res_237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_227_, v_as_228_, v_sz_boxed_235_, v_i_boxed_236_, v_b_231_, v___y_232_, v___y_233_);
lean_dec(v___y_233_);
lean_dec_ref(v___y_232_);
lean_dec_ref(v_as_228_);
lean_dec_ref(v_a_227_);
return v_res_237_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_238_){
_start:
{
if (lean_obj_tag(v_x_238_) == 1)
{
lean_object* v_pre_239_; 
v_pre_239_ = lean_ctor_get(v_x_238_, 0);
if (lean_obj_tag(v_pre_239_) == 0)
{
uint8_t v___x_240_; 
v___x_240_ = 1;
return v___x_240_;
}
else
{
v_x_238_ = v_pre_239_;
goto _start;
}
}
else
{
uint8_t v___x_242_; 
v___x_242_ = 0;
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_243_){
_start:
{
uint8_t v_res_244_; lean_object* v_r_245_; 
v_res_244_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_243_);
lean_dec(v_x_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_246_, lean_object* v_x_247_){
_start:
{
if (lean_obj_tag(v_x_247_) == 1)
{
lean_object* v_pre_248_; uint8_t v___x_249_; 
v_pre_248_ = lean_ctor_get(v_x_247_, 0);
lean_inc(v_pre_248_);
lean_dec_ref_known(v_x_247_, 2);
v___x_249_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_248_);
if (v___x_249_ == 0)
{
lean_dec(v_pre_248_);
return v_env_246_;
}
else
{
lean_object* v___x_250_; 
lean_inc(v_pre_248_);
v___x_250_ = l_Lean_Environment_registerNamespace(v_env_246_, v_pre_248_);
v_env_246_ = v___x_250_;
v_x_247_ = v_pre_248_;
goto _start;
}
}
else
{
lean_dec(v_x_247_);
return v_env_246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_252_, lean_object* v_name_253_){
_start:
{
lean_object* v_name_254_; uint32_t v___y_256_; 
v_name_254_ = l_Lean_privateToUserName(v_name_253_);
if (lean_obj_tag(v_name_254_) == 1)
{
lean_object* v_str_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v_str_260_ = lean_ctor_get(v_name_254_, 1);
lean_inc_ref(v_str_260_);
v___x_261_ = lean_unsigned_to_nat(0u);
v___x_262_ = lean_string_utf8_byte_size(v_str_260_);
v___x_263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_263_, 0, v_str_260_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_262_);
v___x_264_ = l_String_Slice_Pos_get_x3f(v___x_263_, v___x_261_);
lean_dec_ref_known(v___x_263_, 3);
if (lean_obj_tag(v___x_264_) == 0)
{
uint32_t v___x_265_; 
v___x_265_ = 65;
v___y_256_ = v___x_265_;
goto v___jp_255_;
}
else
{
lean_object* v_val_266_; uint32_t v___x_267_; 
v_val_266_ = lean_ctor_get(v___x_264_, 0);
lean_inc(v_val_266_);
lean_dec_ref_known(v___x_264_, 1);
v___x_267_ = lean_unbox_uint32(v_val_266_);
lean_dec(v_val_266_);
v___y_256_ = v___x_267_;
goto v___jp_255_;
}
}
else
{
lean_dec(v_name_254_);
return v_env_252_;
}
v___jp_255_:
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 95;
v___x_258_ = lean_uint32_dec_eq(v___y_256_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
v___x_259_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_252_, v_name_254_);
return v___x_259_;
}
else
{
lean_dec(v_name_254_);
return v_env_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_268_, lean_object* v_decl_269_, lean_object* v_ref_270_){
_start:
{
lean_object* v_defValue_272_; lean_object* v_descr_273_; lean_object* v_deprecation_x3f_274_; lean_object* v___x_275_; uint8_t v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
v_defValue_272_ = lean_ctor_get(v_decl_269_, 0);
v_descr_273_ = lean_ctor_get(v_decl_269_, 1);
v_deprecation_x3f_274_ = lean_ctor_get(v_decl_269_, 2);
v___x_275_ = lean_alloc_ctor(1, 0, 1);
v___x_276_ = lean_unbox(v_defValue_272_);
lean_ctor_set_uint8(v___x_275_, 0, v___x_276_);
lean_inc(v_deprecation_x3f_274_);
lean_inc_ref(v_descr_273_);
lean_inc_n(v_name_268_, 2);
v___x_277_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_277_, 0, v_name_268_);
lean_ctor_set(v___x_277_, 1, v_ref_270_);
lean_ctor_set(v___x_277_, 2, v___x_275_);
lean_ctor_set(v___x_277_, 3, v_descr_273_);
lean_ctor_set(v___x_277_, 4, v_deprecation_x3f_274_);
v___x_278_ = lean_register_option(v_name_268_, v___x_277_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_286_; 
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
lean_object* v_unused_287_; 
v_unused_287_ = lean_ctor_get(v___x_278_, 0);
lean_dec(v_unused_287_);
v___x_280_ = v___x_278_;
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
else
{
lean_dec(v___x_278_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_286_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_284_; 
lean_inc(v_defValue_272_);
v___x_282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_282_, 0, v_name_268_);
lean_ctor_set(v___x_282_, 1, v_defValue_272_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_284_ = v___x_280_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_288_; lean_object* v___x_290_; uint8_t v_isShared_291_; uint8_t v_isSharedCheck_295_; 
lean_dec(v_name_268_);
v_a_288_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_295_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_295_ == 0)
{
v___x_290_ = v___x_278_;
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
else
{
lean_inc(v_a_288_);
lean_dec(v___x_278_);
v___x_290_ = lean_box(0);
v_isShared_291_ = v_isSharedCheck_295_;
goto v_resetjp_289_;
}
v_resetjp_289_:
{
lean_object* v___x_293_; 
if (v_isShared_291_ == 0)
{
v___x_293_ = v___x_290_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_a_288_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
return v___x_293_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_296_, lean_object* v_decl_297_, lean_object* v_ref_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_296_, v_decl_297_, v_ref_298_);
lean_dec_ref(v_decl_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; 
v___x_318_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_319_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_320_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_321_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_318_, v___x_319_, v___x_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v___x_330_; lean_object* v_env_331_; lean_object* v___x_332_; lean_object* v_toCold_333_; lean_object* v_mctx_334_; lean_object* v_lctx_335_; lean_object* v_options_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_330_ = lean_st_ref_get(v___y_328_);
v_env_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc_ref(v_env_331_);
lean_dec(v___x_330_);
v___x_332_ = lean_st_ref_get(v___y_326_);
v_toCold_333_ = lean_ctor_get(v___y_327_, 0);
v_mctx_334_ = lean_ctor_get(v___x_332_, 0);
lean_inc_ref(v_mctx_334_);
lean_dec(v___x_332_);
v_lctx_335_ = lean_ctor_get(v___y_325_, 2);
v_options_336_ = lean_ctor_get(v_toCold_333_, 2);
lean_inc_ref(v_options_336_);
lean_inc_ref(v_lctx_335_);
v___x_337_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_337_, 0, v_env_331_);
lean_ctor_set(v___x_337_, 1, v_mctx_334_);
lean_ctor_set(v___x_337_, 2, v_lctx_335_);
lean_ctor_set(v___x_337_, 3, v_options_336_);
v___x_338_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set(v___x_338_, 1, v_msgData_324_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
lean_dec(v___y_344_);
lean_dec_ref(v___y_343_);
lean_dec(v___y_342_);
lean_dec_ref(v___y_341_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_370_; 
lean_inc_ref(v_s_347_);
v___x_354_ = l_Lean_MessageData_ofExpr(v_s_347_);
v___x_355_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_354_, v___y_349_, v___y_350_, v___y_351_, v___y_352_);
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_370_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_370_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_370_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; uint8_t v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_360_ = lean_st_ref_take(v___y_348_);
v___x_361_ = l_Lean_Expr_isSyntheticSorry(v_s_347_);
lean_dec_ref(v_s_347_);
v___x_362_ = lean_box(v___x_361_);
v___x_363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_362_);
lean_ctor_set(v___x_363_, 1, v_a_356_);
v___x_364_ = lean_array_push(v___x_360_, v___x_363_);
v___x_365_ = lean_st_ref_put(v___y_348_, v___x_364_);
v___x_366_ = lean_box(0);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_366_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_366_);
v___x_368_ = v_reuseFailAlloc_369_;
goto v_reusejp_367_;
}
v_reusejp_367_:
{
return v___x_368_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_){
_start:
{
lean_object* v_res_378_; 
v_res_378_ = l_Lean_warnIfUsesSorry___lam__0(v_s_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
lean_dec(v___y_374_);
lean_dec_ref(v___y_373_);
lean_dec(v___y_372_);
return v_res_378_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v_suppressElabErrors_387_, uint8_t v___y_388_, lean_object* v_x_389_){
_start:
{
if (lean_obj_tag(v_x_389_) == 1)
{
lean_object* v_pre_390_; 
v_pre_390_ = lean_ctor_get(v_x_389_, 0);
switch(lean_obj_tag(v_pre_390_))
{
case 1:
{
lean_object* v_pre_391_; 
v_pre_391_ = lean_ctor_get(v_pre_390_, 0);
switch(lean_obj_tag(v_pre_391_))
{
case 0:
{
lean_object* v_str_392_; lean_object* v_str_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_str_392_ = lean_ctor_get(v_x_389_, 1);
v_str_393_ = lean_ctor_get(v_pre_390_, 1);
v___x_394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_395_ = lean_string_dec_eq(v_str_393_, v___x_394_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_397_ = lean_string_dec_eq(v_str_393_, v___x_396_);
if (v___x_397_ == 0)
{
return v___x_397_;
}
else
{
lean_object* v___x_398_; uint8_t v___x_399_; 
v___x_398_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_399_ = lean_string_dec_eq(v_str_392_, v___x_398_);
if (v___x_399_ == 0)
{
return v___x_399_;
}
else
{
return v_suppressElabErrors_387_;
}
}
}
else
{
lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_400_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_401_ = lean_string_dec_eq(v_str_392_, v___x_400_);
if (v___x_401_ == 0)
{
return v___x_401_;
}
else
{
return v_suppressElabErrors_387_;
}
}
}
case 1:
{
lean_object* v_pre_402_; 
v_pre_402_ = lean_ctor_get(v_pre_391_, 0);
if (lean_obj_tag(v_pre_402_) == 0)
{
lean_object* v_str_403_; lean_object* v_str_404_; lean_object* v_str_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
v_str_403_ = lean_ctor_get(v_x_389_, 1);
v_str_404_ = lean_ctor_get(v_pre_390_, 1);
v_str_405_ = lean_ctor_get(v_pre_391_, 1);
v___x_406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_407_ = lean_string_dec_eq(v_str_405_, v___x_406_);
if (v___x_407_ == 0)
{
return v___x_407_;
}
else
{
lean_object* v___x_408_; uint8_t v___x_409_; 
v___x_408_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_409_ = lean_string_dec_eq(v_str_404_, v___x_408_);
if (v___x_409_ == 0)
{
return v___x_409_;
}
else
{
lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_410_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_411_ = lean_string_dec_eq(v_str_403_, v___x_410_);
if (v___x_411_ == 0)
{
return v___x_411_;
}
else
{
return v_suppressElabErrors_387_;
}
}
}
}
else
{
return v___y_388_;
}
}
default: 
{
return v___y_388_;
}
}
}
case 0:
{
lean_object* v_str_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v_str_412_ = lean_ctor_get(v_x_389_, 1);
v___x_413_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_414_ = lean_string_dec_eq(v_str_412_, v___x_413_);
if (v___x_414_ == 0)
{
return v___x_414_;
}
else
{
return v_suppressElabErrors_387_;
}
}
default: 
{
return v___y_388_;
}
}
}
else
{
return v___y_388_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v_suppressElabErrors_415_, lean_object* v___y_416_, lean_object* v_x_417_){
_start:
{
uint8_t v_suppressElabErrors_boxed_418_; uint8_t v___y_14973__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_suppressElabErrors_boxed_418_ = lean_unbox(v_suppressElabErrors_415_);
v___y_14973__boxed_419_ = lean_unbox(v___y_416_);
v_res_420_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_418_, v___y_14973__boxed_419_, v_x_417_);
lean_dec(v_x_417_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_422_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_424_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_424_, 0, v___x_423_);
return v___x_424_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___x_425_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_426_ = lean_unsigned_to_nat(0u);
v___x_427_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_427_, 0, v___x_426_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
lean_ctor_set(v___x_427_, 2, v___x_426_);
lean_ctor_set(v___x_427_, 3, v___x_426_);
lean_ctor_set(v___x_427_, 4, v___x_425_);
lean_ctor_set(v___x_427_, 5, v___x_425_);
lean_ctor_set(v___x_427_, 6, v___x_425_);
lean_ctor_set(v___x_427_, 7, v___x_425_);
lean_ctor_set(v___x_427_, 8, v___x_425_);
lean_ctor_set(v___x_427_, 9, v___x_425_);
lean_ctor_set(v___x_427_, 10, v___x_425_);
return v___x_427_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
v___x_428_ = lean_unsigned_to_nat(32u);
v___x_429_ = lean_mk_empty_array_with_capacity(v___x_428_);
v___x_430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_430_, 0, v___x_429_);
return v___x_430_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_431_ = ((size_t)5ULL);
v___x_432_ = lean_unsigned_to_nat(0u);
v___x_433_ = lean_unsigned_to_nat(32u);
v___x_434_ = lean_mk_empty_array_with_capacity(v___x_433_);
v___x_435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_436_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_432_);
lean_ctor_set(v___x_436_, 3, v___x_432_);
lean_ctor_set_usize(v___x_436_, 4, v___x_431_);
return v___x_436_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; 
v___x_437_ = lean_box(1);
v___x_438_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_439_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_440_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_440_, 0, v___x_439_);
lean_ctor_set(v___x_440_, 1, v___x_438_);
lean_ctor_set(v___x_440_, 2, v___x_437_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v___x_445_; lean_object* v_toCold_446_; lean_object* v_env_447_; lean_object* v_options_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; 
v___x_445_ = lean_st_ref_get(v___y_443_);
v_toCold_446_ = lean_ctor_get(v___y_442_, 0);
v_env_447_ = lean_ctor_get(v___x_445_, 0);
lean_inc_ref(v_env_447_);
lean_dec(v___x_445_);
v_options_448_ = lean_ctor_get(v_toCold_446_, 2);
v___x_449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_450_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_448_);
v___x_451_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_451_, 0, v_env_447_);
lean_ctor_set(v___x_451_, 1, v___x_449_);
lean_ctor_set(v___x_451_, 2, v___x_450_);
lean_ctor_set(v___x_451_, 3, v_options_448_);
v___x_452_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
lean_ctor_set(v___x_452_, 1, v_msgData_441_);
v___x_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_453_, 0, v___x_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_454_, v___y_455_, v___y_456_);
lean_dec(v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_460_, lean_object* v_msgData_461_, uint8_t v_severity_462_, uint8_t v_isSilent_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; uint8_t v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; uint8_t v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v___y_512_; lean_object* v___y_530_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; uint8_t v___y_536_; lean_object* v___y_537_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; uint8_t v___y_547_; uint8_t v___x_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_558_; uint8_t v___y_559_; uint8_t v___y_560_; uint8_t v___y_562_; uint8_t v___x_578_; 
v___x_552_ = 2;
v___x_578_ = l_Lean_instBEqMessageSeverity_beq(v_severity_462_, v___x_552_);
if (v___x_578_ == 0)
{
v___y_562_ = v___x_578_;
goto v___jp_561_;
}
else
{
uint8_t v___x_579_; 
lean_inc_ref(v_msgData_461_);
v___x_579_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_461_);
v___y_562_ = v___x_579_;
goto v___jp_561_;
}
v___jp_467_:
{
lean_object* v___x_477_; lean_object* v_toCold_478_; lean_object* v_currNamespace_479_; lean_object* v_openDecls_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_traceState_485_; lean_object* v_cache_486_; lean_object* v_messages_487_; lean_object* v_infoState_488_; lean_object* v_snapshotTasks_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
v___x_477_ = lean_st_ref_take(v___y_476_);
v_toCold_478_ = lean_ctor_get(v___y_475_, 0);
v_currNamespace_479_ = lean_ctor_get(v_toCold_478_, 4);
v_openDecls_480_ = lean_ctor_get(v_toCold_478_, 5);
v_env_481_ = lean_ctor_get(v___x_477_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_477_, 1);
v_ngen_483_ = lean_ctor_get(v___x_477_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_477_, 3);
v_traceState_485_ = lean_ctor_get(v___x_477_, 4);
v_cache_486_ = lean_ctor_get(v___x_477_, 5);
v_messages_487_ = lean_ctor_get(v___x_477_, 6);
v_infoState_488_ = lean_ctor_get(v___x_477_, 7);
v_snapshotTasks_489_ = lean_ctor_get(v___x_477_, 8);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_477_);
if (v_isSharedCheck_503_ == 0)
{
v___x_491_ = v___x_477_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_snapshotTasks_489_);
lean_inc(v_infoState_488_);
lean_inc(v_messages_487_);
lean_inc(v_cache_486_);
lean_inc(v_traceState_485_);
lean_inc(v_auxDeclNGen_484_);
lean_inc(v_ngen_483_);
lean_inc(v_nextMacroScope_482_);
lean_inc(v_env_481_);
lean_dec(v___x_477_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
lean_inc(v_openDecls_480_);
lean_inc(v_currNamespace_479_);
v___x_493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_493_, 0, v_currNamespace_479_);
lean_ctor_set(v___x_493_, 1, v_openDecls_480_);
v___x_494_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_493_);
lean_ctor_set(v___x_494_, 1, v___y_471_);
lean_inc_ref(v___y_468_);
lean_inc_ref(v___y_469_);
v___x_495_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_495_, 0, v___y_469_);
lean_ctor_set(v___x_495_, 1, v___y_473_);
lean_ctor_set(v___x_495_, 2, v___y_470_);
lean_ctor_set(v___x_495_, 3, v___y_468_);
lean_ctor_set(v___x_495_, 4, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5, v___y_474_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5 + 1, v___y_472_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5 + 2, v_isSilent_463_);
v___x_496_ = l_Lean_MessageLog_add(v___x_495_, v_messages_487_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 6, v___x_496_);
v___x_498_ = v___x_491_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_env_481_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_502_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_502_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_502_, 4, v_traceState_485_);
lean_ctor_set(v_reuseFailAlloc_502_, 5, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_502_, 6, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_502_, 7, v_infoState_488_);
lean_ctor_set(v_reuseFailAlloc_502_, 8, v_snapshotTasks_489_);
v___x_498_ = v_reuseFailAlloc_502_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_499_ = lean_st_ref_put(v___y_476_, v___x_498_);
v___x_500_ = lean_box(0);
v___x_501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_501_, 0, v___x_500_);
return v___x_501_;
}
}
}
v___jp_504_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_528_; 
v___x_513_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_461_);
v___x_514_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_513_, v___y_464_, v___y_465_);
v_a_515_ = lean_ctor_get(v___x_514_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v___x_514_);
if (v_isSharedCheck_528_ == 0)
{
v___x_517_ = v___x_514_;
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_514_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_528_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_inc_ref_n(v___y_510_, 2);
v___x_519_ = l_Lean_FileMap_toPosition(v___y_510_, v___y_508_);
lean_dec(v___y_508_);
v___x_520_ = l_Lean_FileMap_toPosition(v___y_510_, v___y_512_);
lean_dec(v___y_512_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_507_ == 0)
{
lean_del_object(v___x_517_);
lean_dec_ref(v___y_505_);
v___y_468_ = v___x_522_;
v___y_469_ = v___y_506_;
v___y_470_ = v___x_521_;
v___y_471_ = v_a_515_;
v___y_472_ = v___y_509_;
v___y_473_ = v___x_519_;
v___y_474_ = v___y_511_;
v___y_475_ = v___y_464_;
v___y_476_ = v___y_465_;
goto v___jp_467_;
}
else
{
uint8_t v___x_523_; 
lean_inc(v_a_515_);
v___x_523_ = l_Lean_MessageData_hasTag(v___y_505_, v_a_515_);
if (v___x_523_ == 0)
{
lean_object* v___x_524_; lean_object* v___x_526_; 
lean_dec_ref_known(v___x_521_, 1);
lean_dec_ref(v___x_519_);
lean_dec(v_a_515_);
v___x_524_ = lean_box(0);
if (v_isShared_518_ == 0)
{
lean_ctor_set(v___x_517_, 0, v___x_524_);
v___x_526_ = v___x_517_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
return v___x_526_;
}
}
else
{
lean_del_object(v___x_517_);
v___y_468_ = v___x_522_;
v___y_469_ = v___y_506_;
v___y_470_ = v___x_521_;
v___y_471_ = v_a_515_;
v___y_472_ = v___y_509_;
v___y_473_ = v___x_519_;
v___y_474_ = v___y_511_;
v___y_475_ = v___y_464_;
v___y_476_ = v___y_465_;
goto v___jp_467_;
}
}
}
}
v___jp_529_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Syntax_getTailPos_x3f(v___y_533_, v___y_536_);
lean_dec(v___y_533_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_inc(v___y_537_);
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
v___y_508_ = v___y_537_;
v___y_509_ = v___y_535_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_536_;
v___y_512_ = v___y_537_;
goto v___jp_504_;
}
else
{
lean_object* v_val_539_; 
v_val_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v___x_538_, 1);
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
v___y_508_ = v___y_537_;
v___y_509_ = v___y_535_;
v___y_510_ = v___y_534_;
v___y_511_ = v___y_536_;
v___y_512_ = v_val_539_;
goto v___jp_504_;
}
}
v___jp_540_:
{
lean_object* v_ref_548_; lean_object* v___x_549_; 
v_ref_548_ = l_Lean_replaceRef(v_ref_460_, v___y_542_);
v___x_549_ = l_Lean_Syntax_getPos_x3f(v_ref_548_, v___y_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___y_530_ = v___y_541_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_544_;
v___y_533_ = v_ref_548_;
v___y_534_ = v___y_545_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_546_;
v___y_537_ = v___x_550_;
goto v___jp_529_;
}
else
{
lean_object* v_val_551_; 
v_val_551_ = lean_ctor_get(v___x_549_, 0);
lean_inc(v_val_551_);
lean_dec_ref_known(v___x_549_, 1);
v___y_530_ = v___y_541_;
v___y_531_ = v___y_543_;
v___y_532_ = v___y_544_;
v___y_533_ = v_ref_548_;
v___y_534_ = v___y_545_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_546_;
v___y_537_ = v_val_551_;
goto v___jp_529_;
}
}
v___jp_553_:
{
if (v___y_560_ == 0)
{
v___y_541_ = v___y_555_;
v___y_542_ = v___y_557_;
v___y_543_ = v___y_554_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_556_;
v___y_546_ = v___y_559_;
v___y_547_ = v_severity_462_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___y_555_;
v___y_542_ = v___y_557_;
v___y_543_ = v___y_554_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_556_;
v___y_546_ = v___y_559_;
v___y_547_ = v___x_552_;
goto v___jp_540_;
}
}
v___jp_561_:
{
if (v___y_562_ == 0)
{
lean_object* v_toCold_563_; lean_object* v_ref_564_; uint8_t v_suppressElabErrors_565_; lean_object* v_fileName_566_; lean_object* v_fileMap_567_; lean_object* v_options_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___f_571_; uint8_t v___x_572_; uint8_t v___x_573_; 
v_toCold_563_ = lean_ctor_get(v___y_464_, 0);
v_ref_564_ = lean_ctor_get(v___y_464_, 2);
v_suppressElabErrors_565_ = lean_ctor_get_uint8(v___y_464_, sizeof(void*)*3 + 1);
v_fileName_566_ = lean_ctor_get(v_toCold_563_, 0);
v_fileMap_567_ = lean_ctor_get(v_toCold_563_, 1);
v_options_568_ = lean_ctor_get(v_toCold_563_, 2);
v___x_569_ = lean_box(v_suppressElabErrors_565_);
v___x_570_ = lean_box(v___y_562_);
v___f_571_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_571_, 0, v___x_569_);
lean_closure_set(v___f_571_, 1, v___x_570_);
v___x_572_ = 1;
v___x_573_ = l_Lean_instBEqMessageSeverity_beq(v_severity_462_, v___x_572_);
if (v___x_573_ == 0)
{
v___y_554_ = v_fileName_566_;
v___y_555_ = v___f_571_;
v___y_556_ = v_fileMap_567_;
v___y_557_ = v_ref_564_;
v___y_558_ = v_suppressElabErrors_565_;
v___y_559_ = v___y_562_;
v___y_560_ = v___x_573_;
goto v___jp_553_;
}
else
{
lean_object* v___x_574_; uint8_t v___x_575_; 
v___x_574_ = l_Lean_warningAsError;
v___x_575_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_568_, v___x_574_);
v___y_554_ = v_fileName_566_;
v___y_555_ = v___f_571_;
v___y_556_ = v_fileMap_567_;
v___y_557_ = v_ref_564_;
v___y_558_ = v_suppressElabErrors_565_;
v___y_559_ = v___y_562_;
v___y_560_ = v___x_575_;
goto v___jp_553_;
}
}
else
{
lean_object* v___x_576_; lean_object* v___x_577_; 
lean_dec_ref(v_msgData_461_);
v___x_576_ = lean_box(0);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_580_, lean_object* v_msgData_581_, lean_object* v_severity_582_, lean_object* v_isSilent_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
uint8_t v_severity_boxed_587_; uint8_t v_isSilent_boxed_588_; lean_object* v_res_589_; 
v_severity_boxed_587_ = lean_unbox(v_severity_582_);
v_isSilent_boxed_588_ = lean_unbox(v_isSilent_583_);
v_res_589_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_580_, v_msgData_581_, v_severity_boxed_587_, v_isSilent_boxed_588_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v_ref_580_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_590_, uint8_t v_severity_591_, uint8_t v_isSilent_592_, lean_object* v___y_593_, lean_object* v___y_594_){
_start:
{
lean_object* v_ref_596_; lean_object* v___x_597_; 
v_ref_596_ = lean_ctor_get(v___y_593_, 2);
v___x_597_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_596_, v_msgData_590_, v_severity_591_, v_isSilent_592_, v___y_593_, v___y_594_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_598_, lean_object* v_severity_599_, lean_object* v_isSilent_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_){
_start:
{
uint8_t v_severity_boxed_604_; uint8_t v_isSilent_boxed_605_; lean_object* v_res_606_; 
v_severity_boxed_604_ = lean_unbox(v_severity_599_);
v_isSilent_boxed_605_ = lean_unbox(v_isSilent_600_);
v_res_606_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_598_, v_severity_boxed_604_, v_isSilent_boxed_605_, v___y_601_, v___y_602_);
lean_dec(v___y_602_);
lean_dec_ref(v___y_601_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_607_, lean_object* v___y_608_, lean_object* v___y_609_){
_start:
{
uint8_t v___x_611_; uint8_t v___x_612_; lean_object* v___x_613_; 
v___x_611_ = 1;
v___x_612_ = 0;
v___x_613_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_607_, v___x_611_, v___x_612_, v___y_608_, v___y_609_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_614_, v___y_615_, v___y_616_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_622_, size_t v_sz_623_, size_t v_i_624_, lean_object* v_b_625_){
_start:
{
uint8_t v___x_626_; 
v___x_626_ = lean_usize_dec_lt(v_i_624_, v_sz_623_);
if (v___x_626_ == 0)
{
lean_inc_ref(v_b_625_);
return v_b_625_;
}
else
{
lean_object* v_a_627_; lean_object* v_fst_628_; lean_object* v___x_629_; uint8_t v___x_630_; 
v_a_627_ = lean_array_uget_borrowed(v_as_622_, v_i_624_);
v_fst_628_ = lean_ctor_get(v_a_627_, 0);
v___x_629_ = lean_box(0);
v___x_630_ = lean_unbox(v_fst_628_);
if (v___x_630_ == 0)
{
lean_object* v___x_631_; size_t v___x_632_; size_t v___x_633_; 
v___x_631_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_632_ = ((size_t)1ULL);
v___x_633_ = lean_usize_add(v_i_624_, v___x_632_);
v_i_624_ = v___x_633_;
v_b_625_ = v___x_631_;
goto _start;
}
else
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
lean_inc(v_a_627_);
v___x_635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_635_, 0, v_a_627_);
v___x_636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v___x_629_);
return v___x_637_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_638_, lean_object* v_sz_639_, lean_object* v_i_640_, lean_object* v_b_641_){
_start:
{
size_t v_sz_boxed_642_; size_t v_i_boxed_643_; lean_object* v_res_644_; 
v_sz_boxed_642_ = lean_unbox_usize(v_sz_639_);
lean_dec(v_sz_639_);
v_i_boxed_643_ = lean_unbox_usize(v_i_640_);
lean_dec(v_i_640_);
v_res_644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_638_, v_sz_boxed_642_, v_i_boxed_643_, v_b_641_);
lean_dec_ref(v_b_641_);
lean_dec_ref(v_as_638_);
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_645_, lean_object* v_e_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v___x_653_; 
v___x_653_ = l_Lean_Expr_getSorry_x3f(v_e_646_);
if (lean_obj_tag(v___x_653_) == 1)
{
lean_object* v_val_654_; lean_object* v___x_655_; 
v_val_654_ = lean_ctor_get(v___x_653_, 0);
lean_inc(v_val_654_);
lean_dec_ref_known(v___x_653_, 1);
lean_inc(v___y_651_);
lean_inc_ref(v___y_650_);
lean_inc(v___y_649_);
lean_inc_ref(v___y_648_);
lean_inc(v___y_647_);
v___x_655_ = lean_apply_7(v_fn_645_, v_val_654_, v___y_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_, lean_box(0));
if (lean_obj_tag(v___x_655_) == 0)
{
lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_664_; 
v_isSharedCheck_664_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_664_ == 0)
{
lean_object* v_unused_665_; 
v_unused_665_ = lean_ctor_get(v___x_655_, 0);
lean_dec(v_unused_665_);
v___x_657_ = v___x_655_;
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
else
{
lean_dec(v___x_655_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_664_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
uint8_t v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_659_ = 0;
v___x_660_ = lean_box(v___x_659_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 0, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
else
{
lean_object* v_a_666_; lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_673_; 
v_a_666_ = lean_ctor_get(v___x_655_, 0);
v_isSharedCheck_673_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_673_ == 0)
{
v___x_668_ = v___x_655_;
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
else
{
lean_inc(v_a_666_);
lean_dec(v___x_655_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_673_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v___x_671_; 
if (v_isShared_669_ == 0)
{
v___x_671_ = v___x_668_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
}
}
else
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
lean_dec(v___x_653_);
lean_dec_ref(v_fn_645_);
v___x_674_ = 1;
v___x_675_ = lean_box(v___x_674_);
v___x_676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_676_, 0, v___x_675_);
return v___x_676_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_677_, lean_object* v_e_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v_res_685_; 
v_res_685_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_677_, v_e_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v___y_679_);
lean_dec_ref(v_e_678_);
return v_res_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_apply_1(v_x_687_, lean_box(0));
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_696_, lean_object* v_x_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_){
_start:
{
lean_object* v_res_704_; 
v_res_704_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_696_, v_x_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
lean_dec(v___y_702_);
lean_dec_ref(v___y_701_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
return v_res_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_){
_start:
{
lean_object* v___x_714_; 
lean_inc(v___y_712_);
lean_inc_ref(v___y_711_);
lean_inc(v___y_710_);
lean_inc_ref(v___y_709_);
lean_inc(v___y_707_);
lean_inc(v___y_706_);
v___x_714_ = lean_apply_8(v_k_705_, v_b_708_, v___y_706_, v___y_707_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, lean_box(0));
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v_b_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_715_, v___y_716_, v___y_717_, v_b_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_725_, lean_object* v_type_726_, lean_object* v_val_727_, lean_object* v_k_728_, uint8_t v_nondep_729_, uint8_t v_kind_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v___f_738_; lean_object* v___x_739_; 
lean_inc(v___y_732_);
lean_inc(v___y_731_);
v___f_738_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_738_, 0, v_k_728_);
lean_closure_set(v___f_738_, 1, v___y_731_);
lean_closure_set(v___f_738_, 2, v___y_732_);
v___x_739_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_725_, v_type_726_, v_val_727_, v___f_738_, v_nondep_729_, v_kind_730_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
return v___x_739_;
}
else
{
lean_object* v_a_740_; lean_object* v___x_742_; uint8_t v_isShared_743_; uint8_t v_isSharedCheck_747_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_747_ == 0)
{
v___x_742_ = v___x_739_;
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
else
{
lean_inc(v_a_740_);
lean_dec(v___x_739_);
v___x_742_ = lean_box(0);
v_isShared_743_ = v_isSharedCheck_747_;
goto v_resetjp_741_;
}
v_resetjp_741_:
{
lean_object* v___x_745_; 
if (v_isShared_743_ == 0)
{
v___x_745_ = v___x_742_;
goto v_reusejp_744_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_a_740_);
v___x_745_ = v_reuseFailAlloc_746_;
goto v_reusejp_744_;
}
v_reusejp_744_:
{
return v___x_745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_748_, lean_object* v_type_749_, lean_object* v_val_750_, lean_object* v_k_751_, lean_object* v_nondep_752_, lean_object* v_kind_753_, lean_object* v___y_754_, lean_object* v___y_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_){
_start:
{
uint8_t v_nondep_boxed_761_; uint8_t v_kind_boxed_762_; lean_object* v_res_763_; 
v_nondep_boxed_761_ = lean_unbox(v_nondep_752_);
v_kind_boxed_762_ = lean_unbox(v_kind_753_);
v_res_763_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_748_, v_type_749_, v_val_750_, v_k_751_, v_nondep_boxed_761_, v_kind_boxed_762_, v___y_754_, v___y_755_, v___y_756_, v___y_757_, v___y_758_, v___y_759_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
lean_dec(v___y_757_);
lean_dec_ref(v___y_756_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
return v_res_763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_764_, lean_object* v_f_765_, lean_object* v_body_766_, lean_object* v_x_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
lean_object* v_res_775_; 
v_res_775_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_764_, v_f_765_, v_body_766_, v_x_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec(v___y_768_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_776_, lean_object* v_fvars_777_, lean_object* v_a_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_){
_start:
{
if (lean_obj_tag(v_a_778_) == 8)
{
lean_object* v_declName_786_; lean_object* v_type_787_; lean_object* v_value_788_; lean_object* v_body_789_; lean_object* v_d_790_; lean_object* v___x_791_; 
v_declName_786_ = lean_ctor_get(v_a_778_, 0);
lean_inc(v_declName_786_);
v_type_787_ = lean_ctor_get(v_a_778_, 1);
lean_inc_ref(v_type_787_);
v_value_788_ = lean_ctor_get(v_a_778_, 2);
lean_inc_ref(v_value_788_);
v_body_789_ = lean_ctor_get(v_a_778_, 3);
lean_inc_ref(v_body_789_);
lean_dec_ref_known(v_a_778_, 4);
v_d_790_ = lean_expr_instantiate_rev(v_type_787_, v_fvars_777_);
lean_dec_ref(v_type_787_);
lean_inc_ref(v_f_776_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v_d_790_);
v___x_791_ = lean_apply_8(v_f_776_, v_d_790_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_v_792_; lean_object* v___x_793_; 
lean_dec_ref_known(v___x_791_, 1);
v_v_792_ = lean_expr_instantiate_rev(v_value_788_, v_fvars_777_);
lean_dec_ref(v_value_788_);
lean_inc_ref(v_f_776_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc(v___y_779_);
lean_inc_ref(v_v_792_);
v___x_793_ = lean_apply_8(v_f_776_, v_v_792_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v___f_794_; uint8_t v___x_795_; uint8_t v___x_796_; lean_object* v___x_797_; 
lean_dec_ref_known(v___x_793_, 1);
v___f_794_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_794_, 0, v_fvars_777_);
lean_closure_set(v___f_794_, 1, v_f_776_);
lean_closure_set(v___f_794_, 2, v_body_789_);
v___x_795_ = 0;
v___x_796_ = 0;
v___x_797_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_786_, v_d_790_, v_v_792_, v___f_794_, v___x_795_, v___x_796_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_);
return v___x_797_;
}
else
{
lean_dec_ref(v_v_792_);
lean_dec_ref(v_d_790_);
lean_dec_ref(v_body_789_);
lean_dec(v_declName_786_);
lean_dec_ref(v_fvars_777_);
lean_dec_ref(v_f_776_);
return v___x_793_;
}
}
else
{
lean_dec_ref(v_d_790_);
lean_dec_ref(v_body_789_);
lean_dec_ref(v_value_788_);
lean_dec(v_declName_786_);
lean_dec_ref(v_fvars_777_);
lean_dec_ref(v_f_776_);
return v___x_791_;
}
}
else
{
lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_798_ = lean_expr_instantiate_rev(v_a_778_, v_fvars_777_);
lean_dec_ref(v_fvars_777_);
lean_dec_ref(v_a_778_);
lean_inc(v___y_784_);
lean_inc_ref(v___y_783_);
lean_inc(v___y_782_);
lean_inc_ref(v___y_781_);
lean_inc(v___y_780_);
lean_inc(v___y_779_);
v___x_799_ = lean_apply_8(v_f_776_, v___x_798_, v___y_779_, v___y_780_, v___y_781_, v___y_782_, v___y_783_, v___y_784_, lean_box(0));
return v___x_799_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_800_, lean_object* v_f_801_, lean_object* v_body_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_811_ = lean_array_push(v_fvars_800_, v_x_803_);
v___x_812_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_801_, v___x_811_, v_body_802_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_813_, lean_object* v_fvars_814_, lean_object* v_a_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_813_, v_fvars_814_, v_a_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
lean_dec(v___y_817_);
lean_dec(v___y_816_);
return v_res_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_826_, lean_object* v_e_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; 
v___x_835_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_836_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_826_, v___x_835_, v_e_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
return v___x_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_837_, lean_object* v_e_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_837_, v_e_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec(v___y_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_847_, uint8_t v_bi_848_, lean_object* v_type_849_, lean_object* v_k_850_, uint8_t v_kind_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v___f_859_; lean_object* v___x_860_; 
lean_inc(v___y_853_);
lean_inc(v___y_852_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_859_, 0, v_k_850_);
lean_closure_set(v___f_859_, 1, v___y_852_);
lean_closure_set(v___f_859_, 2, v___y_853_);
v___x_860_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_847_, v_bi_848_, v_type_849_, v___f_859_, v_kind_851_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
if (lean_obj_tag(v___x_860_) == 0)
{
return v___x_860_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
v_a_861_ = lean_ctor_get(v___x_860_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_860_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_860_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_860_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_869_, lean_object* v_bi_870_, lean_object* v_type_871_, lean_object* v_k_872_, lean_object* v_kind_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_){
_start:
{
uint8_t v_bi_boxed_881_; uint8_t v_kind_boxed_882_; lean_object* v_res_883_; 
v_bi_boxed_881_ = lean_unbox(v_bi_870_);
v_kind_boxed_882_ = lean_unbox(v_kind_873_);
v_res_883_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_869_, v_bi_boxed_881_, v_type_871_, v_k_872_, v_kind_boxed_882_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec(v___y_874_);
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_884_, lean_object* v_f_885_, lean_object* v_body_886_, lean_object* v_x_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_884_, v_f_885_, v_body_886_, v_x_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_);
lean_dec(v___y_893_);
lean_dec_ref(v___y_892_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec(v___y_888_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_896_, lean_object* v_fvars_897_, lean_object* v_a_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
if (lean_obj_tag(v_a_898_) == 7)
{
lean_object* v_binderName_906_; lean_object* v_binderType_907_; lean_object* v_body_908_; uint8_t v_binderInfo_909_; lean_object* v_d_910_; lean_object* v___x_911_; 
v_binderName_906_ = lean_ctor_get(v_a_898_, 0);
lean_inc(v_binderName_906_);
v_binderType_907_ = lean_ctor_get(v_a_898_, 1);
lean_inc_ref(v_binderType_907_);
v_body_908_ = lean_ctor_get(v_a_898_, 2);
lean_inc_ref(v_body_908_);
v_binderInfo_909_ = lean_ctor_get_uint8(v_a_898_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_898_, 3);
v_d_910_ = lean_expr_instantiate_rev(v_binderType_907_, v_fvars_897_);
lean_dec_ref(v_binderType_907_);
lean_inc_ref(v_f_896_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc(v___y_899_);
lean_inc_ref(v_d_910_);
v___x_911_ = lean_apply_8(v_f_896_, v_d_910_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
if (lean_obj_tag(v___x_911_) == 0)
{
lean_object* v___f_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
lean_dec_ref_known(v___x_911_, 1);
v___f_912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_912_, 0, v_fvars_897_);
lean_closure_set(v___f_912_, 1, v_f_896_);
lean_closure_set(v___f_912_, 2, v_body_908_);
v___x_913_ = 0;
v___x_914_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_906_, v_binderInfo_909_, v_d_910_, v___f_912_, v___x_913_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_914_;
}
else
{
lean_dec_ref(v_d_910_);
lean_dec_ref(v_body_908_);
lean_dec(v_binderName_906_);
lean_dec_ref(v_fvars_897_);
lean_dec_ref(v_f_896_);
return v___x_911_;
}
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_expr_instantiate_rev(v_a_898_, v_fvars_897_);
lean_dec_ref(v_fvars_897_);
lean_dec_ref(v_a_898_);
lean_inc(v___y_904_);
lean_inc_ref(v___y_903_);
lean_inc(v___y_902_);
lean_inc_ref(v___y_901_);
lean_inc(v___y_900_);
lean_inc(v___y_899_);
v___x_916_ = lean_apply_8(v_f_896_, v___x_915_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, lean_box(0));
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_917_, lean_object* v_f_918_, lean_object* v_body_919_, lean_object* v_x_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = lean_array_push(v_fvars_917_, v_x_920_);
v___x_929_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_918_, v___x_928_, v_body_919_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_930_, lean_object* v_fvars_931_, lean_object* v_a_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_res_940_; 
v_res_940_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_930_, v_fvars_931_, v_a_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v___y_938_);
lean_dec_ref(v___y_937_);
lean_dec(v___y_936_);
lean_dec_ref(v___y_935_);
lean_dec(v___y_934_);
lean_dec(v___y_933_);
return v_res_940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_941_, lean_object* v_e_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_951_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_941_, v___x_950_, v_e_942_, v___y_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_952_, lean_object* v_e_953_, lean_object* v___y_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v_res_961_; 
v_res_961_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_952_, v_e_953_, v___y_954_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec_ref(v___y_956_);
lean_dec(v___y_955_);
lean_dec(v___y_954_);
return v_res_961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_962_, lean_object* v_f_963_, lean_object* v_body_964_, lean_object* v_x_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_962_, v_f_963_, v_body_964_, v_x_965_, v___y_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec(v___y_966_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_974_, lean_object* v_fvars_975_, lean_object* v_a_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
if (lean_obj_tag(v_a_976_) == 6)
{
lean_object* v_binderName_984_; lean_object* v_binderType_985_; lean_object* v_body_986_; uint8_t v_binderInfo_987_; lean_object* v_d_988_; lean_object* v___x_989_; 
v_binderName_984_ = lean_ctor_get(v_a_976_, 0);
lean_inc(v_binderName_984_);
v_binderType_985_ = lean_ctor_get(v_a_976_, 1);
lean_inc_ref(v_binderType_985_);
v_body_986_ = lean_ctor_get(v_a_976_, 2);
lean_inc_ref(v_body_986_);
v_binderInfo_987_ = lean_ctor_get_uint8(v_a_976_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_976_, 3);
v_d_988_ = lean_expr_instantiate_rev(v_binderType_985_, v_fvars_975_);
lean_dec_ref(v_binderType_985_);
lean_inc_ref(v_f_974_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc(v___y_977_);
lean_inc_ref(v_d_988_);
v___x_989_ = lean_apply_8(v_f_974_, v_d_988_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
if (lean_obj_tag(v___x_989_) == 0)
{
lean_object* v___f_990_; uint8_t v___x_991_; lean_object* v___x_992_; 
lean_dec_ref_known(v___x_989_, 1);
v___f_990_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_990_, 0, v_fvars_975_);
lean_closure_set(v___f_990_, 1, v_f_974_);
lean_closure_set(v___f_990_, 2, v_body_986_);
v___x_991_ = 0;
v___x_992_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_984_, v_binderInfo_987_, v_d_988_, v___f_990_, v___x_991_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_992_;
}
else
{
lean_dec_ref(v_d_988_);
lean_dec_ref(v_body_986_);
lean_dec(v_binderName_984_);
lean_dec_ref(v_fvars_975_);
lean_dec_ref(v_f_974_);
return v___x_989_;
}
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = lean_expr_instantiate_rev(v_a_976_, v_fvars_975_);
lean_dec_ref(v_fvars_975_);
lean_dec_ref(v_a_976_);
lean_inc(v___y_982_);
lean_inc_ref(v___y_981_);
lean_inc(v___y_980_);
lean_inc_ref(v___y_979_);
lean_inc(v___y_978_);
lean_inc(v___y_977_);
v___x_994_ = lean_apply_8(v_f_974_, v___x_993_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_, lean_box(0));
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_995_, lean_object* v_f_996_, lean_object* v_body_997_, lean_object* v_x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = lean_array_push(v_fvars_995_, v_x_998_);
v___x_1007_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_996_, v___x_1006_, v_body_997_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1008_, lean_object* v_fvars_1009_, lean_object* v_a_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_){
_start:
{
lean_object* v_res_1018_; 
v_res_1018_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1008_, v_fvars_1009_, v_a_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
lean_dec(v___y_1016_);
lean_dec_ref(v___y_1015_);
lean_dec(v___y_1014_);
lean_dec_ref(v___y_1013_);
lean_dec(v___y_1012_);
lean_dec(v___y_1011_);
return v_res_1018_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1019_, lean_object* v_e_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1029_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1019_, v___x_1028_, v_e_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
return v___x_1029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1030_, lean_object* v_e_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_){
_start:
{
lean_object* v_res_1039_; 
v_res_1039_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1030_, v_e_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_);
lean_dec(v___y_1037_);
lean_dec_ref(v___y_1036_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec(v___y_1032_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1040_, lean_object* v_x_1041_){
_start:
{
if (lean_obj_tag(v_x_1041_) == 0)
{
lean_object* v___x_1042_; 
v___x_1042_ = lean_box(0);
return v___x_1042_;
}
else
{
lean_object* v_key_1043_; lean_object* v_value_1044_; lean_object* v_tail_1045_; uint8_t v___x_1046_; 
v_key_1043_ = lean_ctor_get(v_x_1041_, 0);
v_value_1044_ = lean_ctor_get(v_x_1041_, 1);
v_tail_1045_ = lean_ctor_get(v_x_1041_, 2);
v___x_1046_ = lean_expr_eqv(v_key_1043_, v_a_1040_);
if (v___x_1046_ == 0)
{
v_x_1041_ = v_tail_1045_;
goto _start;
}
else
{
lean_object* v___x_1048_; 
lean_inc(v_value_1044_);
v___x_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1048_, 0, v_value_1044_);
return v___x_1048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1049_, v_x_1050_);
lean_dec(v_x_1050_);
lean_dec_ref(v_a_1049_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_buckets_1054_; lean_object* v___x_1055_; uint64_t v___x_1056_; uint64_t v___x_1057_; uint64_t v___x_1058_; uint64_t v_fold_1059_; uint64_t v___x_1060_; uint64_t v___x_1061_; uint64_t v___x_1062_; size_t v___x_1063_; size_t v___x_1064_; size_t v___x_1065_; size_t v___x_1066_; size_t v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; 
v_buckets_1054_ = lean_ctor_get(v_m_1052_, 1);
v___x_1055_ = lean_array_get_size(v_buckets_1054_);
v___x_1056_ = l_Lean_Expr_hash(v_a_1053_);
v___x_1057_ = 32ULL;
v___x_1058_ = lean_uint64_shift_right(v___x_1056_, v___x_1057_);
v_fold_1059_ = lean_uint64_xor(v___x_1056_, v___x_1058_);
v___x_1060_ = 16ULL;
v___x_1061_ = lean_uint64_shift_right(v_fold_1059_, v___x_1060_);
v___x_1062_ = lean_uint64_xor(v_fold_1059_, v___x_1061_);
v___x_1063_ = lean_uint64_to_usize(v___x_1062_);
v___x_1064_ = lean_usize_of_nat(v___x_1055_);
v___x_1065_ = ((size_t)1ULL);
v___x_1066_ = lean_usize_sub(v___x_1064_, v___x_1065_);
v___x_1067_ = lean_usize_land(v___x_1063_, v___x_1066_);
v___x_1068_ = lean_array_uget_borrowed(v_buckets_1054_, v___x_1067_);
v___x_1069_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1053_, v___x_1068_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1070_, lean_object* v_a_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1070_, v_a_1071_);
lean_dec_ref(v_a_1071_);
lean_dec_ref(v_m_1070_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_apply_1(v_x_1074_, lean_box(0));
v___x_1082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1082_, 0, v___x_1081_);
return v___x_1082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1083_, lean_object* v_x_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1083_, v_x_1084_, v___y_1085_, v___y_1086_, v___y_1087_, v___y_1088_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1092_, lean_object* v_x_1093_){
_start:
{
if (lean_obj_tag(v_x_1093_) == 0)
{
return v_x_1092_;
}
else
{
lean_object* v_key_1094_; lean_object* v_value_1095_; lean_object* v_tail_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1119_; 
v_key_1094_ = lean_ctor_get(v_x_1093_, 0);
v_value_1095_ = lean_ctor_get(v_x_1093_, 1);
v_tail_1096_ = lean_ctor_get(v_x_1093_, 2);
v_isSharedCheck_1119_ = !lean_is_exclusive(v_x_1093_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1098_ = v_x_1093_;
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_tail_1096_);
lean_inc(v_value_1095_);
lean_inc(v_key_1094_);
lean_dec(v_x_1093_);
v___x_1098_ = lean_box(0);
v_isShared_1099_ = v_isSharedCheck_1119_;
goto v_resetjp_1097_;
}
v_resetjp_1097_:
{
lean_object* v___x_1100_; uint64_t v___x_1101_; uint64_t v___x_1102_; uint64_t v___x_1103_; uint64_t v_fold_1104_; uint64_t v___x_1105_; uint64_t v___x_1106_; uint64_t v___x_1107_; size_t v___x_1108_; size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1115_; 
v___x_1100_ = lean_array_get_size(v_x_1092_);
v___x_1101_ = l_Lean_Expr_hash(v_key_1094_);
v___x_1102_ = 32ULL;
v___x_1103_ = lean_uint64_shift_right(v___x_1101_, v___x_1102_);
v_fold_1104_ = lean_uint64_xor(v___x_1101_, v___x_1103_);
v___x_1105_ = 16ULL;
v___x_1106_ = lean_uint64_shift_right(v_fold_1104_, v___x_1105_);
v___x_1107_ = lean_uint64_xor(v_fold_1104_, v___x_1106_);
v___x_1108_ = lean_uint64_to_usize(v___x_1107_);
v___x_1109_ = lean_usize_of_nat(v___x_1100_);
v___x_1110_ = ((size_t)1ULL);
v___x_1111_ = lean_usize_sub(v___x_1109_, v___x_1110_);
v___x_1112_ = lean_usize_land(v___x_1108_, v___x_1111_);
v___x_1113_ = lean_array_uget_borrowed(v_x_1092_, v___x_1112_);
lean_inc(v___x_1113_);
if (v_isShared_1099_ == 0)
{
lean_ctor_set(v___x_1098_, 2, v___x_1113_);
v___x_1115_ = v___x_1098_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_key_1094_);
lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_value_1095_);
lean_ctor_set(v_reuseFailAlloc_1118_, 2, v___x_1113_);
v___x_1115_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
lean_object* v___x_1116_; 
v___x_1116_ = lean_array_uset(v_x_1092_, v___x_1112_, v___x_1115_);
v_x_1092_ = v___x_1116_;
v_x_1093_ = v_tail_1096_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1120_, lean_object* v_source_1121_, lean_object* v_target_1122_){
_start:
{
lean_object* v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = lean_array_get_size(v_source_1121_);
v___x_1124_ = lean_nat_dec_lt(v_i_1120_, v___x_1123_);
if (v___x_1124_ == 0)
{
lean_dec_ref(v_source_1121_);
lean_dec(v_i_1120_);
return v_target_1122_;
}
else
{
lean_object* v_es_1125_; lean_object* v___x_1126_; lean_object* v_source_1127_; lean_object* v_target_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_es_1125_ = lean_array_fget(v_source_1121_, v_i_1120_);
v___x_1126_ = lean_box(0);
v_source_1127_ = lean_array_fset(v_source_1121_, v_i_1120_, v___x_1126_);
v_target_1128_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1122_, v_es_1125_);
v___x_1129_ = lean_unsigned_to_nat(1u);
v___x_1130_ = lean_nat_add(v_i_1120_, v___x_1129_);
lean_dec(v_i_1120_);
v_i_1120_ = v___x_1130_;
v_source_1121_ = v_source_1127_;
v_target_1122_ = v_target_1128_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1132_){
_start:
{
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_nbuckets_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___x_1133_ = lean_array_get_size(v_data_1132_);
v___x_1134_ = lean_unsigned_to_nat(2u);
v_nbuckets_1135_ = lean_nat_mul(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_mk_array(v_nbuckets_1135_, v___x_1137_);
v___x_1139_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1136_, v_data_1132_, v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1140_, lean_object* v_b_1141_, lean_object* v_x_1142_){
_start:
{
if (lean_obj_tag(v_x_1142_) == 0)
{
lean_dec(v_b_1141_);
lean_dec_ref(v_a_1140_);
return v_x_1142_;
}
else
{
lean_object* v_key_1143_; lean_object* v_value_1144_; lean_object* v_tail_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1157_; 
v_key_1143_ = lean_ctor_get(v_x_1142_, 0);
v_value_1144_ = lean_ctor_get(v_x_1142_, 1);
v_tail_1145_ = lean_ctor_get(v_x_1142_, 2);
v_isSharedCheck_1157_ = !lean_is_exclusive(v_x_1142_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1147_ = v_x_1142_;
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_tail_1145_);
lean_inc(v_value_1144_);
lean_inc(v_key_1143_);
lean_dec(v_x_1142_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1157_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_expr_eqv(v_key_1143_, v_a_1140_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1140_, v_b_1141_, v_tail_1145_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 2, v___x_1150_);
v___x_1152_ = v___x_1147_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_key_1143_);
lean_ctor_set(v_reuseFailAlloc_1153_, 1, v_value_1144_);
lean_ctor_set(v_reuseFailAlloc_1153_, 2, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
else
{
lean_object* v___x_1155_; 
lean_dec(v_value_1144_);
lean_dec(v_key_1143_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 1, v_b_1141_);
lean_ctor_set(v___x_1147_, 0, v_a_1140_);
v___x_1155_ = v___x_1147_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1140_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_b_1141_);
lean_ctor_set(v_reuseFailAlloc_1156_, 2, v_tail_1145_);
v___x_1155_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
return v___x_1155_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1158_, lean_object* v_x_1159_){
_start:
{
if (lean_obj_tag(v_x_1159_) == 0)
{
uint8_t v___x_1160_; 
v___x_1160_ = 0;
return v___x_1160_;
}
else
{
lean_object* v_key_1161_; lean_object* v_tail_1162_; uint8_t v___x_1163_; 
v_key_1161_ = lean_ctor_get(v_x_1159_, 0);
v_tail_1162_ = lean_ctor_get(v_x_1159_, 2);
v___x_1163_ = lean_expr_eqv(v_key_1161_, v_a_1158_);
if (v___x_1163_ == 0)
{
v_x_1159_ = v_tail_1162_;
goto _start;
}
else
{
return v___x_1163_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1165_, lean_object* v_x_1166_){
_start:
{
uint8_t v_res_1167_; lean_object* v_r_1168_; 
v_res_1167_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1165_, v_x_1166_);
lean_dec(v_x_1166_);
lean_dec_ref(v_a_1165_);
v_r_1168_ = lean_box(v_res_1167_);
return v_r_1168_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1169_, lean_object* v_a_1170_, lean_object* v_b_1171_){
_start:
{
lean_object* v_size_1172_; lean_object* v_buckets_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1216_; 
v_size_1172_ = lean_ctor_get(v_m_1169_, 0);
v_buckets_1173_ = lean_ctor_get(v_m_1169_, 1);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_m_1169_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1175_ = v_m_1169_;
v_isShared_1176_ = v_isSharedCheck_1216_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_buckets_1173_);
lean_inc(v_size_1172_);
lean_dec(v_m_1169_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1216_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1177_; uint64_t v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v_fold_1181_; uint64_t v___x_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; size_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; lean_object* v_bkt_1190_; uint8_t v___x_1191_; 
v___x_1177_ = lean_array_get_size(v_buckets_1173_);
v___x_1178_ = l_Lean_Expr_hash(v_a_1170_);
v___x_1179_ = 32ULL;
v___x_1180_ = lean_uint64_shift_right(v___x_1178_, v___x_1179_);
v_fold_1181_ = lean_uint64_xor(v___x_1178_, v___x_1180_);
v___x_1182_ = 16ULL;
v___x_1183_ = lean_uint64_shift_right(v_fold_1181_, v___x_1182_);
v___x_1184_ = lean_uint64_xor(v_fold_1181_, v___x_1183_);
v___x_1185_ = lean_uint64_to_usize(v___x_1184_);
v___x_1186_ = lean_usize_of_nat(v___x_1177_);
v___x_1187_ = ((size_t)1ULL);
v___x_1188_ = lean_usize_sub(v___x_1186_, v___x_1187_);
v___x_1189_ = lean_usize_land(v___x_1185_, v___x_1188_);
v_bkt_1190_ = lean_array_uget_borrowed(v_buckets_1173_, v___x_1189_);
v___x_1191_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1170_, v_bkt_1190_);
if (v___x_1191_ == 0)
{
lean_object* v___x_1192_; lean_object* v_size_x27_1193_; lean_object* v___x_1194_; lean_object* v_buckets_x27_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1192_ = lean_unsigned_to_nat(1u);
v_size_x27_1193_ = lean_nat_add(v_size_1172_, v___x_1192_);
lean_dec(v_size_1172_);
lean_inc(v_bkt_1190_);
v___x_1194_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1194_, 0, v_a_1170_);
lean_ctor_set(v___x_1194_, 1, v_b_1171_);
lean_ctor_set(v___x_1194_, 2, v_bkt_1190_);
v_buckets_x27_1195_ = lean_array_uset(v_buckets_1173_, v___x_1189_, v___x_1194_);
v___x_1196_ = lean_unsigned_to_nat(4u);
v___x_1197_ = lean_nat_mul(v_size_x27_1193_, v___x_1196_);
v___x_1198_ = lean_unsigned_to_nat(3u);
v___x_1199_ = lean_nat_div(v___x_1197_, v___x_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_array_get_size(v_buckets_x27_1195_);
v___x_1201_ = lean_nat_dec_le(v___x_1199_, v___x_1200_);
lean_dec(v___x_1199_);
if (v___x_1201_ == 0)
{
lean_object* v_val_1202_; lean_object* v___x_1204_; 
v_val_1202_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1195_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_val_1202_);
lean_ctor_set(v___x_1175_, 0, v_size_x27_1193_);
v___x_1204_ = v___x_1175_;
goto v_reusejp_1203_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v_size_x27_1193_);
lean_ctor_set(v_reuseFailAlloc_1205_, 1, v_val_1202_);
v___x_1204_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1203_;
}
v_reusejp_1203_:
{
return v___x_1204_;
}
}
else
{
lean_object* v___x_1207_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v_buckets_x27_1195_);
lean_ctor_set(v___x_1175_, 0, v_size_x27_1193_);
v___x_1207_ = v___x_1175_;
goto v_reusejp_1206_;
}
else
{
lean_object* v_reuseFailAlloc_1208_; 
v_reuseFailAlloc_1208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1208_, 0, v_size_x27_1193_);
lean_ctor_set(v_reuseFailAlloc_1208_, 1, v_buckets_x27_1195_);
v___x_1207_ = v_reuseFailAlloc_1208_;
goto v_reusejp_1206_;
}
v_reusejp_1206_:
{
return v___x_1207_;
}
}
}
else
{
lean_object* v___x_1209_; lean_object* v_buckets_x27_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1214_; 
lean_inc(v_bkt_1190_);
v___x_1209_ = lean_box(0);
v_buckets_x27_1210_ = lean_array_uset(v_buckets_1173_, v___x_1189_, v___x_1209_);
v___x_1211_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1170_, v_b_1171_, v_bkt_1190_);
v___x_1212_ = lean_array_uset(v_buckets_x27_1210_, v___x_1189_, v___x_1211_);
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 1, v___x_1212_);
v___x_1214_ = v___x_1175_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_size_1172_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1212_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1217_, lean_object* v_e_1218_, lean_object* v_a_1219_){
_start:
{
lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1221_ = lean_st_ref_take(v_a_1217_);
v___x_1222_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1221_, v_e_1218_, v_a_1219_);
v___x_1223_ = lean_st_ref_put(v_a_1217_, v___x_1222_);
v___x_1224_ = lean_box(0);
return v___x_1224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1225_, lean_object* v_e_1226_, lean_object* v_a_1227_, lean_object* v___y_1228_){
_start:
{
lean_object* v_res_1229_; 
v_res_1229_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1225_, v_e_1226_, v_a_1227_);
lean_dec(v_a_1225_);
return v_res_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1230_, lean_object* v_e_1231_, lean_object* v_a_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1230_, v_e_1231_, v_a_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v_a_1232_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1240_, lean_object* v_e_1241_, lean_object* v_a_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v_a_1250_; lean_object* v___y_1262_; lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_inc(v_a_1242_);
v___x_1264_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1264_, 0, lean_box(0));
lean_closure_set(v___x_1264_, 1, lean_box(0));
lean_closure_set(v___x_1264_, 2, v_a_1242_);
v___x_1265_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1264_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1265_) == 0)
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1302_; 
v_a_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1302_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1302_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1266_, v_e_1241_);
lean_dec(v_a_1266_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1271_; 
lean_del_object(v___x_1268_);
lean_inc_ref(v_fn_1240_);
lean_inc(v___y_1247_);
lean_inc_ref(v___y_1246_);
lean_inc(v___y_1245_);
lean_inc_ref(v___y_1244_);
lean_inc(v___y_1243_);
lean_inc_ref(v_e_1241_);
v___x_1271_ = lean_apply_7(v_fn_1240_, v_e_1241_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, lean_box(0));
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v_a_1272_; uint8_t v___x_1273_; 
v_a_1272_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_a_1272_);
lean_dec_ref_known(v___x_1271_, 1);
v___x_1273_ = lean_unbox(v_a_1272_);
lean_dec(v_a_1272_);
if (v___x_1273_ == 0)
{
lean_object* v___x_1274_; 
lean_dec_ref(v_fn_1240_);
v___x_1274_ = lean_box(0);
v_a_1250_ = v___x_1274_;
goto v___jp_1249_;
}
else
{
switch(lean_obj_tag(v_e_1241_))
{
case 7:
{
lean_object* v___x_1275_; lean_object* v___x_1276_; 
v___x_1275_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1275_, 0, v_fn_1240_);
lean_inc_ref(v_e_1241_);
v___x_1276_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1275_, v_e_1241_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1276_;
goto v___jp_1261_;
}
case 6:
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
v___x_1277_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1277_, 0, v_fn_1240_);
lean_inc_ref(v_e_1241_);
v___x_1278_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1277_, v_e_1241_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1278_;
goto v___jp_1261_;
}
case 8:
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
v___x_1279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1279_, 0, v_fn_1240_);
lean_inc_ref(v_e_1241_);
v___x_1280_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1279_, v_e_1241_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1280_;
goto v___jp_1261_;
}
case 5:
{
lean_object* v_fn_1281_; lean_object* v_arg_1282_; lean_object* v___x_1283_; 
v_fn_1281_ = lean_ctor_get(v_e_1241_, 0);
v_arg_1282_ = lean_ctor_get(v_e_1241_, 1);
lean_inc_ref(v_fn_1281_);
lean_inc_ref(v_fn_1240_);
v___x_1283_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1240_, v_fn_1281_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v___x_1284_; 
lean_dec_ref_known(v___x_1283_, 1);
lean_inc_ref(v_arg_1282_);
v___x_1284_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1240_, v_arg_1282_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1284_;
goto v___jp_1261_;
}
else
{
lean_dec_ref(v_fn_1240_);
v___y_1262_ = v___x_1283_;
goto v___jp_1261_;
}
}
case 10:
{
lean_object* v_expr_1285_; lean_object* v___x_1286_; 
v_expr_1285_ = lean_ctor_get(v_e_1241_, 1);
lean_inc_ref(v_expr_1285_);
v___x_1286_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1240_, v_expr_1285_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1286_;
goto v___jp_1261_;
}
case 11:
{
lean_object* v_struct_1287_; lean_object* v___x_1288_; 
v_struct_1287_ = lean_ctor_get(v_e_1241_, 2);
lean_inc_ref(v_struct_1287_);
v___x_1288_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1240_, v_struct_1287_, v_a_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
v___y_1262_ = v___x_1288_;
goto v___jp_1261_;
}
default: 
{
lean_object* v___x_1289_; 
lean_dec_ref(v_fn_1240_);
v___x_1289_ = lean_box(0);
v_a_1250_ = v___x_1289_;
goto v___jp_1249_;
}
}
}
}
else
{
lean_object* v_a_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1297_; 
lean_dec_ref(v_e_1241_);
lean_dec_ref(v_fn_1240_);
v_a_1290_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1297_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1297_ == 0)
{
v___x_1292_ = v___x_1271_;
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_a_1290_);
lean_dec(v___x_1271_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1297_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1295_; 
if (v_isShared_1293_ == 0)
{
v___x_1295_ = v___x_1292_;
goto v_reusejp_1294_;
}
else
{
lean_object* v_reuseFailAlloc_1296_; 
v_reuseFailAlloc_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1296_, 0, v_a_1290_);
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
lean_object* v_val_1298_; lean_object* v___x_1300_; 
lean_dec_ref(v_e_1241_);
lean_dec_ref(v_fn_1240_);
v_val_1298_ = lean_ctor_get(v___x_1270_, 0);
lean_inc(v_val_1298_);
lean_dec_ref_known(v___x_1270_, 1);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v_val_1298_);
v___x_1300_ = v___x_1268_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_val_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
else
{
lean_object* v_a_1303_; lean_object* v___x_1305_; uint8_t v_isShared_1306_; uint8_t v_isSharedCheck_1310_; 
lean_dec_ref(v_e_1241_);
lean_dec_ref(v_fn_1240_);
v_a_1303_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1305_ = v___x_1265_;
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
else
{
lean_inc(v_a_1303_);
lean_dec(v___x_1265_);
v___x_1305_ = lean_box(0);
v_isShared_1306_ = v_isSharedCheck_1310_;
goto v_resetjp_1304_;
}
v_resetjp_1304_:
{
lean_object* v___x_1308_; 
if (v_isShared_1306_ == 0)
{
v___x_1308_ = v___x_1305_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_a_1303_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
v___jp_1249_:
{
lean_object* v___f_1251_; lean_object* v___x_1252_; 
lean_inc(v_a_1242_);
v___f_1251_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1251_, 0, v_a_1242_);
lean_closure_set(v___f_1251_, 1, v_e_1241_);
lean_closure_set(v___f_1251_, 2, v_a_1250_);
v___x_1252_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1251_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1259_ == 0)
{
lean_object* v_unused_1260_; 
v_unused_1260_ = lean_ctor_get(v___x_1252_, 0);
lean_dec(v_unused_1260_);
v___x_1254_ = v___x_1252_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_dec(v___x_1252_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 0, v_a_1250_);
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1250_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
else
{
return v___x_1252_;
}
}
v___jp_1261_:
{
if (lean_obj_tag(v___y_1262_) == 0)
{
lean_object* v_a_1263_; 
v_a_1263_ = lean_ctor_get(v___y_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___y_1262_, 1);
v_a_1250_ = v_a_1263_;
goto v___jp_1249_;
}
else
{
lean_dec_ref(v_e_1241_);
return v___y_1262_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1311_; lean_object* v___x_1312_; lean_object* v___x_1313_; 
v___x_1311_ = lean_box(0);
v___x_1312_ = lean_unsigned_to_nat(16u);
v___x_1313_ = lean_mk_array(v___x_1312_, v___x_1311_);
return v___x_1313_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; 
v___x_1314_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1315_ = lean_unsigned_to_nat(0u);
v___x_1316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1316_, 0, v___x_1315_);
lean_ctor_set(v___x_1316_, 1, v___x_1314_);
return v___x_1316_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1317_; lean_object* v___x_1318_; 
v___x_1317_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1318_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1318_, 0, lean_box(0));
lean_closure_set(v___x_1318_, 1, lean_box(0));
lean_closure_set(v___x_1318_, 2, v___x_1317_);
return v___x_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1319_, lean_object* v_fn_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_){
_start:
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v_a_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1328_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1327_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
v_a_1329_ = lean_ctor_get(v___x_1328_, 0);
lean_inc(v_a_1329_);
lean_dec_ref(v___x_1328_);
v___x_1330_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1320_, v_input_1319_, v_a_1329_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_object* v_a_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1335_; uint8_t v_isShared_1336_; uint8_t v_isSharedCheck_1340_; 
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc(v_a_1331_);
lean_dec_ref_known(v___x_1330_, 1);
v___x_1332_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1332_, 0, lean_box(0));
lean_closure_set(v___x_1332_, 1, lean_box(0));
lean_closure_set(v___x_1332_, 2, v_a_1329_);
v___x_1333_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1332_, v___y_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1333_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v___x_1333_, 0);
lean_dec(v_unused_1341_);
v___x_1335_ = v___x_1333_;
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
else
{
lean_dec(v___x_1333_);
v___x_1335_ = lean_box(0);
v_isShared_1336_ = v_isSharedCheck_1340_;
goto v_resetjp_1334_;
}
v_resetjp_1334_:
{
lean_object* v___x_1338_; 
if (v_isShared_1336_ == 0)
{
lean_ctor_set(v___x_1335_, 0, v_a_1331_);
v___x_1338_ = v___x_1335_;
goto v_reusejp_1337_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_a_1331_);
v___x_1338_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1337_;
}
v_reusejp_1337_:
{
return v___x_1338_;
}
}
}
else
{
lean_dec(v_a_1329_);
return v___x_1330_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1342_, lean_object* v_fn_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v_res_1350_; 
v_res_1350_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1342_, v_fn_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
lean_dec(v___y_1348_);
lean_dec_ref(v___y_1347_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1351_, lean_object* v_fn_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___f_1359_; lean_object* v___x_1360_; 
v___f_1359_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1359_, 0, v_fn_1352_);
v___x_1360_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1351_, v___f_1359_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1361_, lean_object* v_fn_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v_res_1369_; 
v_res_1369_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1361_, v_fn_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_);
lean_dec(v___y_1367_);
lean_dec_ref(v___y_1366_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
return v_res_1369_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1370_, lean_object* v_x_1371_, lean_object* v_x_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_){
_start:
{
if (lean_obj_tag(v_x_1372_) == 0)
{
lean_object* v___x_1379_; 
lean_dec_ref(v_fn_1370_);
v___x_1379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1379_, 0, v_x_1371_);
return v___x_1379_;
}
else
{
lean_object* v_head_1380_; lean_object* v_tail_1381_; lean_object* v_type_1382_; lean_object* v___x_1383_; 
v_head_1380_ = lean_ctor_get(v_x_1372_, 0);
lean_inc(v_head_1380_);
v_tail_1381_ = lean_ctor_get(v_x_1372_, 1);
lean_inc(v_tail_1381_);
lean_dec_ref_known(v_x_1372_, 2);
v_type_1382_ = lean_ctor_get(v_head_1380_, 1);
lean_inc_ref(v_type_1382_);
lean_dec(v_head_1380_);
lean_inc_ref(v_fn_1370_);
v___x_1383_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1382_, v_fn_1370_, v___y_1373_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
if (lean_obj_tag(v___x_1383_) == 0)
{
lean_object* v_a_1384_; 
v_a_1384_ = lean_ctor_get(v___x_1383_, 0);
lean_inc(v_a_1384_);
lean_dec_ref_known(v___x_1383_, 1);
v_x_1371_ = v_a_1384_;
v_x_1372_ = v_tail_1381_;
goto _start;
}
else
{
lean_dec(v_tail_1381_);
lean_dec_ref(v_fn_1370_);
return v___x_1383_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1386_, lean_object* v_x_1387_, lean_object* v_x_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1386_, v_x_1387_, v_x_1388_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
return v_res_1395_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1396_, lean_object* v_x_1397_, lean_object* v_x_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
if (lean_obj_tag(v_x_1398_) == 0)
{
lean_object* v___x_1405_; 
lean_dec_ref(v_fn_1396_);
v___x_1405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1405_, 0, v_x_1397_);
return v___x_1405_;
}
else
{
lean_object* v_head_1406_; lean_object* v_tail_1407_; lean_object* v___y_1409_; lean_object* v_type_1412_; lean_object* v_ctors_1413_; lean_object* v___x_1414_; 
v_head_1406_ = lean_ctor_get(v_x_1398_, 0);
lean_inc(v_head_1406_);
v_tail_1407_ = lean_ctor_get(v_x_1398_, 1);
lean_inc(v_tail_1407_);
lean_dec_ref_known(v_x_1398_, 2);
v_type_1412_ = lean_ctor_get(v_head_1406_, 1);
lean_inc_ref(v_type_1412_);
v_ctors_1413_ = lean_ctor_get(v_head_1406_, 2);
lean_inc(v_ctors_1413_);
lean_dec(v_head_1406_);
lean_inc_ref(v_fn_1396_);
v___x_1414_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1412_, v_fn_1396_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
if (lean_obj_tag(v___x_1414_) == 0)
{
lean_object* v_a_1415_; lean_object* v___x_1416_; 
v_a_1415_ = lean_ctor_get(v___x_1414_, 0);
lean_inc(v_a_1415_);
lean_dec_ref_known(v___x_1414_, 1);
lean_inc_ref(v_fn_1396_);
v___x_1416_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1396_, v_a_1415_, v_ctors_1413_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_);
v___y_1409_ = v___x_1416_;
goto v___jp_1408_;
}
else
{
lean_dec(v_ctors_1413_);
v___y_1409_ = v___x_1414_;
goto v___jp_1408_;
}
v___jp_1408_:
{
if (lean_obj_tag(v___y_1409_) == 0)
{
lean_object* v_a_1410_; 
v_a_1410_ = lean_ctor_get(v___y_1409_, 0);
lean_inc(v_a_1410_);
lean_dec_ref_known(v___y_1409_, 1);
v_x_1397_ = v_a_1410_;
v_x_1398_ = v_tail_1407_;
goto _start;
}
else
{
lean_dec(v_tail_1407_);
lean_dec_ref(v_fn_1396_);
return v___y_1409_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1417_, lean_object* v_x_1418_, lean_object* v_x_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1417_, v_x_1418_, v_x_1419_, v___y_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_);
lean_dec(v___y_1424_);
lean_dec_ref(v___y_1423_);
lean_dec(v___y_1422_);
lean_dec_ref(v___y_1421_);
lean_dec(v___y_1420_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1427_, lean_object* v_x_1428_, lean_object* v_x_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
if (lean_obj_tag(v_x_1429_) == 0)
{
lean_object* v___x_1436_; 
lean_dec_ref(v_fn_1427_);
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_x_1428_);
return v___x_1436_;
}
else
{
lean_object* v_head_1437_; lean_object* v_tail_1438_; lean_object* v___y_1440_; lean_object* v_toConstantVal_1443_; lean_object* v_value_1444_; lean_object* v_type_1445_; lean_object* v___x_1446_; 
v_head_1437_ = lean_ctor_get(v_x_1429_, 0);
lean_inc(v_head_1437_);
v_tail_1438_ = lean_ctor_get(v_x_1429_, 1);
lean_inc(v_tail_1438_);
lean_dec_ref_known(v_x_1429_, 2);
v_toConstantVal_1443_ = lean_ctor_get(v_head_1437_, 0);
lean_inc_ref(v_toConstantVal_1443_);
v_value_1444_ = lean_ctor_get(v_head_1437_, 1);
lean_inc_ref(v_value_1444_);
lean_dec(v_head_1437_);
v_type_1445_ = lean_ctor_get(v_toConstantVal_1443_, 2);
lean_inc_ref(v_type_1445_);
lean_dec_ref(v_toConstantVal_1443_);
lean_inc_ref(v_fn_1427_);
v___x_1446_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1445_, v_fn_1427_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_object* v___x_1447_; 
lean_dec_ref_known(v___x_1446_, 1);
lean_inc_ref(v_fn_1427_);
v___x_1447_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1444_, v_fn_1427_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_);
v___y_1440_ = v___x_1447_;
goto v___jp_1439_;
}
else
{
lean_dec_ref(v_value_1444_);
v___y_1440_ = v___x_1446_;
goto v___jp_1439_;
}
v___jp_1439_:
{
if (lean_obj_tag(v___y_1440_) == 0)
{
lean_object* v_a_1441_; 
v_a_1441_ = lean_ctor_get(v___y_1440_, 0);
lean_inc(v_a_1441_);
lean_dec_ref_known(v___y_1440_, 1);
v_x_1428_ = v_a_1441_;
v_x_1429_ = v_tail_1438_;
goto _start;
}
else
{
lean_dec(v_tail_1438_);
lean_dec_ref(v_fn_1427_);
return v___y_1440_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1448_, lean_object* v_x_1449_, lean_object* v_x_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1448_, v_x_1449_, v_x_1450_, v___y_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1458_, lean_object* v_d_1459_, lean_object* v_a_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
switch(lean_obj_tag(v_d_1459_))
{
case 0:
{
lean_object* v_val_1467_; lean_object* v_toConstantVal_1468_; lean_object* v_type_1469_; lean_object* v___x_1470_; 
v_val_1467_ = lean_ctor_get(v_d_1459_, 0);
lean_inc_ref(v_val_1467_);
lean_dec_ref_known(v_d_1459_, 1);
v_toConstantVal_1468_ = lean_ctor_get(v_val_1467_, 0);
lean_inc_ref(v_toConstantVal_1468_);
lean_dec_ref(v_val_1467_);
v_type_1469_ = lean_ctor_get(v_toConstantVal_1468_, 2);
lean_inc_ref(v_type_1469_);
lean_dec_ref(v_toConstantVal_1468_);
v___x_1470_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1469_, v_fn_1458_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1470_;
}
case 4:
{
lean_object* v___x_1471_; 
lean_dec_ref(v_fn_1458_);
v___x_1471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1471_, 0, v_a_1460_);
return v___x_1471_;
}
case 5:
{
lean_object* v_defns_1472_; lean_object* v___x_1473_; 
v_defns_1472_ = lean_ctor_get(v_d_1459_, 0);
lean_inc(v_defns_1472_);
lean_dec_ref_known(v_d_1459_, 1);
v___x_1473_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1458_, v_a_1460_, v_defns_1472_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1473_;
}
case 6:
{
lean_object* v_types_1474_; lean_object* v___x_1475_; 
v_types_1474_ = lean_ctor_get(v_d_1459_, 2);
lean_inc(v_types_1474_);
lean_dec_ref_known(v_d_1459_, 3);
v___x_1475_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1458_, v_a_1460_, v_types_1474_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1475_;
}
default: 
{
lean_object* v_val_1476_; lean_object* v_toConstantVal_1477_; lean_object* v_value_1478_; lean_object* v_type_1479_; lean_object* v___x_1480_; 
v_val_1476_ = lean_ctor_get(v_d_1459_, 0);
lean_inc_ref(v_val_1476_);
lean_dec(v_d_1459_);
v_toConstantVal_1477_ = lean_ctor_get(v_val_1476_, 0);
lean_inc_ref(v_toConstantVal_1477_);
v_value_1478_ = lean_ctor_get(v_val_1476_, 1);
lean_inc_ref(v_value_1478_);
lean_dec_ref(v_val_1476_);
v_type_1479_ = lean_ctor_get(v_toConstantVal_1477_, 2);
lean_inc_ref(v_type_1479_);
lean_dec_ref(v_toConstantVal_1477_);
lean_inc_ref(v_fn_1458_);
v___x_1480_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1479_, v_fn_1458_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v___x_1481_; 
lean_dec_ref_known(v___x_1480_, 1);
v___x_1481_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1478_, v_fn_1458_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_);
return v___x_1481_;
}
else
{
lean_dec_ref(v_value_1478_);
lean_dec_ref(v_fn_1458_);
return v___x_1480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1482_, lean_object* v_d_1483_, lean_object* v_a_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_){
_start:
{
lean_object* v_res_1491_; 
v_res_1491_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1482_, v_d_1483_, v_a_1484_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
lean_dec(v___y_1489_);
lean_dec_ref(v___y_1488_);
lean_dec(v___y_1487_);
lean_dec_ref(v___y_1486_);
lean_dec(v___y_1485_);
return v_res_1491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1492_, lean_object* v_fn_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1500_ = lean_box(0);
v___x_1501_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1493_, v_decl_1492_, v___x_1500_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1502_, lean_object* v_fn_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1502_, v_fn_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___y_1508_);
lean_dec_ref(v___y_1507_);
lean_dec(v___y_1506_);
lean_dec_ref(v___y_1505_);
lean_dec(v___y_1504_);
return v_res_1510_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1511_; 
v___x_1511_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1511_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1512_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1514_ = lean_box(1);
v___x_1515_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1516_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
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
lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1520_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1521_ = lean_unsigned_to_nat(0u);
v___x_1522_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v___x_1521_);
lean_ctor_set(v___x_1522_, 2, v___x_1521_);
lean_ctor_set(v___x_1522_, 3, v___x_1521_);
lean_ctor_set(v___x_1522_, 4, v___x_1520_);
lean_ctor_set(v___x_1522_, 5, v___x_1520_);
lean_ctor_set(v___x_1522_, 6, v___x_1520_);
lean_ctor_set(v___x_1522_, 7, v___x_1520_);
lean_ctor_set(v___x_1522_, 8, v___x_1520_);
lean_ctor_set(v___x_1522_, 9, v___x_1520_);
lean_ctor_set(v___x_1522_, 10, v___x_1520_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1524_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1523_);
lean_ctor_set(v___x_1524_, 1, v___x_1523_);
lean_ctor_set(v___x_1524_, 2, v___x_1523_);
lean_ctor_set(v___x_1524_, 3, v___x_1523_);
lean_ctor_set(v___x_1524_, 4, v___x_1523_);
lean_ctor_set(v___x_1524_, 5, v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1525_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1526_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1525_);
lean_ctor_set(v___x_1526_, 2, v___x_1525_);
lean_ctor_set(v___x_1526_, 3, v___x_1525_);
lean_ctor_set(v___x_1526_, 4, v___x_1525_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1527_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1528_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1529_ = lean_box(1);
v___x_1530_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1531_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1532_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1530_);
lean_ctor_set(v___x_1532_, 2, v___x_1529_);
lean_ctor_set(v___x_1532_, 3, v___x_1528_);
lean_ctor_set(v___x_1532_, 4, v___x_1527_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1539_ = l_Lean_stringToMessageData(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1542_ = l_Lean_stringToMessageData(v___x_1541_);
return v___x_1542_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1545_ = l_Lean_stringToMessageData(v___x_1544_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1546_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1547_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1548_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1548_, 0, v___x_1547_);
lean_ctor_set(v___x_1548_, 1, v___x_1546_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1552_, lean_object* v_a_1553_, lean_object* v_a_1554_){
_start:
{
lean_object* v_toCold_1556_; lean_object* v_options_1557_; lean_object* v___x_1558_; uint8_t v___x_1559_; 
v_toCold_1556_ = lean_ctor_get(v_a_1553_, 0);
v_options_1557_ = lean_ctor_get(v_toCold_1556_, 2);
v___x_1558_ = l_Lean_warn_sorry;
v___x_1559_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1557_, v___x_1558_);
if (v___x_1559_ == 0)
{
lean_object* v___x_1560_; lean_object* v___x_1561_; 
lean_dec(v_decl_1552_);
v___x_1560_ = lean_box(0);
v___x_1561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
return v___x_1561_;
}
else
{
lean_object* v___x_1562_; lean_object* v_messages_1566_; uint8_t v___x_1567_; 
v___x_1562_ = lean_st_ref_get(v_a_1554_);
v_messages_1566_ = lean_ctor_get(v___x_1562_, 6);
lean_inc_ref(v_messages_1566_);
lean_dec(v___x_1562_);
v___x_1567_ = l_Lean_MessageLog_hasErrors(v_messages_1566_);
lean_dec_ref(v_messages_1566_);
if (v___x_1567_ == 0)
{
if (v___x_1559_ == 0)
{
lean_dec(v_decl_1552_);
goto v___jp_1563_;
}
else
{
uint8_t v___x_1568_; 
v___x_1568_ = l_Lean_Declaration_hasSorry(v_decl_1552_);
if (v___x_1568_ == 0)
{
lean_dec(v_decl_1552_);
goto v___jp_1563_;
}
else
{
lean_object* v___x_1569_; uint8_t v___x_1570_; uint8_t v___x_1571_; uint8_t v___x_1572_; lean_object* v___x_1573_; uint64_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___f_1584_; lean_object* v___x_1585_; 
v___x_1569_ = lean_box(1);
v___x_1570_ = 1;
v___x_1571_ = 0;
v___x_1572_ = 2;
v___x_1573_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1573_, 0, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 2, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 3, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 4, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 5, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 6, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 7, v___x_1567_);
lean_ctor_set_uint8(v___x_1573_, 8, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 9, v___x_1570_);
lean_ctor_set_uint8(v___x_1573_, 10, v___x_1571_);
lean_ctor_set_uint8(v___x_1573_, 11, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 12, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 13, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 14, v___x_1572_);
lean_ctor_set_uint8(v___x_1573_, 15, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 16, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 17, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 18, v___x_1568_);
lean_ctor_set_uint8(v___x_1573_, 19, v___x_1567_);
v___x_1574_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1573_);
v___x_1575_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1575_, 0, v___x_1573_);
lean_ctor_set_uint64(v___x_1575_, sizeof(void*)*1, v___x_1574_);
v___x_1576_ = lean_unsigned_to_nat(0u);
v___x_1577_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1578_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1579_ = lean_box(0);
v___x_1580_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1580_, 0, v___x_1575_);
lean_ctor_set(v___x_1580_, 1, v___x_1569_);
lean_ctor_set(v___x_1580_, 2, v___x_1577_);
lean_ctor_set(v___x_1580_, 3, v___x_1578_);
lean_ctor_set(v___x_1580_, 4, v___x_1579_);
lean_ctor_set(v___x_1580_, 5, v___x_1576_);
lean_ctor_set(v___x_1580_, 6, v___x_1579_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*7, v___x_1567_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*7 + 1, v___x_1567_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*7 + 2, v___x_1567_);
lean_ctor_set_uint8(v___x_1580_, sizeof(void*)*7 + 3, v___x_1559_);
v___x_1581_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1582_ = lean_st_mk_ref(v___x_1581_);
v___x_1583_ = lean_st_mk_ref(v___x_1578_);
v___f_1584_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1585_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1552_, v___f_1584_, v___x_1583_, v___x_1580_, v___x_1582_, v_a_1553_, v_a_1554_);
lean_dec_ref_known(v___x_1580_, 7);
if (lean_obj_tag(v___x_1585_) == 0)
{
lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v_val_1589_; lean_object* v___x_1611_; size_t v_sz_1612_; size_t v___x_1613_; lean_object* v___x_1614_; lean_object* v_fst_1615_; 
lean_dec_ref_known(v___x_1585_, 1);
v___x_1586_ = lean_st_ref_get(v___x_1583_);
lean_dec(v___x_1583_);
v___x_1587_ = lean_st_ref_get(v___x_1582_);
lean_dec(v___x_1582_);
lean_dec(v___x_1587_);
v___x_1611_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1612_ = lean_array_size(v___x_1586_);
v___x_1613_ = ((size_t)0ULL);
v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1586_, v_sz_1612_, v___x_1613_, v___x_1611_);
v_fst_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_fst_1615_);
lean_dec_ref(v___x_1614_);
if (lean_obj_tag(v_fst_1615_) == 0)
{
goto v___jp_1605_;
}
else
{
lean_object* v_val_1616_; 
v_val_1616_ = lean_ctor_get(v_fst_1615_, 0);
lean_inc(v_val_1616_);
lean_dec_ref_known(v_fst_1615_, 1);
if (lean_obj_tag(v_val_1616_) == 0)
{
goto v___jp_1605_;
}
else
{
lean_object* v_val_1617_; 
lean_dec(v___x_1586_);
v_val_1617_ = lean_ctor_get(v_val_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v_val_1616_, 1);
v_val_1589_ = v_val_1617_;
goto v___jp_1588_;
}
}
v___jp_1588_:
{
lean_object* v_snd_1590_; lean_object* v___x_1592_; uint8_t v_isShared_1593_; uint8_t v_isSharedCheck_1603_; 
v_snd_1590_ = lean_ctor_get(v_val_1589_, 1);
v_isSharedCheck_1603_ = !lean_is_exclusive(v_val_1589_);
if (v_isSharedCheck_1603_ == 0)
{
lean_object* v_unused_1604_; 
v_unused_1604_ = lean_ctor_get(v_val_1589_, 0);
lean_dec(v_unused_1604_);
v___x_1592_ = v_val_1589_;
v_isShared_1593_ = v_isSharedCheck_1603_;
goto v_resetjp_1591_;
}
else
{
lean_inc(v_snd_1590_);
lean_dec(v_val_1589_);
v___x_1592_ = lean_box(0);
v_isShared_1593_ = v_isSharedCheck_1603_;
goto v_resetjp_1591_;
}
v_resetjp_1591_:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1594_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1595_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1593_ == 0)
{
lean_ctor_set_tag(v___x_1592_, 7);
lean_ctor_set(v___x_1592_, 0, v___x_1595_);
v___x_1597_ = v___x_1592_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v___x_1595_);
lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_snd_1590_);
v___x_1597_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1599_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1599_, 0, v___x_1597_);
lean_ctor_set(v___x_1599_, 1, v___x_1598_);
v___x_1600_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1594_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1600_, v_a_1553_, v_a_1554_);
return v___x_1601_;
}
}
}
v___jp_1605_:
{
lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1606_ = lean_array_get_size(v___x_1586_);
v___x_1607_ = lean_nat_dec_lt(v___x_1576_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1608_; lean_object* v___x_1609_; 
lean_dec(v___x_1586_);
v___x_1608_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1609_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1608_, v_a_1553_, v_a_1554_);
return v___x_1609_;
}
else
{
lean_object* v___x_1610_; 
v___x_1610_ = lean_array_fget(v___x_1586_, v___x_1576_);
lean_dec(v___x_1586_);
v_val_1589_ = v___x_1610_;
goto v___jp_1588_;
}
}
}
else
{
lean_dec(v___x_1583_);
lean_dec(v___x_1582_);
return v___x_1585_;
}
}
}
}
else
{
lean_dec(v_decl_1552_);
goto v___jp_1563_;
}
v___jp_1563_:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1565_, 0, v___x_1564_);
return v___x_1565_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1618_, lean_object* v_a_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_){
_start:
{
lean_object* v_res_1622_; 
v_res_1622_ = l_Lean_warnIfUsesSorry(v_decl_1618_, v_a_1619_, v_a_1620_);
lean_dec(v_a_1620_);
lean_dec_ref(v_a_1619_);
return v_res_1622_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1623_, lean_object* v_m_1624_, lean_object* v_a_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1624_, v_a_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1627_, lean_object* v_m_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v_res_1630_; 
v_res_1630_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1627_, v_m_1628_, v_a_1629_);
lean_dec_ref(v_a_1629_);
lean_dec_ref(v_m_1628_);
return v_res_1630_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1631_, lean_object* v_m_1632_, lean_object* v_a_1633_, lean_object* v_b_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1632_, v_a_1633_, v_b_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1636_, lean_object* v_a_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1637_, v_x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1640_, lean_object* v_a_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1640_, v_a_1641_, v_x_1642_);
lean_dec(v_x_1642_);
lean_dec_ref(v_a_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1644_, lean_object* v_a_1645_, lean_object* v_x_1646_){
_start:
{
uint8_t v___x_1647_; 
v___x_1647_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1645_, v_x_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1648_, lean_object* v_a_1649_, lean_object* v_x_1650_){
_start:
{
uint8_t v_res_1651_; lean_object* v_r_1652_; 
v_res_1651_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1648_, v_a_1649_, v_x_1650_);
lean_dec(v_x_1650_);
lean_dec_ref(v_a_1649_);
v_r_1652_ = lean_box(v_res_1651_);
return v_r_1652_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1653_, lean_object* v_data_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1656_, lean_object* v_a_1657_, lean_object* v_b_1658_, lean_object* v_x_1659_){
_start:
{
lean_object* v___x_1660_; 
v___x_1660_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1657_, v_b_1658_, v_x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1661_, lean_object* v_name_1662_, uint8_t v_bi_1663_, lean_object* v_type_1664_, lean_object* v_k_1665_, uint8_t v_kind_1666_, lean_object* v___y_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1662_, v_bi_1663_, v_type_1664_, v_k_1665_, v_kind_1666_, v___y_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1675_, lean_object* v_name_1676_, lean_object* v_bi_1677_, lean_object* v_type_1678_, lean_object* v_k_1679_, lean_object* v_kind_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_){
_start:
{
uint8_t v_bi_boxed_1688_; uint8_t v_kind_boxed_1689_; lean_object* v_res_1690_; 
v_bi_boxed_1688_ = lean_unbox(v_bi_1677_);
v_kind_boxed_1689_ = lean_unbox(v_kind_1680_);
v_res_1690_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1675_, v_name_1676_, v_bi_boxed_1688_, v_type_1678_, v_k_1679_, v_kind_boxed_1689_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec(v___y_1681_);
return v_res_1690_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1691_, lean_object* v_name_1692_, lean_object* v_type_1693_, lean_object* v_val_1694_, lean_object* v_k_1695_, uint8_t v_nondep_1696_, uint8_t v_kind_1697_, lean_object* v___y_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_){
_start:
{
lean_object* v___x_1705_; 
v___x_1705_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1692_, v_type_1693_, v_val_1694_, v_k_1695_, v_nondep_1696_, v_kind_1697_, v___y_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1706_, lean_object* v_name_1707_, lean_object* v_type_1708_, lean_object* v_val_1709_, lean_object* v_k_1710_, lean_object* v_nondep_1711_, lean_object* v_kind_1712_, lean_object* v___y_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_){
_start:
{
uint8_t v_nondep_boxed_1720_; uint8_t v_kind_boxed_1721_; lean_object* v_res_1722_; 
v_nondep_boxed_1720_ = lean_unbox(v_nondep_1711_);
v_kind_boxed_1721_ = lean_unbox(v_kind_1712_);
v_res_1722_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1706_, v_name_1707_, v_type_1708_, v_val_1709_, v_k_1710_, v_nondep_boxed_1720_, v_kind_boxed_1721_, v___y_1713_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_);
lean_dec(v___y_1718_);
lean_dec_ref(v___y_1717_);
lean_dec(v___y_1716_);
lean_dec_ref(v___y_1715_);
lean_dec(v___y_1714_);
lean_dec(v___y_1713_);
return v_res_1722_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1723_, lean_object* v_i_1724_, lean_object* v_source_1725_, lean_object* v_target_1726_){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1724_, v_source_1725_, v_target_1726_);
return v___x_1727_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1728_, lean_object* v_x_1729_, lean_object* v_x_1730_){
_start:
{
lean_object* v___x_1731_; 
v___x_1731_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1729_, v_x_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1781_; uint8_t v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1781_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1782_ = 0;
v___x_1783_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1784_ = l_Lean_registerTraceClass(v___x_1781_, v___x_1782_, v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1786_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1787_, lean_object* v___y_1788_){
_start:
{
lean_object* v___x_1790_; lean_object* v_nextMacroScope_1791_; lean_object* v_ngen_1792_; lean_object* v_auxDeclNGen_1793_; lean_object* v_traceState_1794_; lean_object* v_messages_1795_; lean_object* v_infoState_1796_; lean_object* v_snapshotTasks_1797_; lean_object* v___x_1799_; uint8_t v_isShared_1800_; uint8_t v_isSharedCheck_1808_; 
v___x_1790_ = lean_st_ref_take(v___y_1788_);
v_nextMacroScope_1791_ = lean_ctor_get(v___x_1790_, 1);
v_ngen_1792_ = lean_ctor_get(v___x_1790_, 2);
v_auxDeclNGen_1793_ = lean_ctor_get(v___x_1790_, 3);
v_traceState_1794_ = lean_ctor_get(v___x_1790_, 4);
v_messages_1795_ = lean_ctor_get(v___x_1790_, 6);
v_infoState_1796_ = lean_ctor_get(v___x_1790_, 7);
v_snapshotTasks_1797_ = lean_ctor_get(v___x_1790_, 8);
v_isSharedCheck_1808_ = !lean_is_exclusive(v___x_1790_);
if (v_isSharedCheck_1808_ == 0)
{
lean_object* v_unused_1809_; lean_object* v_unused_1810_; 
v_unused_1809_ = lean_ctor_get(v___x_1790_, 5);
lean_dec(v_unused_1809_);
v_unused_1810_ = lean_ctor_get(v___x_1790_, 0);
lean_dec(v_unused_1810_);
v___x_1799_ = v___x_1790_;
v_isShared_1800_ = v_isSharedCheck_1808_;
goto v_resetjp_1798_;
}
else
{
lean_inc(v_snapshotTasks_1797_);
lean_inc(v_infoState_1796_);
lean_inc(v_messages_1795_);
lean_inc(v_traceState_1794_);
lean_inc(v_auxDeclNGen_1793_);
lean_inc(v_ngen_1792_);
lean_inc(v_nextMacroScope_1791_);
lean_dec(v___x_1790_);
v___x_1799_ = lean_box(0);
v_isShared_1800_ = v_isSharedCheck_1808_;
goto v_resetjp_1798_;
}
v_resetjp_1798_:
{
lean_object* v___x_1801_; lean_object* v___x_1803_; 
v___x_1801_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1800_ == 0)
{
lean_ctor_set(v___x_1799_, 5, v___x_1801_);
lean_ctor_set(v___x_1799_, 0, v_env_1787_);
v___x_1803_ = v___x_1799_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1807_; 
v_reuseFailAlloc_1807_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1807_, 0, v_env_1787_);
lean_ctor_set(v_reuseFailAlloc_1807_, 1, v_nextMacroScope_1791_);
lean_ctor_set(v_reuseFailAlloc_1807_, 2, v_ngen_1792_);
lean_ctor_set(v_reuseFailAlloc_1807_, 3, v_auxDeclNGen_1793_);
lean_ctor_set(v_reuseFailAlloc_1807_, 4, v_traceState_1794_);
lean_ctor_set(v_reuseFailAlloc_1807_, 5, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1807_, 6, v_messages_1795_);
lean_ctor_set(v_reuseFailAlloc_1807_, 7, v_infoState_1796_);
lean_ctor_set(v_reuseFailAlloc_1807_, 8, v_snapshotTasks_1797_);
v___x_1803_ = v_reuseFailAlloc_1807_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_st_ref_put(v___y_1788_, v___x_1803_);
v___x_1805_ = lean_box(0);
v___x_1806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1806_, 0, v___x_1805_);
return v___x_1806_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1811_, v___y_1812_);
lean_dec(v___y_1812_);
return v_res_1814_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1815_, lean_object* v___y_1816_, lean_object* v___y_1817_){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1815_, v___y_1817_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1820_, lean_object* v___y_1821_, lean_object* v___y_1822_, lean_object* v___y_1823_){
_start:
{
lean_object* v_res_1824_; 
v_res_1824_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1820_, v___y_1821_, v___y_1822_);
lean_dec(v___y_1822_);
lean_dec_ref(v___y_1821_);
return v_res_1824_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_box(0);
v___x_1826_ = l_Lean_interruptExceptionId;
v___x_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v___x_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1829_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
return v___x_1830_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1831_){
_start:
{
lean_object* v_res_1832_; 
v_res_1832_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1832_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_ref_1837_; lean_object* v___x_1838_; lean_object* v_a_1839_; lean_object* v___x_1841_; uint8_t v_isShared_1842_; uint8_t v_isSharedCheck_1847_; 
v_ref_1837_ = lean_ctor_get(v___y_1834_, 2);
v___x_1838_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1833_, v___y_1834_, v___y_1835_);
v_a_1839_ = lean_ctor_get(v___x_1838_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1838_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1841_ = v___x_1838_;
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
else
{
lean_inc(v_a_1839_);
lean_dec(v___x_1838_);
v___x_1841_ = lean_box(0);
v_isShared_1842_ = v_isSharedCheck_1847_;
goto v_resetjp_1840_;
}
v_resetjp_1840_:
{
lean_object* v___x_1843_; lean_object* v___x_1845_; 
lean_inc(v_ref_1837_);
v___x_1843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1843_, 0, v_ref_1837_);
lean_ctor_set(v___x_1843_, 1, v_a_1839_);
if (v_isShared_1842_ == 0)
{
lean_ctor_set_tag(v___x_1841_, 1);
lean_ctor_set(v___x_1841_, 0, v___x_1843_);
v___x_1845_ = v___x_1841_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v___x_1843_);
v___x_1845_ = v_reuseFailAlloc_1846_;
goto v_reusejp_1844_;
}
v_reusejp_1844_:
{
return v___x_1845_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1848_, lean_object* v___y_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_){
_start:
{
lean_object* v_res_1852_; 
v_res_1852_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1848_, v___y_1849_, v___y_1850_);
lean_dec(v___y_1850_);
lean_dec_ref(v___y_1849_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___y_1858_; lean_object* v___y_1859_; 
if (lean_obj_tag(v_ex_1853_) == 16)
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
v___y_1858_ = v___y_1854_;
v___y_1859_ = v___y_1855_;
goto v___jp_1857_;
}
v___jp_1857_:
{
lean_object* v_toCold_1860_; lean_object* v_options_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; 
v_toCold_1860_ = lean_ctor_get(v___y_1858_, 0);
v_options_1861_ = lean_ctor_get(v_toCold_1860_, 2);
lean_inc_ref(v_options_1861_);
v___x_1862_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1853_, v_options_1861_);
v___x_1863_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1862_, v___y_1858_, v___y_1859_);
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
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1897_ = lean_unsigned_to_nat(1u);
v___x_1898_ = l_Lean_Level_ofNat(v___x_1897_);
return v___x_1898_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1899_ = lean_box(0);
v___x_1900_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1901_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
return v___x_1901_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1908_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1909_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
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
lean_object* v_head_1938_; lean_object* v_tail_1939_; lean_object* v___x_1940_; lean_object* v_toCold_1941_; lean_object* v_env_1942_; lean_object* v_options_1943_; lean_object* v_cancelTk_x3f_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___y_1948_; uint8_t v___y_1949_; lean_object* v_a_1953_; lean_object* v___x_1956_; lean_object* v___x_1957_; uint8_t v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
lean_dec_ref(v_b_1933_);
v_head_1938_ = lean_ctor_get(v_as_x27_1932_, 0);
v_tail_1939_ = lean_ctor_get(v_as_x27_1932_, 1);
v___x_1940_ = lean_st_ref_get(v___y_1935_);
v_toCold_1941_ = lean_ctor_get(v___y_1934_, 0);
v_env_1942_ = lean_ctor_get(v___x_1940_, 0);
lean_inc_ref(v_env_1942_);
lean_dec(v___x_1940_);
v_options_1943_ = lean_ctor_get(v_toCold_1941_, 2);
v_cancelTk_x3f_1944_ = lean_ctor_get(v_toCold_1941_, 10);
v___x_1945_ = lean_box(0);
v___x_1946_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1956_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1938_);
v___x_1957_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1957_, 0, v_head_1938_);
lean_ctor_set(v___x_1957_, 1, v___x_1945_);
lean_ctor_set(v___x_1957_, 2, v___x_1956_);
v___x_1958_ = 0;
v___x_1959_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1959_, 0, v___x_1957_);
lean_ctor_set_uint8(v___x_1959_, sizeof(void*)*1, v___x_1958_);
v___x_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
v___x_1961_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1942_, v_options_1943_, v___x_1960_, v_cancelTk_x3f_1944_);
lean_dec_ref_known(v___x_1960_, 1);
v___x_1962_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1961_, v___y_1934_, v___y_1935_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1972_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1963_, v___y_1935_);
v_isSharedCheck_1972_ = !lean_is_exclusive(v___x_1964_);
if (v_isSharedCheck_1972_ == 0)
{
lean_object* v_unused_1973_; 
v_unused_1973_ = lean_ctor_get(v___x_1964_, 0);
lean_dec(v_unused_1973_);
v___x_1966_ = v___x_1964_;
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
else
{
lean_dec(v___x_1964_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1972_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
lean_object* v___x_1968_; lean_object* v___x_1970_; 
v___x_1968_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1968_);
v___x_1970_ = v___x_1966_;
goto v_reusejp_1969_;
}
else
{
lean_object* v_reuseFailAlloc_1971_; 
v_reuseFailAlloc_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1971_, 0, v___x_1968_);
v___x_1970_ = v_reuseFailAlloc_1971_;
goto v_reusejp_1969_;
}
v_reusejp_1969_:
{
return v___x_1970_;
}
}
}
else
{
lean_object* v_a_1974_; 
v_a_1974_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1974_);
lean_dec_ref_known(v___x_1962_, 1);
v_a_1953_ = v_a_1974_;
goto v___jp_1952_;
}
v___jp_1947_:
{
if (v___y_1949_ == 0)
{
lean_dec_ref(v___y_1948_);
v_as_x27_1932_ = v_tail_1939_;
v_b_1933_ = v___x_1946_;
goto _start;
}
else
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___y_1948_);
return v___x_1951_;
}
}
v___jp_1952_:
{
uint8_t v___x_1954_; 
v___x_1954_ = l_Lean_Exception_isInterrupt(v_a_1953_);
if (v___x_1954_ == 0)
{
uint8_t v___x_1955_; 
lean_inc_ref(v_a_1953_);
v___x_1955_ = l_Lean_Exception_isRuntime(v_a_1953_);
v___y_1948_ = v_a_1953_;
v___y_1949_ = v___x_1955_;
goto v___jp_1947_;
}
else
{
v___y_1948_ = v_a_1953_;
v___y_1949_ = v___x_1954_;
goto v___jp_1947_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1975_, lean_object* v_b_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1975_, v_b_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v_as_x27_1975_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v_a_2018_; lean_object* v___y_2022_; uint8_t v___y_2023_; lean_object* v_a_2026_; 
switch(lean_obj_tag(v_decl_1981_))
{
case 1:
{
lean_object* v_val_2029_; lean_object* v___x_2030_; lean_object* v_toCold_2031_; lean_object* v_toConstantVal_2032_; lean_object* v_env_2033_; lean_object* v_options_2034_; lean_object* v_cancelTk_x3f_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v_fallbackDecl_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_val_2029_ = lean_ctor_get(v_decl_1981_, 0);
v___x_2030_ = lean_st_ref_get(v_a_1983_);
v_toCold_2031_ = lean_ctor_get(v_a_1982_, 0);
v_toConstantVal_2032_ = lean_ctor_get(v_val_2029_, 0);
v_env_2033_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_env_2033_);
lean_dec(v___x_2030_);
v_options_2034_ = lean_ctor_get(v_toCold_2031_, 2);
v_cancelTk_x3f_2035_ = lean_ctor_get(v_toCold_2031_, 10);
v___x_2036_ = 0;
lean_inc_ref(v_toConstantVal_2032_);
v___x_2037_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2037_, 0, v_toConstantVal_2032_);
lean_ctor_set_uint8(v___x_2037_, sizeof(void*)*1, v___x_2036_);
v_fallbackDecl_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2038_, 0, v___x_2037_);
v___x_2039_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2033_, v_options_2034_, v_fallbackDecl_2038_, v_cancelTk_x3f_2035_);
lean_dec_ref_known(v_fallbackDecl_2038_, 1);
v___x_2040_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2039_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref_known(v_decl_1981_, 1);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2040_, 1);
v___x_2042_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2041_, v_a_1983_);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
lean_object* v_unused_2051_; 
v_unused_2051_ = lean_ctor_get(v___x_2042_, 0);
lean_dec(v_unused_2051_);
v___x_2044_ = v___x_2042_;
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
else
{
lean_dec(v___x_2042_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2050_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2046_; lean_object* v___x_2048_; 
v___x_2046_ = lean_box(0);
if (v_isShared_2045_ == 0)
{
lean_ctor_set(v___x_2044_, 0, v___x_2046_);
v___x_2048_ = v___x_2044_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2046_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
else
{
lean_object* v_a_2052_; 
v_a_2052_ = lean_ctor_get(v___x_2040_, 0);
lean_inc(v_a_2052_);
lean_dec_ref_known(v___x_2040_, 1);
v_a_2018_ = v_a_2052_;
goto v___jp_2017_;
}
}
case 2:
{
lean_object* v_val_2053_; lean_object* v___x_2054_; lean_object* v_toCold_2055_; lean_object* v_toConstantVal_2056_; lean_object* v_env_2057_; lean_object* v_options_2058_; lean_object* v_cancelTk_x3f_2059_; uint8_t v___x_2060_; lean_object* v___x_2061_; lean_object* v_fallbackDecl_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v_val_2053_ = lean_ctor_get(v_decl_1981_, 0);
v___x_2054_ = lean_st_ref_get(v_a_1983_);
v_toCold_2055_ = lean_ctor_get(v_a_1982_, 0);
v_toConstantVal_2056_ = lean_ctor_get(v_val_2053_, 0);
v_env_2057_ = lean_ctor_get(v___x_2054_, 0);
lean_inc_ref(v_env_2057_);
lean_dec(v___x_2054_);
v_options_2058_ = lean_ctor_get(v_toCold_2055_, 2);
v_cancelTk_x3f_2059_ = lean_ctor_get(v_toCold_2055_, 10);
v___x_2060_ = 0;
lean_inc_ref(v_toConstantVal_2056_);
v___x_2061_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2061_, 0, v_toConstantVal_2056_);
lean_ctor_set_uint8(v___x_2061_, sizeof(void*)*1, v___x_2060_);
v_fallbackDecl_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2062_, 0, v___x_2061_);
v___x_2063_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2057_, v_options_2058_, v_fallbackDecl_2062_, v_cancelTk_x3f_2059_);
lean_dec_ref_known(v_fallbackDecl_2062_, 1);
v___x_2064_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2063_, v_a_1982_, v_a_1983_);
if (lean_obj_tag(v___x_2064_) == 0)
{
lean_object* v_a_2065_; lean_object* v___x_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2074_; 
lean_dec_ref_known(v_decl_1981_, 1);
v_a_2065_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2064_, 1);
v___x_2066_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2065_, v_a_1983_);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2066_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v___x_2066_, 0);
lean_dec(v_unused_2075_);
v___x_2068_ = v___x_2066_;
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
else
{
lean_dec(v___x_2066_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2074_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2070_; lean_object* v___x_2072_; 
v___x_2070_ = lean_box(0);
if (v_isShared_2069_ == 0)
{
lean_ctor_set(v___x_2068_, 0, v___x_2070_);
v___x_2072_ = v___x_2068_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v___x_2070_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
else
{
lean_object* v_a_2076_; 
v_a_2076_ = lean_ctor_get(v___x_2064_, 0);
lean_inc(v_a_2076_);
lean_dec_ref_known(v___x_2064_, 1);
v_a_2026_ = v_a_2076_;
goto v___jp_2025_;
}
}
default: 
{
v___y_1986_ = v_a_1982_;
v___y_1987_ = v_a_1983_;
goto v___jp_1985_;
}
}
v___jp_1985_:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; 
v___x_1988_ = l_Lean_Declaration_getNames(v_decl_1981_);
v___x_1989_ = lean_box(0);
v___x_1990_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1991_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1988_, v___x_1990_, v___y_1986_, v___y_1987_);
lean_dec(v___x_1988_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v___x_1994_; uint8_t v_isShared_1995_; uint8_t v_isSharedCheck_2004_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2004_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2004_ == 0)
{
v___x_1994_ = v___x_1991_;
v_isShared_1995_ = v_isSharedCheck_2004_;
goto v_resetjp_1993_;
}
else
{
lean_inc(v_a_1992_);
lean_dec(v___x_1991_);
v___x_1994_ = lean_box(0);
v_isShared_1995_ = v_isSharedCheck_2004_;
goto v_resetjp_1993_;
}
v_resetjp_1993_:
{
lean_object* v_fst_1996_; 
v_fst_1996_ = lean_ctor_get(v_a_1992_, 0);
lean_inc(v_fst_1996_);
lean_dec(v_a_1992_);
if (lean_obj_tag(v_fst_1996_) == 0)
{
lean_object* v___x_1998_; 
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v___x_1989_);
v___x_1998_ = v___x_1994_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_1999_; 
v_reuseFailAlloc_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1999_, 0, v___x_1989_);
v___x_1998_ = v_reuseFailAlloc_1999_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
return v___x_1998_;
}
}
else
{
lean_object* v_val_2000_; lean_object* v___x_2002_; 
v_val_2000_ = lean_ctor_get(v_fst_1996_, 0);
lean_inc(v_val_2000_);
lean_dec_ref_known(v_fst_1996_, 1);
if (v_isShared_1995_ == 0)
{
lean_ctor_set(v___x_1994_, 0, v_val_2000_);
v___x_2002_ = v___x_1994_;
goto v_reusejp_2001_;
}
else
{
lean_object* v_reuseFailAlloc_2003_; 
v_reuseFailAlloc_2003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2003_, 0, v_val_2000_);
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
else
{
lean_object* v_a_2005_; lean_object* v___x_2007_; uint8_t v_isShared_2008_; uint8_t v_isSharedCheck_2012_; 
v_a_2005_ = lean_ctor_get(v___x_1991_, 0);
v_isSharedCheck_2012_ = !lean_is_exclusive(v___x_1991_);
if (v_isSharedCheck_2012_ == 0)
{
v___x_2007_ = v___x_1991_;
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
else
{
lean_inc(v_a_2005_);
lean_dec(v___x_1991_);
v___x_2007_ = lean_box(0);
v_isShared_2008_ = v_isSharedCheck_2012_;
goto v_resetjp_2006_;
}
v_resetjp_2006_:
{
lean_object* v___x_2010_; 
if (v_isShared_2008_ == 0)
{
v___x_2010_ = v___x_2007_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2011_; 
v_reuseFailAlloc_2011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2011_, 0, v_a_2005_);
v___x_2010_ = v_reuseFailAlloc_2011_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
return v___x_2010_;
}
}
}
}
v___jp_2013_:
{
if (v___y_2015_ == 0)
{
lean_dec_ref(v___y_2014_);
v___y_1986_ = v_a_1982_;
v___y_1987_ = v_a_1983_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2016_; 
lean_dec(v_decl_1981_);
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
v___jp_2021_:
{
if (v___y_2023_ == 0)
{
lean_dec_ref(v___y_2022_);
v___y_1986_ = v_a_1982_;
v___y_1987_ = v_a_1983_;
goto v___jp_1985_;
}
else
{
lean_object* v___x_2024_; 
lean_dec(v_decl_1981_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___y_2022_);
return v___x_2024_;
}
}
v___jp_2025_:
{
uint8_t v___x_2027_; 
v___x_2027_ = l_Lean_Exception_isInterrupt(v_a_2026_);
if (v___x_2027_ == 0)
{
uint8_t v___x_2028_; 
lean_inc_ref(v_a_2026_);
v___x_2028_ = l_Lean_Exception_isRuntime(v_a_2026_);
v___y_2022_ = v_a_2026_;
v___y_2023_ = v___x_2028_;
goto v___jp_2021_;
}
else
{
v___y_2022_ = v_a_2026_;
v___y_2023_ = v___x_2027_;
goto v___jp_2021_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2082_, lean_object* v_x_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2083_, v___y_2084_, v___y_2085_);
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2088_, lean_object* v_x_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v_res_2093_; 
v_res_2093_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2088_, v_x_2089_, v___y_2090_, v___y_2091_);
lean_dec(v___y_2091_);
lean_dec_ref(v___y_2090_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2094_, lean_object* v_as_x27_2095_, lean_object* v_b_2096_, lean_object* v_a_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v___x_2101_; 
v___x_2101_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2095_, v_b_2096_, v___y_2098_, v___y_2099_);
return v___x_2101_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2102_, lean_object* v_as_x27_2103_, lean_object* v_b_2104_, lean_object* v_a_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v_res_2109_; 
v_res_2109_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2102_, v_as_x27_2103_, v_b_2104_, v_a_2105_, v___y_2106_, v___y_2107_);
lean_dec(v___y_2107_);
lean_dec_ref(v___y_2106_);
lean_dec(v_as_x27_2103_);
lean_dec(v_as_2102_);
return v_res_2109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2115_, v___y_2116_, v___y_2117_);
lean_dec(v___y_2117_);
lean_dec_ref(v___y_2116_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2120_, lean_object* v_ex_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2121_, v___y_2122_, v___y_2123_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2126_, lean_object* v_ex_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2126_, v_ex_2127_, v___y_2128_, v___y_2129_);
lean_dec(v___y_2129_);
lean_dec_ref(v___y_2128_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2132_, lean_object* v_msg_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v___x_2137_; 
v___x_2137_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2133_, v___y_2134_, v___y_2135_);
return v___x_2137_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2138_, lean_object* v_msg_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v_res_2143_; 
v_res_2143_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2138_, v_msg_2139_, v___y_2140_, v___y_2141_);
lean_dec(v___y_2141_);
lean_dec_ref(v___y_2140_);
return v_res_2143_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; 
v___x_2144_ = lean_unsigned_to_nat(32u);
v___x_2145_ = lean_mk_empty_array_with_capacity(v___x_2144_);
v___x_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2146_, 0, v___x_2145_);
return v___x_2146_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2147_ = ((size_t)5ULL);
v___x_2148_ = lean_unsigned_to_nat(0u);
v___x_2149_ = lean_unsigned_to_nat(32u);
v___x_2150_ = lean_mk_empty_array_with_capacity(v___x_2149_);
v___x_2151_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2152_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2152_, 0, v___x_2151_);
lean_ctor_set(v___x_2152_, 1, v___x_2150_);
lean_ctor_set(v___x_2152_, 2, v___x_2148_);
lean_ctor_set(v___x_2152_, 3, v___x_2148_);
lean_ctor_set_usize(v___x_2152_, 4, v___x_2147_);
return v___x_2152_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2153_){
_start:
{
lean_object* v___x_2155_; lean_object* v_traceState_2156_; lean_object* v_traces_2157_; lean_object* v___x_2158_; lean_object* v_traceState_2159_; lean_object* v_env_2160_; lean_object* v_nextMacroScope_2161_; lean_object* v_ngen_2162_; lean_object* v_auxDeclNGen_2163_; lean_object* v_cache_2164_; lean_object* v_messages_2165_; lean_object* v_infoState_2166_; lean_object* v_snapshotTasks_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2186_; 
v___x_2155_ = lean_st_ref_get(v___y_2153_);
v_traceState_2156_ = lean_ctor_get(v___x_2155_, 4);
lean_inc_ref(v_traceState_2156_);
lean_dec(v___x_2155_);
v_traces_2157_ = lean_ctor_get(v_traceState_2156_, 0);
lean_inc_ref(v_traces_2157_);
lean_dec_ref(v_traceState_2156_);
v___x_2158_ = lean_st_ref_take(v___y_2153_);
v_traceState_2159_ = lean_ctor_get(v___x_2158_, 4);
v_env_2160_ = lean_ctor_get(v___x_2158_, 0);
v_nextMacroScope_2161_ = lean_ctor_get(v___x_2158_, 1);
v_ngen_2162_ = lean_ctor_get(v___x_2158_, 2);
v_auxDeclNGen_2163_ = lean_ctor_get(v___x_2158_, 3);
v_cache_2164_ = lean_ctor_get(v___x_2158_, 5);
v_messages_2165_ = lean_ctor_get(v___x_2158_, 6);
v_infoState_2166_ = lean_ctor_get(v___x_2158_, 7);
v_snapshotTasks_2167_ = lean_ctor_get(v___x_2158_, 8);
v_isSharedCheck_2186_ = !lean_is_exclusive(v___x_2158_);
if (v_isSharedCheck_2186_ == 0)
{
v___x_2169_ = v___x_2158_;
v_isShared_2170_ = v_isSharedCheck_2186_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_snapshotTasks_2167_);
lean_inc(v_infoState_2166_);
lean_inc(v_messages_2165_);
lean_inc(v_cache_2164_);
lean_inc(v_traceState_2159_);
lean_inc(v_auxDeclNGen_2163_);
lean_inc(v_ngen_2162_);
lean_inc(v_nextMacroScope_2161_);
lean_inc(v_env_2160_);
lean_dec(v___x_2158_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2186_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
uint64_t v_tid_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2184_; 
v_tid_2171_ = lean_ctor_get_uint64(v_traceState_2159_, sizeof(void*)*1);
v_isSharedCheck_2184_ = !lean_is_exclusive(v_traceState_2159_);
if (v_isSharedCheck_2184_ == 0)
{
lean_object* v_unused_2185_; 
v_unused_2185_ = lean_ctor_get(v_traceState_2159_, 0);
lean_dec(v_unused_2185_);
v___x_2173_ = v_traceState_2159_;
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
else
{
lean_dec(v_traceState_2159_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2184_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2175_; lean_object* v___x_2177_; 
v___x_2175_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2175_);
v___x_2177_ = v___x_2173_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2175_);
lean_ctor_set_uint64(v_reuseFailAlloc_2183_, sizeof(void*)*1, v_tid_2171_);
v___x_2177_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
lean_object* v___x_2179_; 
if (v_isShared_2170_ == 0)
{
lean_ctor_set(v___x_2169_, 4, v___x_2177_);
v___x_2179_ = v___x_2169_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2182_; 
v_reuseFailAlloc_2182_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2182_, 0, v_env_2160_);
lean_ctor_set(v_reuseFailAlloc_2182_, 1, v_nextMacroScope_2161_);
lean_ctor_set(v_reuseFailAlloc_2182_, 2, v_ngen_2162_);
lean_ctor_set(v_reuseFailAlloc_2182_, 3, v_auxDeclNGen_2163_);
lean_ctor_set(v_reuseFailAlloc_2182_, 4, v___x_2177_);
lean_ctor_set(v_reuseFailAlloc_2182_, 5, v_cache_2164_);
lean_ctor_set(v_reuseFailAlloc_2182_, 6, v_messages_2165_);
lean_ctor_set(v_reuseFailAlloc_2182_, 7, v_infoState_2166_);
lean_ctor_set(v_reuseFailAlloc_2182_, 8, v_snapshotTasks_2167_);
v___x_2179_ = v_reuseFailAlloc_2182_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2180_ = lean_st_ref_put(v___y_2153_, v___x_2179_);
v___x_2181_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_traces_2157_);
return v___x_2181_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
lean_object* v_res_2189_; 
v_res_2189_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2187_);
lean_dec(v___y_2187_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2190_, lean_object* v___y_2191_){
_start:
{
lean_object* v___x_2193_; 
v___x_2193_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2191_);
return v___x_2193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2198_, lean_object* v_opts_2199_, lean_object* v_act_2200_, lean_object* v_decl_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; 
lean_inc(v___y_2203_);
lean_inc_ref(v___y_2202_);
v___x_2205_ = lean_apply_2(v_act_2200_, v___y_2202_, v___y_2203_);
v___x_2206_ = l_Lean_profileitIOUnsafe___redArg(v_category_2198_, v_opts_2199_, v___x_2205_, v_decl_2201_);
return v___x_2206_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2207_, lean_object* v_opts_2208_, lean_object* v_act_2209_, lean_object* v_decl_2210_, lean_object* v___y_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2207_, v_opts_2208_, v_act_2209_, v_decl_2210_, v___y_2211_, v___y_2212_);
lean_dec(v___y_2212_);
lean_dec_ref(v___y_2211_);
lean_dec_ref(v_opts_2208_);
lean_dec_ref(v_category_2207_);
return v_res_2214_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2215_, lean_object* v_category_2216_, lean_object* v_opts_2217_, lean_object* v_act_2218_, lean_object* v_decl_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_){
_start:
{
lean_object* v___x_2223_; 
v___x_2223_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2216_, v_opts_2217_, v_act_2218_, v_decl_2219_, v___y_2220_, v___y_2221_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2224_, lean_object* v_category_2225_, lean_object* v_opts_2226_, lean_object* v_act_2227_, lean_object* v_decl_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2224_, v_category_2225_, v_opts_2226_, v_act_2227_, v_decl_2228_, v___y_2229_, v___y_2230_);
lean_dec(v___y_2230_);
lean_dec_ref(v___y_2229_);
lean_dec_ref(v_opts_2226_);
lean_dec_ref(v_category_2225_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2233_, lean_object* v_a_2234_){
_start:
{
if (lean_obj_tag(v_a_2233_) == 0)
{
lean_object* v___x_2235_; 
v___x_2235_ = l_List_reverse___redArg(v_a_2234_);
return v___x_2235_;
}
else
{
lean_object* v_head_2236_; lean_object* v_tail_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2246_; 
v_head_2236_ = lean_ctor_get(v_a_2233_, 0);
v_tail_2237_ = lean_ctor_get(v_a_2233_, 1);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2233_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2239_ = v_a_2233_;
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_tail_2237_);
lean_inc(v_head_2236_);
lean_dec(v_a_2233_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2246_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2241_; lean_object* v___x_2243_; 
v___x_2241_ = l_Lean_MessageData_ofName(v_head_2236_);
if (v_isShared_2240_ == 0)
{
lean_ctor_set(v___x_2239_, 1, v_a_2234_);
lean_ctor_set(v___x_2239_, 0, v___x_2241_);
v___x_2243_ = v___x_2239_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v___x_2241_);
lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_a_2234_);
v___x_2243_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
v_a_2233_ = v_tail_2237_;
v_a_2234_ = v___x_2243_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
return v___x_2249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2250_, lean_object* v_x_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2255_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2256_ = l_Lean_Declaration_getTopLevelNames(v_decl_2250_);
v___x_2257_ = lean_box(0);
v___x_2258_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2256_, v___x_2257_);
v___x_2259_ = l_Lean_MessageData_ofList(v___x_2258_);
v___x_2260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2260_, 0, v___x_2255_);
lean_ctor_set(v___x_2260_, 1, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2262_, lean_object* v_x_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2262_, v_x_2263_, v___y_2264_, v___y_2265_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec_ref(v_x_2263_);
return v_res_2267_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2268_, size_t v_i_2269_, lean_object* v_bs_2270_){
_start:
{
uint8_t v___x_2271_; 
v___x_2271_ = lean_usize_dec_lt(v_i_2269_, v_sz_2268_);
if (v___x_2271_ == 0)
{
return v_bs_2270_;
}
else
{
lean_object* v_v_2272_; lean_object* v_msg_2273_; lean_object* v___x_2274_; lean_object* v_bs_x27_2275_; size_t v___x_2276_; size_t v___x_2277_; lean_object* v___x_2278_; 
v_v_2272_ = lean_array_uget_borrowed(v_bs_2270_, v_i_2269_);
v_msg_2273_ = lean_ctor_get(v_v_2272_, 1);
lean_inc_ref(v_msg_2273_);
v___x_2274_ = lean_unsigned_to_nat(0u);
v_bs_x27_2275_ = lean_array_uset(v_bs_2270_, v_i_2269_, v___x_2274_);
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_add(v_i_2269_, v___x_2276_);
v___x_2278_ = lean_array_uset(v_bs_x27_2275_, v_i_2269_, v_msg_2273_);
v_i_2269_ = v___x_2277_;
v_bs_2270_ = v___x_2278_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2280_, lean_object* v_i_2281_, lean_object* v_bs_2282_){
_start:
{
size_t v_sz_boxed_2283_; size_t v_i_boxed_2284_; lean_object* v_res_2285_; 
v_sz_boxed_2283_ = lean_unbox_usize(v_sz_2280_);
lean_dec(v_sz_2280_);
v_i_boxed_2284_ = lean_unbox_usize(v_i_2281_);
lean_dec(v_i_2281_);
v_res_2285_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2283_, v_i_boxed_2284_, v_bs_2282_);
return v_res_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2286_, lean_object* v_data_2287_, lean_object* v_ref_2288_, lean_object* v_msg_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_){
_start:
{
lean_object* v_toCold_2293_; lean_object* v_currRecDepth_2294_; lean_object* v_ref_2295_; uint8_t v_diag_2296_; uint8_t v_suppressElabErrors_2297_; lean_object* v___x_2298_; lean_object* v_traceState_2299_; lean_object* v_traces_2300_; lean_object* v_ref_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; size_t v_sz_2304_; size_t v___x_2305_; lean_object* v___x_2306_; lean_object* v_msg_2307_; lean_object* v___x_2308_; lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2346_; 
v_toCold_2293_ = lean_ctor_get(v___y_2290_, 0);
v_currRecDepth_2294_ = lean_ctor_get(v___y_2290_, 1);
v_ref_2295_ = lean_ctor_get(v___y_2290_, 2);
v_diag_2296_ = lean_ctor_get_uint8(v___y_2290_, sizeof(void*)*3);
v_suppressElabErrors_2297_ = lean_ctor_get_uint8(v___y_2290_, sizeof(void*)*3 + 1);
v___x_2298_ = lean_st_ref_get(v___y_2291_);
v_traceState_2299_ = lean_ctor_get(v___x_2298_, 4);
lean_inc_ref(v_traceState_2299_);
lean_dec(v___x_2298_);
v_traces_2300_ = lean_ctor_get(v_traceState_2299_, 0);
lean_inc_ref(v_traces_2300_);
lean_dec_ref(v_traceState_2299_);
v_ref_2301_ = l_Lean_replaceRef(v_ref_2288_, v_ref_2295_);
lean_inc(v_currRecDepth_2294_);
lean_inc_ref(v_toCold_2293_);
v___x_2302_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2302_, 0, v_toCold_2293_);
lean_ctor_set(v___x_2302_, 1, v_currRecDepth_2294_);
lean_ctor_set(v___x_2302_, 2, v_ref_2301_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*3, v_diag_2296_);
lean_ctor_set_uint8(v___x_2302_, sizeof(void*)*3 + 1, v_suppressElabErrors_2297_);
v___x_2303_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2300_);
lean_dec_ref(v_traces_2300_);
v_sz_2304_ = lean_array_size(v___x_2303_);
v___x_2305_ = ((size_t)0ULL);
v___x_2306_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2304_, v___x_2305_, v___x_2303_);
v_msg_2307_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2307_, 0, v_data_2287_);
lean_ctor_set(v_msg_2307_, 1, v_msg_2289_);
lean_ctor_set(v_msg_2307_, 2, v___x_2306_);
v___x_2308_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2307_, v___x_2302_, v___y_2291_);
lean_dec_ref_known(v___x_2302_, 3);
v_a_2309_ = lean_ctor_get(v___x_2308_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2308_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2311_ = v___x_2308_;
v_isShared_2312_ = v_isSharedCheck_2346_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2308_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2346_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; lean_object* v_traceState_2314_; lean_object* v_env_2315_; lean_object* v_nextMacroScope_2316_; lean_object* v_ngen_2317_; lean_object* v_auxDeclNGen_2318_; lean_object* v_cache_2319_; lean_object* v_messages_2320_; lean_object* v_infoState_2321_; lean_object* v_snapshotTasks_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2345_; 
v___x_2313_ = lean_st_ref_take(v___y_2291_);
v_traceState_2314_ = lean_ctor_get(v___x_2313_, 4);
v_env_2315_ = lean_ctor_get(v___x_2313_, 0);
v_nextMacroScope_2316_ = lean_ctor_get(v___x_2313_, 1);
v_ngen_2317_ = lean_ctor_get(v___x_2313_, 2);
v_auxDeclNGen_2318_ = lean_ctor_get(v___x_2313_, 3);
v_cache_2319_ = lean_ctor_get(v___x_2313_, 5);
v_messages_2320_ = lean_ctor_get(v___x_2313_, 6);
v_infoState_2321_ = lean_ctor_get(v___x_2313_, 7);
v_snapshotTasks_2322_ = lean_ctor_get(v___x_2313_, 8);
v_isSharedCheck_2345_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2345_ == 0)
{
v___x_2324_ = v___x_2313_;
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_snapshotTasks_2322_);
lean_inc(v_infoState_2321_);
lean_inc(v_messages_2320_);
lean_inc(v_cache_2319_);
lean_inc(v_traceState_2314_);
lean_inc(v_auxDeclNGen_2318_);
lean_inc(v_ngen_2317_);
lean_inc(v_nextMacroScope_2316_);
lean_inc(v_env_2315_);
lean_dec(v___x_2313_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2345_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
uint64_t v_tid_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2343_; 
v_tid_2326_ = lean_ctor_get_uint64(v_traceState_2314_, sizeof(void*)*1);
v_isSharedCheck_2343_ = !lean_is_exclusive(v_traceState_2314_);
if (v_isSharedCheck_2343_ == 0)
{
lean_object* v_unused_2344_; 
v_unused_2344_ = lean_ctor_get(v_traceState_2314_, 0);
lean_dec(v_unused_2344_);
v___x_2328_ = v_traceState_2314_;
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
else
{
lean_dec(v_traceState_2314_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2343_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2333_; 
v___x_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2330_, 0, v_ref_2288_);
lean_ctor_set(v___x_2330_, 1, v_a_2309_);
v___x_2331_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2286_, v___x_2330_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2331_);
v___x_2333_ = v___x_2328_;
goto v_reusejp_2332_;
}
else
{
lean_object* v_reuseFailAlloc_2342_; 
v_reuseFailAlloc_2342_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2342_, 0, v___x_2331_);
lean_ctor_set_uint64(v_reuseFailAlloc_2342_, sizeof(void*)*1, v_tid_2326_);
v___x_2333_ = v_reuseFailAlloc_2342_;
goto v_reusejp_2332_;
}
v_reusejp_2332_:
{
lean_object* v___x_2335_; 
if (v_isShared_2325_ == 0)
{
lean_ctor_set(v___x_2324_, 4, v___x_2333_);
v___x_2335_ = v___x_2324_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_env_2315_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_nextMacroScope_2316_);
lean_ctor_set(v_reuseFailAlloc_2341_, 2, v_ngen_2317_);
lean_ctor_set(v_reuseFailAlloc_2341_, 3, v_auxDeclNGen_2318_);
lean_ctor_set(v_reuseFailAlloc_2341_, 4, v___x_2333_);
lean_ctor_set(v_reuseFailAlloc_2341_, 5, v_cache_2319_);
lean_ctor_set(v_reuseFailAlloc_2341_, 6, v_messages_2320_);
lean_ctor_set(v_reuseFailAlloc_2341_, 7, v_infoState_2321_);
lean_ctor_set(v_reuseFailAlloc_2341_, 8, v_snapshotTasks_2322_);
v___x_2335_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2339_; 
v___x_2336_ = lean_st_ref_put(v___y_2291_, v___x_2335_);
v___x_2337_ = lean_box(0);
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 0, v___x_2337_);
v___x_2339_ = v___x_2311_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2340_; 
v_reuseFailAlloc_2340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2340_, 0, v___x_2337_);
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
lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v_data_2405_; lean_object* v_fst_2408_; lean_object* v_snd_2409_; lean_object* v___x_2410_; uint8_t v___x_2411_; lean_object* v___y_2413_; lean_object* v_a_2414_; uint8_t v___y_2429_; double v___y_2460_; 
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
lean_object* v___x_2465_; uint8_t v___x_2466_; 
v___x_2465_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2466_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2392_, v___x_2465_);
if (v___x_2466_ == 0)
{
lean_object* v___x_2467_; lean_object* v___x_2468_; double v___x_2469_; double v___x_2470_; double v___x_2471_; 
v___x_2467_ = l_Lean_trace_profiler_threshold;
v___x_2468_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2392_, v___x_2467_);
v___x_2469_ = lean_float_of_nat(v___x_2468_);
v___x_2470_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2471_ = lean_float_div(v___x_2469_, v___x_2470_);
v___y_2460_ = v___x_2471_;
goto v___jp_2459_;
}
else
{
lean_object* v___x_2472_; lean_object* v___x_2473_; double v___x_2474_; 
v___x_2472_ = l_Lean_trace_profiler_threshold;
v___x_2473_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2392_, v___x_2472_);
v___x_2474_ = lean_float_of_nat(v___x_2473_);
v___y_2460_ = v___x_2474_;
goto v___jp_2459_;
}
}
v___jp_2402_:
{
lean_object* v___x_2406_; 
lean_inc(v___y_2403_);
v___x_2406_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2394_, v_data_2405_, v___y_2403_, v___y_2404_, v___y_2397_, v___y_2398_);
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
v___y_2403_ = v___y_2413_;
v___y_2404_ = v_a_2414_;
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
v___y_2403_ = v___y_2413_;
v___y_2404_ = v_a_2414_;
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
lean_object* v___x_2430_; lean_object* v_traceState_2431_; lean_object* v_env_2432_; lean_object* v_nextMacroScope_2433_; lean_object* v_ngen_2434_; lean_object* v_auxDeclNGen_2435_; lean_object* v_cache_2436_; lean_object* v_messages_2437_; lean_object* v_infoState_2438_; lean_object* v_snapshotTasks_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2458_; 
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
v_messages_2437_ = lean_ctor_get(v___x_2430_, 6);
v_infoState_2438_ = lean_ctor_get(v___x_2430_, 7);
v_snapshotTasks_2439_ = lean_ctor_get(v___x_2430_, 8);
v_isSharedCheck_2458_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2458_ == 0)
{
v___x_2441_ = v___x_2430_;
v_isShared_2442_ = v_isSharedCheck_2458_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_snapshotTasks_2439_);
lean_inc(v_infoState_2438_);
lean_inc(v_messages_2437_);
lean_inc(v_cache_2436_);
lean_inc(v_traceState_2431_);
lean_inc(v_auxDeclNGen_2435_);
lean_inc(v_ngen_2434_);
lean_inc(v_nextMacroScope_2433_);
lean_inc(v_env_2432_);
lean_dec(v___x_2430_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2458_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
uint64_t v_tid_2443_; lean_object* v_traces_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2457_; 
v_tid_2443_ = lean_ctor_get_uint64(v_traceState_2431_, sizeof(void*)*1);
v_traces_2444_ = lean_ctor_get(v_traceState_2431_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_traceState_2431_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2446_ = v_traceState_2431_;
v_isShared_2447_ = v_isSharedCheck_2457_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_traces_2444_);
lean_dec(v_traceState_2431_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2457_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2394_, v_traces_2444_);
lean_dec_ref(v_traces_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2456_; 
v_reuseFailAlloc_2456_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2456_, 0, v___x_2448_);
lean_ctor_set_uint64(v_reuseFailAlloc_2456_, sizeof(void*)*1, v_tid_2443_);
v___x_2450_ = v_reuseFailAlloc_2456_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 4, v___x_2450_);
v___x_2452_ = v___x_2441_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_env_2432_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_nextMacroScope_2433_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v_ngen_2434_);
lean_ctor_set(v_reuseFailAlloc_2455_, 3, v_auxDeclNGen_2435_);
lean_ctor_set(v_reuseFailAlloc_2455_, 4, v___x_2450_);
lean_ctor_set(v_reuseFailAlloc_2455_, 5, v_cache_2436_);
lean_ctor_set(v_reuseFailAlloc_2455_, 6, v_messages_2437_);
lean_ctor_set(v_reuseFailAlloc_2455_, 7, v_infoState_2438_);
lean_ctor_set(v_reuseFailAlloc_2455_, 8, v_snapshotTasks_2439_);
v___x_2452_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_st_ref_put(v___y_2398_, v___x_2452_);
v___x_2454_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2400_);
return v___x_2454_;
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
v___jp_2459_:
{
double v___x_2461_; double v___x_2462_; double v___x_2463_; uint8_t v___x_2464_; 
v___x_2461_ = lean_unbox_float(v_snd_2409_);
v___x_2462_ = lean_unbox_float(v_fst_2408_);
v___x_2463_ = lean_float_sub(v___x_2461_, v___x_2462_);
v___x_2464_ = lean_float_decLt(v___y_2460_, v___x_2463_);
v___y_2429_ = v___x_2464_;
goto v___jp_2428_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2475_, lean_object* v_collapsed_2476_, lean_object* v_tag_2477_, lean_object* v_opts_2478_, lean_object* v_clsEnabled_2479_, lean_object* v_oldTraces_2480_, lean_object* v_msg_2481_, lean_object* v_resStartStop_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v_collapsed_boxed_2486_; uint8_t v_clsEnabled_boxed_2487_; lean_object* v_res_2488_; 
v_collapsed_boxed_2486_ = lean_unbox(v_collapsed_2476_);
v_clsEnabled_boxed_2487_ = lean_unbox(v_clsEnabled_2479_);
v_res_2488_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2475_, v_collapsed_boxed_2486_, v_tag_2477_, v_opts_2478_, v_clsEnabled_boxed_2487_, v_oldTraces_2480_, v_msg_2481_, v_resStartStop_2482_, v___y_2483_, v___y_2484_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_opts_2478_);
return v_res_2488_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2491_; double v___x_2492_; 
v___x_2491_ = lean_unsigned_to_nat(1000000000u);
v___x_2492_ = lean_float_of_nat(v___x_2491_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2493_, lean_object* v___x_2494_, uint8_t v___x_2495_, lean_object* v___x_2496_, lean_object* v___f_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
lean_object* v___y_2502_; lean_object* v___y_2503_; uint8_t v___y_2504_; lean_object* v___y_2515_; lean_object* v_a_2516_; lean_object* v___y_2520_; lean_object* v___y_2521_; uint8_t v___y_2522_; lean_object* v___y_2533_; lean_object* v_a_2534_; lean_object* v_toCold_2537_; lean_object* v_options_2538_; uint8_t v_hasTrace_2539_; 
v_toCold_2537_ = lean_ctor_get(v___y_2498_, 0);
v_options_2538_ = lean_ctor_get(v_toCold_2537_, 2);
v_hasTrace_2539_ = lean_ctor_get_uint8(v_options_2538_, sizeof(void*)*1);
if (v_hasTrace_2539_ == 0)
{
lean_object* v_cancelTk_x3f_2540_; lean_object* v___x_2541_; 
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec(v___x_2494_);
v_cancelTk_x3f_2540_ = lean_ctor_get(v_toCold_2537_, 10);
lean_inc(v_decl_2493_);
v___x_2541_ = l_Lean_warnIfUsesSorry(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v___x_2542_; lean_object* v_env_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_dec_ref_known(v___x_2541_, 1);
v___x_2542_ = lean_st_ref_get(v___y_2499_);
v_env_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc_ref(v_env_2543_);
lean_dec(v___x_2542_);
v___x_2544_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2543_, v_options_2538_, v_decl_2493_, v_cancelTk_x3f_2540_);
v___x_2545_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2544_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2547_; 
lean_dec(v_decl_2493_);
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
lean_inc(v_a_2546_);
lean_dec_ref_known(v___x_2545_, 1);
v___x_2547_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2546_, v___y_2499_);
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
v___y_2533_ = v___x_2553_;
v_a_2534_ = v_a_2548_;
goto v___jp_2532_;
}
}
}
}
else
{
lean_dec(v_decl_2493_);
return v___x_2541_;
}
}
else
{
lean_object* v_cancelTk_x3f_2556_; lean_object* v_inheritedTraceOptions_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; uint8_t v___x_2560_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_a_2564_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v_a_2579_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v_a_2584_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2596_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v_a_2607_; lean_object* v___y_2617_; lean_object* v___y_2618_; lean_object* v_a_2619_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v_a_2624_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; lean_object* v___y_2639_; lean_object* v___y_2640_; lean_object* v_a_2641_; 
v_cancelTk_x3f_2556_ = lean_ctor_get(v_toCold_2537_, 10);
v_inheritedTraceOptions_2557_ = lean_ctor_get(v_toCold_2537_, 11);
v___x_2558_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2494_);
v___x_2559_ = l_Lean_Name_append(v___x_2558_, v___x_2494_);
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
lean_dec_ref(v___f_2497_);
lean_dec_ref(v___x_2496_);
lean_dec(v___x_2494_);
lean_inc(v_decl_2493_);
v___x_2671_ = l_Lean_warnIfUsesSorry(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v___x_2672_; lean_object* v_env_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; 
lean_dec_ref_known(v___x_2671_, 1);
v___x_2672_ = lean_st_ref_get(v___y_2499_);
v_env_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc_ref(v_env_2673_);
lean_dec(v___x_2672_);
v___x_2674_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2673_, v_options_2538_, v_decl_2493_, v_cancelTk_x3f_2556_);
v___x_2675_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2674_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
lean_dec(v_decl_2493_);
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
v___x_2677_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2676_, v___y_2499_);
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
v___y_2515_ = v___x_2683_;
v_a_2516_ = v_a_2678_;
goto v___jp_2514_;
}
}
}
}
else
{
lean_dec(v_decl_2493_);
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
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2494_, v___x_2495_, v___x_2496_, v_options_2538_, v___x_2560_, v___y_2562_, v___f_2497_, v___x_2574_, v___y_2498_, v___y_2499_);
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
v___x_2597_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_dec_ref_known(v___x_2597_, 1);
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2595_;
v_a_2579_ = v___y_2593_;
goto v___jp_2576_;
}
else
{
lean_dec_ref(v___y_2593_);
v___y_2587_ = v___y_2594_;
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___x_2597_;
goto v___jp_2586_;
}
}
else
{
lean_dec(v_decl_2493_);
v___y_2577_ = v___y_2594_;
v___y_2578_ = v___y_2595_;
v_a_2579_ = v___y_2593_;
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
v___y_2593_ = v_a_2601_;
v___y_2594_ = v___y_2599_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___x_2603_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v_a_2601_;
v___y_2594_ = v___y_2599_;
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
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2494_, v___x_2495_, v___x_2496_, v_options_2538_, v___x_2560_, v___y_2606_, v___f_2497_, v___x_2614_, v___y_2498_, v___y_2499_);
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
v___x_2637_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2493_, v___y_2498_, v___y_2499_);
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
lean_dec(v_decl_2493_);
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
v___x_2645_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2499_);
v_a_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc(v_a_2646_);
lean_dec_ref(v___x_2645_);
v___x_2647_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2648_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2538_, v___x_2647_);
if (v___x_2648_ == 0)
{
lean_object* v___x_2649_; lean_object* v___x_2650_; 
v___x_2649_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2493_);
v___x_2650_ = l_Lean_warnIfUsesSorry(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v___x_2651_; lean_object* v_env_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; 
lean_dec_ref_known(v___x_2650_, 1);
v___x_2651_ = lean_st_ref_get(v___y_2499_);
v_env_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc_ref(v_env_2652_);
lean_dec(v___x_2651_);
v___x_2653_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2652_, v_options_2538_, v_decl_2493_, v_cancelTk_x3f_2556_);
v___x_2654_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2653_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v_a_2655_; lean_object* v___x_2656_; lean_object* v_a_2657_; 
lean_dec(v_decl_2493_);
v_a_2655_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2655_);
lean_dec_ref_known(v___x_2654_, 1);
v___x_2656_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2655_, v___y_2499_);
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref(v___x_2656_);
v___y_2582_ = v_a_2646_;
v___y_2583_ = v___x_2649_;
v_a_2584_ = v_a_2657_;
goto v___jp_2581_;
}
else
{
lean_object* v_a_2658_; 
v_a_2658_ = lean_ctor_get(v___x_2654_, 0);
lean_inc(v_a_2658_);
lean_dec_ref_known(v___x_2654_, 1);
v___y_2599_ = v_a_2646_;
v___y_2600_ = v___x_2649_;
v_a_2601_ = v_a_2658_;
goto v___jp_2598_;
}
}
else
{
lean_dec(v_decl_2493_);
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
lean_inc(v_decl_2493_);
v___x_2660_ = l_Lean_warnIfUsesSorry(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v___x_2661_; lean_object* v_env_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; 
lean_dec_ref_known(v___x_2660_, 1);
v___x_2661_ = lean_st_ref_get(v___y_2499_);
v_env_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc_ref(v_env_2662_);
lean_dec(v___x_2661_);
v___x_2663_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2662_, v_options_2538_, v_decl_2493_, v_cancelTk_x3f_2556_);
v___x_2664_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2663_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; lean_object* v_a_2667_; 
lean_dec(v_decl_2493_);
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
v___x_2666_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2665_, v___y_2499_);
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref(v___x_2666_);
v___y_2622_ = v___x_2659_;
v___y_2623_ = v_a_2646_;
v_a_2624_ = v_a_2667_;
goto v___jp_2621_;
}
else
{
lean_object* v_a_2668_; 
v_a_2668_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v___x_2664_, 1);
v___y_2639_ = v___x_2659_;
v___y_2640_ = v_a_2646_;
v_a_2641_ = v_a_2668_;
goto v___jp_2638_;
}
}
else
{
lean_dec(v_decl_2493_);
v___y_2627_ = v___x_2659_;
v___y_2628_ = v_a_2646_;
v___y_2629_ = v___x_2660_;
goto v___jp_2626_;
}
}
}
}
v___jp_2501_:
{
if (v___y_2504_ == 0)
{
lean_object* v___x_2505_; 
lean_dec_ref(v___y_2502_);
v___x_2505_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2493_, v___y_2498_, v___y_2499_);
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
lean_ctor_set(v___x_2507_, 0, v___y_2503_);
v___x_2510_ = v___x_2507_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___y_2503_);
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
lean_dec_ref(v___y_2503_);
return v___x_2505_;
}
}
else
{
lean_dec_ref(v___y_2503_);
lean_dec(v_decl_2493_);
return v___y_2502_;
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
v___y_2502_ = v___y_2515_;
v___y_2503_ = v_a_2516_;
v___y_2504_ = v___x_2518_;
goto v___jp_2501_;
}
else
{
v___y_2502_ = v___y_2515_;
v___y_2503_ = v_a_2516_;
v___y_2504_ = v___x_2517_;
goto v___jp_2501_;
}
}
v___jp_2519_:
{
if (v___y_2522_ == 0)
{
lean_object* v___x_2523_; 
lean_dec_ref(v___y_2521_);
v___x_2523_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2493_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2530_ == 0)
{
lean_object* v_unused_2531_; 
v_unused_2531_ = lean_ctor_get(v___x_2523_, 0);
lean_dec(v_unused_2531_);
v___x_2525_ = v___x_2523_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_dec(v___x_2523_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
lean_ctor_set_tag(v___x_2525_, 1);
lean_ctor_set(v___x_2525_, 0, v___y_2520_);
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v___y_2520_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
else
{
lean_dec_ref(v___y_2520_);
return v___x_2523_;
}
}
else
{
lean_dec_ref(v___y_2520_);
lean_dec(v_decl_2493_);
return v___y_2521_;
}
}
v___jp_2532_:
{
uint8_t v___x_2535_; 
v___x_2535_ = l_Lean_Exception_isInterrupt(v_a_2534_);
if (v___x_2535_ == 0)
{
uint8_t v___x_2536_; 
lean_inc_ref(v_a_2534_);
v___x_2536_ = l_Lean_Exception_isRuntime(v_a_2534_);
v___y_2520_ = v_a_2534_;
v___y_2521_ = v___y_2533_;
v___y_2522_ = v___x_2536_;
goto v___jp_2519_;
}
else
{
v___y_2520_ = v_a_2534_;
v___y_2521_ = v___y_2533_;
v___y_2522_ = v___x_2535_;
goto v___jp_2519_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2686_, lean_object* v___x_2687_, lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___f_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___x_7930__boxed_2694_; lean_object* v_res_2695_; 
v___x_7930__boxed_2694_ = lean_unbox(v___x_2688_);
v_res_2695_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2686_, v___x_2687_, v___x_7930__boxed_2694_, v___x_2689_, v___f_2690_, v___y_2691_, v___y_2692_);
lean_dec(v___y_2692_);
lean_dec_ref(v___y_2691_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_){
_start:
{
lean_object* v_toCold_2704_; lean_object* v_options_2705_; lean_object* v___f_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; uint8_t v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___f_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; 
v_toCold_2704_ = lean_ctor_get(v_a_2701_, 0);
v_options_2705_ = lean_ctor_get(v_toCold_2704_, 2);
lean_inc(v_decl_2700_);
v___f_2706_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2706_, 0, v_decl_2700_);
v___x_2707_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2708_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2709_ = 1;
v___x_2710_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2711_ = lean_box(v___x_2709_);
v___f_2712_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2712_, 0, v_decl_2700_);
lean_closure_set(v___f_2712_, 1, v___x_2708_);
lean_closure_set(v___f_2712_, 2, v___x_2711_);
lean_closure_set(v___f_2712_, 3, v___x_2710_);
lean_closure_set(v___f_2712_, 4, v___f_2706_);
v___x_2713_ = lean_box(0);
v___x_2714_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2707_, v_options_2705_, v___f_2712_, v___x_2713_, v_a_2701_, v_a_2702_);
return v___x_2714_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2715_, v_a_2716_, v_a_2717_);
lean_dec(v_a_2717_);
lean_dec_ref(v_a_2716_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2721_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2726_, v_x_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2732_, lean_object* v_a_2733_, lean_object* v___y_2734_, lean_object* v_a_x3f_2735_){
_start:
{
lean_object* v___x_2737_; lean_object* v_env_2738_; lean_object* v___x_2739_; 
v___x_2737_ = lean_st_ref_get(v___y_2732_);
v_env_2738_ = lean_ctor_get(v___x_2737_, 0);
lean_inc_ref(v_env_2738_);
lean_dec(v___x_2737_);
v___x_2739_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2733_, v_env_2738_);
if (lean_obj_tag(v___x_2739_) == 0)
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
v_a_2740_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2739_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2739_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
else
{
lean_object* v_a_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2760_; 
v_a_2748_ = lean_ctor_get(v___x_2739_, 0);
v_isSharedCheck_2760_ = !lean_is_exclusive(v___x_2739_);
if (v_isSharedCheck_2760_ == 0)
{
v___x_2750_ = v___x_2739_;
v_isShared_2751_ = v_isSharedCheck_2760_;
goto v_resetjp_2749_;
}
else
{
lean_inc(v_a_2748_);
lean_dec(v___x_2739_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2760_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v_ref_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; 
v_ref_2752_ = lean_ctor_get(v___y_2734_, 2);
v___x_2753_ = lean_io_error_to_string(v_a_2748_);
v___x_2754_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2754_, 0, v___x_2753_);
v___x_2755_ = l_Lean_MessageData_ofFormat(v___x_2754_);
lean_inc(v_ref_2752_);
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v_ref_2752_);
lean_ctor_set(v___x_2756_, 1, v___x_2755_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 0, v___x_2756_);
v___x_2758_ = v___x_2750_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2761_, lean_object* v_a_2762_, lean_object* v___y_2763_, lean_object* v_a_x3f_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_res_2766_; 
v_res_2766_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2761_, v_a_2762_, v___y_2763_, v_a_x3f_2764_);
lean_dec(v_a_x3f_2764_);
lean_dec_ref(v___y_2763_);
lean_dec(v___y_2761_);
return v_res_2766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2767_, lean_object* v_a_2768_, lean_object* v_decl_2769_, lean_object* v_x_2770_, lean_object* v___y_2771_, lean_object* v___y_2772_){
_start:
{
lean_object* v___x_2774_; lean_object* v_r_2775_; 
v___x_2774_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2767_, v___y_2772_);
lean_dec_ref(v___x_2774_);
v_r_2775_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2769_, v___y_2771_, v___y_2772_);
if (lean_obj_tag(v_r_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2792_; 
v_a_2776_ = lean_ctor_get(v_r_2775_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v_r_2775_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2778_ = v_r_2775_;
v_isShared_2779_ = v_isSharedCheck_2792_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v_r_2775_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2792_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
lean_inc(v_a_2776_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set_tag(v___x_2778_, 1);
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
lean_object* v___x_2782_; 
v___x_2782_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2772_, v_a_2768_, v___y_2771_, v___x_2781_);
lean_dec_ref(v___x_2781_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2789_ == 0)
{
lean_object* v_unused_2790_; 
v_unused_2790_ = lean_ctor_get(v___x_2782_, 0);
lean_dec(v_unused_2790_);
v___x_2784_ = v___x_2782_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v___x_2782_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 0, v_a_2776_);
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2776_);
v___x_2787_ = v_reuseFailAlloc_2788_;
goto v_reusejp_2786_;
}
v_reusejp_2786_:
{
return v___x_2787_;
}
}
}
else
{
lean_dec(v_a_2776_);
return v___x_2782_;
}
}
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v_a_2793_ = lean_ctor_get(v_r_2775_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v_r_2775_, 1);
v___x_2794_ = lean_box(0);
v___x_2795_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2772_, v_a_2768_, v___y_2771_, v___x_2794_);
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
lean_ctor_set_tag(v___x_2797_, 1);
lean_ctor_set(v___x_2797_, 0, v_a_2793_);
v___x_2800_ = v___x_2797_;
goto v_reusejp_2799_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2793_);
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
lean_dec(v_a_2793_);
return v___x_2795_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2804_, lean_object* v_a_2805_, lean_object* v_decl_2806_, lean_object* v_x_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2804_, v_a_2805_, v_decl_2806_, v_x_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec_ref(v_x_2807_);
return v_res_2811_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2815_, lean_object* v_x_2816_, lean_object* v___y_2817_, lean_object* v___y_2818_){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2820_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2821_ = l_Lean_Declaration_getNames(v_decl_2815_);
v___x_2822_ = lean_box(0);
v___x_2823_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2821_, v___x_2822_);
v___x_2824_ = l_Lean_MessageData_ofList(v___x_2823_);
v___x_2825_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2825_, 0, v___x_2820_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2825_);
return v___x_2826_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2827_, lean_object* v_x_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_res_2832_; 
v_res_2832_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2827_, v_x_2828_, v___y_2829_, v___y_2830_);
lean_dec(v___y_2830_);
lean_dec_ref(v___y_2829_);
lean_dec_ref(v_x_2828_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2835_, lean_object* v_msg_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_){
_start:
{
lean_object* v_ref_2840_; lean_object* v___x_2841_; lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2886_; 
v_ref_2840_ = lean_ctor_get(v___y_2837_, 2);
v___x_2841_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2836_, v___y_2837_, v___y_2838_);
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2844_ = v___x_2841_;
v_isShared_2845_ = v_isSharedCheck_2886_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2841_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2886_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v_traceState_2847_; lean_object* v_env_2848_; lean_object* v_nextMacroScope_2849_; lean_object* v_ngen_2850_; lean_object* v_auxDeclNGen_2851_; lean_object* v_cache_2852_; lean_object* v_messages_2853_; lean_object* v_infoState_2854_; lean_object* v_snapshotTasks_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2885_; 
v___x_2846_ = lean_st_ref_take(v___y_2838_);
v_traceState_2847_ = lean_ctor_get(v___x_2846_, 4);
v_env_2848_ = lean_ctor_get(v___x_2846_, 0);
v_nextMacroScope_2849_ = lean_ctor_get(v___x_2846_, 1);
v_ngen_2850_ = lean_ctor_get(v___x_2846_, 2);
v_auxDeclNGen_2851_ = lean_ctor_get(v___x_2846_, 3);
v_cache_2852_ = lean_ctor_get(v___x_2846_, 5);
v_messages_2853_ = lean_ctor_get(v___x_2846_, 6);
v_infoState_2854_ = lean_ctor_get(v___x_2846_, 7);
v_snapshotTasks_2855_ = lean_ctor_get(v___x_2846_, 8);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2846_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2857_ = v___x_2846_;
v_isShared_2858_ = v_isSharedCheck_2885_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_snapshotTasks_2855_);
lean_inc(v_infoState_2854_);
lean_inc(v_messages_2853_);
lean_inc(v_cache_2852_);
lean_inc(v_traceState_2847_);
lean_inc(v_auxDeclNGen_2851_);
lean_inc(v_ngen_2850_);
lean_inc(v_nextMacroScope_2849_);
lean_inc(v_env_2848_);
lean_dec(v___x_2846_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2885_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
uint64_t v_tid_2859_; lean_object* v_traces_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2884_; 
v_tid_2859_ = lean_ctor_get_uint64(v_traceState_2847_, sizeof(void*)*1);
v_traces_2860_ = lean_ctor_get(v_traceState_2847_, 0);
v_isSharedCheck_2884_ = !lean_is_exclusive(v_traceState_2847_);
if (v_isSharedCheck_2884_ == 0)
{
v___x_2862_ = v_traceState_2847_;
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_traces_2860_);
lean_dec(v_traceState_2847_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2884_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2864_; double v___x_2865_; uint8_t v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; 
v___x_2864_ = lean_box(0);
v___x_2865_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2866_ = 0;
v___x_2867_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2868_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2868_, 0, v_cls_2835_);
lean_ctor_set(v___x_2868_, 1, v___x_2864_);
lean_ctor_set(v___x_2868_, 2, v___x_2867_);
lean_ctor_set_float(v___x_2868_, sizeof(void*)*3, v___x_2865_);
lean_ctor_set_float(v___x_2868_, sizeof(void*)*3 + 8, v___x_2865_);
lean_ctor_set_uint8(v___x_2868_, sizeof(void*)*3 + 16, v___x_2866_);
v___x_2869_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2870_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2870_, 0, v___x_2868_);
lean_ctor_set(v___x_2870_, 1, v_a_2842_);
lean_ctor_set(v___x_2870_, 2, v___x_2869_);
lean_inc(v_ref_2840_);
v___x_2871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2871_, 0, v_ref_2840_);
lean_ctor_set(v___x_2871_, 1, v___x_2870_);
v___x_2872_ = l_Lean_PersistentArray_push___redArg(v_traces_2860_, v___x_2871_);
if (v_isShared_2863_ == 0)
{
lean_ctor_set(v___x_2862_, 0, v___x_2872_);
v___x_2874_ = v___x_2862_;
goto v_reusejp_2873_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v___x_2872_);
lean_ctor_set_uint64(v_reuseFailAlloc_2883_, sizeof(void*)*1, v_tid_2859_);
v___x_2874_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2873_;
}
v_reusejp_2873_:
{
lean_object* v___x_2876_; 
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 4, v___x_2874_);
v___x_2876_ = v___x_2857_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_env_2848_);
lean_ctor_set(v_reuseFailAlloc_2882_, 1, v_nextMacroScope_2849_);
lean_ctor_set(v_reuseFailAlloc_2882_, 2, v_ngen_2850_);
lean_ctor_set(v_reuseFailAlloc_2882_, 3, v_auxDeclNGen_2851_);
lean_ctor_set(v_reuseFailAlloc_2882_, 4, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2882_, 5, v_cache_2852_);
lean_ctor_set(v_reuseFailAlloc_2882_, 6, v_messages_2853_);
lean_ctor_set(v_reuseFailAlloc_2882_, 7, v_infoState_2854_);
lean_ctor_set(v_reuseFailAlloc_2882_, 8, v_snapshotTasks_2855_);
v___x_2876_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2877_ = lean_st_ref_put(v___y_2838_, v___x_2876_);
v___x_2878_ = lean_box(0);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2878_);
v___x_2880_ = v___x_2844_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2887_, lean_object* v_msg_2888_, lean_object* v___y_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_){
_start:
{
lean_object* v_res_2892_; 
v_res_2892_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2887_, v_msg_2888_, v___y_2889_, v___y_2890_);
lean_dec(v___y_2890_);
lean_dec_ref(v___y_2889_);
return v_res_2892_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2895_ = l_Lean_stringToMessageData(v___x_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2896_, lean_object* v_cls_2897_, lean_object* v_x_2898_, lean_object* v___y_2899_, lean_object* v___y_2900_){
_start:
{
lean_object* v_toCold_2902_; lean_object* v_options_2903_; uint8_t v_hasTrace_2904_; 
v_toCold_2902_ = lean_ctor_get(v___y_2899_, 0);
v_options_2903_ = lean_ctor_get(v_toCold_2902_, 2);
v_hasTrace_2904_ = lean_ctor_get_uint8(v_options_2903_, sizeof(void*)*1);
if (v_hasTrace_2904_ == 0)
{
lean_object* v___x_2905_; 
lean_dec(v_cls_2897_);
v___x_2905_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2896_, v___y_2899_, v___y_2900_);
return v___x_2905_;
}
else
{
lean_object* v_inheritedTraceOptions_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint8_t v___x_2909_; 
v_inheritedTraceOptions_2906_ = lean_ctor_get(v_toCold_2902_, 11);
v___x_2907_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2897_);
v___x_2908_ = l_Lean_Name_append(v___x_2907_, v_cls_2897_);
v___x_2909_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2906_, v_options_2903_, v___x_2908_);
lean_dec(v___x_2908_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; 
lean_dec(v_cls_2897_);
v___x_2910_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2896_, v___y_2899_, v___y_2900_);
return v___x_2910_;
}
else
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2912_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2897_, v___x_2911_, v___y_2899_, v___y_2900_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2913_; 
lean_dec_ref_known(v___x_2912_, 1);
v___x_2913_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2896_, v___y_2899_, v___y_2900_);
return v___x_2913_;
}
else
{
lean_dec(v_decl_2896_);
return v___x_2912_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2914_, lean_object* v_cls_2915_, lean_object* v_x_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_){
_start:
{
lean_object* v_res_2920_; 
v_res_2920_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2914_, v_cls_2915_, v_x_2916_, v___y_2917_, v___y_2918_);
lean_dec(v___y_2918_);
lean_dec_ref(v___y_2917_);
lean_dec(v_x_2916_);
return v_res_2920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_toCold_2924_; lean_object* v_options_2925_; uint8_t v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; 
v_toCold_2924_ = lean_ctor_get(v___y_2922_, 0);
v_options_2925_ = lean_ctor_get(v_toCold_2924_, 2);
v___x_2926_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2925_, v_opt_2921_);
v___x_2927_ = lean_box(v___x_2926_);
v___x_2928_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2928_, 0, v___x_2927_);
return v___x_2928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2929_, v___y_2930_);
lean_dec_ref(v___y_2930_);
lean_dec_ref(v_opt_2929_);
return v_res_2932_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2933_){
_start:
{
if (lean_obj_tag(v_x_2933_) == 0)
{
uint8_t v___x_2934_; 
v___x_2934_ = 1;
return v___x_2934_;
}
else
{
lean_object* v_head_2935_; lean_object* v_tail_2936_; uint8_t v___x_2937_; 
v_head_2935_ = lean_ctor_get(v_x_2933_, 0);
v_tail_2936_ = lean_ctor_get(v_x_2933_, 1);
v___x_2937_ = l_Lean_isPrivateName(v_head_2935_);
if (v___x_2937_ == 0)
{
return v___x_2937_;
}
else
{
v_x_2933_ = v_tail_2936_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2939_){
_start:
{
uint8_t v_res_2940_; lean_object* v_r_2941_; 
v_res_2940_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2939_);
lean_dec(v_x_2939_);
v_r_2941_ = lean_box(v_res_2940_);
return v_r_2941_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2947_; lean_object* v___x_2948_; 
v___x_2947_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2948_ = l_Lean_stringToMessageData(v___x_2947_);
return v___x_2948_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; 
v___x_2950_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2951_ = l_Lean_stringToMessageData(v___x_2950_);
return v___x_2951_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2953_; lean_object* v___x_2954_; 
v___x_2953_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2954_ = l_Lean_stringToMessageData(v___x_2953_);
return v___x_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2955_, uint8_t v_hasTrace_2956_, uint8_t v___x_2957_, lean_object* v___x_2958_, lean_object* v_cls_2959_, lean_object* v___x_2960_, lean_object* v_____x_2961_, lean_object* v_exportedInfo_x3f_2962_, lean_object* v___y_2963_, lean_object* v___y_2964_){
_start:
{
lean_object* v___y_2967_; lean_object* v___y_2968_; lean_object* v_a_2969_; lean_object* v___y_2980_; lean_object* v___y_2981_; lean_object* v_a_2982_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v_snd_3066_; lean_object* v_fst_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3197_; 
v_snd_3066_ = lean_ctor_get(v_____x_2961_, 1);
v_fst_3067_ = lean_ctor_get(v_____x_2961_, 0);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_____x_2961_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3069_ = v_____x_2961_;
v_isShared_3070_ = v_isSharedCheck_3197_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_snd_3066_);
lean_inc(v_fst_3067_);
lean_dec(v_____x_2961_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3197_;
goto v_resetjp_3068_;
}
v___jp_2966_:
{
lean_object* v___x_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v___x_2970_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2968_, v___y_2967_);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2970_, 0);
lean_dec(v_unused_2978_);
v___x_2972_ = v___x_2970_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_dec(v___x_2970_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
lean_ctor_set_tag(v___x_2972_, 1);
lean_ctor_set(v___x_2972_, 0, v_a_2969_);
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2969_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
v___jp_2979_:
{
lean_object* v___x_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
v___x_2983_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2981_, v___y_2980_);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2990_ == 0)
{
lean_object* v_unused_2991_; 
v_unused_2991_ = lean_ctor_get(v___x_2983_, 0);
lean_dec(v_unused_2991_);
v___x_2985_ = v___x_2983_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_dec(v___x_2983_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
lean_ctor_set(v___x_2985_, 0, v_a_2982_);
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2982_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
v___jp_2992_:
{
lean_object* v___x_3003_; 
lean_inc_ref(v___y_3000_);
v___x_3003_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3001_, v___y_3000_, v___y_2998_, v___y_3002_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v___x_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref_known(v___x_3003_, 1);
lean_inc_ref(v___y_2999_);
v___x_3004_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2999_, v___y_2997_);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3051_ == 0)
{
lean_object* v_unused_3052_; 
v_unused_3052_ = lean_ctor_get(v___x_3004_, 0);
lean_dec(v_unused_3052_);
v___x_3006_ = v___x_3004_;
v_isShared_3007_ = v_isSharedCheck_3051_;
goto v_resetjp_3005_;
}
else
{
lean_dec(v___x_3004_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3051_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_toCold_3008_; lean_object* v_options_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_toCold_3008_ = lean_ctor_get(v___y_2996_, 0);
v_options_3009_ = lean_ctor_get(v_toCold_3008_, 2);
v___x_3010_ = l_Lean_Elab_async;
v___x_3011_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3009_, v___x_3010_);
if (v___x_3011_ == 0)
{
lean_object* v___x_3012_; lean_object* v_r_3013_; 
lean_del_object(v___x_3006_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2993_);
v___x_3012_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3000_, v___y_2997_);
lean_dec_ref(v___x_3012_);
v_r_3013_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2955_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v_r_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3023_; 
v_a_3014_ = lean_ctor_get(v_r_3013_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v_r_3013_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3016_ = v_r_3013_;
v_isShared_3017_ = v_isSharedCheck_3023_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v_r_3013_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3023_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
lean_inc(v_a_3014_);
if (v_isShared_3017_ == 0)
{
lean_ctor_set_tag(v___x_3016_, 1);
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
lean_object* v___x_3020_; 
v___x_3020_ = lean_apply_2(v___y_2994_, v___x_3019_, lean_box(0));
if (lean_obj_tag(v___x_3020_) == 0)
{
lean_dec_ref_known(v___x_3020_, 1);
v___y_2980_ = v___y_2997_;
v___y_2981_ = v___y_2999_;
v_a_2982_ = v_a_3014_;
goto v___jp_2979_;
}
else
{
lean_object* v_a_3021_; 
lean_dec(v_a_3014_);
v_a_3021_ = lean_ctor_get(v___x_3020_, 0);
lean_inc(v_a_3021_);
lean_dec_ref_known(v___x_3020_, 1);
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2999_;
v_a_2969_ = v_a_3021_;
goto v___jp_2966_;
}
}
}
}
else
{
lean_object* v_a_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; 
v_a_3024_ = lean_ctor_get(v_r_3013_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v_r_3013_, 1);
v___x_3025_ = lean_box(0);
v___x_3026_ = lean_apply_2(v___y_2994_, v___x_3025_, lean_box(0));
if (lean_obj_tag(v___x_3026_) == 0)
{
lean_dec_ref_known(v___x_3026_, 1);
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2999_;
v_a_2969_ = v_a_3024_;
goto v___jp_2966_;
}
else
{
lean_object* v_a_3027_; 
lean_dec(v_a_3024_);
v_a_3027_ = lean_ctor_get(v___x_3026_, 0);
lean_inc(v_a_3027_);
lean_dec_ref_known(v___x_3026_, 1);
v___y_2967_ = v___y_2997_;
v___y_2968_ = v___y_2999_;
v_a_2969_ = v_a_3027_;
goto v___jp_2966_;
}
}
}
else
{
lean_object* v___x_3028_; lean_object* v___x_3030_; 
lean_dec_ref(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec_ref(v___y_2994_);
lean_dec(v_decl_2955_);
v___x_3028_ = l_IO_CancelToken_new();
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
lean_ctor_set(v___x_3006_, 0, v___x_3028_);
v___x_3030_ = v___x_3006_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3028_);
v___x_3030_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3033_ = l_Lean_Name_toString(v___x_3032_, v_hasTrace_2956_);
lean_inc_ref(v___x_3030_);
v___x_3034_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2993_, v___x_3030_, v___x_3033_, v___y_2996_, v___y_2997_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v_a_3035_; lean_object* v_checked_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; 
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v_checked_3036_ = lean_ctor_get(v___y_2995_, 2);
lean_inc_ref(v_checked_3036_);
lean_dec_ref(v___y_2995_);
v___x_3037_ = lean_io_map_task(v_a_3035_, v_checked_3036_, v___x_3031_, v___x_2957_);
v___x_3038_ = lean_box(0);
v___x_3039_ = lean_box(2);
v___x_3040_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_ctor_set(v___x_3040_, 2, v___x_3030_);
lean_ctor_set(v___x_3040_, 3, v___x_3037_);
v___x_3041_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3040_, v___y_2997_);
return v___x_3041_;
}
else
{
lean_object* v_a_3042_; lean_object* v___x_3044_; uint8_t v_isShared_3045_; uint8_t v_isSharedCheck_3049_; 
lean_dec_ref(v___x_3030_);
lean_dec_ref(v___y_2995_);
v_a_3042_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3049_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3049_ == 0)
{
v___x_3044_ = v___x_3034_;
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
else
{
lean_inc(v_a_3042_);
lean_dec(v___x_3034_);
v___x_3044_ = lean_box(0);
v_isShared_3045_ = v_isSharedCheck_3049_;
goto v_resetjp_3043_;
}
v_resetjp_3043_:
{
lean_object* v___x_3047_; 
if (v_isShared_3045_ == 0)
{
v___x_3047_ = v___x_3044_;
goto v_reusejp_3046_;
}
else
{
lean_object* v_reuseFailAlloc_3048_; 
v_reuseFailAlloc_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3048_, 0, v_a_3042_);
v___x_3047_ = v_reuseFailAlloc_3048_;
goto v_reusejp_3046_;
}
v_reusejp_3046_:
{
return v___x_3047_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v___y_3000_);
lean_dec_ref(v___y_2999_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec(v_decl_2955_);
v_a_3053_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3055_ = v___x_3003_;
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___x_3003_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3065_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v_ref_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v_ref_3057_ = lean_ctor_get(v___y_2996_, 2);
v___x_3058_ = lean_io_error_to_string(v_a_3053_);
v___x_3059_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3059_, 0, v___x_3058_);
v___x_3060_ = l_Lean_MessageData_ofFormat(v___x_3059_);
lean_inc(v_ref_3057_);
v___x_3061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3061_, 0, v_ref_3057_);
lean_ctor_set(v___x_3061_, 1, v___x_3060_);
if (v_isShared_3056_ == 0)
{
lean_ctor_set(v___x_3055_, 0, v___x_3061_);
v___x_3063_ = v___x_3055_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
v_resetjp_3068_:
{
lean_object* v_fst_3071_; lean_object* v_snd_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3196_; 
v_fst_3071_ = lean_ctor_get(v_snd_3066_, 0);
v_snd_3072_ = lean_ctor_get(v_snd_3066_, 1);
v_isSharedCheck_3196_ = !lean_is_exclusive(v_snd_3066_);
if (v_isSharedCheck_3196_ == 0)
{
v___x_3074_ = v_snd_3066_;
v_isShared_3075_ = v_isSharedCheck_3196_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_snd_3072_);
lean_inc(v_fst_3071_);
lean_dec(v_snd_3066_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3196_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___y_3077_; lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v_exportedInfo_x3f_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3124_; lean_object* v___y_3125_; lean_object* v___y_3128_; lean_object* v___y_3129_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___x_3186_; lean_object* v_env_3187_; uint8_t v___x_3188_; 
v___x_3186_ = lean_st_ref_get(v___y_2964_);
v_env_3187_ = lean_ctor_get(v___x_3186_, 0);
lean_inc_ref(v_env_3187_);
lean_dec(v___x_3186_);
v___x_3188_ = l_Lean_Environment_containsOnBranch(v_env_3187_, v_fst_3067_);
lean_dec_ref(v_env_3187_);
if (v___x_3188_ == 0)
{
lean_del_object(v___x_3069_);
v___y_3151_ = v___y_2963_;
v___y_3152_ = v___y_2964_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3189_; lean_object* v_env_3190_; lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_del_object(v___x_3074_);
lean_dec(v_snd_3072_);
lean_dec(v_fst_3071_);
lean_dec(v_exportedInfo_x3f_2962_);
lean_dec(v___x_2960_);
lean_dec(v_cls_2959_);
lean_dec_ref(v___x_2958_);
lean_dec(v_decl_2955_);
v___x_3189_ = lean_st_ref_get(v___y_2964_);
v_env_3190_ = lean_ctor_get(v___x_3189_, 0);
lean_inc_ref(v_env_3190_);
lean_dec(v___x_3189_);
v___x_3191_ = lean_elab_environment_to_kernel_env(v_env_3190_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set_tag(v___x_3069_, 1);
lean_ctor_set(v___x_3069_, 1, v_fst_3067_);
lean_ctor_set(v___x_3069_, 0, v___x_3191_);
v___x_3193_ = v___x_3069_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_fst_3067_);
v___x_3193_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; 
v___x_3194_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3193_, v___y_2963_, v___y_2964_);
return v___x_3194_;
}
}
v___jp_3076_:
{
uint8_t v___x_3084_; lean_object* v___x_3085_; 
v___x_3084_ = lean_unbox(v_snd_3072_);
lean_dec(v_snd_3072_);
lean_inc_ref(v___y_3078_);
v___x_3085_ = l_Lean_Environment_addConstAsync(v___y_3078_, v_fst_3067_, v___x_3084_, v___y_3083_, v___x_2957_, v_hasTrace_2956_);
if (lean_obj_tag(v___x_3085_) == 0)
{
lean_object* v_a_3086_; lean_object* v_mainEnv_3087_; lean_object* v_asyncEnv_3088_; lean_object* v___f_3089_; lean_object* v___f_3090_; lean_object* v___x_3091_; 
lean_del_object(v___x_3074_);
v_a_3086_ = lean_ctor_get(v___x_3085_, 0);
lean_inc_n(v_a_3086_, 3);
lean_dec_ref_known(v___x_3085_, 1);
v_mainEnv_3087_ = lean_ctor_get(v_a_3086_, 0);
lean_inc_ref(v_mainEnv_3087_);
v_asyncEnv_3088_ = lean_ctor_get(v_a_3086_, 1);
lean_inc_ref_n(v_asyncEnv_3088_, 2);
lean_inc_ref(v___y_3077_);
lean_inc(v___y_3079_);
v___f_3089_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3089_, 0, v___y_3079_);
lean_closure_set(v___f_3089_, 1, v_a_3086_);
lean_closure_set(v___f_3089_, 2, v___y_3077_);
lean_inc(v_decl_2955_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3090_, 0, v_asyncEnv_3088_);
lean_closure_set(v___f_3090_, 1, v_a_3086_);
lean_closure_set(v___f_3090_, 2, v_decl_2955_);
v___x_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3091_, 0, v_fst_3071_);
if (lean_obj_tag(v___y_3080_) == 0)
{
lean_inc_ref(v___x_3091_);
v___y_2993_ = v___f_3090_;
v___y_2994_ = v___f_3089_;
v___y_2995_ = v___y_3078_;
v___y_2996_ = v___y_3081_;
v___y_2997_ = v___y_3082_;
v___y_2998_ = v___x_3091_;
v___y_2999_ = v_mainEnv_3087_;
v___y_3000_ = v_asyncEnv_3088_;
v___y_3001_ = v_a_3086_;
v___y_3002_ = v___x_3091_;
goto v___jp_2992_;
}
else
{
v___y_2993_ = v___f_3090_;
v___y_2994_ = v___f_3089_;
v___y_2995_ = v___y_3078_;
v___y_2996_ = v___y_3081_;
v___y_2997_ = v___y_3082_;
v___y_2998_ = v___x_3091_;
v___y_2999_ = v_mainEnv_3087_;
v___y_3000_ = v_asyncEnv_3088_;
v___y_3001_ = v_a_3086_;
v___y_3002_ = v___y_3080_;
goto v___jp_2992_;
}
}
else
{
lean_object* v_a_3092_; lean_object* v___x_3094_; uint8_t v_isShared_3095_; uint8_t v_isSharedCheck_3106_; 
lean_dec(v___y_3080_);
lean_dec_ref(v___y_3078_);
lean_dec(v_fst_3071_);
lean_dec(v_decl_2955_);
v_a_3092_ = lean_ctor_get(v___x_3085_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3085_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3094_ = v___x_3085_;
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
else
{
lean_inc(v_a_3092_);
lean_dec(v___x_3085_);
v___x_3094_ = lean_box(0);
v_isShared_3095_ = v_isSharedCheck_3106_;
goto v_resetjp_3093_;
}
v_resetjp_3093_:
{
lean_object* v_ref_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v_ref_3096_ = lean_ctor_get(v___y_3081_, 2);
v___x_3097_ = lean_io_error_to_string(v_a_3092_);
v___x_3098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3098_, 0, v___x_3097_);
v___x_3099_ = l_Lean_MessageData_ofFormat(v___x_3098_);
lean_inc(v_ref_3096_);
if (v_isShared_3075_ == 0)
{
lean_ctor_set(v___x_3074_, 1, v___x_3099_);
lean_ctor_set(v___x_3074_, 0, v_ref_3096_);
v___x_3101_ = v___x_3074_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_ref_3096_);
lean_ctor_set(v_reuseFailAlloc_3105_, 1, v___x_3099_);
v___x_3101_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
lean_object* v___x_3103_; 
if (v_isShared_3095_ == 0)
{
lean_ctor_set(v___x_3094_, 0, v___x_3101_);
v___x_3103_ = v___x_3094_;
goto v_reusejp_3102_;
}
else
{
lean_object* v_reuseFailAlloc_3104_; 
v_reuseFailAlloc_3104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3104_, 0, v___x_3101_);
v___x_3103_ = v_reuseFailAlloc_3104_;
goto v_reusejp_3102_;
}
v_reusejp_3102_:
{
return v___x_3103_;
}
}
}
}
}
v___jp_3107_:
{
lean_object* v___x_3111_; 
v___x_3111_ = lean_st_ref_get(v___y_3110_);
if (lean_obj_tag(v_exportedInfo_x3f_3108_) == 0)
{
lean_object* v_env_3112_; lean_object* v___x_3113_; 
v_env_3112_ = lean_ctor_get(v___x_3111_, 0);
lean_inc_ref(v_env_3112_);
lean_dec(v___x_3111_);
v___x_3113_ = lean_box(0);
v___y_3077_ = v___y_3109_;
v___y_3078_ = v_env_3112_;
v___y_3079_ = v___y_3110_;
v___y_3080_ = v_exportedInfo_x3f_3108_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___x_3113_;
goto v___jp_3076_;
}
else
{
lean_object* v_env_3114_; lean_object* v_val_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; 
v_env_3114_ = lean_ctor_get(v___x_3111_, 0);
lean_inc_ref(v_env_3114_);
lean_dec(v___x_3111_);
v_val_3115_ = lean_ctor_get(v_exportedInfo_x3f_3108_, 0);
v___x_3116_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3115_);
v___x_3117_ = lean_box(v___x_3116_);
v___x_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3118_, 0, v___x_3117_);
v___y_3077_ = v___y_3109_;
v___y_3078_ = v_env_3114_;
v___y_3079_ = v___y_3110_;
v___y_3080_ = v_exportedInfo_x3f_3108_;
v___y_3081_ = v___y_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___x_3118_;
goto v___jp_3076_;
}
}
v___jp_3119_:
{
lean_object* v___x_3122_; 
lean_inc(v_fst_3071_);
v___x_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_fst_3071_);
v_exportedInfo_x3f_3108_ = v___x_3122_;
v___y_3109_ = v___y_3120_;
v___y_3110_ = v___y_3121_;
goto v___jp_3107_;
}
v___jp_3123_:
{
lean_object* v___x_3126_; 
lean_inc(v_fst_3071_);
v___x_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_fst_3071_);
v_exportedInfo_x3f_3108_ = v___x_3126_;
v___y_3109_ = v___y_3124_;
v___y_3110_ = v___y_3125_;
goto v___jp_3107_;
}
v___jp_3127_:
{
lean_object* v___x_3130_; lean_object* v_env_3131_; lean_object* v_nextMacroScope_3132_; lean_object* v_ngen_3133_; lean_object* v_auxDeclNGen_3134_; lean_object* v_traceState_3135_; lean_object* v_messages_3136_; lean_object* v_infoState_3137_; lean_object* v_snapshotTasks_3138_; lean_object* v___x_3140_; uint8_t v_isShared_3141_; uint8_t v_isSharedCheck_3148_; 
v___x_3130_ = lean_st_ref_take(v___y_3128_);
v_env_3131_ = lean_ctor_get(v___x_3130_, 0);
v_nextMacroScope_3132_ = lean_ctor_get(v___x_3130_, 1);
v_ngen_3133_ = lean_ctor_get(v___x_3130_, 2);
v_auxDeclNGen_3134_ = lean_ctor_get(v___x_3130_, 3);
v_traceState_3135_ = lean_ctor_get(v___x_3130_, 4);
v_messages_3136_ = lean_ctor_get(v___x_3130_, 6);
v_infoState_3137_ = lean_ctor_get(v___x_3130_, 7);
v_snapshotTasks_3138_ = lean_ctor_get(v___x_3130_, 8);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3148_ == 0)
{
lean_object* v_unused_3149_; 
v_unused_3149_ = lean_ctor_get(v___x_3130_, 5);
lean_dec(v_unused_3149_);
v___x_3140_ = v___x_3130_;
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
else
{
lean_inc(v_snapshotTasks_3138_);
lean_inc(v_infoState_3137_);
lean_inc(v_messages_3136_);
lean_inc(v_traceState_3135_);
lean_inc(v_auxDeclNGen_3134_);
lean_inc(v_ngen_3133_);
lean_inc(v_nextMacroScope_3132_);
lean_inc(v_env_3131_);
lean_dec(v___x_3130_);
v___x_3140_ = lean_box(0);
v_isShared_3141_ = v_isSharedCheck_3148_;
goto v_resetjp_3139_;
}
v_resetjp_3139_:
{
lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3145_; 
v___x_3142_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3072_);
lean_inc(v_fst_3067_);
v___x_3143_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3142_, v_env_3131_, v_fst_3067_, v_snd_3072_);
if (v_isShared_3141_ == 0)
{
lean_ctor_set(v___x_3140_, 5, v___x_2958_);
lean_ctor_set(v___x_3140_, 0, v___x_3143_);
v___x_3145_ = v___x_3140_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v___x_3143_);
lean_ctor_set(v_reuseFailAlloc_3147_, 1, v_nextMacroScope_3132_);
lean_ctor_set(v_reuseFailAlloc_3147_, 2, v_ngen_3133_);
lean_ctor_set(v_reuseFailAlloc_3147_, 3, v_auxDeclNGen_3134_);
lean_ctor_set(v_reuseFailAlloc_3147_, 4, v_traceState_3135_);
lean_ctor_set(v_reuseFailAlloc_3147_, 5, v___x_2958_);
lean_ctor_set(v_reuseFailAlloc_3147_, 6, v_messages_3136_);
lean_ctor_set(v_reuseFailAlloc_3147_, 7, v_infoState_3137_);
lean_ctor_set(v_reuseFailAlloc_3147_, 8, v_snapshotTasks_3138_);
v___x_3145_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
lean_object* v___x_3146_; 
v___x_3146_ = lean_st_ref_put(v___y_3128_, v___x_3145_);
v_exportedInfo_x3f_3108_ = v_exportedInfo_x3f_2962_;
v___y_3109_ = v___y_3129_;
v___y_3110_ = v___y_3128_;
goto v___jp_3107_;
}
}
}
v___jp_3150_:
{
lean_object* v___x_3153_; uint8_t v___x_3154_; 
lean_inc(v_decl_2955_);
v___x_3153_ = l_Lean_Declaration_getTopLevelNames(v_decl_2955_);
v___x_3154_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3153_);
lean_dec(v___x_3153_);
if (v___x_3154_ == 0)
{
lean_dec(v___x_2960_);
if (lean_obj_tag(v_exportedInfo_x3f_2962_) == 0)
{
if (v___x_3154_ == 0)
{
lean_object* v_toCold_3155_; lean_object* v_options_3156_; uint8_t v_hasTrace_3157_; 
lean_dec_ref(v___x_2958_);
v_toCold_3155_ = lean_ctor_get(v___y_3151_, 0);
v_options_3156_ = lean_ctor_get(v_toCold_3155_, 2);
v_hasTrace_3157_ = lean_ctor_get_uint8(v_options_3156_, sizeof(void*)*1);
if (v_hasTrace_3157_ == 0)
{
lean_dec(v_cls_2959_);
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
goto v___jp_3119_;
}
else
{
lean_object* v_inheritedTraceOptions_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; uint8_t v___x_3161_; 
v_inheritedTraceOptions_3158_ = lean_ctor_get(v_toCold_3155_, 11);
v___x_3159_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2959_);
v___x_3160_ = l_Lean_Name_append(v___x_3159_, v_cls_2959_);
v___x_3161_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3158_, v_options_3156_, v___x_3160_);
lean_dec(v___x_3160_);
if (v___x_3161_ == 0)
{
lean_dec(v_cls_2959_);
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3163_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2959_, v___x_3162_, v___y_3151_, v___y_3152_);
if (lean_obj_tag(v___x_3163_) == 0)
{
lean_dec_ref_known(v___x_3163_, 1);
v___y_3120_ = v___y_3151_;
v___y_3121_ = v___y_3152_;
goto v___jp_3119_;
}
else
{
lean_del_object(v___x_3074_);
lean_dec(v_snd_3072_);
lean_dec(v_fst_3071_);
lean_dec(v_fst_3067_);
lean_dec(v_decl_2955_);
return v___x_3163_;
}
}
}
}
else
{
lean_dec(v_cls_2959_);
v___y_3128_ = v___y_3152_;
v___y_3129_ = v___y_3151_;
goto v___jp_3127_;
}
}
else
{
lean_dec(v_cls_2959_);
v___y_3128_ = v___y_3152_;
v___y_3129_ = v___y_3151_;
goto v___jp_3127_;
}
}
else
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v_a_3166_; uint8_t v___x_3167_; 
lean_dec(v_exportedInfo_x3f_2962_);
lean_dec_ref(v___x_2958_);
v___x_3164_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3165_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3164_, v___y_3151_);
v_a_3166_ = lean_ctor_get(v___x_3165_, 0);
lean_inc(v_a_3166_);
lean_dec_ref(v___x_3165_);
v___x_3167_ = lean_unbox(v_a_3166_);
lean_dec(v_a_3166_);
if (v___x_3167_ == 0)
{
lean_object* v_toCold_3168_; lean_object* v_options_3169_; uint8_t v_hasTrace_3170_; 
v_toCold_3168_ = lean_ctor_get(v___y_3151_, 0);
v_options_3169_ = lean_ctor_get(v_toCold_3168_, 2);
v_hasTrace_3170_ = lean_ctor_get_uint8(v_options_3169_, sizeof(void*)*1);
if (v_hasTrace_3170_ == 0)
{
lean_dec(v_cls_2959_);
v_exportedInfo_x3f_3108_ = v___x_2960_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3152_;
goto v___jp_3107_;
}
else
{
lean_object* v_inheritedTraceOptions_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_inheritedTraceOptions_3171_ = lean_ctor_get(v_toCold_3168_, 11);
v___x_3172_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2959_);
v___x_3173_ = l_Lean_Name_append(v___x_3172_, v_cls_2959_);
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3171_, v_options_3169_, v___x_3173_);
lean_dec(v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec(v_cls_2959_);
v_exportedInfo_x3f_3108_ = v___x_2960_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3152_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3176_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2959_, v___x_3175_, v___y_3151_, v___y_3152_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_dec_ref_known(v___x_3176_, 1);
v_exportedInfo_x3f_3108_ = v___x_2960_;
v___y_3109_ = v___y_3151_;
v___y_3110_ = v___y_3152_;
goto v___jp_3107_;
}
else
{
lean_del_object(v___x_3074_);
lean_dec(v_snd_3072_);
lean_dec(v_fst_3071_);
lean_dec(v_fst_3067_);
lean_dec(v___x_2960_);
lean_dec(v_decl_2955_);
return v___x_3176_;
}
}
}
}
else
{
lean_object* v_toCold_3177_; lean_object* v_options_3178_; uint8_t v_hasTrace_3179_; 
lean_dec(v___x_2960_);
v_toCold_3177_ = lean_ctor_get(v___y_3151_, 0);
v_options_3178_ = lean_ctor_get(v_toCold_3177_, 2);
v_hasTrace_3179_ = lean_ctor_get_uint8(v_options_3178_, sizeof(void*)*1);
if (v_hasTrace_3179_ == 0)
{
lean_dec(v_cls_2959_);
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
goto v___jp_3123_;
}
else
{
lean_object* v_inheritedTraceOptions_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; uint8_t v___x_3183_; 
v_inheritedTraceOptions_3180_ = lean_ctor_get(v_toCold_3177_, 11);
v___x_3181_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2959_);
v___x_3182_ = l_Lean_Name_append(v___x_3181_, v_cls_2959_);
v___x_3183_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3180_, v_options_3178_, v___x_3182_);
lean_dec(v___x_3182_);
if (v___x_3183_ == 0)
{
lean_dec(v_cls_2959_);
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
goto v___jp_3123_;
}
else
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3185_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2959_, v___x_3184_, v___y_3151_, v___y_3152_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_dec_ref_known(v___x_3185_, 1);
v___y_3124_ = v___y_3151_;
v___y_3125_ = v___y_3152_;
goto v___jp_3123_;
}
else
{
lean_del_object(v___x_3074_);
lean_dec(v_snd_3072_);
lean_dec(v_fst_3071_);
lean_dec(v_fst_3067_);
lean_dec(v_decl_2955_);
return v___x_3185_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3198_, lean_object* v_hasTrace_3199_, lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v_cls_3202_, lean_object* v___x_3203_, lean_object* v_____x_3204_, lean_object* v_exportedInfo_x3f_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_){
_start:
{
uint8_t v_hasTrace_boxed_3209_; uint8_t v___x_53058__boxed_3210_; lean_object* v_res_3211_; 
v_hasTrace_boxed_3209_ = lean_unbox(v_hasTrace_3199_);
v___x_53058__boxed_3210_ = lean_unbox(v___x_3200_);
v_res_3211_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3198_, v_hasTrace_boxed_3209_, v___x_53058__boxed_3210_, v___x_3201_, v_cls_3202_, v___x_3203_, v_____x_3204_, v_exportedInfo_x3f_3205_, v___y_3206_, v___y_3207_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3211_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3213_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3214_ = l_Lean_stringToMessageData(v___x_3213_);
return v___x_3214_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3217_ = l_Lean_stringToMessageData(v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3218_, uint8_t v___x_3219_, lean_object* v_cls_3220_, lean_object* v___x_3221_, uint8_t v_forceExpose_3222_, lean_object* v_defn_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_){
_start:
{
lean_object* v_exportedInfo_x3f_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; uint8_t v___y_3243_; uint8_t v___y_3248_; lean_object* v___y_3249_; lean_object* v___y_3250_; lean_object* v___x_3255_; lean_object* v___x_3256_; uint8_t v___y_3258_; lean_object* v_env_3274_; lean_object* v_env_3275_; 
v___x_3255_ = lean_st_ref_get(v___y_3225_);
v___x_3256_ = lean_st_ref_get(v___y_3225_);
v_env_3274_ = lean_ctor_get(v___x_3255_, 0);
lean_inc_ref(v_env_3274_);
lean_dec(v___x_3255_);
v_env_3275_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3275_);
lean_dec(v___x_3256_);
if (v_forceExpose_3222_ == 0)
{
goto v___jp_3276_;
}
else
{
if (v___x_3219_ == 0)
{
lean_dec_ref(v_env_3275_);
lean_dec_ref(v_env_3274_);
lean_dec(v_cls_3220_);
v_exportedInfo_x3f_3228_ = v___x_3221_;
v___y_3229_ = v___y_3224_;
v___y_3230_ = v___y_3225_;
goto v___jp_3227_;
}
else
{
goto v___jp_3276_;
}
}
v___jp_3227_:
{
lean_object* v_toConstantVal_3231_; lean_object* v_name_3232_; lean_object* v___x_3233_; uint8_t v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; 
v_toConstantVal_3231_ = lean_ctor_get(v_defn_3223_, 0);
v_name_3232_ = lean_ctor_get(v_toConstantVal_3231_, 0);
lean_inc(v_name_3232_);
v___x_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3233_, 0, v_defn_3223_);
v___x_3234_ = 0;
v___x_3235_ = lean_box(v___x_3234_);
v___x_3236_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3233_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v_name_3232_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
lean_inc(v___y_3230_);
lean_inc_ref(v___y_3229_);
v___x_3238_ = lean_apply_5(v___f_3218_, v___x_3237_, v_exportedInfo_x3f_3228_, v___y_3229_, v___y_3230_, lean_box(0));
return v___x_3238_;
}
v___jp_3239_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3244_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3244_, 0, v___y_3242_);
lean_ctor_set_uint8(v___x_3244_, sizeof(void*)*1, v___y_3243_);
v___x_3245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3244_);
v___x_3246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
v_exportedInfo_x3f_3228_ = v___x_3246_;
v___y_3229_ = v___y_3241_;
v___y_3230_ = v___y_3240_;
goto v___jp_3227_;
}
v___jp_3247_:
{
lean_object* v_toConstantVal_3251_; uint8_t v_safety_3252_; uint8_t v___x_3253_; uint8_t v___x_3254_; 
v_toConstantVal_3251_ = lean_ctor_get(v_defn_3223_, 0);
v_safety_3252_ = lean_ctor_get_uint8(v_defn_3223_, sizeof(void*)*4);
v___x_3253_ = 1;
v___x_3254_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3252_, v___x_3253_);
if (v___x_3254_ == 0)
{
lean_inc_ref(v_toConstantVal_3251_);
v___y_3240_ = v___y_3250_;
v___y_3241_ = v___y_3249_;
v___y_3242_ = v_toConstantVal_3251_;
v___y_3243_ = v___y_3248_;
goto v___jp_3239_;
}
else
{
lean_inc_ref(v_toConstantVal_3251_);
v___y_3240_ = v___y_3250_;
v___y_3241_ = v___y_3249_;
v___y_3242_ = v_toConstantVal_3251_;
v___y_3243_ = v___x_3219_;
goto v___jp_3239_;
}
}
v___jp_3257_:
{
lean_object* v_toCold_3259_; lean_object* v_options_3260_; uint8_t v_hasTrace_3261_; 
v_toCold_3259_ = lean_ctor_get(v___y_3224_, 0);
v_options_3260_ = lean_ctor_get(v_toCold_3259_, 2);
v_hasTrace_3261_ = lean_ctor_get_uint8(v_options_3260_, sizeof(void*)*1);
if (v_hasTrace_3261_ == 0)
{
lean_dec(v_cls_3220_);
v___y_3248_ = v___y_3258_;
v___y_3249_ = v___y_3224_;
v___y_3250_ = v___y_3225_;
goto v___jp_3247_;
}
else
{
lean_object* v_inheritedTraceOptions_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; uint8_t v___x_3265_; 
v_inheritedTraceOptions_3262_ = lean_ctor_get(v_toCold_3259_, 11);
v___x_3263_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3220_);
v___x_3264_ = l_Lean_Name_append(v___x_3263_, v_cls_3220_);
v___x_3265_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3262_, v_options_3260_, v___x_3264_);
lean_dec(v___x_3264_);
if (v___x_3265_ == 0)
{
lean_dec(v_cls_3220_);
v___y_3248_ = v___y_3258_;
v___y_3249_ = v___y_3224_;
v___y_3250_ = v___y_3225_;
goto v___jp_3247_;
}
else
{
lean_object* v_toConstantVal_3266_; lean_object* v_name_3267_; lean_object* v___x_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; 
v_toConstantVal_3266_ = lean_ctor_get(v_defn_3223_, 0);
v_name_3267_ = lean_ctor_get(v_toConstantVal_3266_, 0);
v___x_3268_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3267_);
v___x_3269_ = l_Lean_MessageData_ofName(v_name_3267_);
v___x_3270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3270_, 0, v___x_3268_);
lean_ctor_set(v___x_3270_, 1, v___x_3269_);
v___x_3271_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3270_);
lean_ctor_set(v___x_3272_, 1, v___x_3271_);
v___x_3273_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3220_, v___x_3272_, v___y_3224_, v___y_3225_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_dec_ref_known(v___x_3273_, 1);
v___y_3248_ = v___y_3258_;
v___y_3249_ = v___y_3224_;
v___y_3250_ = v___y_3225_;
goto v___jp_3247_;
}
else
{
lean_dec_ref(v_defn_3223_);
lean_dec_ref(v___f_3218_);
return v___x_3273_;
}
}
}
}
v___jp_3276_:
{
lean_object* v___x_3277_; uint8_t v_isModule_3278_; 
v___x_3277_ = l_Lean_Environment_header(v_env_3274_);
lean_dec_ref(v_env_3274_);
v_isModule_3278_ = lean_ctor_get_uint8(v___x_3277_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3277_);
if (v_isModule_3278_ == 0)
{
lean_dec_ref(v_env_3275_);
lean_dec(v_cls_3220_);
v_exportedInfo_x3f_3228_ = v___x_3221_;
v___y_3229_ = v___y_3224_;
v___y_3230_ = v___y_3225_;
goto v___jp_3227_;
}
else
{
uint8_t v_isExporting_3279_; 
v_isExporting_3279_ = lean_ctor_get_uint8(v_env_3275_, sizeof(void*)*8);
lean_dec_ref(v_env_3275_);
if (v_isExporting_3279_ == 0)
{
lean_dec(v___x_3221_);
v___y_3258_ = v_isModule_3278_;
goto v___jp_3257_;
}
else
{
if (v___x_3219_ == 0)
{
lean_dec(v_cls_3220_);
v_exportedInfo_x3f_3228_ = v___x_3221_;
v___y_3229_ = v___y_3224_;
v___y_3230_ = v___y_3225_;
goto v___jp_3227_;
}
else
{
lean_dec(v___x_3221_);
v___y_3258_ = v___x_3219_;
goto v___jp_3257_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3280_, lean_object* v___x_3281_, lean_object* v_cls_3282_, lean_object* v___x_3283_, lean_object* v_forceExpose_3284_, lean_object* v_defn_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_){
_start:
{
uint8_t v___x_53530__boxed_3289_; uint8_t v_forceExpose_boxed_3290_; lean_object* v_res_3291_; 
v___x_53530__boxed_3289_ = lean_unbox(v___x_3281_);
v_forceExpose_boxed_3290_ = lean_unbox(v_forceExpose_3284_);
v_res_3291_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3280_, v___x_53530__boxed_3289_, v_cls_3282_, v___x_3283_, v_forceExpose_boxed_3290_, v_defn_3285_, v___y_3286_, v___y_3287_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
return v_res_3291_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3292_, lean_object* v___f_3293_, lean_object* v_____r_3294_, lean_object* v_exportedInfo_x3f_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v_toConstantVal_3299_; lean_object* v_name_3300_; lean_object* v___x_3301_; uint8_t v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_toConstantVal_3299_ = lean_ctor_get(v_val_3292_, 0);
v_name_3300_ = lean_ctor_get(v_toConstantVal_3299_, 0);
lean_inc(v_name_3300_);
v___x_3301_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3301_, 0, v_val_3292_);
v___x_3302_ = 1;
v___x_3303_ = lean_box(v___x_3302_);
v___x_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3301_);
lean_ctor_set(v___x_3304_, 1, v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v_name_3300_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
lean_inc(v___y_3297_);
lean_inc_ref(v___y_3296_);
v___x_3306_ = lean_apply_5(v___f_3293_, v___x_3305_, v_exportedInfo_x3f_3295_, v___y_3296_, v___y_3297_, lean_box(0));
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3307_, lean_object* v___f_3308_, lean_object* v_____r_3309_, lean_object* v_exportedInfo_x3f_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_res_3314_; 
v_res_3314_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3307_, v___f_3308_, v_____r_3309_, v_exportedInfo_x3f_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
return v_res_3314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3315_, uint8_t v___x_3316_, lean_object* v___f_3317_, lean_object* v_____r_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_){
_start:
{
lean_object* v_toConstantVal_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_toConstantVal_3322_ = lean_ctor_get(v_val_3315_, 0);
lean_inc_ref(v_toConstantVal_3322_);
v___x_3323_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3323_, 0, v_toConstantVal_3322_);
lean_ctor_set_uint8(v___x_3323_, sizeof(void*)*1, v___x_3316_);
v___x_3324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3324_, 0, v___x_3323_);
v___x_3325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
v___x_3326_ = lean_box(0);
lean_inc(v___y_3320_);
lean_inc_ref(v___y_3319_);
v___x_3327_ = lean_apply_5(v___f_3317_, v___x_3326_, v___x_3325_, v___y_3319_, v___y_3320_, lean_box(0));
return v___x_3327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3328_, lean_object* v___x_3329_, lean_object* v___f_3330_, lean_object* v_____r_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
uint8_t v___x_53665__boxed_3335_; lean_object* v_res_3336_; 
v___x_53665__boxed_3335_ = lean_unbox(v___x_3329_);
v_res_3336_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3328_, v___x_53665__boxed_3335_, v___f_3330_, v_____r_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec_ref(v_val_3328_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3337_, lean_object* v___f_3338_, lean_object* v_____r_3339_, lean_object* v_exportedInfo_x3f_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_){
_start:
{
lean_object* v_toConstantVal_3344_; lean_object* v_name_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_toConstantVal_3344_ = lean_ctor_get(v_val_3337_, 0);
v_name_3345_ = lean_ctor_get(v_toConstantVal_3344_, 0);
lean_inc(v_name_3345_);
v___x_3346_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_val_3337_);
v___x_3347_ = 3;
v___x_3348_ = lean_box(v___x_3347_);
v___x_3349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3346_);
lean_ctor_set(v___x_3349_, 1, v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v_name_3345_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
lean_inc(v___y_3342_);
lean_inc_ref(v___y_3341_);
v___x_3351_ = lean_apply_5(v___f_3338_, v___x_3350_, v_exportedInfo_x3f_3340_, v___y_3341_, v___y_3342_, lean_box(0));
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3352_, lean_object* v___f_3353_, lean_object* v_____r_3354_, lean_object* v_exportedInfo_x3f_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_res_3359_; 
v_res_3359_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3352_, v___f_3353_, v_____r_3354_, v_exportedInfo_x3f_3355_, v___y_3356_, v___y_3357_);
lean_dec(v___y_3357_);
lean_dec_ref(v___y_3356_);
return v_res_3359_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3360_, lean_object* v___f_3361_, lean_object* v_____r_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v_toConstantVal_3366_; uint8_t v_isUnsafe_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; 
v_toConstantVal_3366_ = lean_ctor_get(v_val_3360_, 0);
v_isUnsafe_3367_ = lean_ctor_get_uint8(v_val_3360_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3366_);
v___x_3368_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3368_, 0, v_toConstantVal_3366_);
lean_ctor_set_uint8(v___x_3368_, sizeof(void*)*1, v_isUnsafe_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3369_, 0, v___x_3368_);
v___x_3370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = lean_box(0);
lean_inc(v___y_3364_);
lean_inc_ref(v___y_3363_);
v___x_3372_ = lean_apply_5(v___f_3361_, v___x_3371_, v___x_3370_, v___y_3363_, v___y_3364_, lean_box(0));
return v___x_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3373_, lean_object* v___f_3374_, lean_object* v_____r_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_){
_start:
{
lean_object* v_res_3379_; 
v_res_3379_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3373_, v___f_3374_, v_____r_3375_, v___y_3376_, v___y_3377_);
lean_dec(v___y_3377_);
lean_dec_ref(v___y_3376_);
lean_dec_ref(v_val_3373_);
return v_res_3379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3380_, uint8_t v___x_3381_, lean_object* v_cls_3382_, lean_object* v___x_3383_, lean_object* v___x_3384_, lean_object* v_____x_3385_, lean_object* v_exportedInfo_x3f_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_){
_start:
{
lean_object* v___y_3391_; lean_object* v___y_3392_; lean_object* v_a_3393_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v_a_3406_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v_snd_3491_; lean_object* v_fst_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3624_; 
v_snd_3491_ = lean_ctor_get(v_____x_3385_, 1);
v_fst_3492_ = lean_ctor_get(v_____x_3385_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_____x_3385_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3494_ = v_____x_3385_;
v_isShared_3495_ = v_isSharedCheck_3624_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_snd_3491_);
lean_inc(v_fst_3492_);
lean_dec(v_____x_3385_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3624_;
goto v_resetjp_3493_;
}
v___jp_3390_:
{
lean_object* v___x_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
v___x_3394_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3391_, v___y_3392_);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3394_);
if (v_isSharedCheck_3401_ == 0)
{
lean_object* v_unused_3402_; 
v_unused_3402_ = lean_ctor_get(v___x_3394_, 0);
lean_dec(v_unused_3402_);
v___x_3396_ = v___x_3394_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_dec(v___x_3394_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
lean_ctor_set_tag(v___x_3396_, 1);
lean_ctor_set(v___x_3396_, 0, v_a_3393_);
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3393_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
v___jp_3403_:
{
lean_object* v___x_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3414_; 
v___x_3407_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3404_, v___y_3405_);
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3407_, 0);
lean_dec(v_unused_3415_);
v___x_3409_ = v___x_3407_;
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
else
{
lean_dec(v___x_3407_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3414_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3412_; 
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 0, v_a_3406_);
v___x_3412_ = v___x_3409_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v_a_3406_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
v___jp_3416_:
{
lean_object* v___x_3428_; 
lean_inc_ref(v___y_3423_);
v___x_3428_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3426_, v___y_3423_, v___y_3424_, v___y_3427_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v___x_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref_known(v___x_3428_, 1);
lean_inc_ref(v___y_3418_);
v___x_3429_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3418_, v___y_3425_);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3476_ == 0)
{
lean_object* v_unused_3477_; 
v_unused_3477_ = lean_ctor_get(v___x_3429_, 0);
lean_dec(v_unused_3477_);
v___x_3431_ = v___x_3429_;
v_isShared_3432_ = v_isSharedCheck_3476_;
goto v_resetjp_3430_;
}
else
{
lean_dec(v___x_3429_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3476_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v_toCold_3433_; lean_object* v_options_3434_; lean_object* v___x_3435_; uint8_t v___x_3436_; 
v_toCold_3433_ = lean_ctor_get(v___y_3420_, 0);
v_options_3434_ = lean_ctor_get(v_toCold_3433_, 2);
v___x_3435_ = l_Lean_Elab_async;
v___x_3436_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3434_, v___x_3435_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v_r_3438_; 
lean_del_object(v___x_3431_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3417_);
v___x_3437_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3423_, v___y_3425_);
lean_dec_ref(v___x_3437_);
v_r_3438_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3380_, v___y_3420_, v___y_3425_);
if (lean_obj_tag(v_r_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v___x_3441_; uint8_t v_isShared_3442_; uint8_t v_isSharedCheck_3448_; 
v_a_3439_ = lean_ctor_get(v_r_3438_, 0);
v_isSharedCheck_3448_ = !lean_is_exclusive(v_r_3438_);
if (v_isSharedCheck_3448_ == 0)
{
v___x_3441_ = v_r_3438_;
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
else
{
lean_inc(v_a_3439_);
lean_dec(v_r_3438_);
v___x_3441_ = lean_box(0);
v_isShared_3442_ = v_isSharedCheck_3448_;
goto v_resetjp_3440_;
}
v_resetjp_3440_:
{
lean_object* v___x_3444_; 
lean_inc(v_a_3439_);
if (v_isShared_3442_ == 0)
{
lean_ctor_set_tag(v___x_3441_, 1);
v___x_3444_ = v___x_3441_;
goto v_reusejp_3443_;
}
else
{
lean_object* v_reuseFailAlloc_3447_; 
v_reuseFailAlloc_3447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3447_, 0, v_a_3439_);
v___x_3444_ = v_reuseFailAlloc_3447_;
goto v_reusejp_3443_;
}
v_reusejp_3443_:
{
lean_object* v___x_3445_; 
v___x_3445_ = lean_apply_2(v___y_3419_, v___x_3444_, lean_box(0));
if (lean_obj_tag(v___x_3445_) == 0)
{
lean_dec_ref_known(v___x_3445_, 1);
v___y_3404_ = v___y_3418_;
v___y_3405_ = v___y_3425_;
v_a_3406_ = v_a_3439_;
goto v___jp_3403_;
}
else
{
lean_object* v_a_3446_; 
lean_dec(v_a_3439_);
v_a_3446_ = lean_ctor_get(v___x_3445_, 0);
lean_inc(v_a_3446_);
lean_dec_ref_known(v___x_3445_, 1);
v___y_3391_ = v___y_3418_;
v___y_3392_ = v___y_3425_;
v_a_3393_ = v_a_3446_;
goto v___jp_3390_;
}
}
}
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_a_3449_ = lean_ctor_get(v_r_3438_, 0);
lean_inc(v_a_3449_);
lean_dec_ref_known(v_r_3438_, 1);
v___x_3450_ = lean_box(0);
v___x_3451_ = lean_apply_2(v___y_3419_, v___x_3450_, lean_box(0));
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_dec_ref_known(v___x_3451_, 1);
v___y_3391_ = v___y_3418_;
v___y_3392_ = v___y_3425_;
v_a_3393_ = v_a_3449_;
goto v___jp_3390_;
}
else
{
lean_object* v_a_3452_; 
lean_dec(v_a_3449_);
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___y_3391_ = v___y_3418_;
v___y_3392_ = v___y_3425_;
v_a_3393_ = v_a_3452_;
goto v___jp_3390_;
}
}
}
else
{
lean_object* v___x_3453_; lean_object* v___x_3455_; 
lean_dec_ref(v___y_3423_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v_decl_3380_);
v___x_3453_ = l_IO_CancelToken_new();
if (v_isShared_3432_ == 0)
{
lean_ctor_set_tag(v___x_3431_, 1);
lean_ctor_set(v___x_3431_, 0, v___x_3453_);
v___x_3455_ = v___x_3431_;
goto v_reusejp_3454_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v___x_3453_);
v___x_3455_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3454_;
}
v_reusejp_3454_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v___x_3456_ = lean_unsigned_to_nat(0u);
v___x_3457_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3458_ = l_Lean_Name_toString(v___x_3457_, v___x_3381_);
lean_inc_ref(v___x_3455_);
v___x_3459_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3421_, v___x_3455_, v___x_3458_, v___y_3420_, v___y_3425_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v_checked_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v_checked_3461_ = lean_ctor_get(v___y_3417_, 2);
lean_inc_ref(v_checked_3461_);
lean_dec_ref(v___y_3417_);
v___x_3462_ = lean_io_map_task(v_a_3460_, v_checked_3461_, v___x_3456_, v___y_3422_);
v___x_3463_ = lean_box(0);
v___x_3464_ = lean_box(2);
v___x_3465_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3463_);
lean_ctor_set(v___x_3465_, 1, v___x_3464_);
lean_ctor_set(v___x_3465_, 2, v___x_3455_);
lean_ctor_set(v___x_3465_, 3, v___x_3462_);
v___x_3466_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3465_, v___y_3425_);
return v___x_3466_;
}
else
{
lean_object* v_a_3467_; lean_object* v___x_3469_; uint8_t v_isShared_3470_; uint8_t v_isSharedCheck_3474_; 
lean_dec_ref(v___x_3455_);
lean_dec_ref(v___y_3417_);
v_a_3467_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3469_ = v___x_3459_;
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
else
{
lean_inc(v_a_3467_);
lean_dec(v___x_3459_);
v___x_3469_ = lean_box(0);
v_isShared_3470_ = v_isSharedCheck_3474_;
goto v_resetjp_3468_;
}
v_resetjp_3468_:
{
lean_object* v___x_3472_; 
if (v_isShared_3470_ == 0)
{
v___x_3472_ = v___x_3469_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3467_);
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
}
}
}
else
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v___y_3423_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec_ref(v___y_3417_);
lean_dec(v_decl_3380_);
v_a_3478_ = lean_ctor_get(v___x_3428_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3428_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3480_ = v___x_3428_;
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v___x_3428_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3490_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v_ref_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3488_; 
v_ref_3482_ = lean_ctor_get(v___y_3420_, 2);
v___x_3483_ = lean_io_error_to_string(v_a_3478_);
v___x_3484_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3483_);
v___x_3485_ = l_Lean_MessageData_ofFormat(v___x_3484_);
lean_inc(v_ref_3482_);
v___x_3486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3486_, 0, v_ref_3482_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set(v___x_3480_, 0, v___x_3486_);
v___x_3488_ = v___x_3480_;
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
lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v_exportedInfo_x3f_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___y_3556_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___x_3613_; lean_object* v_env_3614_; uint8_t v___x_3615_; 
v___x_3613_ = lean_st_ref_get(v___y_3388_);
v_env_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_ref(v_env_3614_);
lean_dec(v___x_3613_);
v___x_3615_ = l_Lean_Environment_containsOnBranch(v_env_3614_, v_fst_3492_);
lean_dec_ref(v_env_3614_);
if (v___x_3615_ == 0)
{
lean_del_object(v___x_3494_);
v___y_3587_ = v___y_3387_;
v___y_3588_ = v___y_3388_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3616_; lean_object* v_env_3617_; lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_exportedInfo_x3f_3386_);
lean_dec(v___x_3384_);
lean_dec_ref(v___x_3383_);
lean_dec(v_cls_3382_);
lean_dec(v_decl_3380_);
v___x_3616_ = lean_st_ref_get(v___y_3388_);
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
v___x_3621_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3620_, v___y_3387_, v___y_3388_);
return v___x_3621_;
}
}
v___jp_3501_:
{
uint8_t v___x_3509_; uint8_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3509_ = 0;
v___x_3510_ = lean_unbox(v_snd_3497_);
lean_dec(v_snd_3497_);
lean_inc_ref(v___y_3504_);
v___x_3511_ = l_Lean_Environment_addConstAsync(v___y_3504_, v_fst_3492_, v___x_3510_, v___y_3508_, v___x_3509_, v___x_3381_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v_mainEnv_3513_; lean_object* v_asyncEnv_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
lean_del_object(v___x_3499_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc_n(v_a_3512_, 3);
lean_dec_ref_known(v___x_3511_, 1);
v_mainEnv_3513_ = lean_ctor_get(v_a_3512_, 0);
lean_inc_ref(v_mainEnv_3513_);
v_asyncEnv_3514_ = lean_ctor_get(v_a_3512_, 1);
lean_inc_ref_n(v_asyncEnv_3514_, 2);
lean_inc_ref(v___y_3503_);
lean_inc(v___y_3502_);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3515_, 0, v___y_3502_);
lean_closure_set(v___f_3515_, 1, v_a_3512_);
lean_closure_set(v___f_3515_, 2, v___y_3503_);
lean_inc(v_decl_3380_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3516_, 0, v_asyncEnv_3514_);
lean_closure_set(v___f_3516_, 1, v_a_3512_);
lean_closure_set(v___f_3516_, 2, v_decl_3380_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_fst_3496_);
if (lean_obj_tag(v___y_3507_) == 0)
{
lean_inc_ref(v___x_3517_);
v___y_3417_ = v___y_3504_;
v___y_3418_ = v_mainEnv_3513_;
v___y_3419_ = v___f_3515_;
v___y_3420_ = v___y_3505_;
v___y_3421_ = v___f_3516_;
v___y_3422_ = v___x_3509_;
v___y_3423_ = v_asyncEnv_3514_;
v___y_3424_ = v___x_3517_;
v___y_3425_ = v___y_3506_;
v___y_3426_ = v_a_3512_;
v___y_3427_ = v___x_3517_;
goto v___jp_3416_;
}
else
{
v___y_3417_ = v___y_3504_;
v___y_3418_ = v_mainEnv_3513_;
v___y_3419_ = v___f_3515_;
v___y_3420_ = v___y_3505_;
v___y_3421_ = v___f_3516_;
v___y_3422_ = v___x_3509_;
v___y_3423_ = v_asyncEnv_3514_;
v___y_3424_ = v___x_3517_;
v___y_3425_ = v___y_3506_;
v___y_3426_ = v_a_3512_;
v___y_3427_ = v___y_3507_;
goto v___jp_3416_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v___y_3507_);
lean_dec_ref(v___y_3504_);
lean_dec(v_fst_3496_);
lean_dec(v_decl_3380_);
v_a_3518_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3520_ = v___x_3511_;
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
else
{
lean_inc(v_a_3518_);
lean_dec(v___x_3511_);
v___x_3520_ = lean_box(0);
v_isShared_3521_ = v_isSharedCheck_3532_;
goto v_resetjp_3519_;
}
v_resetjp_3519_:
{
lean_object* v_ref_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3527_; 
v_ref_3522_ = lean_ctor_get(v___y_3505_, 2);
v___x_3523_ = lean_io_error_to_string(v_a_3518_);
v___x_3524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
v___x_3525_ = l_Lean_MessageData_ofFormat(v___x_3524_);
lean_inc(v_ref_3522_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 1, v___x_3525_);
lean_ctor_set(v___x_3499_, 0, v_ref_3522_);
v___x_3527_ = v___x_3499_;
goto v_reusejp_3526_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_ref_3522_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3525_);
v___x_3527_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3526_;
}
v_reusejp_3526_:
{
lean_object* v___x_3529_; 
if (v_isShared_3521_ == 0)
{
lean_ctor_set(v___x_3520_, 0, v___x_3527_);
v___x_3529_ = v___x_3520_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v___x_3527_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
}
v___jp_3533_:
{
lean_object* v___x_3537_; 
v___x_3537_ = lean_st_ref_get(v___y_3536_);
if (lean_obj_tag(v_exportedInfo_x3f_3534_) == 0)
{
lean_object* v_env_3538_; lean_object* v___x_3539_; 
v_env_3538_ = lean_ctor_get(v___x_3537_, 0);
lean_inc_ref(v_env_3538_);
lean_dec(v___x_3537_);
v___x_3539_ = lean_box(0);
v___y_3502_ = v___y_3536_;
v___y_3503_ = v___y_3535_;
v___y_3504_ = v_env_3538_;
v___y_3505_ = v___y_3535_;
v___y_3506_ = v___y_3536_;
v___y_3507_ = v_exportedInfo_x3f_3534_;
v___y_3508_ = v___x_3539_;
goto v___jp_3501_;
}
else
{
lean_object* v_env_3540_; lean_object* v_val_3541_; uint8_t v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v_env_3540_ = lean_ctor_get(v___x_3537_, 0);
lean_inc_ref(v_env_3540_);
lean_dec(v___x_3537_);
v_val_3541_ = lean_ctor_get(v_exportedInfo_x3f_3534_, 0);
v___x_3542_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3541_);
v___x_3543_ = lean_box(v___x_3542_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v___x_3543_);
v___y_3502_ = v___y_3536_;
v___y_3503_ = v___y_3535_;
v___y_3504_ = v_env_3540_;
v___y_3505_ = v___y_3535_;
v___y_3506_ = v___y_3536_;
v___y_3507_ = v_exportedInfo_x3f_3534_;
v___y_3508_ = v___x_3544_;
goto v___jp_3501_;
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
lean_inc(v_fst_3496_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_fst_3496_);
v_exportedInfo_x3f_3534_ = v___x_3548_;
v___y_3535_ = v___y_3546_;
v___y_3536_ = v___y_3547_;
goto v___jp_3533_;
}
v___jp_3549_:
{
lean_object* v___x_3552_; 
lean_inc(v_fst_3496_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_fst_3496_);
v_exportedInfo_x3f_3534_ = v___x_3552_;
v___y_3535_ = v___y_3550_;
v___y_3536_ = v___y_3551_;
goto v___jp_3533_;
}
v___jp_3553_:
{
if (v___y_3556_ == 0)
{
lean_object* v_toCold_3557_; lean_object* v_options_3558_; uint8_t v_hasTrace_3559_; 
lean_dec(v_exportedInfo_x3f_3386_);
lean_dec_ref(v___x_3383_);
v_toCold_3557_ = lean_ctor_get(v___y_3555_, 0);
v_options_3558_ = lean_ctor_get(v_toCold_3557_, 2);
v_hasTrace_3559_ = lean_ctor_get_uint8(v_options_3558_, sizeof(void*)*1);
if (v_hasTrace_3559_ == 0)
{
lean_dec(v_cls_3382_);
v___y_3546_ = v___y_3555_;
v___y_3547_ = v___y_3554_;
goto v___jp_3545_;
}
else
{
lean_object* v_inheritedTraceOptions_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; uint8_t v___x_3563_; 
v_inheritedTraceOptions_3560_ = lean_ctor_get(v_toCold_3557_, 11);
v___x_3561_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3382_);
v___x_3562_ = l_Lean_Name_append(v___x_3561_, v_cls_3382_);
v___x_3563_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3560_, v_options_3558_, v___x_3562_);
lean_dec(v___x_3562_);
if (v___x_3563_ == 0)
{
lean_dec(v_cls_3382_);
v___y_3546_ = v___y_3555_;
v___y_3547_ = v___y_3554_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3565_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3382_, v___x_3564_, v___y_3555_, v___y_3554_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_dec_ref_known(v___x_3565_, 1);
v___y_3546_ = v___y_3555_;
v___y_3547_ = v___y_3554_;
goto v___jp_3545_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v_decl_3380_);
return v___x_3565_;
}
}
}
}
else
{
lean_object* v___x_3566_; lean_object* v_env_3567_; lean_object* v_nextMacroScope_3568_; lean_object* v_ngen_3569_; lean_object* v_auxDeclNGen_3570_; lean_object* v_traceState_3571_; lean_object* v_messages_3572_; lean_object* v_infoState_3573_; lean_object* v_snapshotTasks_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_cls_3382_);
v___x_3566_ = lean_st_ref_take(v___y_3554_);
v_env_3567_ = lean_ctor_get(v___x_3566_, 0);
v_nextMacroScope_3568_ = lean_ctor_get(v___x_3566_, 1);
v_ngen_3569_ = lean_ctor_get(v___x_3566_, 2);
v_auxDeclNGen_3570_ = lean_ctor_get(v___x_3566_, 3);
v_traceState_3571_ = lean_ctor_get(v___x_3566_, 4);
v_messages_3572_ = lean_ctor_get(v___x_3566_, 6);
v_infoState_3573_ = lean_ctor_get(v___x_3566_, 7);
v_snapshotTasks_3574_ = lean_ctor_get(v___x_3566_, 8);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3584_ == 0)
{
lean_object* v_unused_3585_; 
v_unused_3585_ = lean_ctor_get(v___x_3566_, 5);
lean_dec(v_unused_3585_);
v___x_3576_ = v___x_3566_;
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snapshotTasks_3574_);
lean_inc(v_infoState_3573_);
lean_inc(v_messages_3572_);
lean_inc(v_traceState_3571_);
lean_inc(v_auxDeclNGen_3570_);
lean_inc(v_ngen_3569_);
lean_inc(v_nextMacroScope_3568_);
lean_inc(v_env_3567_);
lean_dec(v___x_3566_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3584_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
v___x_3578_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3497_);
lean_inc(v_fst_3492_);
v___x_3579_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3578_, v_env_3567_, v_fst_3492_, v_snd_3497_);
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 5, v___x_3383_);
lean_ctor_set(v___x_3576_, 0, v___x_3579_);
v___x_3581_ = v___x_3576_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3583_, 1, v_nextMacroScope_3568_);
lean_ctor_set(v_reuseFailAlloc_3583_, 2, v_ngen_3569_);
lean_ctor_set(v_reuseFailAlloc_3583_, 3, v_auxDeclNGen_3570_);
lean_ctor_set(v_reuseFailAlloc_3583_, 4, v_traceState_3571_);
lean_ctor_set(v_reuseFailAlloc_3583_, 5, v___x_3383_);
lean_ctor_set(v_reuseFailAlloc_3583_, 6, v_messages_3572_);
lean_ctor_set(v_reuseFailAlloc_3583_, 7, v_infoState_3573_);
lean_ctor_set(v_reuseFailAlloc_3583_, 8, v_snapshotTasks_3574_);
v___x_3581_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; 
v___x_3582_ = lean_st_ref_put(v___y_3554_, v___x_3581_);
v_exportedInfo_x3f_3534_ = v_exportedInfo_x3f_3386_;
v___y_3535_ = v___y_3555_;
v___y_3536_ = v___y_3554_;
goto v___jp_3533_;
}
}
}
}
v___jp_3586_:
{
lean_object* v___x_3589_; uint8_t v___x_3590_; 
lean_inc(v_decl_3380_);
v___x_3589_ = l_Lean_Declaration_getTopLevelNames(v_decl_3380_);
v___x_3590_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3589_);
lean_dec(v___x_3589_);
if (v___x_3590_ == 0)
{
lean_dec(v___x_3384_);
if (lean_obj_tag(v_exportedInfo_x3f_3386_) == 0)
{
v___y_3554_ = v___y_3588_;
v___y_3555_ = v___y_3587_;
v___y_3556_ = v___x_3590_;
goto v___jp_3553_;
}
else
{
v___y_3554_ = v___y_3588_;
v___y_3555_ = v___y_3587_;
v___y_3556_ = v___x_3381_;
goto v___jp_3553_;
}
}
else
{
lean_object* v___x_3591_; lean_object* v___x_3592_; lean_object* v_a_3593_; uint8_t v___x_3594_; 
lean_dec(v_exportedInfo_x3f_3386_);
lean_dec_ref(v___x_3383_);
v___x_3591_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3592_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3591_, v___y_3587_);
v_a_3593_ = lean_ctor_get(v___x_3592_, 0);
lean_inc(v_a_3593_);
lean_dec_ref(v___x_3592_);
v___x_3594_ = lean_unbox(v_a_3593_);
lean_dec(v_a_3593_);
if (v___x_3594_ == 0)
{
lean_object* v_toCold_3595_; lean_object* v_options_3596_; uint8_t v_hasTrace_3597_; 
v_toCold_3595_ = lean_ctor_get(v___y_3587_, 0);
v_options_3596_ = lean_ctor_get(v_toCold_3595_, 2);
v_hasTrace_3597_ = lean_ctor_get_uint8(v_options_3596_, sizeof(void*)*1);
if (v_hasTrace_3597_ == 0)
{
lean_dec(v_cls_3382_);
v_exportedInfo_x3f_3534_ = v___x_3384_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
goto v___jp_3533_;
}
else
{
lean_object* v_inheritedTraceOptions_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v_inheritedTraceOptions_3598_ = lean_ctor_get(v_toCold_3595_, 11);
v___x_3599_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3382_);
v___x_3600_ = l_Lean_Name_append(v___x_3599_, v_cls_3382_);
v___x_3601_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3598_, v_options_3596_, v___x_3600_);
lean_dec(v___x_3600_);
if (v___x_3601_ == 0)
{
lean_dec(v_cls_3382_);
v_exportedInfo_x3f_3534_ = v___x_3384_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3602_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3603_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3382_, v___x_3602_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3603_) == 0)
{
lean_dec_ref_known(v___x_3603_, 1);
v_exportedInfo_x3f_3534_ = v___x_3384_;
v___y_3535_ = v___y_3587_;
v___y_3536_ = v___y_3588_;
goto v___jp_3533_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v___x_3384_);
lean_dec(v_decl_3380_);
return v___x_3603_;
}
}
}
}
else
{
lean_object* v_toCold_3604_; lean_object* v_options_3605_; uint8_t v_hasTrace_3606_; 
lean_dec(v___x_3384_);
v_toCold_3604_ = lean_ctor_get(v___y_3587_, 0);
v_options_3605_ = lean_ctor_get(v_toCold_3604_, 2);
v_hasTrace_3606_ = lean_ctor_get_uint8(v_options_3605_, sizeof(void*)*1);
if (v_hasTrace_3606_ == 0)
{
lean_dec(v_cls_3382_);
v___y_3550_ = v___y_3587_;
v___y_3551_ = v___y_3588_;
goto v___jp_3549_;
}
else
{
lean_object* v_inheritedTraceOptions_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; uint8_t v___x_3610_; 
v_inheritedTraceOptions_3607_ = lean_ctor_get(v_toCold_3604_, 11);
v___x_3608_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3382_);
v___x_3609_ = l_Lean_Name_append(v___x_3608_, v_cls_3382_);
v___x_3610_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3607_, v_options_3605_, v___x_3609_);
lean_dec(v___x_3609_);
if (v___x_3610_ == 0)
{
lean_dec(v_cls_3382_);
v___y_3550_ = v___y_3587_;
v___y_3551_ = v___y_3588_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3611_; lean_object* v___x_3612_; 
v___x_3611_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3612_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3382_, v___x_3611_, v___y_3587_, v___y_3588_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_dec_ref_known(v___x_3612_, 1);
v___y_3550_ = v___y_3587_;
v___y_3551_ = v___y_3588_;
goto v___jp_3549_;
}
else
{
lean_del_object(v___x_3499_);
lean_dec(v_snd_3497_);
lean_dec(v_fst_3496_);
lean_dec(v_fst_3492_);
lean_dec(v_decl_3380_);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3625_, lean_object* v___x_3626_, lean_object* v_cls_3627_, lean_object* v___x_3628_, lean_object* v___x_3629_, lean_object* v_____x_3630_, lean_object* v_exportedInfo_x3f_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
uint8_t v___x_53796__boxed_3635_; lean_object* v_res_3636_; 
v___x_53796__boxed_3635_ = lean_unbox(v___x_3626_);
v_res_3636_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3625_, v___x_53796__boxed_3635_, v_cls_3627_, v___x_3628_, v___x_3629_, v_____x_3630_, v_exportedInfo_x3f_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
return v_res_3636_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3637_, uint8_t v_forceExpose_3638_, uint8_t v___x_3639_, lean_object* v___x_3640_, lean_object* v_cls_3641_, lean_object* v_defn_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v_exportedInfo_x3f_3647_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3659_; lean_object* v___y_3660_; lean_object* v___y_3661_; uint8_t v___y_3662_; lean_object* v___x_3666_; lean_object* v___x_3667_; 
v___x_3666_ = lean_st_ref_get(v___y_3644_);
v___x_3667_ = lean_st_ref_get(v___y_3644_);
if (v_forceExpose_3638_ == 0)
{
if (v___x_3639_ == 0)
{
lean_dec(v___x_3667_);
lean_dec(v___x_3666_);
lean_dec(v_cls_3641_);
v_exportedInfo_x3f_3647_ = v___x_3640_;
v___y_3648_ = v___y_3643_;
v___y_3649_ = v___y_3644_;
goto v___jp_3646_;
}
else
{
lean_object* v_env_3668_; lean_object* v_env_3669_; lean_object* v___x_3670_; uint8_t v_isModule_3671_; 
v_env_3668_ = lean_ctor_get(v___x_3666_, 0);
lean_inc_ref(v_env_3668_);
lean_dec(v___x_3666_);
v_env_3669_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3667_);
v___x_3670_ = l_Lean_Environment_header(v_env_3668_);
lean_dec_ref(v_env_3668_);
v_isModule_3671_ = lean_ctor_get_uint8(v___x_3670_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3670_);
if (v_isModule_3671_ == 0)
{
lean_dec_ref(v_env_3669_);
lean_dec(v_cls_3641_);
v_exportedInfo_x3f_3647_ = v___x_3640_;
v___y_3648_ = v___y_3643_;
v___y_3649_ = v___y_3644_;
goto v___jp_3646_;
}
else
{
uint8_t v_isExporting_3672_; lean_object* v___y_3674_; lean_object* v___y_3675_; 
v_isExporting_3672_ = lean_ctor_get_uint8(v_env_3669_, sizeof(void*)*8);
lean_dec_ref(v_env_3669_);
if (v_isExporting_3672_ == 0)
{
lean_object* v_toCold_3680_; lean_object* v_options_3681_; uint8_t v_hasTrace_3682_; 
lean_dec(v___x_3640_);
v_toCold_3680_ = lean_ctor_get(v___y_3643_, 0);
v_options_3681_ = lean_ctor_get(v_toCold_3680_, 2);
v_hasTrace_3682_ = lean_ctor_get_uint8(v_options_3681_, sizeof(void*)*1);
if (v_hasTrace_3682_ == 0)
{
lean_dec(v_cls_3641_);
v___y_3674_ = v___y_3643_;
v___y_3675_ = v___y_3644_;
goto v___jp_3673_;
}
else
{
lean_object* v_inheritedTraceOptions_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; uint8_t v___x_3686_; 
v_inheritedTraceOptions_3683_ = lean_ctor_get(v_toCold_3680_, 11);
v___x_3684_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3641_);
v___x_3685_ = l_Lean_Name_append(v___x_3684_, v_cls_3641_);
v___x_3686_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3683_, v_options_3681_, v___x_3685_);
lean_dec(v___x_3685_);
if (v___x_3686_ == 0)
{
lean_dec(v_cls_3641_);
v___y_3674_ = v___y_3643_;
v___y_3675_ = v___y_3644_;
goto v___jp_3673_;
}
else
{
lean_object* v_toConstantVal_3687_; lean_object* v_name_3688_; lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_toConstantVal_3687_ = lean_ctor_get(v_defn_3642_, 0);
v_name_3688_ = lean_ctor_get(v_toConstantVal_3687_, 0);
v___x_3689_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3688_);
v___x_3690_ = l_Lean_MessageData_ofName(v_name_3688_);
v___x_3691_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3689_);
lean_ctor_set(v___x_3691_, 1, v___x_3690_);
v___x_3692_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3693_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3693_, 0, v___x_3691_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
v___x_3694_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3641_, v___x_3693_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3694_) == 0)
{
lean_dec_ref_known(v___x_3694_, 1);
v___y_3674_ = v___y_3643_;
v___y_3675_ = v___y_3644_;
goto v___jp_3673_;
}
else
{
lean_dec_ref(v_defn_3642_);
lean_dec_ref(v___f_3637_);
return v___x_3694_;
}
}
}
}
else
{
lean_dec(v_cls_3641_);
v_exportedInfo_x3f_3647_ = v___x_3640_;
v___y_3648_ = v___y_3643_;
v___y_3649_ = v___y_3644_;
goto v___jp_3646_;
}
v___jp_3673_:
{
lean_object* v_toConstantVal_3676_; uint8_t v_safety_3677_; uint8_t v___x_3678_; uint8_t v___x_3679_; 
v_toConstantVal_3676_ = lean_ctor_get(v_defn_3642_, 0);
v_safety_3677_ = lean_ctor_get_uint8(v_defn_3642_, sizeof(void*)*4);
v___x_3678_ = 1;
v___x_3679_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3677_, v___x_3678_);
if (v___x_3679_ == 0)
{
lean_inc_ref(v_toConstantVal_3676_);
v___y_3659_ = v___y_3675_;
v___y_3660_ = v___y_3674_;
v___y_3661_ = v_toConstantVal_3676_;
v___y_3662_ = v_isModule_3671_;
goto v___jp_3658_;
}
else
{
lean_inc_ref(v_toConstantVal_3676_);
v___y_3659_ = v___y_3675_;
v___y_3660_ = v___y_3674_;
v___y_3661_ = v_toConstantVal_3676_;
v___y_3662_ = v_isExporting_3672_;
goto v___jp_3658_;
}
}
}
}
}
else
{
lean_dec(v___x_3667_);
lean_dec(v___x_3666_);
lean_dec(v_cls_3641_);
v_exportedInfo_x3f_3647_ = v___x_3640_;
v___y_3648_ = v___y_3643_;
v___y_3649_ = v___y_3644_;
goto v___jp_3646_;
}
v___jp_3646_:
{
lean_object* v_toConstantVal_3650_; lean_object* v_name_3651_; lean_object* v___x_3652_; uint8_t v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; 
v_toConstantVal_3650_ = lean_ctor_get(v_defn_3642_, 0);
v_name_3651_ = lean_ctor_get(v_toConstantVal_3650_, 0);
lean_inc(v_name_3651_);
v___x_3652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3652_, 0, v_defn_3642_);
v___x_3653_ = 0;
v___x_3654_ = lean_box(v___x_3653_);
v___x_3655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3652_);
lean_ctor_set(v___x_3655_, 1, v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v_name_3651_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
lean_inc(v___y_3649_);
lean_inc_ref(v___y_3648_);
v___x_3657_ = lean_apply_5(v___f_3637_, v___x_3656_, v_exportedInfo_x3f_3647_, v___y_3648_, v___y_3649_, lean_box(0));
return v___x_3657_;
}
v___jp_3658_:
{
lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3663_, 0, v___y_3661_);
lean_ctor_set_uint8(v___x_3663_, sizeof(void*)*1, v___y_3662_);
v___x_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3663_);
v___x_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v_exportedInfo_x3f_3647_ = v___x_3665_;
v___y_3648_ = v___y_3660_;
v___y_3649_ = v___y_3659_;
goto v___jp_3646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3695_, lean_object* v_forceExpose_3696_, lean_object* v___x_3697_, lean_object* v___x_3698_, lean_object* v_cls_3699_, lean_object* v_defn_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
uint8_t v_forceExpose_boxed_3704_; uint8_t v___x_54271__boxed_3705_; lean_object* v_res_3706_; 
v_forceExpose_boxed_3704_ = lean_unbox(v_forceExpose_3696_);
v___x_54271__boxed_3705_ = lean_unbox(v___x_3697_);
v_res_3706_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3695_, v_forceExpose_boxed_3704_, v___x_54271__boxed_3705_, v___x_3698_, v_cls_3699_, v_defn_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3707_, uint8_t v_forceExpose_3708_, lean_object* v___f_3709_, lean_object* v_____r_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_){
_start:
{
lean_object* v_toConstantVal_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; 
v_toConstantVal_3714_ = lean_ctor_get(v_val_3707_, 0);
lean_inc_ref(v_toConstantVal_3714_);
v___x_3715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3715_, 0, v_toConstantVal_3714_);
lean_ctor_set_uint8(v___x_3715_, sizeof(void*)*1, v_forceExpose_3708_);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
v___x_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
v___x_3718_ = lean_box(0);
lean_inc(v___y_3712_);
lean_inc_ref(v___y_3711_);
v___x_3719_ = lean_apply_5(v___f_3709_, v___x_3718_, v___x_3717_, v___y_3711_, v___y_3712_, lean_box(0));
return v___x_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3720_, lean_object* v_forceExpose_3721_, lean_object* v___f_3722_, lean_object* v_____r_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_){
_start:
{
uint8_t v_forceExpose_boxed_3727_; lean_object* v_res_3728_; 
v_forceExpose_boxed_3727_ = lean_unbox(v_forceExpose_3721_);
v_res_3728_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3720_, v_forceExpose_boxed_3727_, v___f_3722_, v_____r_3723_, v___y_3724_, v___y_3725_);
lean_dec(v___y_3725_);
lean_dec_ref(v___y_3724_);
lean_dec_ref(v_val_3720_);
return v_res_3728_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3729_, lean_object* v_x_3730_){
_start:
{
if (lean_obj_tag(v_x_3730_) == 0)
{
return v_x_3729_;
}
else
{
lean_object* v_head_3731_; lean_object* v_tail_3732_; lean_object* v___x_3733_; 
v_head_3731_ = lean_ctor_get(v_x_3730_, 0);
lean_inc(v_head_3731_);
v_tail_3732_ = lean_ctor_get(v_x_3730_, 1);
lean_inc(v_tail_3732_);
lean_dec_ref_known(v_x_3730_, 2);
v___x_3733_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3729_, v_head_3731_);
v_x_3729_ = v___x_3733_;
v_x_3730_ = v_tail_3732_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; 
v_cls_3735_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3736_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3737_ = l_Lean_Name_append(v___x_3736_, v_cls_3735_);
return v___x_3737_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3739_; lean_object* v___x_3740_; 
v___x_3739_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3740_ = l_Lean_stringToMessageData(v___x_3739_);
return v___x_3740_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3743_ = l_Lean_stringToMessageData(v___x_3742_);
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3744_, uint8_t v_forceExpose_3745_, lean_object* v_a_3746_, lean_object* v_a_3747_){
_start:
{
lean_object* v___y_3750_; lean_object* v___y_3751_; lean_object* v_a_3752_; lean_object* v___y_3763_; lean_object* v___y_3764_; lean_object* v_a_3765_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v_a_3778_; lean_object* v___y_3789_; lean_object* v___y_3790_; lean_object* v_a_3791_; lean_object* v_toCold_3801_; lean_object* v_options_3802_; lean_object* v_inheritedTraceOptions_3803_; uint8_t v_hasTrace_3804_; lean_object* v___y_3806_; lean_object* v___y_3807_; uint8_t v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3881_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; uint8_t v___y_3885_; lean_object* v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; uint8_t v___y_3913_; lean_object* v___y_3914_; lean_object* v___y_3915_; lean_object* v_exportedInfo_x3f_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; uint8_t v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; uint8_t v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v_cls_3941_; 
v_toCold_3801_ = lean_ctor_get(v_a_3746_, 0);
v_options_3802_ = lean_ctor_get(v_toCold_3801_, 2);
v_inheritedTraceOptions_3803_ = lean_ctor_get(v_toCold_3801_, 11);
v_hasTrace_3804_ = lean_ctor_get_uint8(v_options_3802_, sizeof(void*)*1);
v_cls_3941_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3804_ == 0)
{
lean_object* v___x_3942_; lean_object* v_env_3943_; lean_object* v_nextMacroScope_3944_; lean_object* v_ngen_3945_; lean_object* v_auxDeclNGen_3946_; lean_object* v_traceState_3947_; lean_object* v_messages_3948_; lean_object* v_infoState_3949_; lean_object* v_snapshotTasks_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4152_; 
v___x_3942_ = lean_st_ref_take(v_a_3747_);
v_env_3943_ = lean_ctor_get(v___x_3942_, 0);
v_nextMacroScope_3944_ = lean_ctor_get(v___x_3942_, 1);
v_ngen_3945_ = lean_ctor_get(v___x_3942_, 2);
v_auxDeclNGen_3946_ = lean_ctor_get(v___x_3942_, 3);
v_traceState_3947_ = lean_ctor_get(v___x_3942_, 4);
v_messages_3948_ = lean_ctor_get(v___x_3942_, 6);
v_infoState_3949_ = lean_ctor_get(v___x_3942_, 7);
v_snapshotTasks_3950_ = lean_ctor_get(v___x_3942_, 8);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_4152_ == 0)
{
lean_object* v_unused_4153_; 
v_unused_4153_ = lean_ctor_get(v___x_3942_, 5);
lean_dec(v_unused_4153_);
v___x_3952_ = v___x_3942_;
v_isShared_3953_ = v_isSharedCheck_4152_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_snapshotTasks_3950_);
lean_inc(v_infoState_3949_);
lean_inc(v_messages_3948_);
lean_inc(v_traceState_3947_);
lean_inc(v_auxDeclNGen_3946_);
lean_inc(v_ngen_3945_);
lean_inc(v_nextMacroScope_3944_);
lean_inc(v_env_3943_);
lean_dec(v___x_3942_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4152_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; uint8_t v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___x_3986_; 
lean_inc(v_decl_3744_);
v___x_3954_ = l_Lean_Declaration_getNames(v_decl_3744_);
v___x_3955_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3943_, v___x_3954_);
v___x_3956_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 5, v___x_3956_);
lean_ctor_set(v___x_3952_, 0, v___x_3955_);
v___x_3986_ = v___x_3952_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v___x_3955_);
lean_ctor_set(v_reuseFailAlloc_4151_, 1, v_nextMacroScope_3944_);
lean_ctor_set(v_reuseFailAlloc_4151_, 2, v_ngen_3945_);
lean_ctor_set(v_reuseFailAlloc_4151_, 3, v_auxDeclNGen_3946_);
lean_ctor_set(v_reuseFailAlloc_4151_, 4, v_traceState_3947_);
lean_ctor_set(v_reuseFailAlloc_4151_, 5, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_4151_, 6, v_messages_3948_);
lean_ctor_set(v_reuseFailAlloc_4151_, 7, v_infoState_3949_);
lean_ctor_set(v_reuseFailAlloc_4151_, 8, v_snapshotTasks_3950_);
v___x_3986_ = v_reuseFailAlloc_4151_;
goto v_reusejp_3985_;
}
v___jp_3957_:
{
lean_object* v___x_3964_; lean_object* v_env_3965_; lean_object* v_nextMacroScope_3966_; lean_object* v_ngen_3967_; lean_object* v_auxDeclNGen_3968_; lean_object* v_traceState_3969_; lean_object* v_messages_3970_; lean_object* v_infoState_3971_; lean_object* v_snapshotTasks_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3983_; 
v___x_3964_ = lean_st_ref_take(v___y_3961_);
v_env_3965_ = lean_ctor_get(v___x_3964_, 0);
v_nextMacroScope_3966_ = lean_ctor_get(v___x_3964_, 1);
v_ngen_3967_ = lean_ctor_get(v___x_3964_, 2);
v_auxDeclNGen_3968_ = lean_ctor_get(v___x_3964_, 3);
v_traceState_3969_ = lean_ctor_get(v___x_3964_, 4);
v_messages_3970_ = lean_ctor_get(v___x_3964_, 6);
v_infoState_3971_ = lean_ctor_get(v___x_3964_, 7);
v_snapshotTasks_3972_ = lean_ctor_get(v___x_3964_, 8);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3964_);
if (v_isSharedCheck_3983_ == 0)
{
lean_object* v_unused_3984_; 
v_unused_3984_ = lean_ctor_get(v___x_3964_, 5);
lean_dec(v_unused_3984_);
v___x_3974_ = v___x_3964_;
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_snapshotTasks_3972_);
lean_inc(v_infoState_3971_);
lean_inc(v_messages_3970_);
lean_inc(v_traceState_3969_);
lean_inc(v_auxDeclNGen_3968_);
lean_inc(v_ngen_3967_);
lean_inc(v_nextMacroScope_3966_);
lean_inc(v_env_3965_);
lean_dec(v___x_3964_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3983_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3976_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3977_ = lean_box(v___y_3958_);
lean_inc(v___y_3963_);
v___x_3978_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3976_, v_env_3965_, v___y_3963_, v___x_3977_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 5, v___x_3956_);
lean_ctor_set(v___x_3974_, 0, v___x_3978_);
v___x_3980_ = v___x_3974_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_nextMacroScope_3966_);
lean_ctor_set(v_reuseFailAlloc_3982_, 2, v_ngen_3967_);
lean_ctor_set(v_reuseFailAlloc_3982_, 3, v_auxDeclNGen_3968_);
lean_ctor_set(v_reuseFailAlloc_3982_, 4, v_traceState_3969_);
lean_ctor_set(v_reuseFailAlloc_3982_, 5, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3982_, 6, v_messages_3970_);
lean_ctor_set(v_reuseFailAlloc_3982_, 7, v_infoState_3971_);
lean_ctor_set(v_reuseFailAlloc_3982_, 8, v_snapshotTasks_3972_);
v___x_3980_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v___x_3981_; 
v___x_3981_ = lean_st_ref_put(v___y_3961_, v___x_3980_);
v___y_3913_ = v___y_3958_;
v___y_3914_ = v___y_3960_;
v___y_3915_ = v___y_3963_;
v_exportedInfo_x3f_3916_ = v___y_3962_;
v___y_3917_ = v___y_3959_;
v___y_3918_ = v___y_3961_;
goto v___jp_3912_;
}
}
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; lean_object* v___x_3988_; uint8_t v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v_fst_4027_; lean_object* v_fst_4028_; uint8_t v_snd_4029_; lean_object* v_exportedInfo_x3f_4030_; lean_object* v___y_4031_; lean_object* v___y_4032_; lean_object* v___y_4042_; lean_object* v_exportedInfo_x3f_4043_; lean_object* v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4051_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; uint8_t v___y_4055_; uint8_t v___y_4060_; lean_object* v___y_4061_; lean_object* v_toConstantVal_4062_; uint8_t v_safety_4063_; lean_object* v___y_4064_; lean_object* v___y_4065_; uint8_t v___y_4069_; lean_object* v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v_defn_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; 
v___x_3987_ = lean_st_ref_put(v_a_3747_, v___x_3986_);
v___x_3988_ = lean_box(0);
switch(lean_obj_tag(v_decl_3744_))
{
case 2:
{
lean_object* v_val_4101_; lean_object* v_exportedInfo_x3f_4103_; lean_object* v___y_4104_; lean_object* v___y_4105_; lean_object* v___x_4110_; 
v_val_4101_ = lean_ctor_get(v_decl_3744_, 0);
v___x_4110_ = lean_st_ref_get(v_a_3747_);
if (v_forceExpose_3745_ == 0)
{
lean_object* v_env_4111_; lean_object* v___x_4112_; uint8_t v_isModule_4113_; 
v_env_4111_ = lean_ctor_get(v___x_4110_, 0);
lean_inc_ref(v_env_4111_);
lean_dec(v___x_4110_);
v___x_4112_ = l_Lean_Environment_header(v_env_4111_);
lean_dec_ref(v_env_4111_);
v_isModule_4113_ = lean_ctor_get_uint8(v___x_4112_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4112_);
if (v_isModule_4113_ == 0)
{
v_exportedInfo_x3f_4103_ = v___x_3988_;
v___y_4104_ = v_a_3746_;
v___y_4105_ = v_a_3747_;
goto v___jp_4102_;
}
else
{
lean_object* v_toConstantVal_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; 
v_toConstantVal_4114_ = lean_ctor_get(v_val_4101_, 0);
lean_inc_ref(v_toConstantVal_4114_);
v___x_4115_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4115_, 0, v_toConstantVal_4114_);
lean_ctor_set_uint8(v___x_4115_, sizeof(void*)*1, v_hasTrace_3804_);
v___x_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
v___x_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
v_exportedInfo_x3f_4103_ = v___x_4117_;
v___y_4104_ = v_a_3746_;
v___y_4105_ = v_a_3747_;
goto v___jp_4102_;
}
}
else
{
lean_dec(v___x_4110_);
v_exportedInfo_x3f_4103_ = v___x_3988_;
v___y_4104_ = v_a_3746_;
v___y_4105_ = v_a_3747_;
goto v___jp_4102_;
}
v___jp_4102_:
{
lean_object* v_toConstantVal_4106_; lean_object* v_name_4107_; lean_object* v___x_4108_; uint8_t v___x_4109_; 
v_toConstantVal_4106_ = lean_ctor_get(v_val_4101_, 0);
v_name_4107_ = lean_ctor_get(v_toConstantVal_4106_, 0);
lean_inc_ref(v_val_4101_);
v___x_4108_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4108_, 0, v_val_4101_);
v___x_4109_ = 1;
lean_inc(v_name_4107_);
v_fst_4027_ = v_name_4107_;
v_fst_4028_ = v___x_4108_;
v_snd_4029_ = v___x_4109_;
v_exportedInfo_x3f_4030_ = v_exportedInfo_x3f_4103_;
v___y_4031_ = v___y_4104_;
v___y_4032_ = v___y_4105_;
goto v___jp_4026_;
}
}
case 1:
{
lean_object* v_val_4118_; 
v_val_4118_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref(v_val_4118_);
v_defn_4076_ = v_val_4118_;
v___y_4077_ = v_a_3746_;
v___y_4078_ = v_a_3747_;
goto v___jp_4075_;
}
case 5:
{
lean_object* v_defns_4119_; 
v_defns_4119_ = lean_ctor_get(v_decl_3744_, 0);
if (lean_obj_tag(v_defns_4119_) == 1)
{
lean_object* v_tail_4120_; 
v_tail_4120_ = lean_ctor_get(v_defns_4119_, 1);
if (lean_obj_tag(v_tail_4120_) == 0)
{
lean_object* v_head_4121_; 
v_head_4121_ = lean_ctor_get(v_defns_4119_, 0);
lean_inc(v_head_4121_);
v_defn_4076_ = v_head_4121_;
v___y_4077_ = v_a_3746_;
v___y_4078_ = v_a_3747_;
goto v___jp_4075_;
}
else
{
lean_object* v___x_4122_; 
v___x_4122_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v_a_3746_, v_a_3747_);
return v___x_4122_;
}
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v_a_3746_, v_a_3747_);
return v___x_4123_;
}
}
case 3:
{
lean_object* v_val_4124_; lean_object* v_exportedInfo_x3f_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___x_4133_; lean_object* v___x_4134_; 
v_val_4124_ = lean_ctor_get(v_decl_3744_, 0);
v___x_4133_ = lean_st_ref_get(v_a_3747_);
v___x_4134_ = lean_st_ref_get(v_a_3747_);
if (v_forceExpose_3745_ == 0)
{
lean_object* v_env_4135_; lean_object* v_env_4136_; lean_object* v___x_4137_; uint8_t v_isModule_4138_; 
v_env_4135_ = lean_ctor_get(v___x_4133_, 0);
lean_inc_ref(v_env_4135_);
lean_dec(v___x_4133_);
v_env_4136_ = lean_ctor_get(v___x_4134_, 0);
lean_inc_ref(v_env_4136_);
lean_dec(v___x_4134_);
v___x_4137_ = l_Lean_Environment_header(v_env_4135_);
lean_dec_ref(v_env_4135_);
v_isModule_4138_ = lean_ctor_get_uint8(v___x_4137_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4137_);
if (v_isModule_4138_ == 0)
{
lean_dec_ref(v_env_4136_);
v_exportedInfo_x3f_4126_ = v___x_3988_;
v___y_4127_ = v_a_3746_;
v___y_4128_ = v_a_3747_;
goto v___jp_4125_;
}
else
{
uint8_t v_isExporting_4139_; 
v_isExporting_4139_ = lean_ctor_get_uint8(v_env_4136_, sizeof(void*)*8);
lean_dec_ref(v_env_4136_);
if (v_isExporting_4139_ == 0)
{
lean_object* v_toConstantVal_4140_; uint8_t v_isUnsafe_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v_toConstantVal_4140_ = lean_ctor_get(v_val_4124_, 0);
v_isUnsafe_4141_ = lean_ctor_get_uint8(v_val_4124_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4140_);
v___x_4142_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4142_, 0, v_toConstantVal_4140_);
lean_ctor_set_uint8(v___x_4142_, sizeof(void*)*1, v_isUnsafe_4141_);
v___x_4143_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4142_);
v___x_4144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v_exportedInfo_x3f_4126_ = v___x_4144_;
v___y_4127_ = v_a_3746_;
v___y_4128_ = v_a_3747_;
goto v___jp_4125_;
}
else
{
v_exportedInfo_x3f_4126_ = v___x_3988_;
v___y_4127_ = v_a_3746_;
v___y_4128_ = v_a_3747_;
goto v___jp_4125_;
}
}
}
else
{
lean_dec(v___x_4134_);
lean_dec(v___x_4133_);
v_exportedInfo_x3f_4126_ = v___x_3988_;
v___y_4127_ = v_a_3746_;
v___y_4128_ = v_a_3747_;
goto v___jp_4125_;
}
v___jp_4125_:
{
lean_object* v_toConstantVal_4129_; lean_object* v_name_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; 
v_toConstantVal_4129_ = lean_ctor_get(v_val_4124_, 0);
v_name_4130_ = lean_ctor_get(v_toConstantVal_4129_, 0);
lean_inc_ref(v_val_4124_);
v___x_4131_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4131_, 0, v_val_4124_);
v___x_4132_ = 3;
lean_inc(v_name_4130_);
v_fst_4027_ = v_name_4130_;
v_fst_4028_ = v___x_4131_;
v_snd_4029_ = v___x_4132_;
v_exportedInfo_x3f_4030_ = v_exportedInfo_x3f_4126_;
v___y_4031_ = v___y_4127_;
v___y_4032_ = v___y_4128_;
goto v___jp_4026_;
}
}
case 0:
{
lean_object* v_val_4145_; lean_object* v_toConstantVal_4146_; lean_object* v_name_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; 
v_val_4145_ = lean_ctor_get(v_decl_3744_, 0);
v_toConstantVal_4146_ = lean_ctor_get(v_val_4145_, 0);
v_name_4147_ = lean_ctor_get(v_toConstantVal_4146_, 0);
lean_inc_ref(v_val_4145_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v_val_4145_);
v___x_4149_ = 2;
lean_inc(v_name_4147_);
v_fst_4027_ = v_name_4147_;
v_fst_4028_ = v___x_4148_;
v_snd_4029_ = v___x_4149_;
v_exportedInfo_x3f_4030_ = v___x_3988_;
v___y_4031_ = v_a_3746_;
v___y_4032_ = v_a_3747_;
goto v___jp_4026_;
}
default: 
{
lean_object* v___x_4150_; 
v___x_4150_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v_a_3746_, v_a_3747_);
return v___x_4150_;
}
}
v___jp_3989_:
{
lean_object* v___x_3996_; uint8_t v___x_3997_; 
lean_inc(v_decl_3744_);
v___x_3996_ = l_Lean_Declaration_getTopLevelNames(v_decl_3744_);
v___x_3997_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3996_);
lean_dec(v___x_3996_);
if (v___x_3997_ == 0)
{
if (lean_obj_tag(v___y_3992_) == 0)
{
if (v___x_3997_ == 0)
{
lean_object* v_toCold_3998_; lean_object* v_options_3999_; uint8_t v_hasTrace_4000_; 
v_toCold_3998_ = lean_ctor_get(v___y_3994_, 0);
v_options_3999_ = lean_ctor_get(v_toCold_3998_, 2);
v_hasTrace_4000_ = lean_ctor_get_uint8(v_options_3999_, sizeof(void*)*1);
if (v_hasTrace_4000_ == 0)
{
v___y_3935_ = v___y_3990_;
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3993_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
goto v___jp_3934_;
}
else
{
lean_object* v_inheritedTraceOptions_4001_; lean_object* v___x_4002_; uint8_t v___x_4003_; 
v_inheritedTraceOptions_4001_ = lean_ctor_get(v_toCold_3998_, 11);
v___x_4002_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4003_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4001_, v_options_3999_, v___x_4002_);
if (v___x_4003_ == 0)
{
v___y_3935_ = v___y_3990_;
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3993_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
goto v___jp_3934_;
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4005_; 
v___x_4004_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4005_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4004_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4005_) == 0)
{
lean_dec_ref_known(v___x_4005_, 1);
v___y_3935_ = v___y_3990_;
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3993_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
goto v___jp_3934_;
}
else
{
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3991_);
lean_dec(v_decl_3744_);
return v___x_4005_;
}
}
}
}
else
{
v___y_3958_ = v___y_3990_;
v___y_3959_ = v___y_3994_;
v___y_3960_ = v___y_3991_;
v___y_3961_ = v___y_3995_;
v___y_3962_ = v___y_3992_;
v___y_3963_ = v___y_3993_;
goto v___jp_3957_;
}
}
else
{
v___y_3958_ = v___y_3990_;
v___y_3959_ = v___y_3994_;
v___y_3960_ = v___y_3991_;
v___y_3961_ = v___y_3995_;
v___y_3962_ = v___y_3992_;
v___y_3963_ = v___y_3993_;
goto v___jp_3957_;
}
}
else
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v_a_4008_; uint8_t v___x_4009_; 
lean_dec(v___y_3992_);
v___x_4006_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4007_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4006_, v___y_3994_);
v_a_4008_ = lean_ctor_get(v___x_4007_, 0);
lean_inc(v_a_4008_);
lean_dec_ref(v___x_4007_);
v___x_4009_ = lean_unbox(v_a_4008_);
lean_dec(v_a_4008_);
if (v___x_4009_ == 0)
{
lean_object* v_toCold_4010_; lean_object* v_options_4011_; uint8_t v_hasTrace_4012_; 
v_toCold_4010_ = lean_ctor_get(v___y_3994_, 0);
v_options_4011_ = lean_ctor_get(v_toCold_4010_, 2);
v_hasTrace_4012_ = lean_ctor_get_uint8(v_options_4011_, sizeof(void*)*1);
if (v_hasTrace_4012_ == 0)
{
v___y_3913_ = v___y_3990_;
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3993_;
v_exportedInfo_x3f_3916_ = v___x_3988_;
v___y_3917_ = v___y_3994_;
v___y_3918_ = v___y_3995_;
goto v___jp_3912_;
}
else
{
lean_object* v_inheritedTraceOptions_4013_; lean_object* v___x_4014_; uint8_t v___x_4015_; 
v_inheritedTraceOptions_4013_ = lean_ctor_get(v_toCold_4010_, 11);
v___x_4014_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4015_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4013_, v_options_4011_, v___x_4014_);
if (v___x_4015_ == 0)
{
v___y_3913_ = v___y_3990_;
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3993_;
v_exportedInfo_x3f_3916_ = v___x_3988_;
v___y_3917_ = v___y_3994_;
v___y_3918_ = v___y_3995_;
goto v___jp_3912_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4016_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4017_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4016_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4017_) == 0)
{
lean_dec_ref_known(v___x_4017_, 1);
v___y_3913_ = v___y_3990_;
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3993_;
v_exportedInfo_x3f_3916_ = v___x_3988_;
v___y_3917_ = v___y_3994_;
v___y_3918_ = v___y_3995_;
goto v___jp_3912_;
}
else
{
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3991_);
lean_dec(v_decl_3744_);
return v___x_4017_;
}
}
}
}
else
{
lean_object* v_toCold_4018_; lean_object* v_options_4019_; uint8_t v_hasTrace_4020_; 
v_toCold_4018_ = lean_ctor_get(v___y_3994_, 0);
v_options_4019_ = lean_ctor_get(v_toCold_4018_, 2);
v_hasTrace_4020_ = lean_ctor_get_uint8(v_options_4019_, sizeof(void*)*1);
if (v_hasTrace_4020_ == 0)
{
v___y_3928_ = v___y_3990_;
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3993_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
goto v___jp_3927_;
}
else
{
lean_object* v_inheritedTraceOptions_4021_; lean_object* v___x_4022_; uint8_t v___x_4023_; 
v_inheritedTraceOptions_4021_ = lean_ctor_get(v_toCold_4018_, 11);
v___x_4022_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4023_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4021_, v_options_4019_, v___x_4022_);
if (v___x_4023_ == 0)
{
v___y_3928_ = v___y_3990_;
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3993_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
goto v___jp_3927_;
}
else
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4025_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4024_, v___y_3994_, v___y_3995_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_dec_ref_known(v___x_4025_, 1);
v___y_3928_ = v___y_3990_;
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3993_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
goto v___jp_3927_;
}
else
{
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3991_);
lean_dec(v_decl_3744_);
return v___x_4025_;
}
}
}
}
}
}
v___jp_4026_:
{
lean_object* v___x_4033_; lean_object* v_env_4034_; uint8_t v___x_4035_; 
v___x_4033_ = lean_st_ref_get(v___y_4032_);
v_env_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc_ref(v_env_4034_);
lean_dec(v___x_4033_);
v___x_4035_ = l_Lean_Environment_containsOnBranch(v_env_4034_, v_fst_4027_);
lean_dec_ref(v_env_4034_);
if (v___x_4035_ == 0)
{
v___y_3990_ = v_snd_4029_;
v___y_3991_ = v_fst_4028_;
v___y_3992_ = v_exportedInfo_x3f_4030_;
v___y_3993_ = v_fst_4027_;
v___y_3994_ = v___y_4031_;
v___y_3995_ = v___y_4032_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4036_; lean_object* v_env_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; 
lean_dec(v_exportedInfo_x3f_4030_);
lean_dec_ref(v_fst_4028_);
lean_dec(v_decl_3744_);
v___x_4036_ = lean_st_ref_get(v___y_4032_);
v_env_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc_ref(v_env_4037_);
lean_dec(v___x_4036_);
v___x_4038_ = lean_elab_environment_to_kernel_env(v_env_4037_);
v___x_4039_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v_fst_4027_);
v___x_4040_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4039_, v___y_4031_, v___y_4032_);
return v___x_4040_;
}
}
v___jp_4041_:
{
lean_object* v_toConstantVal_4046_; lean_object* v_name_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
v_toConstantVal_4046_ = lean_ctor_get(v___y_4042_, 0);
v_name_4047_ = lean_ctor_get(v_toConstantVal_4046_, 0);
lean_inc(v_name_4047_);
v___x_4048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___y_4042_);
v___x_4049_ = 0;
v_fst_4027_ = v_name_4047_;
v_fst_4028_ = v___x_4048_;
v_snd_4029_ = v___x_4049_;
v_exportedInfo_x3f_4030_ = v_exportedInfo_x3f_4043_;
v___y_4031_ = v___y_4044_;
v___y_4032_ = v___y_4045_;
goto v___jp_4026_;
}
v___jp_4050_:
{
lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; 
v___x_4056_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4056_, 0, v___y_4051_);
lean_ctor_set_uint8(v___x_4056_, sizeof(void*)*1, v___y_4055_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
v___x_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
v___y_4042_ = v___y_4054_;
v_exportedInfo_x3f_4043_ = v___x_4058_;
v___y_4044_ = v___y_4052_;
v___y_4045_ = v___y_4053_;
goto v___jp_4041_;
}
v___jp_4059_:
{
uint8_t v___x_4066_; uint8_t v___x_4067_; 
v___x_4066_ = 1;
v___x_4067_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4063_, v___x_4066_);
if (v___x_4067_ == 0)
{
v___y_4051_ = v_toConstantVal_4062_;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4061_;
v___y_4055_ = v___y_4060_;
goto v___jp_4050_;
}
else
{
v___y_4051_ = v_toConstantVal_4062_;
v___y_4052_ = v___y_4064_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4061_;
v___y_4055_ = v_hasTrace_3804_;
goto v___jp_4050_;
}
}
v___jp_4068_:
{
lean_object* v_toConstantVal_4073_; uint8_t v_safety_4074_; 
v_toConstantVal_4073_ = lean_ctor_get(v___y_4070_, 0);
lean_inc_ref(v_toConstantVal_4073_);
v_safety_4074_ = lean_ctor_get_uint8(v___y_4070_, sizeof(void*)*4);
v___y_4060_ = v___y_4069_;
v___y_4061_ = v___y_4070_;
v_toConstantVal_4062_ = v_toConstantVal_4073_;
v_safety_4063_ = v_safety_4074_;
v___y_4064_ = v___y_4071_;
v___y_4065_ = v___y_4072_;
goto v___jp_4059_;
}
v___jp_4075_:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = lean_st_ref_get(v___y_4078_);
v___x_4080_ = lean_st_ref_get(v___y_4078_);
if (v_forceExpose_3745_ == 0)
{
lean_object* v_env_4081_; lean_object* v_env_4082_; lean_object* v___x_4083_; uint8_t v_isModule_4084_; 
v_env_4081_ = lean_ctor_get(v___x_4079_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4079_);
v_env_4082_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4082_);
lean_dec(v___x_4080_);
v___x_4083_ = l_Lean_Environment_header(v_env_4081_);
lean_dec_ref(v_env_4081_);
v_isModule_4084_ = lean_ctor_get_uint8(v___x_4083_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4083_);
if (v_isModule_4084_ == 0)
{
lean_dec_ref(v_env_4082_);
v___y_4042_ = v_defn_4076_;
v_exportedInfo_x3f_4043_ = v___x_3988_;
v___y_4044_ = v___y_4077_;
v___y_4045_ = v___y_4078_;
goto v___jp_4041_;
}
else
{
uint8_t v_isExporting_4085_; 
v_isExporting_4085_ = lean_ctor_get_uint8(v_env_4082_, sizeof(void*)*8);
lean_dec_ref(v_env_4082_);
if (v_isExporting_4085_ == 0)
{
lean_object* v_toCold_4086_; lean_object* v_options_4087_; uint8_t v_hasTrace_4088_; 
v_toCold_4086_ = lean_ctor_get(v___y_4077_, 0);
v_options_4087_ = lean_ctor_get(v_toCold_4086_, 2);
v_hasTrace_4088_ = lean_ctor_get_uint8(v_options_4087_, sizeof(void*)*1);
if (v_hasTrace_4088_ == 0)
{
v___y_4069_ = v_isModule_4084_;
v___y_4070_ = v_defn_4076_;
v___y_4071_ = v___y_4077_;
v___y_4072_ = v___y_4078_;
goto v___jp_4068_;
}
else
{
lean_object* v_inheritedTraceOptions_4089_; lean_object* v___x_4090_; uint8_t v___x_4091_; 
v_inheritedTraceOptions_4089_ = lean_ctor_get(v_toCold_4086_, 11);
v___x_4090_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4091_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4089_, v_options_4087_, v___x_4090_);
if (v___x_4091_ == 0)
{
v___y_4069_ = v_isModule_4084_;
v___y_4070_ = v_defn_4076_;
v___y_4071_ = v___y_4077_;
v___y_4072_ = v___y_4078_;
goto v___jp_4068_;
}
else
{
lean_object* v_toConstantVal_4092_; uint8_t v_safety_4093_; lean_object* v_name_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v_toConstantVal_4092_ = lean_ctor_get(v_defn_4076_, 0);
lean_inc_ref(v_toConstantVal_4092_);
v_safety_4093_ = lean_ctor_get_uint8(v_defn_4076_, sizeof(void*)*4);
v_name_4094_ = lean_ctor_get(v_toConstantVal_4092_, 0);
v___x_4095_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4094_);
v___x_4096_ = l_Lean_MessageData_ofName(v_name_4094_);
v___x_4097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4095_);
lean_ctor_set(v___x_4097_, 1, v___x_4096_);
v___x_4098_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4099_, 0, v___x_4097_);
lean_ctor_set(v___x_4099_, 1, v___x_4098_);
v___x_4100_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4099_, v___y_4077_, v___y_4078_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_dec_ref_known(v___x_4100_, 1);
v___y_4060_ = v_isModule_4084_;
v___y_4061_ = v_defn_4076_;
v_toConstantVal_4062_ = v_toConstantVal_4092_;
v_safety_4063_ = v_safety_4093_;
v___y_4064_ = v___y_4077_;
v___y_4065_ = v___y_4078_;
goto v___jp_4059_;
}
else
{
lean_dec_ref(v_toConstantVal_4092_);
lean_dec_ref(v_defn_4076_);
lean_dec(v_decl_3744_);
return v___x_4100_;
}
}
}
}
else
{
v___y_4042_ = v_defn_4076_;
v_exportedInfo_x3f_4043_ = v___x_3988_;
v___y_4044_ = v___y_4077_;
v___y_4045_ = v___y_4078_;
goto v___jp_4041_;
}
}
}
else
{
lean_dec(v___x_4080_);
lean_dec(v___x_4079_);
v___y_4042_ = v_defn_4076_;
v_exportedInfo_x3f_4043_ = v___x_3988_;
v___y_4044_ = v___y_4077_;
v___y_4045_ = v___y_4078_;
goto v___jp_4041_;
}
}
}
}
}
else
{
lean_object* v___f_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; uint8_t v___x_4157_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_a_4161_; lean_object* v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4198_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v_a_4207_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4264_; lean_object* v___y_4265_; lean_object* v___y_4266_; uint8_t v___y_4267_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4277_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; 
lean_inc(v_decl_3744_);
v___f_4154_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4154_, 0, v_decl_3744_);
v___x_4155_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4156_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4157_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3803_, v_options_3802_, v___x_4156_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4457_; uint8_t v___x_4458_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; uint8_t v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4565_; lean_object* v___y_4566_; uint8_t v___y_4567_; lean_object* v_exportedInfo_x3f_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4580_; lean_object* v___y_4581_; uint8_t v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4587_; lean_object* v___y_4588_; uint8_t v___y_4589_; lean_object* v___y_4590_; lean_object* v___y_4591_; 
v___x_4457_ = l_Lean_trace_profiler;
v___x_4458_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3802_, v___x_4457_);
if (v___x_4458_ == 0)
{
lean_object* v___x_4593_; lean_object* v_env_4594_; lean_object* v_nextMacroScope_4595_; lean_object* v_ngen_4596_; lean_object* v_auxDeclNGen_4597_; lean_object* v_traceState_4598_; lean_object* v_messages_4599_; lean_object* v_infoState_4600_; lean_object* v_snapshotTasks_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4844_; 
lean_dec_ref(v___f_4154_);
v___x_4593_ = lean_st_ref_take(v_a_3747_);
v_env_4594_ = lean_ctor_get(v___x_4593_, 0);
v_nextMacroScope_4595_ = lean_ctor_get(v___x_4593_, 1);
v_ngen_4596_ = lean_ctor_get(v___x_4593_, 2);
v_auxDeclNGen_4597_ = lean_ctor_get(v___x_4593_, 3);
v_traceState_4598_ = lean_ctor_get(v___x_4593_, 4);
v_messages_4599_ = lean_ctor_get(v___x_4593_, 6);
v_infoState_4600_ = lean_ctor_get(v___x_4593_, 7);
v_snapshotTasks_4601_ = lean_ctor_get(v___x_4593_, 8);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4593_);
if (v_isSharedCheck_4844_ == 0)
{
lean_object* v_unused_4845_; 
v_unused_4845_ = lean_ctor_get(v___x_4593_, 5);
lean_dec(v_unused_4845_);
v___x_4603_ = v___x_4593_;
v_isShared_4604_ = v_isSharedCheck_4844_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_snapshotTasks_4601_);
lean_inc(v_infoState_4600_);
lean_inc(v_messages_4599_);
lean_inc(v_traceState_4598_);
lean_inc(v_auxDeclNGen_4597_);
lean_inc(v_ngen_4596_);
lean_inc(v_nextMacroScope_4595_);
lean_inc(v_env_4594_);
lean_dec(v___x_4593_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4844_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___y_4609_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; uint8_t v___y_4614_; lean_object* v___x_4637_; 
lean_inc(v_decl_3744_);
v___x_4605_ = l_Lean_Declaration_getNames(v_decl_3744_);
v___x_4606_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4594_, v___x_4605_);
v___x_4607_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4604_ == 0)
{
lean_ctor_set(v___x_4603_, 5, v___x_4607_);
lean_ctor_set(v___x_4603_, 0, v___x_4606_);
v___x_4637_ = v___x_4603_;
goto v_reusejp_4636_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4606_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_nextMacroScope_4595_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_ngen_4596_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_auxDeclNGen_4597_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_traceState_4598_);
lean_ctor_set(v_reuseFailAlloc_4843_, 5, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4843_, 6, v_messages_4599_);
lean_ctor_set(v_reuseFailAlloc_4843_, 7, v_infoState_4600_);
lean_ctor_set(v_reuseFailAlloc_4843_, 8, v_snapshotTasks_4601_);
v___x_4637_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4636_;
}
v___jp_4608_:
{
lean_object* v___x_4615_; lean_object* v_env_4616_; lean_object* v_nextMacroScope_4617_; lean_object* v_ngen_4618_; lean_object* v_auxDeclNGen_4619_; lean_object* v_traceState_4620_; lean_object* v_messages_4621_; lean_object* v_infoState_4622_; lean_object* v_snapshotTasks_4623_; lean_object* v___x_4625_; uint8_t v_isShared_4626_; uint8_t v_isSharedCheck_4634_; 
v___x_4615_ = lean_st_ref_take(v___y_4613_);
v_env_4616_ = lean_ctor_get(v___x_4615_, 0);
v_nextMacroScope_4617_ = lean_ctor_get(v___x_4615_, 1);
v_ngen_4618_ = lean_ctor_get(v___x_4615_, 2);
v_auxDeclNGen_4619_ = lean_ctor_get(v___x_4615_, 3);
v_traceState_4620_ = lean_ctor_get(v___x_4615_, 4);
v_messages_4621_ = lean_ctor_get(v___x_4615_, 6);
v_infoState_4622_ = lean_ctor_get(v___x_4615_, 7);
v_snapshotTasks_4623_ = lean_ctor_get(v___x_4615_, 8);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4634_ == 0)
{
lean_object* v_unused_4635_; 
v_unused_4635_ = lean_ctor_get(v___x_4615_, 5);
lean_dec(v_unused_4635_);
v___x_4625_ = v___x_4615_;
v_isShared_4626_ = v_isSharedCheck_4634_;
goto v_resetjp_4624_;
}
else
{
lean_inc(v_snapshotTasks_4623_);
lean_inc(v_infoState_4622_);
lean_inc(v_messages_4621_);
lean_inc(v_traceState_4620_);
lean_inc(v_auxDeclNGen_4619_);
lean_inc(v_ngen_4618_);
lean_inc(v_nextMacroScope_4617_);
lean_inc(v_env_4616_);
lean_dec(v___x_4615_);
v___x_4625_ = lean_box(0);
v_isShared_4626_ = v_isSharedCheck_4634_;
goto v_resetjp_4624_;
}
v_resetjp_4624_:
{
lean_object* v___x_4627_; lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4631_; 
v___x_4627_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4628_ = lean_box(v___y_4614_);
lean_inc(v___y_4612_);
v___x_4629_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4627_, v_env_4616_, v___y_4612_, v___x_4628_);
if (v_isShared_4626_ == 0)
{
lean_ctor_set(v___x_4625_, 5, v___x_4607_);
lean_ctor_set(v___x_4625_, 0, v___x_4629_);
v___x_4631_ = v___x_4625_;
goto v_reusejp_4630_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v___x_4629_);
lean_ctor_set(v_reuseFailAlloc_4633_, 1, v_nextMacroScope_4617_);
lean_ctor_set(v_reuseFailAlloc_4633_, 2, v_ngen_4618_);
lean_ctor_set(v_reuseFailAlloc_4633_, 3, v_auxDeclNGen_4619_);
lean_ctor_set(v_reuseFailAlloc_4633_, 4, v_traceState_4620_);
lean_ctor_set(v_reuseFailAlloc_4633_, 5, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4633_, 6, v_messages_4621_);
lean_ctor_set(v_reuseFailAlloc_4633_, 7, v_infoState_4622_);
lean_ctor_set(v_reuseFailAlloc_4633_, 8, v_snapshotTasks_4623_);
v___x_4631_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4630_;
}
v_reusejp_4630_:
{
lean_object* v___x_4632_; 
v___x_4632_ = lean_st_ref_put(v___y_4613_, v___x_4631_);
v___y_4565_ = v___y_4611_;
v___y_4566_ = v___y_4612_;
v___y_4567_ = v___y_4614_;
v_exportedInfo_x3f_4568_ = v___y_4610_;
v___y_4569_ = v___y_4609_;
v___y_4570_ = v___y_4613_;
goto v___jp_4564_;
}
}
}
v_reusejp_4636_:
{
lean_object* v___x_4638_; lean_object* v___y_4640_; lean_object* v_options_4641_; lean_object* v_inheritedTraceOptions_4642_; lean_object* v___y_4643_; lean_object* v___x_4649_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; uint8_t v___y_4654_; lean_object* v___y_4655_; lean_object* v___y_4656_; lean_object* v_fst_4685_; lean_object* v_fst_4686_; uint8_t v_snd_4687_; lean_object* v_exportedInfo_x3f_4688_; lean_object* v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4700_; lean_object* v_exportedInfo_x3f_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v___y_4709_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; uint8_t v___y_4713_; lean_object* v___y_4718_; lean_object* v_toConstantVal_4719_; uint8_t v_safety_4720_; uint8_t v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4727_; uint8_t v___y_4728_; lean_object* v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4734_; lean_object* v___y_4735_; lean_object* v___y_4736_; uint8_t v___y_4737_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v_defn_4762_; lean_object* v___y_4763_; lean_object* v___y_4764_; 
v___x_4638_ = lean_st_ref_put(v_a_3747_, v___x_4637_);
v___x_4649_ = lean_box(0);
switch(lean_obj_tag(v_decl_3744_))
{
case 2:
{
lean_object* v_val_4771_; lean_object* v_exportedInfo_x3f_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v___x_4787_; lean_object* v_env_4788_; 
v_val_4771_ = lean_ctor_get(v_decl_3744_, 0);
v___x_4787_ = lean_st_ref_get(v_a_3747_);
v_env_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc_ref(v_env_4788_);
lean_dec(v___x_4787_);
if (v_forceExpose_3745_ == 0)
{
goto v___jp_4789_;
}
else
{
if (v___x_4458_ == 0)
{
lean_dec_ref(v_env_4788_);
v_exportedInfo_x3f_4773_ = v___x_4649_;
v___y_4774_ = v_a_3746_;
v___y_4775_ = v_a_3747_;
goto v___jp_4772_;
}
else
{
goto v___jp_4789_;
}
}
v___jp_4772_:
{
lean_object* v_toConstantVal_4776_; lean_object* v_name_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v_toConstantVal_4776_ = lean_ctor_get(v_val_4771_, 0);
v_name_4777_ = lean_ctor_get(v_toConstantVal_4776_, 0);
lean_inc_ref(v_val_4771_);
v___x_4778_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4778_, 0, v_val_4771_);
v___x_4779_ = 1;
lean_inc(v_name_4777_);
v_fst_4685_ = v_name_4777_;
v_fst_4686_ = v___x_4778_;
v_snd_4687_ = v___x_4779_;
v_exportedInfo_x3f_4688_ = v_exportedInfo_x3f_4773_;
v___y_4689_ = v___y_4774_;
v___y_4690_ = v___y_4775_;
goto v___jp_4684_;
}
v___jp_4780_:
{
lean_object* v_toConstantVal_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v_toConstantVal_4783_ = lean_ctor_get(v_val_4771_, 0);
lean_inc_ref(v_toConstantVal_4783_);
v___x_4784_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4784_, 0, v_toConstantVal_4783_);
lean_ctor_set_uint8(v___x_4784_, sizeof(void*)*1, v___x_4458_);
v___x_4785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4785_, 0, v___x_4784_);
v___x_4786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
v_exportedInfo_x3f_4773_ = v___x_4786_;
v___y_4774_ = v___y_4781_;
v___y_4775_ = v___y_4782_;
goto v___jp_4772_;
}
v___jp_4789_:
{
lean_object* v___x_4790_; uint8_t v_isModule_4791_; 
v___x_4790_ = l_Lean_Environment_header(v_env_4788_);
lean_dec_ref(v_env_4788_);
v_isModule_4791_ = lean_ctor_get_uint8(v___x_4790_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4790_);
if (v_isModule_4791_ == 0)
{
v_exportedInfo_x3f_4773_ = v___x_4649_;
v___y_4774_ = v_a_3746_;
v___y_4775_ = v_a_3747_;
goto v___jp_4772_;
}
else
{
if (v___x_4157_ == 0)
{
v___y_4781_ = v_a_3746_;
v___y_4782_ = v_a_3747_;
goto v___jp_4780_;
}
else
{
lean_object* v_toConstantVal_4792_; lean_object* v_name_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
v_toConstantVal_4792_ = lean_ctor_get(v_val_4771_, 0);
v_name_4793_ = lean_ctor_get(v_toConstantVal_4792_, 0);
v___x_4794_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4793_);
v___x_4795_ = l_Lean_MessageData_ofName(v_name_4793_);
v___x_4796_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4796_, 0, v___x_4794_);
lean_ctor_set(v___x_4796_, 1, v___x_4795_);
v___x_4797_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4798_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4796_);
lean_ctor_set(v___x_4798_, 1, v___x_4797_);
v___x_4799_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4798_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_dec_ref_known(v___x_4799_, 1);
v___y_4781_ = v_a_3746_;
v___y_4782_ = v_a_3747_;
goto v___jp_4780_;
}
else
{
lean_dec_ref_known(v_decl_3744_, 1);
return v___x_4799_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4800_; 
v_val_4800_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref(v_val_4800_);
v_defn_4762_ = v_val_4800_;
v___y_4763_ = v_a_3746_;
v___y_4764_ = v_a_3747_;
goto v___jp_4761_;
}
case 5:
{
lean_object* v_defns_4801_; 
v_defns_4801_ = lean_ctor_get(v_decl_3744_, 0);
if (lean_obj_tag(v_defns_4801_) == 1)
{
lean_object* v_tail_4802_; 
v_tail_4802_ = lean_ctor_get(v_defns_4801_, 1);
if (lean_obj_tag(v_tail_4802_) == 0)
{
lean_object* v_head_4803_; 
v_head_4803_ = lean_ctor_get(v_defns_4801_, 0);
lean_inc(v_head_4803_);
v_defn_4762_ = v_head_4803_;
v___y_4763_ = v_a_3746_;
v___y_4764_ = v_a_3747_;
goto v___jp_4761_;
}
else
{
v___y_4640_ = v_a_3746_;
v_options_4641_ = v_options_3802_;
v_inheritedTraceOptions_4642_ = v_inheritedTraceOptions_3803_;
v___y_4643_ = v_a_3747_;
goto v___jp_4639_;
}
}
else
{
v___y_4640_ = v_a_3746_;
v_options_4641_ = v_options_3802_;
v_inheritedTraceOptions_4642_ = v_inheritedTraceOptions_3803_;
v___y_4643_ = v_a_3747_;
goto v___jp_4639_;
}
}
case 3:
{
lean_object* v_val_4804_; lean_object* v_exportedInfo_x3f_4806_; lean_object* v___y_4807_; lean_object* v___y_4808_; lean_object* v___y_4814_; lean_object* v___y_4815_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v_env_4832_; lean_object* v_env_4833_; 
v_val_4804_ = lean_ctor_get(v_decl_3744_, 0);
v___x_4821_ = lean_st_ref_get(v_a_3747_);
v___x_4822_ = lean_st_ref_get(v_a_3747_);
v_env_4832_ = lean_ctor_get(v___x_4821_, 0);
lean_inc_ref(v_env_4832_);
lean_dec(v___x_4821_);
v_env_4833_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_env_4833_);
lean_dec(v___x_4822_);
if (v_forceExpose_3745_ == 0)
{
goto v___jp_4834_;
}
else
{
if (v___x_4458_ == 0)
{
lean_dec_ref(v_env_4833_);
lean_dec_ref(v_env_4832_);
v_exportedInfo_x3f_4806_ = v___x_4649_;
v___y_4807_ = v_a_3746_;
v___y_4808_ = v_a_3747_;
goto v___jp_4805_;
}
else
{
goto v___jp_4834_;
}
}
v___jp_4805_:
{
lean_object* v_toConstantVal_4809_; lean_object* v_name_4810_; lean_object* v___x_4811_; uint8_t v___x_4812_; 
v_toConstantVal_4809_ = lean_ctor_get(v_val_4804_, 0);
v_name_4810_ = lean_ctor_get(v_toConstantVal_4809_, 0);
lean_inc_ref(v_val_4804_);
v___x_4811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4811_, 0, v_val_4804_);
v___x_4812_ = 3;
lean_inc(v_name_4810_);
v_fst_4685_ = v_name_4810_;
v_fst_4686_ = v___x_4811_;
v_snd_4687_ = v___x_4812_;
v_exportedInfo_x3f_4688_ = v_exportedInfo_x3f_4806_;
v___y_4689_ = v___y_4807_;
v___y_4690_ = v___y_4808_;
goto v___jp_4684_;
}
v___jp_4813_:
{
lean_object* v_toConstantVal_4816_; uint8_t v_isUnsafe_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; 
v_toConstantVal_4816_ = lean_ctor_get(v_val_4804_, 0);
v_isUnsafe_4817_ = lean_ctor_get_uint8(v_val_4804_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4816_);
v___x_4818_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4818_, 0, v_toConstantVal_4816_);
lean_ctor_set_uint8(v___x_4818_, sizeof(void*)*1, v_isUnsafe_4817_);
v___x_4819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4819_, 0, v___x_4818_);
v___x_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
v_exportedInfo_x3f_4806_ = v___x_4820_;
v___y_4807_ = v___y_4814_;
v___y_4808_ = v___y_4815_;
goto v___jp_4805_;
}
v___jp_4823_:
{
if (v___x_4157_ == 0)
{
v___y_4814_ = v_a_3746_;
v___y_4815_ = v_a_3747_;
goto v___jp_4813_;
}
else
{
lean_object* v_toConstantVal_4824_; lean_object* v_name_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v_toConstantVal_4824_ = lean_ctor_get(v_val_4804_, 0);
v_name_4825_ = lean_ctor_get(v_toConstantVal_4824_, 0);
v___x_4826_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4825_);
v___x_4827_ = l_Lean_MessageData_ofName(v_name_4825_);
v___x_4828_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4828_, 0, v___x_4826_);
lean_ctor_set(v___x_4828_, 1, v___x_4827_);
v___x_4829_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4830_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4830_, 0, v___x_4828_);
lean_ctor_set(v___x_4830_, 1, v___x_4829_);
v___x_4831_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4830_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4831_) == 0)
{
lean_dec_ref_known(v___x_4831_, 1);
v___y_4814_ = v_a_3746_;
v___y_4815_ = v_a_3747_;
goto v___jp_4813_;
}
else
{
lean_dec_ref_known(v_decl_3744_, 1);
return v___x_4831_;
}
}
}
v___jp_4834_:
{
lean_object* v___x_4835_; uint8_t v_isModule_4836_; 
v___x_4835_ = l_Lean_Environment_header(v_env_4832_);
lean_dec_ref(v_env_4832_);
v_isModule_4836_ = lean_ctor_get_uint8(v___x_4835_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4835_);
if (v_isModule_4836_ == 0)
{
lean_dec_ref(v_env_4833_);
v_exportedInfo_x3f_4806_ = v___x_4649_;
v___y_4807_ = v_a_3746_;
v___y_4808_ = v_a_3747_;
goto v___jp_4805_;
}
else
{
uint8_t v_isExporting_4837_; 
v_isExporting_4837_ = lean_ctor_get_uint8(v_env_4833_, sizeof(void*)*8);
lean_dec_ref(v_env_4833_);
if (v_isExporting_4837_ == 0)
{
goto v___jp_4823_;
}
else
{
if (v___x_4458_ == 0)
{
v_exportedInfo_x3f_4806_ = v___x_4649_;
v___y_4807_ = v_a_3746_;
v___y_4808_ = v_a_3747_;
goto v___jp_4805_;
}
else
{
goto v___jp_4823_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4838_; lean_object* v_toConstantVal_4839_; lean_object* v_name_4840_; lean_object* v___x_4841_; uint8_t v___x_4842_; 
v_val_4838_ = lean_ctor_get(v_decl_3744_, 0);
v_toConstantVal_4839_ = lean_ctor_get(v_val_4838_, 0);
v_name_4840_ = lean_ctor_get(v_toConstantVal_4839_, 0);
lean_inc_ref(v_val_4838_);
v___x_4841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4841_, 0, v_val_4838_);
v___x_4842_ = 2;
lean_inc(v_name_4840_);
v_fst_4685_ = v_name_4840_;
v_fst_4686_ = v___x_4841_;
v_snd_4687_ = v___x_4842_;
v_exportedInfo_x3f_4688_ = v___x_4649_;
v___y_4689_ = v_a_3746_;
v___y_4690_ = v_a_3747_;
goto v___jp_4684_;
}
default: 
{
v___y_4640_ = v_a_3746_;
v_options_4641_ = v_options_3802_;
v_inheritedTraceOptions_4642_ = v_inheritedTraceOptions_3803_;
v___y_4643_ = v_a_3747_;
goto v___jp_4639_;
}
}
v___jp_4639_:
{
uint8_t v___x_4644_; 
v___x_4644_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4642_, v_options_4641_, v___x_4156_);
if (v___x_4644_ == 0)
{
lean_object* v___x_4645_; 
v___x_4645_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v___y_4640_, v___y_4643_);
return v___x_4645_;
}
else
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
v___x_4646_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4647_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4646_, v___y_4640_, v___y_4643_);
if (lean_obj_tag(v___x_4647_) == 0)
{
lean_object* v___x_4648_; 
lean_dec_ref_known(v___x_4647_, 1);
v___x_4648_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v___y_4640_, v___y_4643_);
return v___x_4648_;
}
else
{
lean_dec(v_decl_3744_);
return v___x_4647_;
}
}
}
v___jp_4650_:
{
lean_object* v___x_4657_; uint8_t v___x_4658_; 
lean_inc(v_decl_3744_);
v___x_4657_ = l_Lean_Declaration_getTopLevelNames(v_decl_3744_);
v___x_4658_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4657_);
lean_dec(v___x_4657_);
if (v___x_4658_ == 0)
{
if (lean_obj_tag(v___y_4651_) == 0)
{
if (v___x_4658_ == 0)
{
lean_object* v_toCold_4659_; lean_object* v_options_4660_; uint8_t v_hasTrace_4661_; 
v_toCold_4659_ = lean_ctor_get(v___y_4655_, 0);
v_options_4660_ = lean_ctor_get(v_toCold_4659_, 2);
v_hasTrace_4661_ = lean_ctor_get_uint8(v_options_4660_, sizeof(void*)*1);
if (v_hasTrace_4661_ == 0)
{
v___y_4580_ = v___y_4652_;
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
goto v___jp_4579_;
}
else
{
lean_object* v_inheritedTraceOptions_4662_; uint8_t v___x_4663_; 
v_inheritedTraceOptions_4662_ = lean_ctor_get(v_toCold_4659_, 11);
v___x_4663_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4662_, v_options_4660_, v___x_4156_);
if (v___x_4663_ == 0)
{
v___y_4580_ = v___y_4652_;
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
goto v___jp_4579_;
}
else
{
lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4664_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4665_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4664_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_dec_ref_known(v___x_4665_, 1);
v___y_4580_ = v___y_4652_;
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
goto v___jp_4579_;
}
else
{
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v_decl_3744_);
return v___x_4665_;
}
}
}
}
else
{
v___y_4609_ = v___y_4655_;
v___y_4610_ = v___y_4651_;
v___y_4611_ = v___y_4652_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4654_;
goto v___jp_4608_;
}
}
else
{
v___y_4609_ = v___y_4655_;
v___y_4610_ = v___y_4651_;
v___y_4611_ = v___y_4652_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4656_;
v___y_4614_ = v___y_4654_;
goto v___jp_4608_;
}
}
else
{
lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v_a_4668_; uint8_t v___x_4669_; 
lean_dec(v___y_4651_);
v___x_4666_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4667_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4666_, v___y_4655_);
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
lean_inc(v_a_4668_);
lean_dec_ref(v___x_4667_);
v___x_4669_ = lean_unbox(v_a_4668_);
lean_dec(v_a_4668_);
if (v___x_4669_ == 0)
{
lean_object* v_toCold_4670_; lean_object* v_options_4671_; uint8_t v_hasTrace_4672_; 
v_toCold_4670_ = lean_ctor_get(v___y_4655_, 0);
v_options_4671_ = lean_ctor_get(v_toCold_4670_, 2);
v_hasTrace_4672_ = lean_ctor_get_uint8(v_options_4671_, sizeof(void*)*1);
if (v_hasTrace_4672_ == 0)
{
v___y_4565_ = v___y_4652_;
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v_exportedInfo_x3f_4568_ = v___x_4649_;
v___y_4569_ = v___y_4655_;
v___y_4570_ = v___y_4656_;
goto v___jp_4564_;
}
else
{
lean_object* v_inheritedTraceOptions_4673_; uint8_t v___x_4674_; 
v_inheritedTraceOptions_4673_ = lean_ctor_get(v_toCold_4670_, 11);
v___x_4674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4673_, v_options_4671_, v___x_4156_);
if (v___x_4674_ == 0)
{
v___y_4565_ = v___y_4652_;
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v_exportedInfo_x3f_4568_ = v___x_4649_;
v___y_4569_ = v___y_4655_;
v___y_4570_ = v___y_4656_;
goto v___jp_4564_;
}
else
{
lean_object* v___x_4675_; lean_object* v___x_4676_; 
v___x_4675_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4676_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4675_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4676_) == 0)
{
lean_dec_ref_known(v___x_4676_, 1);
v___y_4565_ = v___y_4652_;
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v_exportedInfo_x3f_4568_ = v___x_4649_;
v___y_4569_ = v___y_4655_;
v___y_4570_ = v___y_4656_;
goto v___jp_4564_;
}
else
{
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v_decl_3744_);
return v___x_4676_;
}
}
}
}
else
{
lean_object* v_toCold_4677_; lean_object* v_options_4678_; uint8_t v_hasTrace_4679_; 
v_toCold_4677_ = lean_ctor_get(v___y_4655_, 0);
v_options_4678_ = lean_ctor_get(v_toCold_4677_, 2);
v_hasTrace_4679_ = lean_ctor_get_uint8(v_options_4678_, sizeof(void*)*1);
if (v_hasTrace_4679_ == 0)
{
v___y_4587_ = v___y_4652_;
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
goto v___jp_4586_;
}
else
{
lean_object* v_inheritedTraceOptions_4680_; uint8_t v___x_4681_; 
v_inheritedTraceOptions_4680_ = lean_ctor_get(v_toCold_4677_, 11);
v___x_4681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4680_, v_options_4678_, v___x_4156_);
if (v___x_4681_ == 0)
{
v___y_4587_ = v___y_4652_;
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
goto v___jp_4586_;
}
else
{
lean_object* v___x_4682_; lean_object* v___x_4683_; 
v___x_4682_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4683_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4682_, v___y_4655_, v___y_4656_);
if (lean_obj_tag(v___x_4683_) == 0)
{
lean_dec_ref_known(v___x_4683_, 1);
v___y_4587_ = v___y_4652_;
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
goto v___jp_4586_;
}
else
{
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v_decl_3744_);
return v___x_4683_;
}
}
}
}
}
}
v___jp_4684_:
{
lean_object* v___x_4691_; lean_object* v_env_4692_; uint8_t v___x_4693_; 
v___x_4691_ = lean_st_ref_get(v___y_4690_);
v_env_4692_ = lean_ctor_get(v___x_4691_, 0);
lean_inc_ref(v_env_4692_);
lean_dec(v___x_4691_);
v___x_4693_ = l_Lean_Environment_containsOnBranch(v_env_4692_, v_fst_4685_);
lean_dec_ref(v_env_4692_);
if (v___x_4693_ == 0)
{
v___y_4651_ = v_exportedInfo_x3f_4688_;
v___y_4652_ = v_fst_4686_;
v___y_4653_ = v_fst_4685_;
v___y_4654_ = v_snd_4687_;
v___y_4655_ = v___y_4689_;
v___y_4656_ = v___y_4690_;
goto v___jp_4650_;
}
else
{
lean_object* v___x_4694_; lean_object* v_env_4695_; lean_object* v___x_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; 
lean_dec(v_exportedInfo_x3f_4688_);
lean_dec_ref(v_fst_4686_);
lean_dec(v_decl_3744_);
v___x_4694_ = lean_st_ref_get(v___y_4690_);
v_env_4695_ = lean_ctor_get(v___x_4694_, 0);
lean_inc_ref(v_env_4695_);
lean_dec(v___x_4694_);
v___x_4696_ = lean_elab_environment_to_kernel_env(v_env_4695_);
v___x_4697_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4697_, 0, v___x_4696_);
lean_ctor_set(v___x_4697_, 1, v_fst_4685_);
v___x_4698_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4697_, v___y_4689_, v___y_4690_);
return v___x_4698_;
}
}
v___jp_4699_:
{
lean_object* v_toConstantVal_4704_; lean_object* v_name_4705_; lean_object* v___x_4706_; uint8_t v___x_4707_; 
v_toConstantVal_4704_ = lean_ctor_get(v___y_4700_, 0);
v_name_4705_ = lean_ctor_get(v_toConstantVal_4704_, 0);
lean_inc(v_name_4705_);
v___x_4706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4706_, 0, v___y_4700_);
v___x_4707_ = 0;
v_fst_4685_ = v_name_4705_;
v_fst_4686_ = v___x_4706_;
v_snd_4687_ = v___x_4707_;
v_exportedInfo_x3f_4688_ = v_exportedInfo_x3f_4701_;
v___y_4689_ = v___y_4702_;
v___y_4690_ = v___y_4703_;
goto v___jp_4684_;
}
v___jp_4708_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; 
v___x_4714_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4714_, 0, v___y_4712_);
lean_ctor_set_uint8(v___x_4714_, sizeof(void*)*1, v___y_4713_);
v___x_4715_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4714_);
v___x_4716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___y_4700_ = v___y_4709_;
v_exportedInfo_x3f_4701_ = v___x_4716_;
v___y_4702_ = v___y_4711_;
v___y_4703_ = v___y_4710_;
goto v___jp_4699_;
}
v___jp_4717_:
{
uint8_t v___x_4724_; uint8_t v___x_4725_; 
v___x_4724_ = 1;
v___x_4725_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4720_, v___x_4724_);
if (v___x_4725_ == 0)
{
v___y_4709_ = v___y_4718_;
v___y_4710_ = v___y_4723_;
v___y_4711_ = v___y_4722_;
v___y_4712_ = v_toConstantVal_4719_;
v___y_4713_ = v___y_4721_;
goto v___jp_4708_;
}
else
{
v___y_4709_ = v___y_4718_;
v___y_4710_ = v___y_4723_;
v___y_4711_ = v___y_4722_;
v___y_4712_ = v_toConstantVal_4719_;
v___y_4713_ = v___x_4458_;
goto v___jp_4708_;
}
}
v___jp_4726_:
{
lean_object* v_toConstantVal_4731_; uint8_t v_safety_4732_; 
v_toConstantVal_4731_ = lean_ctor_get(v___y_4727_, 0);
lean_inc_ref(v_toConstantVal_4731_);
v_safety_4732_ = lean_ctor_get_uint8(v___y_4727_, sizeof(void*)*4);
v___y_4718_ = v___y_4727_;
v_toConstantVal_4719_ = v_toConstantVal_4731_;
v_safety_4720_ = v_safety_4732_;
v___y_4721_ = v___y_4728_;
v___y_4722_ = v___y_4729_;
v___y_4723_ = v___y_4730_;
goto v___jp_4717_;
}
v___jp_4733_:
{
lean_object* v_toCold_4738_; lean_object* v_options_4739_; uint8_t v_hasTrace_4740_; 
v_toCold_4738_ = lean_ctor_get(v___y_4734_, 0);
v_options_4739_ = lean_ctor_get(v_toCold_4738_, 2);
v_hasTrace_4740_ = lean_ctor_get_uint8(v_options_4739_, sizeof(void*)*1);
if (v_hasTrace_4740_ == 0)
{
v___y_4727_ = v___y_4736_;
v___y_4728_ = v___y_4737_;
v___y_4729_ = v___y_4734_;
v___y_4730_ = v___y_4735_;
goto v___jp_4726_;
}
else
{
lean_object* v_inheritedTraceOptions_4741_; uint8_t v___x_4742_; 
v_inheritedTraceOptions_4741_ = lean_ctor_get(v_toCold_4738_, 11);
v___x_4742_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4741_, v_options_4739_, v___x_4156_);
if (v___x_4742_ == 0)
{
v___y_4727_ = v___y_4736_;
v___y_4728_ = v___y_4737_;
v___y_4729_ = v___y_4734_;
v___y_4730_ = v___y_4735_;
goto v___jp_4726_;
}
else
{
lean_object* v_toConstantVal_4743_; uint8_t v_safety_4744_; lean_object* v_name_4745_; lean_object* v___x_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; 
v_toConstantVal_4743_ = lean_ctor_get(v___y_4736_, 0);
lean_inc_ref(v_toConstantVal_4743_);
v_safety_4744_ = lean_ctor_get_uint8(v___y_4736_, sizeof(void*)*4);
v_name_4745_ = lean_ctor_get(v_toConstantVal_4743_, 0);
v___x_4746_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4745_);
v___x_4747_ = l_Lean_MessageData_ofName(v_name_4745_);
v___x_4748_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4748_, 0, v___x_4746_);
lean_ctor_set(v___x_4748_, 1, v___x_4747_);
v___x_4749_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4750_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4748_);
lean_ctor_set(v___x_4750_, 1, v___x_4749_);
v___x_4751_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4750_, v___y_4734_, v___y_4735_);
if (lean_obj_tag(v___x_4751_) == 0)
{
lean_dec_ref_known(v___x_4751_, 1);
v___y_4718_ = v___y_4736_;
v_toConstantVal_4719_ = v_toConstantVal_4743_;
v_safety_4720_ = v_safety_4744_;
v___y_4721_ = v___y_4737_;
v___y_4722_ = v___y_4734_;
v___y_4723_ = v___y_4735_;
goto v___jp_4717_;
}
else
{
lean_dec_ref(v_toConstantVal_4743_);
lean_dec_ref(v___y_4736_);
lean_dec(v_decl_3744_);
return v___x_4751_;
}
}
}
}
v___jp_4752_:
{
lean_object* v___x_4758_; uint8_t v_isModule_4759_; 
v___x_4758_ = l_Lean_Environment_header(v___y_4755_);
lean_dec_ref(v___y_4755_);
v_isModule_4759_ = lean_ctor_get_uint8(v___x_4758_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4758_);
if (v_isModule_4759_ == 0)
{
lean_dec_ref(v___y_4757_);
v___y_4700_ = v___y_4756_;
v_exportedInfo_x3f_4701_ = v___x_4649_;
v___y_4702_ = v___y_4753_;
v___y_4703_ = v___y_4754_;
goto v___jp_4699_;
}
else
{
uint8_t v_isExporting_4760_; 
v_isExporting_4760_ = lean_ctor_get_uint8(v___y_4757_, sizeof(void*)*8);
lean_dec_ref(v___y_4757_);
if (v_isExporting_4760_ == 0)
{
v___y_4734_ = v___y_4753_;
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4756_;
v___y_4737_ = v_isModule_4759_;
goto v___jp_4733_;
}
else
{
if (v___x_4458_ == 0)
{
v___y_4700_ = v___y_4756_;
v_exportedInfo_x3f_4701_ = v___x_4649_;
v___y_4702_ = v___y_4753_;
v___y_4703_ = v___y_4754_;
goto v___jp_4699_;
}
else
{
v___y_4734_ = v___y_4753_;
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4756_;
v___y_4737_ = v___x_4458_;
goto v___jp_4733_;
}
}
}
}
v___jp_4761_:
{
lean_object* v___x_4765_; lean_object* v___x_4766_; 
v___x_4765_ = lean_st_ref_get(v___y_4764_);
v___x_4766_ = lean_st_ref_get(v___y_4764_);
if (v_forceExpose_3745_ == 0)
{
lean_object* v_env_4767_; lean_object* v_env_4768_; 
v_env_4767_ = lean_ctor_get(v___x_4765_, 0);
lean_inc_ref(v_env_4767_);
lean_dec(v___x_4765_);
v_env_4768_ = lean_ctor_get(v___x_4766_, 0);
lean_inc_ref(v_env_4768_);
lean_dec(v___x_4766_);
v___y_4753_ = v___y_4763_;
v___y_4754_ = v___y_4764_;
v___y_4755_ = v_env_4767_;
v___y_4756_ = v_defn_4762_;
v___y_4757_ = v_env_4768_;
goto v___jp_4752_;
}
else
{
if (v___x_4458_ == 0)
{
lean_dec(v___x_4766_);
lean_dec(v___x_4765_);
v___y_4700_ = v_defn_4762_;
v_exportedInfo_x3f_4701_ = v___x_4649_;
v___y_4702_ = v___y_4763_;
v___y_4703_ = v___y_4764_;
goto v___jp_4699_;
}
else
{
lean_object* v_env_4769_; lean_object* v_env_4770_; 
v_env_4769_ = lean_ctor_get(v___x_4765_, 0);
lean_inc_ref(v_env_4769_);
lean_dec(v___x_4765_);
v_env_4770_ = lean_ctor_get(v___x_4766_, 0);
lean_inc_ref(v_env_4770_);
lean_dec(v___x_4766_);
v___y_4753_ = v___y_4763_;
v___y_4754_ = v___y_4764_;
v___y_4755_ = v_env_4769_;
v___y_4756_ = v_defn_4762_;
v___y_4757_ = v_env_4770_;
goto v___jp_4752_;
}
}
}
}
}
}
else
{
goto v___jp_4305_;
}
v___jp_4459_:
{
lean_object* v___x_4470_; 
lean_inc_ref(v___y_4466_);
v___x_4470_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4462_, v___y_4466_, v___y_4467_, v___y_4469_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v___x_4471_; lean_object* v___x_4473_; uint8_t v_isShared_4474_; uint8_t v_isSharedCheck_4518_; 
lean_dec_ref_known(v___x_4470_, 1);
lean_inc_ref(v___y_4461_);
v___x_4471_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4461_, v___y_4468_);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4518_ == 0)
{
lean_object* v_unused_4519_; 
v_unused_4519_ = lean_ctor_get(v___x_4471_, 0);
lean_dec(v_unused_4519_);
v___x_4473_ = v___x_4471_;
v_isShared_4474_ = v_isSharedCheck_4518_;
goto v_resetjp_4472_;
}
else
{
lean_dec(v___x_4471_);
v___x_4473_ = lean_box(0);
v_isShared_4474_ = v_isSharedCheck_4518_;
goto v_resetjp_4472_;
}
v_resetjp_4472_:
{
lean_object* v_toCold_4475_; lean_object* v_options_4476_; lean_object* v___x_4477_; uint8_t v___x_4478_; 
v_toCold_4475_ = lean_ctor_get(v___y_4465_, 0);
v_options_4476_ = lean_ctor_get(v_toCold_4475_, 2);
v___x_4477_ = l_Lean_Elab_async;
v___x_4478_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4476_, v___x_4477_);
if (v___x_4478_ == 0)
{
lean_object* v___x_4479_; lean_object* v_r_4480_; 
lean_del_object(v___x_4473_);
lean_dec_ref(v___y_4464_);
lean_dec_ref(v___y_4463_);
v___x_4479_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4466_, v___y_4468_);
lean_dec_ref(v___x_4479_);
v_r_4480_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v___y_4465_, v___y_4468_);
if (lean_obj_tag(v_r_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4490_; 
v_a_4481_ = lean_ctor_get(v_r_4480_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v_r_4480_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4483_ = v_r_4480_;
v_isShared_4484_ = v_isSharedCheck_4490_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v_r_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4490_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v___x_4486_; 
lean_inc(v_a_4481_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set_tag(v___x_4483_, 1);
v___x_4486_ = v___x_4483_;
goto v_reusejp_4485_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4481_);
v___x_4486_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4485_;
}
v_reusejp_4485_:
{
lean_object* v___x_4487_; 
v___x_4487_ = lean_apply_2(v___y_4460_, v___x_4486_, lean_box(0));
if (lean_obj_tag(v___x_4487_) == 0)
{
lean_dec_ref_known(v___x_4487_, 1);
v___y_3750_ = v___y_4461_;
v___y_3751_ = v___y_4468_;
v_a_3752_ = v_a_4481_;
goto v___jp_3749_;
}
else
{
lean_object* v_a_4488_; 
lean_dec(v_a_4481_);
v_a_4488_ = lean_ctor_get(v___x_4487_, 0);
lean_inc(v_a_4488_);
lean_dec_ref_known(v___x_4487_, 1);
v___y_3763_ = v___y_4461_;
v___y_3764_ = v___y_4468_;
v_a_3765_ = v_a_4488_;
goto v___jp_3762_;
}
}
}
}
else
{
lean_object* v_a_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; 
v_a_4491_ = lean_ctor_get(v_r_4480_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v_r_4480_, 1);
v___x_4492_ = lean_box(0);
v___x_4493_ = lean_apply_2(v___y_4460_, v___x_4492_, lean_box(0));
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_dec_ref_known(v___x_4493_, 1);
v___y_3763_ = v___y_4461_;
v___y_3764_ = v___y_4468_;
v_a_3765_ = v_a_4491_;
goto v___jp_3762_;
}
else
{
lean_object* v_a_4494_; 
lean_dec(v_a_4491_);
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
v___y_3763_ = v___y_4461_;
v___y_3764_ = v___y_4468_;
v_a_3765_ = v_a_4494_;
goto v___jp_3762_;
}
}
}
else
{
lean_object* v___x_4495_; lean_object* v___x_4497_; 
lean_dec_ref(v___y_4466_);
lean_dec_ref(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v_decl_3744_);
v___x_4495_ = l_IO_CancelToken_new();
if (v_isShared_4474_ == 0)
{
lean_ctor_set_tag(v___x_4473_, 1);
lean_ctor_set(v___x_4473_, 0, v___x_4495_);
v___x_4497_ = v___x_4473_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v___x_4495_);
v___x_4497_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v___x_4498_ = lean_unsigned_to_nat(0u);
v___x_4499_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4500_ = l_Lean_Name_toString(v___x_4499_, v_hasTrace_3804_);
lean_inc_ref(v___x_4497_);
v___x_4501_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4463_, v___x_4497_, v___x_4500_, v___y_4465_, v___y_4468_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v_checked_4503_; lean_object* v___x_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v_checked_4503_ = lean_ctor_get(v___y_4464_, 2);
lean_inc_ref(v_checked_4503_);
lean_dec_ref(v___y_4464_);
v___x_4504_ = lean_io_map_task(v_a_4502_, v_checked_4503_, v___x_4498_, v___x_4458_);
v___x_4505_ = lean_box(0);
v___x_4506_ = lean_box(2);
v___x_4507_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4505_);
lean_ctor_set(v___x_4507_, 1, v___x_4506_);
lean_ctor_set(v___x_4507_, 2, v___x_4497_);
lean_ctor_set(v___x_4507_, 3, v___x_4504_);
v___x_4508_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4507_, v___y_4468_);
return v___x_4508_;
}
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec_ref(v___x_4497_);
lean_dec_ref(v___y_4464_);
v_a_4509_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4501_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4501_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4514_; 
if (v_isShared_4512_ == 0)
{
v___x_4514_ = v___x_4511_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v_a_4509_);
v___x_4514_ = v_reuseFailAlloc_4515_;
goto v_reusejp_4513_;
}
v_reusejp_4513_:
{
return v___x_4514_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4532_; 
lean_dec_ref(v___y_4466_);
lean_dec_ref(v___y_4464_);
lean_dec_ref(v___y_4463_);
lean_dec_ref(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v_decl_3744_);
v_a_4520_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4532_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4532_ == 0)
{
v___x_4522_ = v___x_4470_;
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4470_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4532_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v_ref_4524_; lean_object* v___x_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4530_; 
v_ref_4524_ = lean_ctor_get(v___y_4465_, 2);
v___x_4525_ = lean_io_error_to_string(v_a_4520_);
v___x_4526_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4526_, 0, v___x_4525_);
v___x_4527_ = l_Lean_MessageData_ofFormat(v___x_4526_);
lean_inc(v_ref_4524_);
v___x_4528_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4528_, 0, v_ref_4524_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
if (v_isShared_4523_ == 0)
{
lean_ctor_set(v___x_4522_, 0, v___x_4528_);
v___x_4530_ = v___x_4522_;
goto v_reusejp_4529_;
}
else
{
lean_object* v_reuseFailAlloc_4531_; 
v_reuseFailAlloc_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4531_, 0, v___x_4528_);
v___x_4530_ = v_reuseFailAlloc_4531_;
goto v_reusejp_4529_;
}
v_reusejp_4529_:
{
return v___x_4530_;
}
}
}
}
v___jp_4533_:
{
lean_object* v___x_4544_; 
lean_inc_ref(v___y_4535_);
v___x_4544_ = l_Lean_Environment_addConstAsync(v___y_4535_, v___y_4539_, v___y_4542_, v___y_4543_, v___x_4458_, v_hasTrace_3804_);
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v_mainEnv_4546_; lean_object* v_asyncEnv_4547_; lean_object* v___f_4548_; lean_object* v___f_4549_; lean_object* v___x_4550_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
lean_inc_n(v_a_4545_, 3);
lean_dec_ref_known(v___x_4544_, 1);
v_mainEnv_4546_ = lean_ctor_get(v_a_4545_, 0);
lean_inc_ref(v_mainEnv_4546_);
v_asyncEnv_4547_ = lean_ctor_get(v_a_4545_, 1);
lean_inc_ref_n(v_asyncEnv_4547_, 2);
lean_inc_ref(v___y_4534_);
lean_inc(v___y_4536_);
v___f_4548_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4548_, 0, v___y_4536_);
lean_closure_set(v___f_4548_, 1, v_a_4545_);
lean_closure_set(v___f_4548_, 2, v___y_4534_);
lean_inc(v_decl_3744_);
v___f_4549_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4549_, 0, v_asyncEnv_4547_);
lean_closure_set(v___f_4549_, 1, v_a_4545_);
lean_closure_set(v___f_4549_, 2, v_decl_3744_);
v___x_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4550_, 0, v___y_4537_);
if (lean_obj_tag(v___y_4541_) == 0)
{
lean_inc_ref(v___x_4550_);
v___y_4460_ = v___f_4548_;
v___y_4461_ = v_mainEnv_4546_;
v___y_4462_ = v_a_4545_;
v___y_4463_ = v___f_4549_;
v___y_4464_ = v___y_4535_;
v___y_4465_ = v___y_4538_;
v___y_4466_ = v_asyncEnv_4547_;
v___y_4467_ = v___x_4550_;
v___y_4468_ = v___y_4540_;
v___y_4469_ = v___x_4550_;
goto v___jp_4459_;
}
else
{
v___y_4460_ = v___f_4548_;
v___y_4461_ = v_mainEnv_4546_;
v___y_4462_ = v_a_4545_;
v___y_4463_ = v___f_4549_;
v___y_4464_ = v___y_4535_;
v___y_4465_ = v___y_4538_;
v___y_4466_ = v_asyncEnv_4547_;
v___y_4467_ = v___x_4550_;
v___y_4468_ = v___y_4540_;
v___y_4469_ = v___y_4541_;
goto v___jp_4459_;
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4563_; 
lean_dec(v___y_4541_);
lean_dec_ref(v___y_4537_);
lean_dec_ref(v___y_4535_);
lean_dec(v_decl_3744_);
v_a_4551_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4563_ == 0)
{
v___x_4553_ = v___x_4544_;
v_isShared_4554_ = v_isSharedCheck_4563_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4544_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4563_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v_ref_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4561_; 
v_ref_4555_ = lean_ctor_get(v___y_4538_, 2);
v___x_4556_ = lean_io_error_to_string(v_a_4551_);
v___x_4557_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4556_);
v___x_4558_ = l_Lean_MessageData_ofFormat(v___x_4557_);
lean_inc(v_ref_4555_);
v___x_4559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4559_, 0, v_ref_4555_);
lean_ctor_set(v___x_4559_, 1, v___x_4558_);
if (v_isShared_4554_ == 0)
{
lean_ctor_set(v___x_4553_, 0, v___x_4559_);
v___x_4561_ = v___x_4553_;
goto v_reusejp_4560_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4559_);
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
v___jp_4564_:
{
lean_object* v___x_4571_; 
v___x_4571_ = lean_st_ref_get(v___y_4570_);
if (lean_obj_tag(v_exportedInfo_x3f_4568_) == 0)
{
lean_object* v_env_4572_; lean_object* v___x_4573_; 
v_env_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc_ref(v_env_4572_);
lean_dec(v___x_4571_);
v___x_4573_ = lean_box(0);
v___y_4534_ = v___y_4569_;
v___y_4535_ = v_env_4572_;
v___y_4536_ = v___y_4570_;
v___y_4537_ = v___y_4565_;
v___y_4538_ = v___y_4569_;
v___y_4539_ = v___y_4566_;
v___y_4540_ = v___y_4570_;
v___y_4541_ = v_exportedInfo_x3f_4568_;
v___y_4542_ = v___y_4567_;
v___y_4543_ = v___x_4573_;
goto v___jp_4533_;
}
else
{
lean_object* v_env_4574_; lean_object* v_val_4575_; uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; 
v_env_4574_ = lean_ctor_get(v___x_4571_, 0);
lean_inc_ref(v_env_4574_);
lean_dec(v___x_4571_);
v_val_4575_ = lean_ctor_get(v_exportedInfo_x3f_4568_, 0);
v___x_4576_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4575_);
v___x_4577_ = lean_box(v___x_4576_);
v___x_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4578_, 0, v___x_4577_);
v___y_4534_ = v___y_4569_;
v___y_4535_ = v_env_4574_;
v___y_4536_ = v___y_4570_;
v___y_4537_ = v___y_4565_;
v___y_4538_ = v___y_4569_;
v___y_4539_ = v___y_4566_;
v___y_4540_ = v___y_4570_;
v___y_4541_ = v_exportedInfo_x3f_4568_;
v___y_4542_ = v___y_4567_;
v___y_4543_ = v___x_4578_;
goto v___jp_4533_;
}
}
v___jp_4579_:
{
lean_object* v___x_4585_; 
lean_inc_ref(v___y_4580_);
v___x_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4585_, 0, v___y_4580_);
v___y_4565_ = v___y_4580_;
v___y_4566_ = v___y_4581_;
v___y_4567_ = v___y_4582_;
v_exportedInfo_x3f_4568_ = v___x_4585_;
v___y_4569_ = v___y_4583_;
v___y_4570_ = v___y_4584_;
goto v___jp_4564_;
}
v___jp_4586_:
{
lean_object* v___x_4592_; 
lean_inc_ref(v___y_4587_);
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v___y_4587_);
v___y_4565_ = v___y_4587_;
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___y_4589_;
v_exportedInfo_x3f_4568_ = v___x_4592_;
v___y_4569_ = v___y_4590_;
v___y_4570_ = v___y_4591_;
goto v___jp_4564_;
}
}
else
{
goto v___jp_4305_;
}
v___jp_4158_:
{
lean_object* v___x_4162_; double v___x_4163_; double v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; 
v___x_4162_ = lean_io_get_num_heartbeats();
v___x_4163_ = lean_float_of_nat(v___y_4160_);
v___x_4164_ = lean_float_of_nat(v___x_4162_);
v___x_4165_ = lean_box_float(v___x_4163_);
v___x_4166_ = lean_box_float(v___x_4164_);
v___x_4167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4168_, 0, v_a_4161_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3941_, v_hasTrace_3804_, v___x_4155_, v_options_3802_, v___x_4157_, v___y_4159_, v___f_4154_, v___x_4168_, v_a_3746_, v_a_3747_);
return v___x_4169_;
}
v___jp_4170_:
{
if (lean_obj_tag(v___y_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
v_a_4174_ = lean_ctor_get(v___y_4173_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___y_4173_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___y_4173_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___y_4173_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
lean_ctor_set_tag(v___x_4176_, 1);
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
v___y_4159_ = v___y_4171_;
v___y_4160_ = v___y_4172_;
v_a_4161_ = v___x_4179_;
goto v___jp_4158_;
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
v_a_4182_ = lean_ctor_get(v___y_4173_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___y_4173_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___y_4173_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___y_4173_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
lean_ctor_set_tag(v___x_4184_, 0);
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
v___y_4159_ = v___y_4171_;
v___y_4160_ = v___y_4172_;
v_a_4161_ = v___x_4187_;
goto v___jp_4158_;
}
}
}
}
v___jp_4190_:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4196_ = lean_apply_5(v___y_4194_, v___x_4195_, v___y_4191_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4171_ = v___y_4192_;
v___y_4172_ = v___y_4193_;
v___y_4173_ = v___x_4196_;
goto v___jp_4170_;
}
v___jp_4197_:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4203_ = lean_apply_5(v___y_4201_, v___x_4202_, v___y_4198_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4171_ = v___y_4199_;
v___y_4172_ = v___y_4200_;
v___y_4173_ = v___x_4203_;
goto v___jp_4170_;
}
v___jp_4204_:
{
lean_object* v___x_4208_; double v___x_4209_; double v___x_4210_; double v___x_4211_; double v___x_4212_; double v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4208_ = lean_io_mono_nanos_now();
v___x_4209_ = lean_float_of_nat(v___y_4206_);
v___x_4210_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4211_ = lean_float_div(v___x_4209_, v___x_4210_);
v___x_4212_ = lean_float_of_nat(v___x_4208_);
v___x_4213_ = lean_float_div(v___x_4212_, v___x_4210_);
v___x_4214_ = lean_box_float(v___x_4211_);
v___x_4215_ = lean_box_float(v___x_4213_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v_a_4207_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3941_, v_hasTrace_3804_, v___x_4155_, v_options_3802_, v___x_4157_, v___y_4205_, v___f_4154_, v___x_4217_, v_a_3746_, v_a_3747_);
return v___x_4218_;
}
v___jp_4219_:
{
if (lean_obj_tag(v___y_4222_) == 0)
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
v_a_4223_ = lean_ctor_get(v___y_4222_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___y_4222_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___y_4222_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___y_4222_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
lean_ctor_set_tag(v___x_4225_, 1);
v___x_4228_ = v___x_4225_;
goto v_reusejp_4227_;
}
else
{
lean_object* v_reuseFailAlloc_4229_; 
v_reuseFailAlloc_4229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4229_, 0, v_a_4223_);
v___x_4228_ = v_reuseFailAlloc_4229_;
goto v_reusejp_4227_;
}
v_reusejp_4227_:
{
v___y_4205_ = v___y_4220_;
v___y_4206_ = v___y_4221_;
v_a_4207_ = v___x_4228_;
goto v___jp_4204_;
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
v_a_4231_ = lean_ctor_get(v___y_4222_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___y_4222_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___y_4222_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___y_4222_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
lean_ctor_set_tag(v___x_4233_, 0);
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
v___y_4205_ = v___y_4220_;
v___y_4206_ = v___y_4221_;
v_a_4207_ = v___x_4236_;
goto v___jp_4204_;
}
}
}
}
v___jp_4239_:
{
lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4244_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4245_ = lean_apply_5(v___y_4242_, v___x_4244_, v___y_4240_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4241_;
v___y_4221_ = v___y_4243_;
v___y_4222_ = v___x_4245_;
goto v___jp_4219_;
}
v___jp_4246_:
{
if (v___x_4157_ == 0)
{
lean_object* v___x_4251_; lean_object* v___x_4252_; 
lean_dec_ref(v___y_4248_);
v___x_4251_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4252_ = lean_apply_4(v___y_4249_, v___x_4251_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4250_;
v___y_4222_ = v___x_4252_;
goto v___jp_4219_;
}
else
{
lean_object* v_toConstantVal_4253_; lean_object* v_name_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; 
v_toConstantVal_4253_ = lean_ctor_get(v___y_4248_, 0);
lean_inc_ref(v_toConstantVal_4253_);
lean_dec_ref(v___y_4248_);
v_name_4254_ = lean_ctor_get(v_toConstantVal_4253_, 0);
lean_inc(v_name_4254_);
lean_dec_ref(v_toConstantVal_4253_);
v___x_4255_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4256_ = l_Lean_MessageData_ofName(v_name_4254_);
v___x_4257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4257_, 0, v___x_4255_);
lean_ctor_set(v___x_4257_, 1, v___x_4256_);
v___x_4258_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4259_, 0, v___x_4257_);
lean_ctor_set(v___x_4259_, 1, v___x_4258_);
v___x_4260_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4259_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4260_) == 0)
{
lean_object* v_a_4261_; lean_object* v___x_4262_; 
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
lean_inc(v_a_4261_);
lean_dec_ref_known(v___x_4260_, 1);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4262_ = lean_apply_4(v___y_4249_, v_a_4261_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4250_;
v___y_4222_ = v___x_4262_;
goto v___jp_4219_;
}
else
{
lean_dec_ref(v___y_4249_);
v___y_4220_ = v___y_4247_;
v___y_4221_ = v___y_4250_;
v___y_4222_ = v___x_4260_;
goto v___jp_4219_;
}
}
}
v___jp_4263_:
{
lean_object* v___x_4273_; uint8_t v_isModule_4274_; 
v___x_4273_ = l_Lean_Environment_header(v___y_4271_);
lean_dec_ref(v___y_4271_);
v_isModule_4274_ = lean_ctor_get_uint8(v___x_4273_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4273_);
if (v_isModule_4274_ == 0)
{
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
lean_dec_ref(v___y_4265_);
v___y_4240_ = v___y_4264_;
v___y_4241_ = v___y_4266_;
v___y_4242_ = v___y_4270_;
v___y_4243_ = v___y_4272_;
goto v___jp_4239_;
}
else
{
uint8_t v_isExporting_4275_; 
v_isExporting_4275_ = lean_ctor_get_uint8(v___y_4265_, sizeof(void*)*8);
lean_dec_ref(v___y_4265_);
if (v_isExporting_4275_ == 0)
{
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4264_);
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4269_;
v___y_4249_ = v___y_4268_;
v___y_4250_ = v___y_4272_;
goto v___jp_4246_;
}
else
{
if (v___y_4267_ == 0)
{
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4268_);
v___y_4240_ = v___y_4264_;
v___y_4241_ = v___y_4266_;
v___y_4242_ = v___y_4270_;
v___y_4243_ = v___y_4272_;
goto v___jp_4239_;
}
else
{
lean_dec_ref(v___y_4270_);
lean_dec(v___y_4264_);
v___y_4247_ = v___y_4266_;
v___y_4248_ = v___y_4269_;
v___y_4249_ = v___y_4268_;
v___y_4250_ = v___y_4272_;
goto v___jp_4246_;
}
}
}
}
v___jp_4276_:
{
lean_object* v___x_4281_; lean_object* v___x_4282_; 
v___x_4281_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4282_ = lean_apply_5(v___y_4278_, v___x_4281_, v___y_4277_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4279_;
v___y_4221_ = v___y_4280_;
v___y_4222_ = v___x_4282_;
goto v___jp_4219_;
}
v___jp_4283_:
{
lean_object* v___x_4291_; uint8_t v_isModule_4292_; 
v___x_4291_ = l_Lean_Environment_header(v___y_4285_);
lean_dec_ref(v___y_4285_);
v_isModule_4292_ = lean_ctor_get_uint8(v___x_4291_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4291_);
if (v_isModule_4292_ == 0)
{
lean_dec_ref(v___y_4289_);
lean_dec_ref(v___y_4288_);
v___y_4277_ = v___y_4284_;
v___y_4278_ = v___y_4286_;
v___y_4279_ = v___y_4287_;
v___y_4280_ = v___y_4290_;
goto v___jp_4276_;
}
else
{
lean_dec_ref(v___y_4286_);
lean_dec(v___y_4284_);
if (v___x_4157_ == 0)
{
lean_object* v___x_4293_; lean_object* v___x_4294_; 
lean_dec_ref(v___y_4289_);
v___x_4293_ = lean_box(0);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4294_ = lean_apply_4(v___y_4288_, v___x_4293_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4287_;
v___y_4221_ = v___y_4290_;
v___y_4222_ = v___x_4294_;
goto v___jp_4219_;
}
else
{
lean_object* v_toConstantVal_4295_; lean_object* v_name_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_toConstantVal_4295_ = lean_ctor_get(v___y_4289_, 0);
lean_inc_ref(v_toConstantVal_4295_);
lean_dec_ref(v___y_4289_);
v_name_4296_ = lean_ctor_get(v_toConstantVal_4295_, 0);
lean_inc(v_name_4296_);
lean_dec_ref(v_toConstantVal_4295_);
v___x_4297_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4298_ = l_Lean_MessageData_ofName(v_name_4296_);
v___x_4299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4299_, 0, v___x_4297_);
lean_ctor_set(v___x_4299_, 1, v___x_4298_);
v___x_4300_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4299_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4301_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
lean_inc(v_a_3747_);
lean_inc_ref(v_a_3746_);
v___x_4304_ = lean_apply_4(v___y_4288_, v_a_4303_, v_a_3746_, v_a_3747_, lean_box(0));
v___y_4220_ = v___y_4287_;
v___y_4221_ = v___y_4290_;
v___y_4222_ = v___x_4304_;
goto v___jp_4219_;
}
else
{
lean_dec_ref(v___y_4288_);
v___y_4220_ = v___y_4287_;
v___y_4221_ = v___y_4290_;
v___y_4222_ = v___x_4302_;
goto v___jp_4219_;
}
}
}
}
v___jp_4305_:
{
lean_object* v___x_4306_; lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4456_; 
v___x_4306_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3747_);
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4309_ = v___x_4306_;
v_isShared_4310_ = v_isSharedCheck_4456_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___x_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4456_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4311_; uint8_t v___x_4312_; 
v___x_4311_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4312_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3802_, v___x_4311_);
if (v___x_4312_ == 0)
{
lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v_env_4315_; lean_object* v_nextMacroScope_4316_; lean_object* v_ngen_4317_; lean_object* v_auxDeclNGen_4318_; lean_object* v_traceState_4319_; lean_object* v_messages_4320_; lean_object* v_infoState_4321_; lean_object* v_snapshotTasks_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4370_; 
v___x_4313_ = lean_io_mono_nanos_now();
v___x_4314_ = lean_st_ref_take(v_a_3747_);
v_env_4315_ = lean_ctor_get(v___x_4314_, 0);
v_nextMacroScope_4316_ = lean_ctor_get(v___x_4314_, 1);
v_ngen_4317_ = lean_ctor_get(v___x_4314_, 2);
v_auxDeclNGen_4318_ = lean_ctor_get(v___x_4314_, 3);
v_traceState_4319_ = lean_ctor_get(v___x_4314_, 4);
v_messages_4320_ = lean_ctor_get(v___x_4314_, 6);
v_infoState_4321_ = lean_ctor_get(v___x_4314_, 7);
v_snapshotTasks_4322_ = lean_ctor_get(v___x_4314_, 8);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4370_ == 0)
{
lean_object* v_unused_4371_; 
v_unused_4371_ = lean_ctor_get(v___x_4314_, 5);
lean_dec(v_unused_4371_);
v___x_4324_ = v___x_4314_;
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_snapshotTasks_4322_);
lean_inc(v_infoState_4321_);
lean_inc(v_messages_4320_);
lean_inc(v_traceState_4319_);
lean_inc(v_auxDeclNGen_4318_);
lean_inc(v_ngen_4317_);
lean_inc(v_nextMacroScope_4316_);
lean_inc(v_env_4315_);
lean_dec(v___x_4314_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4370_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4330_; 
lean_inc(v_decl_3744_);
v___x_4326_ = l_Lean_Declaration_getNames(v_decl_3744_);
v___x_4327_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4315_, v___x_4326_);
v___x_4328_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4325_ == 0)
{
lean_ctor_set(v___x_4324_, 5, v___x_4328_);
lean_ctor_set(v___x_4324_, 0, v___x_4327_);
v___x_4330_ = v___x_4324_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4327_);
lean_ctor_set(v_reuseFailAlloc_4369_, 1, v_nextMacroScope_4316_);
lean_ctor_set(v_reuseFailAlloc_4369_, 2, v_ngen_4317_);
lean_ctor_set(v_reuseFailAlloc_4369_, 3, v_auxDeclNGen_4318_);
lean_ctor_set(v_reuseFailAlloc_4369_, 4, v_traceState_4319_);
lean_ctor_set(v_reuseFailAlloc_4369_, 5, v___x_4328_);
lean_ctor_set(v_reuseFailAlloc_4369_, 6, v_messages_4320_);
lean_ctor_set(v_reuseFailAlloc_4369_, 7, v_infoState_4321_);
lean_ctor_set(v_reuseFailAlloc_4369_, 8, v_snapshotTasks_4322_);
v___x_4330_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
lean_object* v___x_4331_; lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___f_4335_; 
v___x_4331_ = lean_st_ref_put(v_a_3747_, v___x_4330_);
v___x_4332_ = lean_box(0);
v___x_4333_ = lean_box(v_hasTrace_3804_);
v___x_4334_ = lean_box(v___x_4312_);
lean_inc(v_decl_3744_);
v___f_4335_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4335_, 0, v_decl_3744_);
lean_closure_set(v___f_4335_, 1, v___x_4333_);
lean_closure_set(v___f_4335_, 2, v___x_4334_);
lean_closure_set(v___f_4335_, 3, v___x_4328_);
lean_closure_set(v___f_4335_, 4, v_cls_3941_);
lean_closure_set(v___f_4335_, 5, v___x_4332_);
switch(lean_obj_tag(v_decl_3744_))
{
case 2:
{
lean_object* v_val_4336_; lean_object* v___x_4337_; lean_object* v_env_4338_; lean_object* v___f_4339_; lean_object* v___x_4340_; lean_object* v___f_4341_; 
lean_del_object(v___x_4309_);
v_val_4336_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref_n(v_val_4336_, 3);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4337_ = lean_st_ref_get(v_a_3747_);
v_env_4338_ = lean_ctor_get(v___x_4337_, 0);
lean_inc_ref(v_env_4338_);
lean_dec(v___x_4337_);
v___f_4339_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4339_, 0, v_val_4336_);
lean_closure_set(v___f_4339_, 1, v___f_4335_);
v___x_4340_ = lean_box(v___x_4312_);
lean_inc_ref(v___f_4339_);
v___f_4341_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4341_, 0, v_val_4336_);
lean_closure_set(v___f_4341_, 1, v___x_4340_);
lean_closure_set(v___f_4341_, 2, v___f_4339_);
if (v_forceExpose_3745_ == 0)
{
v___y_4284_ = v___x_4332_;
v___y_4285_ = v_env_4338_;
v___y_4286_ = v___f_4339_;
v___y_4287_ = v_a_4307_;
v___y_4288_ = v___f_4341_;
v___y_4289_ = v_val_4336_;
v___y_4290_ = v___x_4313_;
goto v___jp_4283_;
}
else
{
if (v___x_4312_ == 0)
{
lean_dec_ref(v___f_4341_);
lean_dec_ref(v_env_4338_);
lean_dec_ref(v_val_4336_);
v___y_4277_ = v___x_4332_;
v___y_4278_ = v___f_4339_;
v___y_4279_ = v_a_4307_;
v___y_4280_ = v___x_4313_;
goto v___jp_4276_;
}
else
{
v___y_4284_ = v___x_4332_;
v___y_4285_ = v_env_4338_;
v___y_4286_ = v___f_4339_;
v___y_4287_ = v_a_4307_;
v___y_4288_ = v___f_4341_;
v___y_4289_ = v_val_4336_;
v___y_4290_ = v___x_4313_;
goto v___jp_4283_;
}
}
}
case 1:
{
lean_object* v_val_4342_; lean_object* v___x_4343_; 
lean_del_object(v___x_4309_);
v_val_4342_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref(v_val_4342_);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4343_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4335_, v___x_4312_, v_cls_3941_, v___x_4332_, v_forceExpose_3745_, v_val_4342_, v_a_3746_, v_a_3747_);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4343_;
goto v___jp_4219_;
}
case 5:
{
lean_object* v_defns_4344_; 
lean_del_object(v___x_4309_);
v_defns_4344_ = lean_ctor_get(v_decl_3744_, 0);
if (lean_obj_tag(v_defns_4344_) == 1)
{
lean_object* v_tail_4345_; 
v_tail_4345_ = lean_ctor_get(v_defns_4344_, 1);
if (lean_obj_tag(v_tail_4345_) == 0)
{
lean_object* v_head_4346_; lean_object* v___x_4347_; 
lean_inc_ref(v_defns_4344_);
lean_dec_ref_known(v_decl_3744_, 1);
v_head_4346_ = lean_ctor_get(v_defns_4344_, 0);
lean_inc(v_head_4346_);
lean_dec_ref_known(v_defns_4344_, 2);
v___x_4347_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4335_, v___x_4312_, v_cls_3941_, v___x_4332_, v_forceExpose_3745_, v_head_4346_, v_a_3746_, v_a_3747_);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4347_;
goto v___jp_4219_;
}
else
{
lean_object* v___x_4348_; 
lean_dec_ref(v___f_4335_);
lean_inc_ref(v_decl_3744_);
v___x_4348_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec_ref_known(v_decl_3744_, 1);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4348_;
goto v___jp_4219_;
}
}
else
{
lean_object* v___x_4349_; 
lean_dec_ref(v___f_4335_);
lean_inc_ref(v_decl_3744_);
v___x_4349_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec_ref_known(v_decl_3744_, 1);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4349_;
goto v___jp_4219_;
}
}
case 3:
{
lean_object* v_val_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; lean_object* v_env_4353_; lean_object* v_env_4354_; lean_object* v___f_4355_; lean_object* v___f_4356_; 
lean_del_object(v___x_4309_);
v_val_4350_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref_n(v_val_4350_, 3);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4351_ = lean_st_ref_get(v_a_3747_);
v___x_4352_ = lean_st_ref_get(v_a_3747_);
v_env_4353_ = lean_ctor_get(v___x_4351_, 0);
lean_inc_ref(v_env_4353_);
lean_dec(v___x_4351_);
v_env_4354_ = lean_ctor_get(v___x_4352_, 0);
lean_inc_ref(v_env_4354_);
lean_dec(v___x_4352_);
v___f_4355_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4355_, 0, v_val_4350_);
lean_closure_set(v___f_4355_, 1, v___f_4335_);
lean_inc_ref(v___f_4355_);
v___f_4356_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4356_, 0, v_val_4350_);
lean_closure_set(v___f_4356_, 1, v___f_4355_);
if (v_forceExpose_3745_ == 0)
{
v___y_4264_ = v___x_4332_;
v___y_4265_ = v_env_4354_;
v___y_4266_ = v_a_4307_;
v___y_4267_ = v___x_4312_;
v___y_4268_ = v___f_4356_;
v___y_4269_ = v_val_4350_;
v___y_4270_ = v___f_4355_;
v___y_4271_ = v_env_4353_;
v___y_4272_ = v___x_4313_;
goto v___jp_4263_;
}
else
{
if (v___x_4312_ == 0)
{
lean_dec_ref(v___f_4356_);
lean_dec_ref(v_env_4354_);
lean_dec_ref(v_env_4353_);
lean_dec_ref(v_val_4350_);
v___y_4240_ = v___x_4332_;
v___y_4241_ = v_a_4307_;
v___y_4242_ = v___f_4355_;
v___y_4243_ = v___x_4313_;
goto v___jp_4239_;
}
else
{
v___y_4264_ = v___x_4332_;
v___y_4265_ = v_env_4354_;
v___y_4266_ = v_a_4307_;
v___y_4267_ = v___x_4312_;
v___y_4268_ = v___f_4356_;
v___y_4269_ = v_val_4350_;
v___y_4270_ = v___f_4355_;
v___y_4271_ = v_env_4353_;
v___y_4272_ = v___x_4313_;
goto v___jp_4263_;
}
}
}
case 0:
{
lean_object* v_val_4357_; lean_object* v_toConstantVal_4358_; lean_object* v_name_4359_; lean_object* v___x_4361_; 
lean_dec_ref(v___f_4335_);
v_val_4357_ = lean_ctor_get(v_decl_3744_, 0);
v_toConstantVal_4358_ = lean_ctor_get(v_val_4357_, 0);
v_name_4359_ = lean_ctor_get(v_toConstantVal_4358_, 0);
lean_inc_ref(v_val_4357_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v_val_4357_);
v___x_4361_ = v___x_4309_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4367_; 
v_reuseFailAlloc_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4367_, 0, v_val_4357_);
v___x_4361_ = v_reuseFailAlloc_4367_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
uint8_t v___x_4362_; lean_object* v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; 
v___x_4362_ = 2;
v___x_4363_ = lean_box(v___x_4362_);
v___x_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4361_);
lean_ctor_set(v___x_4364_, 1, v___x_4363_);
lean_inc(v_name_4359_);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v_name_4359_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
v___x_4366_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3744_, v_hasTrace_3804_, v___x_4312_, v___x_4328_, v_cls_3941_, v___x_4332_, v___x_4365_, v___x_4332_, v_a_3746_, v_a_3747_);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4366_;
goto v___jp_4219_;
}
}
default: 
{
lean_object* v___x_4368_; 
lean_dec_ref(v___f_4335_);
lean_del_object(v___x_4309_);
lean_inc(v_decl_3744_);
v___x_4368_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec(v_decl_3744_);
v___y_4220_ = v_a_4307_;
v___y_4221_ = v___x_4313_;
v___y_4222_ = v___x_4368_;
goto v___jp_4219_;
}
}
}
}
}
else
{
lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v_env_4374_; lean_object* v_nextMacroScope_4375_; lean_object* v_ngen_4376_; lean_object* v_auxDeclNGen_4377_; lean_object* v_traceState_4378_; lean_object* v_messages_4379_; lean_object* v_infoState_4380_; lean_object* v_snapshotTasks_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4454_; 
v___x_4372_ = lean_io_get_num_heartbeats();
v___x_4373_ = lean_st_ref_take(v_a_3747_);
v_env_4374_ = lean_ctor_get(v___x_4373_, 0);
v_nextMacroScope_4375_ = lean_ctor_get(v___x_4373_, 1);
v_ngen_4376_ = lean_ctor_get(v___x_4373_, 2);
v_auxDeclNGen_4377_ = lean_ctor_get(v___x_4373_, 3);
v_traceState_4378_ = lean_ctor_get(v___x_4373_, 4);
v_messages_4379_ = lean_ctor_get(v___x_4373_, 6);
v_infoState_4380_ = lean_ctor_get(v___x_4373_, 7);
v_snapshotTasks_4381_ = lean_ctor_get(v___x_4373_, 8);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4454_ == 0)
{
lean_object* v_unused_4455_; 
v_unused_4455_ = lean_ctor_get(v___x_4373_, 5);
lean_dec(v_unused_4455_);
v___x_4383_ = v___x_4373_;
v_isShared_4384_ = v_isSharedCheck_4454_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_snapshotTasks_4381_);
lean_inc(v_infoState_4380_);
lean_inc(v_messages_4379_);
lean_inc(v_traceState_4378_);
lean_inc(v_auxDeclNGen_4377_);
lean_inc(v_ngen_4376_);
lean_inc(v_nextMacroScope_4375_);
lean_inc(v_env_4374_);
lean_dec(v___x_4373_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4454_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4385_; lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4389_; 
lean_inc(v_decl_3744_);
v___x_4385_ = l_Lean_Declaration_getNames(v_decl_3744_);
v___x_4386_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4374_, v___x_4385_);
v___x_4387_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4384_ == 0)
{
lean_ctor_set(v___x_4383_, 5, v___x_4387_);
lean_ctor_set(v___x_4383_, 0, v___x_4386_);
v___x_4389_ = v___x_4383_;
goto v_reusejp_4388_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v___x_4386_);
lean_ctor_set(v_reuseFailAlloc_4453_, 1, v_nextMacroScope_4375_);
lean_ctor_set(v_reuseFailAlloc_4453_, 2, v_ngen_4376_);
lean_ctor_set(v_reuseFailAlloc_4453_, 3, v_auxDeclNGen_4377_);
lean_ctor_set(v_reuseFailAlloc_4453_, 4, v_traceState_4378_);
lean_ctor_set(v_reuseFailAlloc_4453_, 5, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4453_, 6, v_messages_4379_);
lean_ctor_set(v_reuseFailAlloc_4453_, 7, v_infoState_4380_);
lean_ctor_set(v_reuseFailAlloc_4453_, 8, v_snapshotTasks_4381_);
v___x_4389_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4388_;
}
v_reusejp_4388_:
{
lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___f_4393_; 
v___x_4390_ = lean_st_ref_put(v_a_3747_, v___x_4389_);
v___x_4391_ = lean_box(0);
v___x_4392_ = lean_box(v___x_4312_);
lean_inc(v_decl_3744_);
v___f_4393_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4393_, 0, v_decl_3744_);
lean_closure_set(v___f_4393_, 1, v___x_4392_);
lean_closure_set(v___f_4393_, 2, v_cls_3941_);
lean_closure_set(v___f_4393_, 3, v___x_4387_);
lean_closure_set(v___f_4393_, 4, v___x_4391_);
switch(lean_obj_tag(v_decl_3744_))
{
case 2:
{
lean_object* v_val_4394_; lean_object* v___x_4395_; lean_object* v_env_4396_; lean_object* v___f_4397_; 
lean_del_object(v___x_4309_);
v_val_4394_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref_n(v_val_4394_, 2);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4395_ = lean_st_ref_get(v_a_3747_);
v_env_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc_ref(v_env_4396_);
lean_dec(v___x_4395_);
v___f_4397_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4397_, 0, v_val_4394_);
lean_closure_set(v___f_4397_, 1, v___f_4393_);
if (v_forceExpose_3745_ == 0)
{
if (v___x_4312_ == 0)
{
lean_dec_ref(v_env_4396_);
lean_dec_ref(v_val_4394_);
v___y_4198_ = v___x_4391_;
v___y_4199_ = v_a_4307_;
v___y_4200_ = v___x_4372_;
v___y_4201_ = v___f_4397_;
goto v___jp_4197_;
}
else
{
lean_object* v___x_4398_; uint8_t v_isModule_4399_; 
v___x_4398_ = l_Lean_Environment_header(v_env_4396_);
lean_dec_ref(v_env_4396_);
v_isModule_4399_ = lean_ctor_get_uint8(v___x_4398_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4398_);
if (v_isModule_4399_ == 0)
{
lean_dec_ref(v_val_4394_);
v___y_4198_ = v___x_4391_;
v___y_4199_ = v_a_4307_;
v___y_4200_ = v___x_4372_;
v___y_4201_ = v___f_4397_;
goto v___jp_4197_;
}
else
{
if (v___x_4157_ == 0)
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_box(0);
v___x_4401_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4394_, v_forceExpose_3745_, v___f_4397_, v___x_4400_, v_a_3746_, v_a_3747_);
lean_dec_ref(v_val_4394_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4401_;
goto v___jp_4170_;
}
else
{
lean_object* v_toConstantVal_4402_; lean_object* v_name_4403_; lean_object* v___x_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; 
v_toConstantVal_4402_ = lean_ctor_get(v_val_4394_, 0);
v_name_4403_ = lean_ctor_get(v_toConstantVal_4402_, 0);
v___x_4404_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4403_);
v___x_4405_ = l_Lean_MessageData_ofName(v_name_4403_);
v___x_4406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4404_);
lean_ctor_set(v___x_4406_, 1, v___x_4405_);
v___x_4407_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4408_, 0, v___x_4406_);
lean_ctor_set(v___x_4408_, 1, v___x_4407_);
v___x_4409_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4408_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4394_, v_forceExpose_3745_, v___f_4397_, v_a_4410_, v_a_3746_, v_a_3747_);
lean_dec_ref(v_val_4394_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4411_;
goto v___jp_4170_;
}
else
{
lean_dec_ref(v___f_4397_);
lean_dec_ref(v_val_4394_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4409_;
goto v___jp_4170_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4396_);
lean_dec_ref(v_val_4394_);
v___y_4198_ = v___x_4391_;
v___y_4199_ = v_a_4307_;
v___y_4200_ = v___x_4372_;
v___y_4201_ = v___f_4397_;
goto v___jp_4197_;
}
}
case 1:
{
lean_object* v_val_4412_; lean_object* v___x_4413_; 
lean_del_object(v___x_4309_);
v_val_4412_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref(v_val_4412_);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4413_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4393_, v_forceExpose_3745_, v___x_4312_, v___x_4391_, v_cls_3941_, v_val_4412_, v_a_3746_, v_a_3747_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4413_;
goto v___jp_4170_;
}
case 5:
{
lean_object* v_defns_4414_; 
lean_del_object(v___x_4309_);
v_defns_4414_ = lean_ctor_get(v_decl_3744_, 0);
if (lean_obj_tag(v_defns_4414_) == 1)
{
lean_object* v_tail_4415_; 
v_tail_4415_ = lean_ctor_get(v_defns_4414_, 1);
if (lean_obj_tag(v_tail_4415_) == 0)
{
lean_object* v_head_4416_; lean_object* v___x_4417_; 
lean_inc_ref(v_defns_4414_);
lean_dec_ref_known(v_decl_3744_, 1);
v_head_4416_ = lean_ctor_get(v_defns_4414_, 0);
lean_inc(v_head_4416_);
lean_dec_ref_known(v_defns_4414_, 2);
v___x_4417_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4393_, v_forceExpose_3745_, v___x_4312_, v___x_4391_, v_cls_3941_, v_head_4416_, v_a_3746_, v_a_3747_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4417_;
goto v___jp_4170_;
}
else
{
lean_object* v___x_4418_; 
lean_dec_ref(v___f_4393_);
lean_inc_ref(v_decl_3744_);
v___x_4418_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec_ref_known(v_decl_3744_, 1);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4418_;
goto v___jp_4170_;
}
}
else
{
lean_object* v___x_4419_; 
lean_dec_ref(v___f_4393_);
lean_inc_ref(v_decl_3744_);
v___x_4419_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec_ref_known(v_decl_3744_, 1);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4419_;
goto v___jp_4170_;
}
}
case 3:
{
lean_object* v_val_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v_env_4423_; lean_object* v_env_4424_; lean_object* v___f_4425_; 
lean_del_object(v___x_4309_);
v_val_4420_ = lean_ctor_get(v_decl_3744_, 0);
lean_inc_ref_n(v_val_4420_, 2);
lean_dec_ref_known(v_decl_3744_, 1);
v___x_4421_ = lean_st_ref_get(v_a_3747_);
v___x_4422_ = lean_st_ref_get(v_a_3747_);
v_env_4423_ = lean_ctor_get(v___x_4421_, 0);
lean_inc_ref(v_env_4423_);
lean_dec(v___x_4421_);
v_env_4424_ = lean_ctor_get(v___x_4422_, 0);
lean_inc_ref(v_env_4424_);
lean_dec(v___x_4422_);
v___f_4425_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4425_, 0, v_val_4420_);
lean_closure_set(v___f_4425_, 1, v___f_4393_);
if (v_forceExpose_3745_ == 0)
{
if (v___x_4312_ == 0)
{
lean_dec_ref(v_env_4424_);
lean_dec_ref(v_env_4423_);
lean_dec_ref(v_val_4420_);
v___y_4191_ = v___x_4391_;
v___y_4192_ = v_a_4307_;
v___y_4193_ = v___x_4372_;
v___y_4194_ = v___f_4425_;
goto v___jp_4190_;
}
else
{
lean_object* v___x_4426_; uint8_t v_isModule_4427_; 
v___x_4426_ = l_Lean_Environment_header(v_env_4423_);
lean_dec_ref(v_env_4423_);
v_isModule_4427_ = lean_ctor_get_uint8(v___x_4426_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4426_);
if (v_isModule_4427_ == 0)
{
lean_dec_ref(v_env_4424_);
lean_dec_ref(v_val_4420_);
v___y_4191_ = v___x_4391_;
v___y_4192_ = v_a_4307_;
v___y_4193_ = v___x_4372_;
v___y_4194_ = v___f_4425_;
goto v___jp_4190_;
}
else
{
uint8_t v_isExporting_4428_; 
v_isExporting_4428_ = lean_ctor_get_uint8(v_env_4424_, sizeof(void*)*8);
lean_dec_ref(v_env_4424_);
if (v_isExporting_4428_ == 0)
{
if (v___x_4157_ == 0)
{
lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4429_ = lean_box(0);
v___x_4430_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4420_, v___f_4425_, v___x_4429_, v_a_3746_, v_a_3747_);
lean_dec_ref(v_val_4420_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4430_;
goto v___jp_4170_;
}
else
{
lean_object* v_toConstantVal_4431_; lean_object* v_name_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; 
v_toConstantVal_4431_ = lean_ctor_get(v_val_4420_, 0);
v_name_4432_ = lean_ctor_get(v_toConstantVal_4431_, 0);
v___x_4433_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4432_);
v___x_4434_ = l_Lean_MessageData_ofName(v_name_4432_);
v___x_4435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4435_, 0, v___x_4433_);
lean_ctor_set(v___x_4435_, 1, v___x_4434_);
v___x_4436_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4437_, 0, v___x_4435_);
lean_ctor_set(v___x_4437_, 1, v___x_4436_);
v___x_4438_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3941_, v___x_4437_, v_a_3746_, v_a_3747_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4438_, 1);
v___x_4440_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4420_, v___f_4425_, v_a_4439_, v_a_3746_, v_a_3747_);
lean_dec_ref(v_val_4420_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4440_;
goto v___jp_4170_;
}
else
{
lean_dec_ref(v___f_4425_);
lean_dec_ref(v_val_4420_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4438_;
goto v___jp_4170_;
}
}
}
else
{
lean_dec_ref(v_val_4420_);
v___y_4191_ = v___x_4391_;
v___y_4192_ = v_a_4307_;
v___y_4193_ = v___x_4372_;
v___y_4194_ = v___f_4425_;
goto v___jp_4190_;
}
}
}
}
else
{
lean_dec_ref(v_env_4424_);
lean_dec_ref(v_env_4423_);
lean_dec_ref(v_val_4420_);
v___y_4191_ = v___x_4391_;
v___y_4192_ = v_a_4307_;
v___y_4193_ = v___x_4372_;
v___y_4194_ = v___f_4425_;
goto v___jp_4190_;
}
}
case 0:
{
lean_object* v_val_4441_; lean_object* v_toConstantVal_4442_; lean_object* v_name_4443_; lean_object* v___x_4445_; 
lean_dec_ref(v___f_4393_);
v_val_4441_ = lean_ctor_get(v_decl_3744_, 0);
v_toConstantVal_4442_ = lean_ctor_get(v_val_4441_, 0);
v_name_4443_ = lean_ctor_get(v_toConstantVal_4442_, 0);
lean_inc_ref(v_val_4441_);
if (v_isShared_4310_ == 0)
{
lean_ctor_set(v___x_4309_, 0, v_val_4441_);
v___x_4445_ = v___x_4309_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_val_4441_);
v___x_4445_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
uint8_t v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; 
v___x_4446_ = 2;
v___x_4447_ = lean_box(v___x_4446_);
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4445_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
lean_inc(v_name_4443_);
v___x_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4449_, 0, v_name_4443_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3744_, v___x_4312_, v_cls_3941_, v___x_4387_, v___x_4391_, v___x_4449_, v___x_4391_, v_a_3746_, v_a_3747_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4450_;
goto v___jp_4170_;
}
}
default: 
{
lean_object* v___x_4452_; 
lean_dec_ref(v___f_4393_);
lean_del_object(v___x_4309_);
lean_inc(v_decl_3744_);
v___x_4452_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3744_, v_cls_3941_, v_decl_3744_, v_a_3746_, v_a_3747_);
lean_dec(v_decl_3744_);
v___y_4171_ = v_a_4307_;
v___y_4172_ = v___x_4372_;
v___y_4173_ = v___x_4452_;
goto v___jp_4170_;
}
}
}
}
}
}
}
}
v___jp_3749_:
{
lean_object* v___x_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
v___x_3753_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3750_, v___y_3751_);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3753_);
if (v_isSharedCheck_3760_ == 0)
{
lean_object* v_unused_3761_; 
v_unused_3761_ = lean_ctor_get(v___x_3753_, 0);
lean_dec(v_unused_3761_);
v___x_3755_ = v___x_3753_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_dec(v___x_3753_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
lean_ctor_set(v___x_3755_, 0, v_a_3752_);
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3752_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
v___jp_3762_:
{
lean_object* v___x_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
v___x_3766_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3763_, v___y_3764_);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3766_);
if (v_isSharedCheck_3773_ == 0)
{
lean_object* v_unused_3774_; 
v_unused_3774_ = lean_ctor_get(v___x_3766_, 0);
lean_dec(v_unused_3774_);
v___x_3768_ = v___x_3766_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_dec(v___x_3766_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
lean_ctor_set_tag(v___x_3768_, 1);
lean_ctor_set(v___x_3768_, 0, v_a_3765_);
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3765_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
v___jp_3775_:
{
lean_object* v___x_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v___x_3779_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3776_, v___y_3777_);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3779_);
if (v_isSharedCheck_3786_ == 0)
{
lean_object* v_unused_3787_; 
v_unused_3787_ = lean_ctor_get(v___x_3779_, 0);
lean_dec(v_unused_3787_);
v___x_3781_ = v___x_3779_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_dec(v___x_3779_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
lean_ctor_set(v___x_3781_, 0, v_a_3778_);
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3778_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
v___jp_3788_:
{
lean_object* v___x_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
v___x_3792_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3789_, v___y_3790_);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3799_ == 0)
{
lean_object* v_unused_3800_; 
v_unused_3800_ = lean_ctor_get(v___x_3792_, 0);
lean_dec(v_unused_3800_);
v___x_3794_ = v___x_3792_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_dec(v___x_3792_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
lean_ctor_set_tag(v___x_3794_, 1);
lean_ctor_set(v___x_3794_, 0, v_a_3791_);
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3791_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
v___jp_3805_:
{
lean_object* v___x_3817_; 
lean_inc_ref(v___y_3815_);
v___x_3817_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3807_, v___y_3815_, v___y_3810_, v___y_3816_);
if (lean_obj_tag(v___x_3817_) == 0)
{
lean_object* v___x_3818_; lean_object* v___x_3820_; uint8_t v_isShared_3821_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref_known(v___x_3817_, 1);
lean_inc_ref(v___y_3809_);
v___x_3818_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3809_, v___y_3811_);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3865_ == 0)
{
lean_object* v_unused_3866_; 
v_unused_3866_ = lean_ctor_get(v___x_3818_, 0);
lean_dec(v_unused_3866_);
v___x_3820_ = v___x_3818_;
v_isShared_3821_ = v_isSharedCheck_3865_;
goto v_resetjp_3819_;
}
else
{
lean_dec(v___x_3818_);
v___x_3820_ = lean_box(0);
v_isShared_3821_ = v_isSharedCheck_3865_;
goto v_resetjp_3819_;
}
v_resetjp_3819_:
{
lean_object* v_toCold_3822_; lean_object* v_options_3823_; lean_object* v___x_3824_; uint8_t v___x_3825_; 
v_toCold_3822_ = lean_ctor_get(v___y_3806_, 0);
v_options_3823_ = lean_ctor_get(v_toCold_3822_, 2);
v___x_3824_ = l_Lean_Elab_async;
v___x_3825_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3823_, v___x_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; lean_object* v_r_3827_; 
lean_del_object(v___x_3820_);
lean_dec_ref(v___y_3813_);
lean_dec_ref(v___y_3812_);
v___x_3826_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3815_, v___y_3811_);
lean_dec_ref(v___x_3826_);
v_r_3827_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3744_, v___y_3806_, v___y_3811_);
if (lean_obj_tag(v_r_3827_) == 0)
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3837_; 
v_a_3828_ = lean_ctor_get(v_r_3827_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_r_3827_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3830_ = v_r_3827_;
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v_r_3827_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3837_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
lean_inc(v_a_3828_);
if (v_isShared_3831_ == 0)
{
lean_ctor_set_tag(v___x_3830_, 1);
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
lean_object* v___x_3834_; 
v___x_3834_ = lean_apply_2(v___y_3814_, v___x_3833_, lean_box(0));
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_dec_ref_known(v___x_3834_, 1);
v___y_3776_ = v___y_3809_;
v___y_3777_ = v___y_3811_;
v_a_3778_ = v_a_3828_;
goto v___jp_3775_;
}
else
{
lean_object* v_a_3835_; 
lean_dec(v_a_3828_);
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v___y_3789_ = v___y_3809_;
v___y_3790_ = v___y_3811_;
v_a_3791_ = v_a_3835_;
goto v___jp_3788_;
}
}
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; 
v_a_3838_ = lean_ctor_get(v_r_3827_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v_r_3827_, 1);
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_apply_2(v___y_3814_, v___x_3839_, lean_box(0));
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_dec_ref_known(v___x_3840_, 1);
v___y_3789_ = v___y_3809_;
v___y_3790_ = v___y_3811_;
v_a_3791_ = v_a_3838_;
goto v___jp_3788_;
}
else
{
lean_object* v_a_3841_; 
lean_dec(v_a_3838_);
v_a_3841_ = lean_ctor_get(v___x_3840_, 0);
lean_inc(v_a_3841_);
lean_dec_ref_known(v___x_3840_, 1);
v___y_3789_ = v___y_3809_;
v___y_3790_ = v___y_3811_;
v_a_3791_ = v_a_3841_;
goto v___jp_3788_;
}
}
}
else
{
lean_object* v___x_3842_; lean_object* v___x_3844_; 
lean_dec_ref(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v___y_3809_);
lean_dec(v_decl_3744_);
v___x_3842_ = l_IO_CancelToken_new();
if (v_isShared_3821_ == 0)
{
lean_ctor_set_tag(v___x_3820_, 1);
lean_ctor_set(v___x_3820_, 0, v___x_3842_);
v___x_3844_ = v___x_3820_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; 
v___x_3845_ = lean_unsigned_to_nat(0u);
v___x_3846_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3847_ = l_Lean_Name_toString(v___x_3846_, v___y_3808_);
lean_inc_ref(v___x_3844_);
v___x_3848_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3813_, v___x_3844_, v___x_3847_, v___y_3806_, v___y_3811_);
if (lean_obj_tag(v___x_3848_) == 0)
{
lean_object* v_a_3849_; lean_object* v_checked_3850_; lean_object* v___x_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_a_3849_ = lean_ctor_get(v___x_3848_, 0);
lean_inc(v_a_3849_);
lean_dec_ref_known(v___x_3848_, 1);
v_checked_3850_ = lean_ctor_get(v___y_3812_, 2);
lean_inc_ref(v_checked_3850_);
lean_dec_ref(v___y_3812_);
v___x_3851_ = lean_io_map_task(v_a_3849_, v_checked_3850_, v___x_3845_, v_hasTrace_3804_);
v___x_3852_ = lean_box(0);
v___x_3853_ = lean_box(2);
v___x_3854_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3854_, 0, v___x_3852_);
lean_ctor_set(v___x_3854_, 1, v___x_3853_);
lean_ctor_set(v___x_3854_, 2, v___x_3844_);
lean_ctor_set(v___x_3854_, 3, v___x_3851_);
v___x_3855_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3854_, v___y_3811_);
return v___x_3855_;
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v___x_3844_);
lean_dec_ref(v___y_3812_);
v_a_3856_ = lean_ctor_get(v___x_3848_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3848_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3848_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3848_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
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
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3879_; 
lean_dec_ref(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec_ref(v___y_3812_);
lean_dec_ref(v___y_3809_);
lean_dec(v_decl_3744_);
v_a_3867_ = lean_ctor_get(v___x_3817_, 0);
v_isSharedCheck_3879_ = !lean_is_exclusive(v___x_3817_);
if (v_isSharedCheck_3879_ == 0)
{
v___x_3869_ = v___x_3817_;
v_isShared_3870_ = v_isSharedCheck_3879_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3817_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3879_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v_ref_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3877_; 
v_ref_3871_ = lean_ctor_get(v___y_3806_, 2);
v___x_3872_ = lean_io_error_to_string(v_a_3867_);
v___x_3873_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3872_);
v___x_3874_ = l_Lean_MessageData_ofFormat(v___x_3873_);
lean_inc(v_ref_3871_);
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v_ref_3871_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
if (v_isShared_3870_ == 0)
{
lean_ctor_set(v___x_3869_, 0, v___x_3875_);
v___x_3877_ = v___x_3869_;
goto v_reusejp_3876_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3875_);
v___x_3877_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3876_;
}
v_reusejp_3876_:
{
return v___x_3877_;
}
}
}
}
v___jp_3880_:
{
uint8_t v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = 1;
lean_inc_ref(v___y_3883_);
v___x_3892_ = l_Lean_Environment_addConstAsync(v___y_3883_, v___y_3889_, v___y_3885_, v___y_3890_, v_hasTrace_3804_, v___x_3891_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v_mainEnv_3894_; lean_object* v_asyncEnv_3895_; lean_object* v___f_3896_; lean_object* v___f_3897_; lean_object* v___x_3898_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
lean_inc_n(v_a_3893_, 3);
lean_dec_ref_known(v___x_3892_, 1);
v_mainEnv_3894_ = lean_ctor_get(v_a_3893_, 0);
lean_inc_ref(v_mainEnv_3894_);
v_asyncEnv_3895_ = lean_ctor_get(v_a_3893_, 1);
lean_inc_ref_n(v_asyncEnv_3895_, 2);
lean_inc_ref(v___y_3881_);
lean_inc(v___y_3882_);
v___f_3896_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3896_, 0, v___y_3882_);
lean_closure_set(v___f_3896_, 1, v_a_3893_);
lean_closure_set(v___f_3896_, 2, v___y_3881_);
lean_inc(v_decl_3744_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3897_, 0, v_asyncEnv_3895_);
lean_closure_set(v___f_3897_, 1, v_a_3893_);
lean_closure_set(v___f_3897_, 2, v_decl_3744_);
v___x_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3898_, 0, v___y_3886_);
if (lean_obj_tag(v___y_3888_) == 0)
{
lean_inc_ref(v___x_3898_);
v___y_3806_ = v___y_3884_;
v___y_3807_ = v_a_3893_;
v___y_3808_ = v___x_3891_;
v___y_3809_ = v_mainEnv_3894_;
v___y_3810_ = v___x_3898_;
v___y_3811_ = v___y_3887_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___f_3897_;
v___y_3814_ = v___f_3896_;
v___y_3815_ = v_asyncEnv_3895_;
v___y_3816_ = v___x_3898_;
goto v___jp_3805_;
}
else
{
v___y_3806_ = v___y_3884_;
v___y_3807_ = v_a_3893_;
v___y_3808_ = v___x_3891_;
v___y_3809_ = v_mainEnv_3894_;
v___y_3810_ = v___x_3898_;
v___y_3811_ = v___y_3887_;
v___y_3812_ = v___y_3883_;
v___y_3813_ = v___f_3897_;
v___y_3814_ = v___f_3896_;
v___y_3815_ = v_asyncEnv_3895_;
v___y_3816_ = v___y_3888_;
goto v___jp_3805_;
}
}
else
{
lean_object* v_a_3899_; lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3911_; 
lean_dec(v___y_3888_);
lean_dec_ref(v___y_3886_);
lean_dec_ref(v___y_3883_);
lean_dec(v_decl_3744_);
v_a_3899_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3901_ = v___x_3892_;
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
else
{
lean_inc(v_a_3899_);
lean_dec(v___x_3892_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v_ref_3903_; lean_object* v___x_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3909_; 
v_ref_3903_ = lean_ctor_get(v___y_3884_, 2);
v___x_3904_ = lean_io_error_to_string(v_a_3899_);
v___x_3905_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
v___x_3906_ = l_Lean_MessageData_ofFormat(v___x_3905_);
lean_inc(v_ref_3903_);
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v_ref_3903_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3907_);
v___x_3909_ = v___x_3901_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
return v___x_3909_;
}
}
}
}
v___jp_3912_:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_st_ref_get(v___y_3918_);
if (lean_obj_tag(v_exportedInfo_x3f_3916_) == 0)
{
lean_object* v_env_3920_; lean_object* v___x_3921_; 
v_env_3920_ = lean_ctor_get(v___x_3919_, 0);
lean_inc_ref(v_env_3920_);
lean_dec(v___x_3919_);
v___x_3921_ = lean_box(0);
v___y_3881_ = v___y_3917_;
v___y_3882_ = v___y_3918_;
v___y_3883_ = v_env_3920_;
v___y_3884_ = v___y_3917_;
v___y_3885_ = v___y_3913_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3918_;
v___y_3888_ = v_exportedInfo_x3f_3916_;
v___y_3889_ = v___y_3915_;
v___y_3890_ = v___x_3921_;
goto v___jp_3880_;
}
else
{
lean_object* v_env_3922_; lean_object* v_val_3923_; uint8_t v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; 
v_env_3922_ = lean_ctor_get(v___x_3919_, 0);
lean_inc_ref(v_env_3922_);
lean_dec(v___x_3919_);
v_val_3923_ = lean_ctor_get(v_exportedInfo_x3f_3916_, 0);
v___x_3924_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3923_);
v___x_3925_ = lean_box(v___x_3924_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3925_);
v___y_3881_ = v___y_3917_;
v___y_3882_ = v___y_3918_;
v___y_3883_ = v_env_3922_;
v___y_3884_ = v___y_3917_;
v___y_3885_ = v___y_3913_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3918_;
v___y_3888_ = v_exportedInfo_x3f_3916_;
v___y_3889_ = v___y_3915_;
v___y_3890_ = v___x_3926_;
goto v___jp_3880_;
}
}
v___jp_3927_:
{
lean_object* v___x_3933_; 
lean_inc_ref(v___y_3929_);
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___y_3929_);
v___y_3913_ = v___y_3928_;
v___y_3914_ = v___y_3929_;
v___y_3915_ = v___y_3930_;
v_exportedInfo_x3f_3916_ = v___x_3933_;
v___y_3917_ = v___y_3931_;
v___y_3918_ = v___y_3932_;
goto v___jp_3912_;
}
v___jp_3934_:
{
lean_object* v___x_3940_; 
lean_inc_ref(v___y_3936_);
v___x_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3940_, 0, v___y_3936_);
v___y_3913_ = v___y_3935_;
v___y_3914_ = v___y_3936_;
v___y_3915_ = v___y_3937_;
v_exportedInfo_x3f_3916_ = v___x_3940_;
v___y_3917_ = v___y_3938_;
v___y_3918_ = v___y_3939_;
goto v___jp_3912_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4846_, lean_object* v_forceExpose_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
uint8_t v_forceExpose_boxed_4851_; lean_object* v_res_4852_; 
v_forceExpose_boxed_4851_ = lean_unbox(v_forceExpose_4847_);
v_res_4852_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4846_, v_forceExpose_boxed_4851_, v_a_4848_, v_a_4849_);
lean_dec(v_a_4849_);
lean_dec_ref(v_a_4848_);
return v_res_4852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4857_; 
v___x_4857_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4853_, v___y_4854_);
return v___x_4857_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4858_, v___y_4859_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
lean_dec_ref(v_opt_4858_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4863_, lean_object* v_x_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
if (lean_obj_tag(v_x_4863_) == 0)
{
lean_object* v___x_4868_; lean_object* v___x_4869_; 
v___x_4868_ = l_List_reverse___redArg(v_x_4864_);
v___x_4869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4869_, 0, v___x_4868_);
return v___x_4869_;
}
else
{
lean_object* v_head_4870_; lean_object* v_tail_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4889_; 
v_head_4870_ = lean_ctor_get(v_x_4863_, 0);
v_tail_4871_ = lean_ctor_get(v_x_4863_, 1);
v_isSharedCheck_4889_ = !lean_is_exclusive(v_x_4863_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4873_ = v_x_4863_;
v_isShared_4874_ = v_isSharedCheck_4889_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_tail_4871_);
lean_inc(v_head_4870_);
lean_dec(v_x_4863_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4889_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; 
v___x_4875_ = l_Lean_snapshotEnvLinterOptions(v_head_4870_, v___y_4865_, v___y_4866_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; lean_object* v___x_4878_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref_known(v___x_4875_, 1);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 1, v_x_4864_);
lean_ctor_set(v___x_4873_, 0, v_a_4876_);
v___x_4878_ = v___x_4873_;
goto v_reusejp_4877_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v_a_4876_);
lean_ctor_set(v_reuseFailAlloc_4880_, 1, v_x_4864_);
v___x_4878_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4877_;
}
v_reusejp_4877_:
{
v_x_4863_ = v_tail_4871_;
v_x_4864_ = v___x_4878_;
goto _start;
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
lean_del_object(v___x_4873_);
lean_dec(v_tail_4871_);
lean_dec(v_x_4864_);
v_a_4881_ = lean_ctor_get(v___x_4875_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4875_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4875_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4886_; 
if (v_isShared_4884_ == 0)
{
v___x_4886_ = v___x_4883_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v_a_4881_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4890_, lean_object* v_x_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_){
_start:
{
lean_object* v_res_4895_; 
v_res_4895_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4890_, v_x_4891_, v___y_4892_, v___y_4893_);
lean_dec(v___y_4893_);
lean_dec_ref(v___y_4892_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4896_, uint8_t v_forceExpose_4897_, lean_object* v_a_4898_, lean_object* v_a_4899_){
_start:
{
lean_object* v___x_4901_; 
lean_inc(v_decl_4896_);
v___x_4901_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4896_, v_forceExpose_4897_, v_a_4898_, v_a_4899_);
if (lean_obj_tag(v___x_4901_) == 0)
{
lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
lean_dec_ref_known(v___x_4901_, 1);
v___x_4902_ = l_Lean_Declaration_getTopLevelNames(v_decl_4896_);
v___x_4903_ = lean_box(0);
v___x_4904_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4902_, v___x_4903_, v_a_4898_, v_a_4899_);
if (lean_obj_tag(v___x_4904_) == 0)
{
lean_object* v___x_4906_; uint8_t v_isShared_4907_; uint8_t v_isSharedCheck_4912_; 
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; 
v_unused_4913_ = lean_ctor_get(v___x_4904_, 0);
lean_dec(v_unused_4913_);
v___x_4906_ = v___x_4904_;
v_isShared_4907_ = v_isSharedCheck_4912_;
goto v_resetjp_4905_;
}
else
{
lean_dec(v___x_4904_);
v___x_4906_ = lean_box(0);
v_isShared_4907_ = v_isSharedCheck_4912_;
goto v_resetjp_4905_;
}
v_resetjp_4905_:
{
lean_object* v___x_4908_; lean_object* v___x_4910_; 
v___x_4908_ = lean_box(0);
if (v_isShared_4907_ == 0)
{
lean_ctor_set(v___x_4906_, 0, v___x_4908_);
v___x_4910_ = v___x_4906_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
else
{
lean_object* v_a_4914_; lean_object* v___x_4916_; uint8_t v_isShared_4917_; uint8_t v_isSharedCheck_4921_; 
v_a_4914_ = lean_ctor_get(v___x_4904_, 0);
v_isSharedCheck_4921_ = !lean_is_exclusive(v___x_4904_);
if (v_isSharedCheck_4921_ == 0)
{
v___x_4916_ = v___x_4904_;
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
else
{
lean_inc(v_a_4914_);
lean_dec(v___x_4904_);
v___x_4916_ = lean_box(0);
v_isShared_4917_ = v_isSharedCheck_4921_;
goto v_resetjp_4915_;
}
v_resetjp_4915_:
{
lean_object* v___x_4919_; 
if (v_isShared_4917_ == 0)
{
v___x_4919_ = v___x_4916_;
goto v_reusejp_4918_;
}
else
{
lean_object* v_reuseFailAlloc_4920_; 
v_reuseFailAlloc_4920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4920_, 0, v_a_4914_);
v___x_4919_ = v_reuseFailAlloc_4920_;
goto v_reusejp_4918_;
}
v_reusejp_4918_:
{
return v___x_4919_;
}
}
}
}
else
{
lean_dec(v_decl_4896_);
return v___x_4901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4922_, lean_object* v_forceExpose_4923_, lean_object* v_a_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_){
_start:
{
uint8_t v_forceExpose_boxed_4927_; lean_object* v_res_4928_; 
v_forceExpose_boxed_4927_ = lean_unbox(v_forceExpose_4923_);
v_res_4928_ = l_Lean_addDecl(v_decl_4922_, v_forceExpose_boxed_4927_, v_a_4924_, v_a_4925_);
lean_dec(v_a_4925_);
lean_dec_ref(v_a_4924_);
return v_res_4928_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4929_, lean_object* v_b_4930_, lean_object* v___y_4931_){
_start:
{
if (lean_obj_tag(v_as_x27_4929_) == 0)
{
lean_object* v___x_4933_; 
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v_b_4930_);
return v___x_4933_;
}
else
{
lean_object* v_head_4934_; lean_object* v_tail_4935_; lean_object* v___x_4936_; lean_object* v_env_4937_; lean_object* v_nextMacroScope_4938_; lean_object* v_ngen_4939_; lean_object* v_auxDeclNGen_4940_; lean_object* v_traceState_4941_; lean_object* v_messages_4942_; lean_object* v_infoState_4943_; lean_object* v_snapshotTasks_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4956_; 
v_head_4934_ = lean_ctor_get(v_as_x27_4929_, 0);
v_tail_4935_ = lean_ctor_get(v_as_x27_4929_, 1);
v___x_4936_ = lean_st_ref_take(v___y_4931_);
v_env_4937_ = lean_ctor_get(v___x_4936_, 0);
v_nextMacroScope_4938_ = lean_ctor_get(v___x_4936_, 1);
v_ngen_4939_ = lean_ctor_get(v___x_4936_, 2);
v_auxDeclNGen_4940_ = lean_ctor_get(v___x_4936_, 3);
v_traceState_4941_ = lean_ctor_get(v___x_4936_, 4);
v_messages_4942_ = lean_ctor_get(v___x_4936_, 6);
v_infoState_4943_ = lean_ctor_get(v___x_4936_, 7);
v_snapshotTasks_4944_ = lean_ctor_get(v___x_4936_, 8);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4936_);
if (v_isSharedCheck_4956_ == 0)
{
lean_object* v_unused_4957_; 
v_unused_4957_ = lean_ctor_get(v___x_4936_, 5);
lean_dec(v_unused_4957_);
v___x_4946_ = v___x_4936_;
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_snapshotTasks_4944_);
lean_inc(v_infoState_4943_);
lean_inc(v_messages_4942_);
lean_inc(v_traceState_4941_);
lean_inc(v_auxDeclNGen_4940_);
lean_inc(v_ngen_4939_);
lean_inc(v_nextMacroScope_4938_);
lean_inc(v_env_4937_);
lean_dec(v___x_4936_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4956_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4948_; lean_object* v___x_4949_; lean_object* v___x_4951_; 
lean_inc(v_head_4934_);
v___x_4948_ = l_Lean_markMeta(v_env_4937_, v_head_4934_);
v___x_4949_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4947_ == 0)
{
lean_ctor_set(v___x_4946_, 5, v___x_4949_);
lean_ctor_set(v___x_4946_, 0, v___x_4948_);
v___x_4951_ = v___x_4946_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v___x_4948_);
lean_ctor_set(v_reuseFailAlloc_4955_, 1, v_nextMacroScope_4938_);
lean_ctor_set(v_reuseFailAlloc_4955_, 2, v_ngen_4939_);
lean_ctor_set(v_reuseFailAlloc_4955_, 3, v_auxDeclNGen_4940_);
lean_ctor_set(v_reuseFailAlloc_4955_, 4, v_traceState_4941_);
lean_ctor_set(v_reuseFailAlloc_4955_, 5, v___x_4949_);
lean_ctor_set(v_reuseFailAlloc_4955_, 6, v_messages_4942_);
lean_ctor_set(v_reuseFailAlloc_4955_, 7, v_infoState_4943_);
lean_ctor_set(v_reuseFailAlloc_4955_, 8, v_snapshotTasks_4944_);
v___x_4951_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
lean_object* v___x_4952_; lean_object* v___x_4953_; 
v___x_4952_ = lean_st_ref_put(v___y_4931_, v___x_4951_);
v___x_4953_ = lean_box(0);
v_as_x27_4929_ = v_tail_4935_;
v_b_4930_ = v___x_4953_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4958_, lean_object* v_b_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
lean_object* v_res_4962_; 
v_res_4962_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4958_, v_b_4959_, v___y_4960_);
lean_dec(v___y_4960_);
lean_dec(v_as_x27_4958_);
return v_res_4962_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4963_, uint8_t v_logCompileErrors_4964_, uint8_t v_markMeta_4965_, lean_object* v_a_4966_, lean_object* v_a_4967_){
_start:
{
uint8_t v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = 0;
lean_inc(v_decl_4963_);
v___x_4970_ = l_Lean_addDecl(v_decl_4963_, v___x_4969_, v_a_4966_, v_a_4967_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_dec_ref_known(v___x_4970_, 1);
if (v_markMeta_4965_ == 0)
{
lean_object* v___x_4971_; 
v___x_4971_ = l_Lean_compileDecl(v_decl_4963_, v_logCompileErrors_4964_, v_a_4966_, v_a_4967_);
return v___x_4971_;
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; 
lean_inc(v_decl_4963_);
v___x_4972_ = l_Lean_Declaration_getNames(v_decl_4963_);
v___x_4973_ = lean_box(0);
v___x_4974_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4972_, v___x_4973_, v_a_4967_);
lean_dec(v___x_4972_);
lean_dec_ref(v___x_4974_);
v___x_4975_ = l_Lean_compileDecl(v_decl_4963_, v_logCompileErrors_4964_, v_a_4966_, v_a_4967_);
return v___x_4975_;
}
}
else
{
lean_dec(v_decl_4963_);
return v___x_4970_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4976_, lean_object* v_logCompileErrors_4977_, lean_object* v_markMeta_4978_, lean_object* v_a_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_){
_start:
{
uint8_t v_logCompileErrors_boxed_4982_; uint8_t v_markMeta_boxed_4983_; lean_object* v_res_4984_; 
v_logCompileErrors_boxed_4982_ = lean_unbox(v_logCompileErrors_4977_);
v_markMeta_boxed_4983_ = lean_unbox(v_markMeta_4978_);
v_res_4984_ = l_Lean_addAndCompile(v_decl_4976_, v_logCompileErrors_boxed_4982_, v_markMeta_boxed_4983_, v_a_4979_, v_a_4980_);
lean_dec(v_a_4980_);
lean_dec_ref(v_a_4979_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4985_, lean_object* v_as_x27_4986_, lean_object* v_b_4987_, lean_object* v_a_4988_, lean_object* v___y_4989_, lean_object* v___y_4990_){
_start:
{
lean_object* v___x_4992_; 
v___x_4992_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4986_, v_b_4987_, v___y_4990_);
return v___x_4992_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4993_, lean_object* v_as_x27_4994_, lean_object* v_b_4995_, lean_object* v_a_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v_res_5000_; 
v_res_5000_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4993_, v_as_x27_4994_, v_b_4995_, v_a_4996_, v___y_4997_, v___y_4998_);
lean_dec(v___y_4998_);
lean_dec_ref(v___y_4997_);
lean_dec(v_as_x27_4994_);
lean_dec(v_as_4993_);
return v_res_5000_;
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
