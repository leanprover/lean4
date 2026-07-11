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
uint8_t lean_bool_not(uint8_t);
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, size_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Kernel_Exception_toMessageData(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_interruptExceptionId;
lean_object* lean_io_mono_nanos_now();
double lean_float_of_nat(lean_object*);
double lean_float_div(double, double);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
lean_object* l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(lean_object*);
lean_object* l_Lean_FileMap_toPosition(lean_object*, lean_object*);
uint8_t l_Lean_MessageData_hasTag(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getTailPos_x3f(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t l_Lean_instBEqMessageSeverity_beq(uint8_t, uint8_t);
extern lean_object* l_Lean_warningAsError;
uint8_t l_Lean_MessageData_hasSyntheticSorry(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Expr_isSyntheticSorry(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
uint8_t l_Lean_Declaration_hasSorry(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_profileitIOUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Linter_linterSetsExt;
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean_Environment_header(lean_object*);
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
static const lean_string_object l_Lean_warnIfUsesSorry___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "hasSorry"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__0 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__0_value;
static const lean_ctor_object l_Lean_warnIfUsesSorry___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_warnIfUsesSorry___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 250, 94, 52, 248, 92, 138, 251)}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__1 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__1_value;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "declaration uses `"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__2 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__2_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__3;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__4 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__4_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__5;
static const lean_string_object l_Lean_warnIfUsesSorry___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "declaration uses `sorry`"};
static const lean_object* l_Lean_warnIfUsesSorry___closed__6 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__6_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__7;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__8;
static const lean_closure_object l_Lean_warnIfUsesSorry___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_warnIfUsesSorry___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_warnIfUsesSorry___closed__9 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__9_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__10;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__11;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__12;
static const lean_array_object l_Lean_warnIfUsesSorry___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_warnIfUsesSorry___closed__13 = (const lean_object*)&l_Lean_warnIfUsesSorry___closed__13_value;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__14;
static lean_once_cell_t l_Lean_warnIfUsesSorry___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_warnIfUsesSorry___closed__15;
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_value;
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
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "adding declarations "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0 = (const lean_object*)&l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "no matching async adding rules, adding synchronously"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "addDeclCore"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__0_value;
static const lean_ctor_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_AddDecl_0__Lean_initFn___closed__8_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 15, 132, 113, 234, 47, 152, 164)}};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1_value;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "no matching exporting rules, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 41, .m_capacity = 41, .m_length = 40, .m_data = "not exporting private declaration at all"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__4 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__4_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "private decl under `privateInPublic`, exporting as is"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__6 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__6_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "exporting definition "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__0 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__0_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " as axiom"};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "exporting opaque "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3;
static const lean_string_object l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "exporting theorem "};
static const lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4 = (const lean_object*)&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_value;
static lean_once_cell_t l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5;
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
lean_object* v___x_48_; size_t v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; size_t v___x_52_; lean_object* v___x_53_; uint8_t v___x_54_; uint8_t v___x_55_; lean_object* v___x_56_; 
v___x_48_ = l_Lean_Core_getMaxHeartbeats(v_opts_45_);
v___x_49_ = lean_usize_of_nat(v___x_48_);
lean_dec(v___x_48_);
v___x_50_ = l_Lean_maxRecDepth;
v___x_51_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_45_, v___x_50_);
v___x_52_ = lean_usize_of_nat(v___x_51_);
lean_dec(v___x_51_);
v___x_53_ = l_Lean_debug_skipKernelTC;
v___x_54_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_45_, v___x_53_);
v___x_55_ = lean_bool_not(v___x_54_);
v___x_56_ = l_Lean_Environment_addDeclCore(v_env_44_, v___x_49_, v___x_52_, v_decl_46_, v_cancelTk_x3f_47_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* v_env_57_, lean_object* v_opts_58_, lean_object* v_decl_59_, lean_object* v_cancelTk_x3f_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_57_, v_opts_58_, v_decl_59_, v_cancelTk_x3f_60_);
lean_dec(v_cancelTk_x3f_60_);
lean_dec(v_decl_59_);
lean_dec_ref(v_opts_58_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object* v_a_62_, lean_object* v_as_63_, size_t v_sz_64_, size_t v_i_65_, lean_object* v_b_66_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = lean_usize_dec_lt(v_i_65_, v_sz_64_);
if (v___x_68_ == 0)
{
lean_object* v___x_69_; 
v___x_69_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_69_, 0, v_b_66_);
return v___x_69_;
}
else
{
lean_object* v_a_70_; lean_object* v_name_71_; uint8_t v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; size_t v___x_75_; size_t v___x_76_; 
v_a_70_ = lean_array_uget_borrowed(v_as_63_, v_i_65_);
v_name_71_ = lean_ctor_get(v_a_70_, 0);
v___x_72_ = l_Lean_Linter_getLinterValue(v_a_70_, v_a_62_);
v___x_73_ = lean_box(v___x_72_);
lean_inc(v_name_71_);
v___x_74_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_71_, v___x_73_, v_b_66_);
v___x_75_ = ((size_t)1ULL);
v___x_76_ = lean_usize_add(v_i_65_, v___x_75_);
v_i_65_ = v___x_76_;
v_b_66_ = v___x_74_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object* v_a_78_, lean_object* v_as_79_, lean_object* v_sz_80_, lean_object* v_i_81_, lean_object* v_b_82_, lean_object* v___y_83_){
_start:
{
size_t v_sz_boxed_84_; size_t v_i_boxed_85_; lean_object* v_res_86_; 
v_sz_boxed_84_ = lean_unbox_usize(v_sz_80_);
lean_dec(v_sz_80_);
v_i_boxed_85_ = lean_unbox_usize(v_i_81_);
lean_dec(v_i_81_);
v_res_86_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_78_, v_as_79_, v_sz_boxed_84_, v_i_boxed_85_, v_b_82_);
lean_dec_ref(v_as_79_);
lean_dec_ref(v_a_78_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object* v_o_87_, lean_object* v___y_88_){
_start:
{
lean_object* v___x_90_; lean_object* v_env_91_; lean_object* v___x_92_; lean_object* v_toEnvExtension_93_; lean_object* v_asyncMode_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v_merged_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_106_; 
v___x_90_ = lean_st_ref_get(v___y_88_);
v_env_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc_ref(v_env_91_);
lean_dec(v___x_90_);
v___x_92_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_93_ = lean_ctor_get(v___x_92_, 0);
v_asyncMode_94_ = lean_ctor_get(v_toEnvExtension_93_, 2);
v___x_95_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_96_ = lean_box(0);
v___x_97_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_95_, v___x_92_, v_env_91_, v_asyncMode_94_, v___x_96_);
v_merged_98_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_106_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_106_ == 0)
{
lean_object* v_unused_107_; 
v_unused_107_ = lean_ctor_get(v___x_97_, 1);
lean_dec(v_unused_107_);
v___x_100_ = v___x_97_;
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_merged_98_);
lean_dec(v___x_97_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_106_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_103_; 
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v_merged_98_);
lean_ctor_set(v___x_100_, 0, v_o_87_);
v___x_103_ = v___x_100_;
goto v_reusejp_102_;
}
else
{
lean_object* v_reuseFailAlloc_105_; 
v_reuseFailAlloc_105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_105_, 0, v_o_87_);
lean_ctor_set(v_reuseFailAlloc_105_, 1, v_merged_98_);
v___x_103_ = v_reuseFailAlloc_105_;
goto v_reusejp_102_;
}
v_reusejp_102_:
{
lean_object* v___x_104_; 
v___x_104_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_104_, 0, v___x_103_);
return v___x_104_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_108_, v___y_109_);
lean_dec(v___y_109_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v_options_115_; lean_object* v___x_116_; 
v_options_115_ = lean_ctor_get(v___y_112_, 2);
lean_inc_ref(v_options_115_);
v___x_116_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_options_115_, v___y_113_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_120_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_121_; 
v___x_121_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_121_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_123_, 0, v___x_122_);
return v___x_123_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_125_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_125_, 0, v___x_124_);
lean_ctor_set(v___x_125_, 1, v___x_124_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_126_, lean_object* v_a_127_, lean_object* v_a_128_){
_start:
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; uint8_t v___x_134_; 
v___x_130_ = l_Lean_Linter_envLinterOptionsRef;
v___x_131_ = lean_st_ref_get(v___x_130_);
v___x_132_ = lean_array_get_size(v___x_131_);
v___x_133_ = lean_unsigned_to_nat(0u);
v___x_134_ = lean_nat_dec_eq(v___x_132_, v___x_133_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v_a_136_; lean_object* v___x_137_; 
v___x_135_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_127_, v_a_128_);
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref(v___x_135_);
lean_inc(v_declName_126_);
v___x_137_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_126_, v_a_128_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_189_; 
v_a_138_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_189_ == 0)
{
v___x_140_ = v___x_137_;
v_isShared_141_ = v_isSharedCheck_189_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_137_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_189_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
uint8_t v___x_142_; 
v___x_142_ = lean_unbox(v_a_138_);
lean_dec(v_a_138_);
if (v___x_142_ == 0)
{
lean_object* v___x_143_; size_t v_sz_144_; size_t v___x_145_; lean_object* v___x_146_; 
lean_del_object(v___x_140_);
v___x_143_ = lean_box(1);
v_sz_144_ = lean_array_size(v___x_131_);
v___x_145_ = ((size_t)0ULL);
v___x_146_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_136_, v___x_131_, v_sz_144_, v___x_145_, v___x_143_);
lean_dec(v___x_131_);
lean_dec(v_a_136_);
if (lean_obj_tag(v___x_146_) == 0)
{
lean_object* v_a_147_; lean_object* v___x_149_; uint8_t v_isShared_150_; uint8_t v_isSharedCheck_176_; 
v_a_147_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_176_ == 0)
{
v___x_149_ = v___x_146_;
v_isShared_150_ = v_isSharedCheck_176_;
goto v_resetjp_148_;
}
else
{
lean_inc(v_a_147_);
lean_dec(v___x_146_);
v___x_149_ = lean_box(0);
v_isShared_150_ = v_isSharedCheck_176_;
goto v_resetjp_148_;
}
v_resetjp_148_:
{
lean_object* v___x_151_; lean_object* v_env_152_; lean_object* v_nextMacroScope_153_; lean_object* v_ngen_154_; lean_object* v_auxDeclNGen_155_; lean_object* v_traceState_156_; lean_object* v_messages_157_; lean_object* v_infoState_158_; lean_object* v_snapshotTasks_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_174_; 
v___x_151_ = lean_st_ref_take(v_a_128_);
v_env_152_ = lean_ctor_get(v___x_151_, 0);
v_nextMacroScope_153_ = lean_ctor_get(v___x_151_, 1);
v_ngen_154_ = lean_ctor_get(v___x_151_, 2);
v_auxDeclNGen_155_ = lean_ctor_get(v___x_151_, 3);
v_traceState_156_ = lean_ctor_get(v___x_151_, 4);
v_messages_157_ = lean_ctor_get(v___x_151_, 6);
v_infoState_158_ = lean_ctor_get(v___x_151_, 7);
v_snapshotTasks_159_ = lean_ctor_get(v___x_151_, 8);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_151_);
if (v_isSharedCheck_174_ == 0)
{
lean_object* v_unused_175_; 
v_unused_175_ = lean_ctor_get(v___x_151_, 5);
lean_dec(v_unused_175_);
v___x_161_ = v___x_151_;
v_isShared_162_ = v_isSharedCheck_174_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_snapshotTasks_159_);
lean_inc(v_infoState_158_);
lean_inc(v_messages_157_);
lean_inc(v_traceState_156_);
lean_inc(v_auxDeclNGen_155_);
lean_inc(v_ngen_154_);
lean_inc(v_nextMacroScope_153_);
lean_inc(v_env_152_);
lean_dec(v___x_151_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_174_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_163_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_164_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_163_, v_env_152_, v_declName_126_, v_a_147_);
v___x_165_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 5, v___x_165_);
lean_ctor_set(v___x_161_, 0, v___x_164_);
v___x_167_ = v___x_161_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_164_);
lean_ctor_set(v_reuseFailAlloc_173_, 1, v_nextMacroScope_153_);
lean_ctor_set(v_reuseFailAlloc_173_, 2, v_ngen_154_);
lean_ctor_set(v_reuseFailAlloc_173_, 3, v_auxDeclNGen_155_);
lean_ctor_set(v_reuseFailAlloc_173_, 4, v_traceState_156_);
lean_ctor_set(v_reuseFailAlloc_173_, 5, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_173_, 6, v_messages_157_);
lean_ctor_set(v_reuseFailAlloc_173_, 7, v_infoState_158_);
lean_ctor_set(v_reuseFailAlloc_173_, 8, v_snapshotTasks_159_);
v___x_167_ = v_reuseFailAlloc_173_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_168_ = lean_st_ref_set(v_a_128_, v___x_167_);
v___x_169_ = lean_box(0);
if (v_isShared_150_ == 0)
{
lean_ctor_set(v___x_149_, 0, v___x_169_);
v___x_171_ = v___x_149_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_172_; 
v_reuseFailAlloc_172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_172_, 0, v___x_169_);
v___x_171_ = v_reuseFailAlloc_172_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
return v___x_171_;
}
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_declName_126_);
v_a_177_ = lean_ctor_get(v___x_146_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_146_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_146_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_146_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v___x_185_; lean_object* v___x_187_; 
lean_dec(v_a_136_);
lean_dec(v___x_131_);
lean_dec(v_declName_126_);
v___x_185_ = lean_box(0);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_185_);
v___x_187_ = v___x_140_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
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
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec(v_a_136_);
lean_dec(v___x_131_);
lean_dec(v_declName_126_);
v_a_190_ = lean_ctor_get(v___x_137_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_137_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_137_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_137_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
else
{
lean_object* v___x_198_; lean_object* v___x_199_; 
lean_dec(v___x_131_);
lean_dec(v_declName_126_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_200_, lean_object* v_a_201_, lean_object* v_a_202_, lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_snapshotEnvLinterOptions(v_declName_200_, v_a_201_, v_a_202_);
lean_dec(v_a_202_);
lean_dec_ref(v_a_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v___x_209_; 
v___x_209_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_205_, v___y_207_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_210_, v___y_211_, v___y_212_);
lean_dec(v___y_212_);
lean_dec_ref(v___y_211_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_215_, lean_object* v_as_216_, size_t v_sz_217_, size_t v_i_218_, lean_object* v_b_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_215_, v_as_216_, v_sz_217_, v_i_218_, v_b_219_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_224_, lean_object* v_as_225_, lean_object* v_sz_226_, lean_object* v_i_227_, lean_object* v_b_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
size_t v_sz_boxed_232_; size_t v_i_boxed_233_; lean_object* v_res_234_; 
v_sz_boxed_232_ = lean_unbox_usize(v_sz_226_);
lean_dec(v_sz_226_);
v_i_boxed_233_ = lean_unbox_usize(v_i_227_);
lean_dec(v_i_227_);
v_res_234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_224_, v_as_225_, v_sz_boxed_232_, v_i_boxed_233_, v_b_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec_ref(v_as_225_);
lean_dec_ref(v_a_224_);
return v_res_234_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_235_){
_start:
{
if (lean_obj_tag(v_x_235_) == 1)
{
lean_object* v_pre_236_; 
v_pre_236_ = lean_ctor_get(v_x_235_, 0);
if (lean_obj_tag(v_pre_236_) == 0)
{
uint8_t v___x_237_; 
v___x_237_ = 1;
return v___x_237_;
}
else
{
v_x_235_ = v_pre_236_;
goto _start;
}
}
else
{
uint8_t v___x_239_; 
v___x_239_ = 0;
return v___x_239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_240_);
lean_dec(v_x_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_243_, lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 1)
{
lean_object* v_pre_245_; uint8_t v___x_246_; 
v_pre_245_ = lean_ctor_get(v_x_244_, 0);
lean_inc(v_pre_245_);
lean_dec_ref_known(v_x_244_, 2);
v___x_246_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_245_);
if (v___x_246_ == 0)
{
lean_dec(v_pre_245_);
return v_env_243_;
}
else
{
lean_object* v___x_247_; 
lean_inc(v_pre_245_);
v___x_247_ = l_Lean_Environment_registerNamespace(v_env_243_, v_pre_245_);
v_env_243_ = v___x_247_;
v_x_244_ = v_pre_245_;
goto _start;
}
}
else
{
lean_dec(v_x_244_);
return v_env_243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_249_, lean_object* v_name_250_){
_start:
{
lean_object* v_name_251_; uint32_t v___y_253_; 
v_name_251_ = l_Lean_privateToUserName(v_name_250_);
if (lean_obj_tag(v_name_251_) == 1)
{
lean_object* v_str_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; 
v_str_257_ = lean_ctor_get(v_name_251_, 1);
lean_inc_ref(v_str_257_);
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = lean_string_utf8_byte_size(v_str_257_);
v___x_260_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_260_, 0, v_str_257_);
lean_ctor_set(v___x_260_, 1, v___x_258_);
lean_ctor_set(v___x_260_, 2, v___x_259_);
v___x_261_ = l_String_Slice_Pos_get_x3f(v___x_260_, v___x_258_);
lean_dec_ref_known(v___x_260_, 3);
if (lean_obj_tag(v___x_261_) == 0)
{
uint32_t v___x_262_; 
v___x_262_ = 65;
v___y_253_ = v___x_262_;
goto v___jp_252_;
}
else
{
lean_object* v_val_263_; uint32_t v___x_264_; 
v_val_263_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v___x_261_, 1);
v___x_264_ = lean_unbox_uint32(v_val_263_);
lean_dec(v_val_263_);
v___y_253_ = v___x_264_;
goto v___jp_252_;
}
}
else
{
lean_dec(v_name_251_);
return v_env_249_;
}
v___jp_252_:
{
uint32_t v___x_254_; uint8_t v___x_255_; 
v___x_254_ = 95;
v___x_255_ = lean_uint32_dec_eq(v___y_253_, v___x_254_);
if (v___x_255_ == 0)
{
lean_object* v___x_256_; 
v___x_256_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_249_, v_name_251_);
return v___x_256_;
}
else
{
lean_dec(v_name_251_);
return v_env_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_265_, lean_object* v_decl_266_, lean_object* v_ref_267_){
_start:
{
lean_object* v_defValue_269_; lean_object* v_descr_270_; lean_object* v_deprecation_x3f_271_; lean_object* v___x_272_; uint8_t v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_defValue_269_ = lean_ctor_get(v_decl_266_, 0);
v_descr_270_ = lean_ctor_get(v_decl_266_, 1);
v_deprecation_x3f_271_ = lean_ctor_get(v_decl_266_, 2);
v___x_272_ = lean_alloc_ctor(1, 0, 1);
v___x_273_ = lean_unbox(v_defValue_269_);
lean_ctor_set_uint8(v___x_272_, 0, v___x_273_);
lean_inc(v_deprecation_x3f_271_);
lean_inc_ref(v_descr_270_);
lean_inc_n(v_name_265_, 2);
v___x_274_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_274_, 0, v_name_265_);
lean_ctor_set(v___x_274_, 1, v_ref_267_);
lean_ctor_set(v___x_274_, 2, v___x_272_);
lean_ctor_set(v___x_274_, 3, v_descr_270_);
lean_ctor_set(v___x_274_, 4, v_deprecation_x3f_271_);
v___x_275_ = lean_register_option(v_name_265_, v___x_274_);
if (lean_obj_tag(v___x_275_) == 0)
{
lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_283_; 
v_isSharedCheck_283_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_283_ == 0)
{
lean_object* v_unused_284_; 
v_unused_284_ = lean_ctor_get(v___x_275_, 0);
lean_dec(v_unused_284_);
v___x_277_ = v___x_275_;
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
else
{
lean_dec(v___x_275_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_283_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_279_; lean_object* v___x_281_; 
lean_inc(v_defValue_269_);
v___x_279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_279_, 0, v_name_265_);
lean_ctor_set(v___x_279_, 1, v_defValue_269_);
if (v_isShared_278_ == 0)
{
lean_ctor_set(v___x_277_, 0, v___x_279_);
v___x_281_ = v___x_277_;
goto v_reusejp_280_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v___x_279_);
v___x_281_ = v_reuseFailAlloc_282_;
goto v_reusejp_280_;
}
v_reusejp_280_:
{
return v___x_281_;
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_name_265_);
v_a_285_ = lean_ctor_get(v___x_275_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_275_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_275_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_293_, lean_object* v_decl_294_, lean_object* v_ref_295_, lean_object* v_a_296_){
_start:
{
lean_object* v_res_297_; 
v_res_297_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_293_, v_decl_294_, v_ref_295_);
lean_dec_ref(v_decl_294_);
return v_res_297_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_315_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_316_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_317_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_318_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_315_, v___x_316_, v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_319_){
_start:
{
lean_object* v_res_320_; 
v_res_320_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_){
_start:
{
lean_object* v___x_327_; lean_object* v_env_328_; lean_object* v___x_329_; lean_object* v_mctx_330_; lean_object* v_lctx_331_; lean_object* v_options_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; 
v___x_327_ = lean_st_ref_get(v___y_325_);
v_env_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc_ref(v_env_328_);
lean_dec(v___x_327_);
v___x_329_ = lean_st_ref_get(v___y_323_);
v_mctx_330_ = lean_ctor_get(v___x_329_, 0);
lean_inc_ref(v_mctx_330_);
lean_dec(v___x_329_);
v_lctx_331_ = lean_ctor_get(v___y_322_, 2);
v_options_332_ = lean_ctor_get(v___y_324_, 2);
lean_inc_ref(v_options_332_);
lean_inc_ref(v_lctx_331_);
v___x_333_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_333_, 0, v_env_328_);
lean_ctor_set(v___x_333_, 1, v_mctx_330_);
lean_ctor_set(v___x_333_, 2, v_lctx_331_);
lean_ctor_set(v___x_333_, 3, v_options_332_);
v___x_334_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_333_);
lean_ctor_set(v___x_334_, 1, v_msgData_321_);
v___x_335_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_){
_start:
{
lean_object* v_res_342_; 
v_res_342_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_);
lean_dec(v___y_340_);
lean_dec_ref(v___y_339_);
lean_dec(v___y_338_);
lean_dec_ref(v___y_337_);
return v_res_342_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v_a_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_366_; 
lean_inc_ref(v_s_343_);
v___x_350_ = l_Lean_MessageData_ofExpr(v_s_343_);
v___x_351_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_350_, v___y_345_, v___y_346_, v___y_347_, v___y_348_);
v_a_352_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_366_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_366_ == 0)
{
v___x_354_ = v___x_351_;
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_a_352_);
lean_dec(v___x_351_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_366_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; uint8_t v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_364_; 
v___x_356_ = lean_st_ref_take(v___y_344_);
v___x_357_ = l_Lean_Expr_isSyntheticSorry(v_s_343_);
lean_dec_ref(v_s_343_);
v___x_358_ = lean_box(v___x_357_);
v___x_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_358_);
lean_ctor_set(v___x_359_, 1, v_a_352_);
v___x_360_ = lean_array_push(v___x_356_, v___x_359_);
v___x_361_ = lean_st_ref_set(v___y_344_, v___x_360_);
v___x_362_ = lean_box(0);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_362_);
v___x_364_ = v___x_354_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_365_; 
v_reuseFailAlloc_365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_365_, 0, v___x_362_);
v___x_364_ = v_reuseFailAlloc_365_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
return v___x_364_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_warnIfUsesSorry___lam__0(v_s_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
return v_res_374_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_383_, uint8_t v_suppressElabErrors_384_, lean_object* v_x_385_){
_start:
{
if (lean_obj_tag(v_x_385_) == 1)
{
lean_object* v_pre_386_; 
v_pre_386_ = lean_ctor_get(v_x_385_, 0);
switch(lean_obj_tag(v_pre_386_))
{
case 1:
{
lean_object* v_pre_387_; 
v_pre_387_ = lean_ctor_get(v_pre_386_, 0);
switch(lean_obj_tag(v_pre_387_))
{
case 0:
{
lean_object* v_str_388_; lean_object* v_str_389_; lean_object* v___x_390_; uint8_t v___x_391_; 
v_str_388_ = lean_ctor_get(v_x_385_, 1);
v_str_389_ = lean_ctor_get(v_pre_386_, 1);
v___x_390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_391_ = lean_string_dec_eq(v_str_389_, v___x_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_393_ = lean_string_dec_eq(v_str_389_, v___x_392_);
if (v___x_393_ == 0)
{
return v___y_383_;
}
else
{
lean_object* v___x_394_; uint8_t v___x_395_; 
v___x_394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_395_ = lean_string_dec_eq(v_str_388_, v___x_394_);
if (v___x_395_ == 0)
{
return v___y_383_;
}
else
{
return v_suppressElabErrors_384_;
}
}
}
else
{
lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_397_ = lean_string_dec_eq(v_str_388_, v___x_396_);
if (v___x_397_ == 0)
{
return v___y_383_;
}
else
{
return v_suppressElabErrors_384_;
}
}
}
case 1:
{
lean_object* v_pre_398_; 
v_pre_398_ = lean_ctor_get(v_pre_387_, 0);
if (lean_obj_tag(v_pre_398_) == 0)
{
lean_object* v_str_399_; lean_object* v_str_400_; lean_object* v_str_401_; lean_object* v___x_402_; uint8_t v___x_403_; 
v_str_399_ = lean_ctor_get(v_x_385_, 1);
v_str_400_ = lean_ctor_get(v_pre_386_, 1);
v_str_401_ = lean_ctor_get(v_pre_387_, 1);
v___x_402_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_403_ = lean_string_dec_eq(v_str_401_, v___x_402_);
if (v___x_403_ == 0)
{
return v___y_383_;
}
else
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_405_ = lean_string_dec_eq(v_str_400_, v___x_404_);
if (v___x_405_ == 0)
{
return v___y_383_;
}
else
{
lean_object* v___x_406_; uint8_t v___x_407_; 
v___x_406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_407_ = lean_string_dec_eq(v_str_399_, v___x_406_);
if (v___x_407_ == 0)
{
return v___y_383_;
}
else
{
return v_suppressElabErrors_384_;
}
}
}
}
else
{
return v___y_383_;
}
}
default: 
{
return v___y_383_;
}
}
}
case 0:
{
lean_object* v_str_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v_str_408_ = lean_ctor_get(v_x_385_, 1);
v___x_409_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_410_ = lean_string_dec_eq(v_str_408_, v___x_409_);
if (v___x_410_ == 0)
{
return v___y_383_;
}
else
{
return v_suppressElabErrors_384_;
}
}
default: 
{
return v___y_383_;
}
}
}
else
{
return v___y_383_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_411_, lean_object* v_suppressElabErrors_412_, lean_object* v_x_413_){
_start:
{
uint8_t v___y_15533__boxed_414_; uint8_t v_suppressElabErrors_boxed_415_; uint8_t v_res_416_; lean_object* v_r_417_; 
v___y_15533__boxed_414_ = lean_unbox(v___y_411_);
v_suppressElabErrors_boxed_415_ = lean_unbox(v_suppressElabErrors_412_);
v_res_416_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15533__boxed_414_, v_suppressElabErrors_boxed_415_, v_x_413_);
lean_dec(v_x_413_);
v_r_417_ = lean_box(v_res_416_);
return v_r_417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_418_; 
v___x_418_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_418_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_420_, 0, v___x_419_);
return v___x_420_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_422_ = lean_unsigned_to_nat(0u);
v___x_423_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
lean_ctor_set(v___x_423_, 2, v___x_422_);
lean_ctor_set(v___x_423_, 3, v___x_422_);
lean_ctor_set(v___x_423_, 4, v___x_421_);
lean_ctor_set(v___x_423_, 5, v___x_421_);
lean_ctor_set(v___x_423_, 6, v___x_421_);
lean_ctor_set(v___x_423_, 7, v___x_421_);
lean_ctor_set(v___x_423_, 8, v___x_421_);
lean_ctor_set(v___x_423_, 9, v___x_421_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_unsigned_to_nat(32u);
v___x_425_ = lean_mk_empty_array_with_capacity(v___x_424_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_427_ = ((size_t)5ULL);
v___x_428_ = lean_unsigned_to_nat(0u);
v___x_429_ = lean_unsigned_to_nat(32u);
v___x_430_ = lean_mk_empty_array_with_capacity(v___x_429_);
v___x_431_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_432_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v___x_430_);
lean_ctor_set(v___x_432_, 2, v___x_428_);
lean_ctor_set(v___x_432_, 3, v___x_428_);
lean_ctor_set_usize(v___x_432_, 4, v___x_427_);
return v___x_432_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_433_ = lean_box(1);
v___x_434_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_435_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_436_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_436_, 0, v___x_435_);
lean_ctor_set(v___x_436_, 1, v___x_434_);
lean_ctor_set(v___x_436_, 2, v___x_433_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_437_, lean_object* v___y_438_, lean_object* v___y_439_){
_start:
{
lean_object* v___x_441_; lean_object* v_env_442_; lean_object* v_options_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_441_ = lean_st_ref_get(v___y_439_);
v_env_442_ = lean_ctor_get(v___x_441_, 0);
lean_inc_ref(v_env_442_);
lean_dec(v___x_441_);
v_options_443_ = lean_ctor_get(v___y_438_, 2);
v___x_444_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_445_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_443_);
v___x_446_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_446_, 0, v_env_442_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___x_445_);
lean_ctor_set(v___x_446_, 3, v_options_443_);
v___x_447_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_447_, 0, v___x_446_);
lean_ctor_set(v___x_447_, 1, v_msgData_437_);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_449_, v___y_450_, v___y_451_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_455_, lean_object* v_msgData_456_, uint8_t v_severity_457_, uint8_t v_isSilent_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
uint8_t v___y_463_; lean_object* v___y_464_; lean_object* v___y_465_; uint8_t v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_499_; uint8_t v___y_500_; uint8_t v___y_501_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_506_; lean_object* v___y_524_; uint8_t v___y_525_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; lean_object* v___y_529_; uint8_t v___y_530_; lean_object* v___y_531_; lean_object* v___y_535_; uint8_t v___y_536_; lean_object* v___y_537_; lean_object* v___y_538_; lean_object* v___y_539_; uint8_t v___y_540_; uint8_t v___y_541_; uint8_t v___x_546_; lean_object* v___y_548_; lean_object* v___y_549_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; uint8_t v___y_553_; uint8_t v___y_554_; uint8_t v___y_556_; uint8_t v___x_571_; 
v___x_546_ = 2;
v___x_571_ = l_Lean_instBEqMessageSeverity_beq(v_severity_457_, v___x_546_);
if (v___x_571_ == 0)
{
v___y_556_ = v___x_571_;
goto v___jp_555_;
}
else
{
uint8_t v___x_572_; 
lean_inc_ref(v_msgData_456_);
v___x_572_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_456_);
v___y_556_ = v___x_572_;
goto v___jp_555_;
}
v___jp_462_:
{
lean_object* v___x_472_; lean_object* v_currNamespace_473_; lean_object* v_openDecls_474_; lean_object* v_env_475_; lean_object* v_nextMacroScope_476_; lean_object* v_ngen_477_; lean_object* v_auxDeclNGen_478_; lean_object* v_traceState_479_; lean_object* v_cache_480_; lean_object* v_messages_481_; lean_object* v_infoState_482_; lean_object* v_snapshotTasks_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_497_; 
v___x_472_ = lean_st_ref_take(v___y_471_);
v_currNamespace_473_ = lean_ctor_get(v___y_470_, 6);
v_openDecls_474_ = lean_ctor_get(v___y_470_, 7);
v_env_475_ = lean_ctor_get(v___x_472_, 0);
v_nextMacroScope_476_ = lean_ctor_get(v___x_472_, 1);
v_ngen_477_ = lean_ctor_get(v___x_472_, 2);
v_auxDeclNGen_478_ = lean_ctor_get(v___x_472_, 3);
v_traceState_479_ = lean_ctor_get(v___x_472_, 4);
v_cache_480_ = lean_ctor_get(v___x_472_, 5);
v_messages_481_ = lean_ctor_get(v___x_472_, 6);
v_infoState_482_ = lean_ctor_get(v___x_472_, 7);
v_snapshotTasks_483_ = lean_ctor_get(v___x_472_, 8);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_472_);
if (v_isSharedCheck_497_ == 0)
{
v___x_485_ = v___x_472_;
v_isShared_486_ = v_isSharedCheck_497_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_snapshotTasks_483_);
lean_inc(v_infoState_482_);
lean_inc(v_messages_481_);
lean_inc(v_cache_480_);
lean_inc(v_traceState_479_);
lean_inc(v_auxDeclNGen_478_);
lean_inc(v_ngen_477_);
lean_inc(v_nextMacroScope_476_);
lean_inc(v_env_475_);
lean_dec(v___x_472_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_497_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_492_; 
lean_inc(v_openDecls_474_);
lean_inc(v_currNamespace_473_);
v___x_487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_487_, 0, v_currNamespace_473_);
lean_ctor_set(v___x_487_, 1, v_openDecls_474_);
v___x_488_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_488_, 0, v___x_487_);
lean_ctor_set(v___x_488_, 1, v___y_469_);
lean_inc_ref(v___y_465_);
lean_inc_ref(v___y_467_);
v___x_489_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_489_, 0, v___y_467_);
lean_ctor_set(v___x_489_, 1, v___y_468_);
lean_ctor_set(v___x_489_, 2, v___y_464_);
lean_ctor_set(v___x_489_, 3, v___y_465_);
lean_ctor_set(v___x_489_, 4, v___x_488_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5, v___y_463_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 1, v___y_466_);
lean_ctor_set_uint8(v___x_489_, sizeof(void*)*5 + 2, v_isSilent_458_);
v___x_490_ = l_Lean_MessageLog_add(v___x_489_, v_messages_481_);
if (v_isShared_486_ == 0)
{
lean_ctor_set(v___x_485_, 6, v___x_490_);
v___x_492_ = v___x_485_;
goto v_reusejp_491_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_env_475_);
lean_ctor_set(v_reuseFailAlloc_496_, 1, v_nextMacroScope_476_);
lean_ctor_set(v_reuseFailAlloc_496_, 2, v_ngen_477_);
lean_ctor_set(v_reuseFailAlloc_496_, 3, v_auxDeclNGen_478_);
lean_ctor_set(v_reuseFailAlloc_496_, 4, v_traceState_479_);
lean_ctor_set(v_reuseFailAlloc_496_, 5, v_cache_480_);
lean_ctor_set(v_reuseFailAlloc_496_, 6, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_496_, 7, v_infoState_482_);
lean_ctor_set(v_reuseFailAlloc_496_, 8, v_snapshotTasks_483_);
v___x_492_ = v_reuseFailAlloc_496_;
goto v_reusejp_491_;
}
v_reusejp_491_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; 
v___x_493_ = lean_st_ref_set(v___y_471_, v___x_492_);
v___x_494_ = lean_box(0);
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v___x_494_);
return v___x_495_;
}
}
}
v___jp_498_:
{
lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v_a_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_522_; 
v___x_507_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_456_);
v___x_508_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_507_, v___y_459_, v___y_460_);
v_a_509_ = lean_ctor_get(v___x_508_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_508_);
if (v_isSharedCheck_522_ == 0)
{
v___x_511_ = v___x_508_;
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_a_509_);
lean_dec(v___x_508_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_522_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
lean_inc_ref_n(v___y_503_, 2);
v___x_513_ = l_Lean_FileMap_toPosition(v___y_503_, v___y_504_);
lean_dec(v___y_504_);
v___x_514_ = l_Lean_FileMap_toPosition(v___y_503_, v___y_506_);
lean_dec(v___y_506_);
v___x_515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
v___x_516_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_505_ == 0)
{
lean_del_object(v___x_511_);
lean_dec_ref(v___y_499_);
v___y_463_ = v___y_500_;
v___y_464_ = v___x_515_;
v___y_465_ = v___x_516_;
v___y_466_ = v___y_501_;
v___y_467_ = v___y_502_;
v___y_468_ = v___x_513_;
v___y_469_ = v_a_509_;
v___y_470_ = v___y_459_;
v___y_471_ = v___y_460_;
goto v___jp_462_;
}
else
{
uint8_t v___x_517_; 
lean_inc(v_a_509_);
v___x_517_ = l_Lean_MessageData_hasTag(v___y_499_, v_a_509_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_520_; 
lean_dec_ref_known(v___x_515_, 1);
lean_dec_ref(v___x_513_);
lean_dec(v_a_509_);
v___x_518_ = lean_box(0);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 0, v___x_518_);
v___x_520_ = v___x_511_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v___x_518_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
else
{
lean_del_object(v___x_511_);
v___y_463_ = v___y_500_;
v___y_464_ = v___x_515_;
v___y_465_ = v___x_516_;
v___y_466_ = v___y_501_;
v___y_467_ = v___y_502_;
v___y_468_ = v___x_513_;
v___y_469_ = v_a_509_;
v___y_470_ = v___y_459_;
v___y_471_ = v___y_460_;
goto v___jp_462_;
}
}
}
}
v___jp_523_:
{
lean_object* v___x_532_; 
v___x_532_ = l_Lean_Syntax_getTailPos_x3f(v___y_526_, v___y_525_);
lean_dec(v___y_526_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_inc(v___y_531_);
v___y_499_ = v___y_524_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_527_;
v___y_502_ = v___y_528_;
v___y_503_ = v___y_529_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
goto v___jp_498_;
}
else
{
lean_object* v_val_533_; 
v_val_533_ = lean_ctor_get(v___x_532_, 0);
lean_inc(v_val_533_);
lean_dec_ref_known(v___x_532_, 1);
v___y_499_ = v___y_524_;
v___y_500_ = v___y_525_;
v___y_501_ = v___y_527_;
v___y_502_ = v___y_528_;
v___y_503_ = v___y_529_;
v___y_504_ = v___y_531_;
v___y_505_ = v___y_530_;
v___y_506_ = v_val_533_;
goto v___jp_498_;
}
}
v___jp_534_:
{
lean_object* v_ref_542_; lean_object* v___x_543_; 
v_ref_542_ = l_Lean_replaceRef(v_ref_455_, v___y_539_);
v___x_543_ = l_Lean_Syntax_getPos_x3f(v_ref_542_, v___y_536_);
if (lean_obj_tag(v___x_543_) == 0)
{
lean_object* v___x_544_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___y_524_ = v___y_535_;
v___y_525_ = v___y_536_;
v___y_526_ = v_ref_542_;
v___y_527_ = v___y_541_;
v___y_528_ = v___y_537_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_540_;
v___y_531_ = v___x_544_;
goto v___jp_523_;
}
else
{
lean_object* v_val_545_; 
v_val_545_ = lean_ctor_get(v___x_543_, 0);
lean_inc(v_val_545_);
lean_dec_ref_known(v___x_543_, 1);
v___y_524_ = v___y_535_;
v___y_525_ = v___y_536_;
v___y_526_ = v_ref_542_;
v___y_527_ = v___y_541_;
v___y_528_ = v___y_537_;
v___y_529_ = v___y_538_;
v___y_530_ = v___y_540_;
v___y_531_ = v_val_545_;
goto v___jp_523_;
}
}
v___jp_547_:
{
if (v___y_554_ == 0)
{
v___y_535_ = v___y_548_;
v___y_536_ = v___y_553_;
v___y_537_ = v___y_549_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v_severity_457_;
goto v___jp_534_;
}
else
{
v___y_535_ = v___y_548_;
v___y_536_ = v___y_553_;
v___y_537_ = v___y_549_;
v___y_538_ = v___y_550_;
v___y_539_ = v___y_551_;
v___y_540_ = v___y_552_;
v___y_541_ = v___x_546_;
goto v___jp_534_;
}
}
v___jp_555_:
{
if (v___y_556_ == 0)
{
lean_object* v_fileName_557_; lean_object* v_fileMap_558_; lean_object* v_options_559_; lean_object* v_ref_560_; uint8_t v_suppressElabErrors_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___f_564_; uint8_t v___x_565_; uint8_t v___x_566_; 
v_fileName_557_ = lean_ctor_get(v___y_459_, 0);
v_fileMap_558_ = lean_ctor_get(v___y_459_, 1);
v_options_559_ = lean_ctor_get(v___y_459_, 2);
v_ref_560_ = lean_ctor_get(v___y_459_, 5);
v_suppressElabErrors_561_ = lean_ctor_get_uint8(v___y_459_, sizeof(void*)*14 + 1);
v___x_562_ = lean_box(v___y_556_);
v___x_563_ = lean_box(v_suppressElabErrors_561_);
v___f_564_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_564_, 0, v___x_562_);
lean_closure_set(v___f_564_, 1, v___x_563_);
v___x_565_ = 1;
v___x_566_ = l_Lean_instBEqMessageSeverity_beq(v_severity_457_, v___x_565_);
if (v___x_566_ == 0)
{
v___y_548_ = v___f_564_;
v___y_549_ = v_fileName_557_;
v___y_550_ = v_fileMap_558_;
v___y_551_ = v_ref_560_;
v___y_552_ = v_suppressElabErrors_561_;
v___y_553_ = v___y_556_;
v___y_554_ = v___x_566_;
goto v___jp_547_;
}
else
{
lean_object* v___x_567_; uint8_t v___x_568_; 
v___x_567_ = l_Lean_warningAsError;
v___x_568_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_559_, v___x_567_);
v___y_548_ = v___f_564_;
v___y_549_ = v_fileName_557_;
v___y_550_ = v_fileMap_558_;
v___y_551_ = v_ref_560_;
v___y_552_ = v_suppressElabErrors_561_;
v___y_553_ = v___y_556_;
v___y_554_ = v___x_568_;
goto v___jp_547_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; 
lean_dec_ref(v_msgData_456_);
v___x_569_ = lean_box(0);
v___x_570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_570_, 0, v___x_569_);
return v___x_570_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_573_, lean_object* v_msgData_574_, lean_object* v_severity_575_, lean_object* v_isSilent_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
uint8_t v_severity_boxed_580_; uint8_t v_isSilent_boxed_581_; lean_object* v_res_582_; 
v_severity_boxed_580_ = lean_unbox(v_severity_575_);
v_isSilent_boxed_581_ = lean_unbox(v_isSilent_576_);
v_res_582_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_573_, v_msgData_574_, v_severity_boxed_580_, v_isSilent_boxed_581_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v_ref_573_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_583_, uint8_t v_severity_584_, uint8_t v_isSilent_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_ref_589_; lean_object* v___x_590_; 
v_ref_589_ = lean_ctor_get(v___y_586_, 5);
v___x_590_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_589_, v_msgData_583_, v_severity_584_, v_isSilent_585_, v___y_586_, v___y_587_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_591_, lean_object* v_severity_592_, lean_object* v_isSilent_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
uint8_t v_severity_boxed_597_; uint8_t v_isSilent_boxed_598_; lean_object* v_res_599_; 
v_severity_boxed_597_ = lean_unbox(v_severity_592_);
v_isSilent_boxed_598_ = lean_unbox(v_isSilent_593_);
v_res_599_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_591_, v_severity_boxed_597_, v_isSilent_boxed_598_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_600_, lean_object* v___y_601_, lean_object* v___y_602_){
_start:
{
uint8_t v___x_604_; uint8_t v___x_605_; lean_object* v___x_606_; 
v___x_604_ = 1;
v___x_605_ = 0;
v___x_606_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_600_, v___x_604_, v___x_605_, v___y_601_, v___y_602_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_607_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_615_, size_t v_sz_616_, size_t v_i_617_, lean_object* v_b_618_){
_start:
{
uint8_t v___x_619_; 
v___x_619_ = lean_usize_dec_lt(v_i_617_, v_sz_616_);
if (v___x_619_ == 0)
{
lean_inc_ref(v_b_618_);
return v_b_618_;
}
else
{
lean_object* v_a_620_; lean_object* v_fst_621_; lean_object* v___x_622_; uint8_t v___x_623_; 
v_a_620_ = lean_array_uget_borrowed(v_as_615_, v_i_617_);
v_fst_621_ = lean_ctor_get(v_a_620_, 0);
v___x_622_ = lean_box(0);
v___x_623_ = lean_unbox(v_fst_621_);
if (v___x_623_ == 0)
{
lean_object* v___x_624_; size_t v___x_625_; size_t v___x_626_; 
v___x_624_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_625_ = ((size_t)1ULL);
v___x_626_ = lean_usize_add(v_i_617_, v___x_625_);
v_i_617_ = v___x_626_;
v_b_618_ = v___x_624_;
goto _start;
}
else
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_inc(v_a_620_);
v___x_628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_628_, 0, v_a_620_);
v___x_629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
lean_ctor_set(v___x_630_, 1, v___x_622_);
return v___x_630_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_631_, lean_object* v_sz_632_, lean_object* v_i_633_, lean_object* v_b_634_){
_start:
{
size_t v_sz_boxed_635_; size_t v_i_boxed_636_; lean_object* v_res_637_; 
v_sz_boxed_635_ = lean_unbox_usize(v_sz_632_);
lean_dec(v_sz_632_);
v_i_boxed_636_ = lean_unbox_usize(v_i_633_);
lean_dec(v_i_633_);
v_res_637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_631_, v_sz_boxed_635_, v_i_boxed_636_, v_b_634_);
lean_dec_ref(v_b_634_);
lean_dec_ref(v_as_631_);
return v_res_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_638_, lean_object* v_e_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; 
v___x_646_ = l_Lean_Expr_getSorry_x3f(v_e_639_);
if (lean_obj_tag(v___x_646_) == 1)
{
lean_object* v_val_647_; lean_object* v___x_648_; 
v_val_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_val_647_);
lean_dec_ref_known(v___x_646_, 1);
lean_inc(v___y_644_);
lean_inc_ref(v___y_643_);
lean_inc(v___y_642_);
lean_inc_ref(v___y_641_);
lean_inc(v___y_640_);
v___x_648_ = lean_apply_7(v_fn_638_, v_val_647_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, lean_box(0));
if (lean_obj_tag(v___x_648_) == 0)
{
lean_object* v___x_650_; uint8_t v_isShared_651_; uint8_t v_isSharedCheck_657_; 
v_isSharedCheck_657_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_657_ == 0)
{
lean_object* v_unused_658_; 
v_unused_658_ = lean_ctor_get(v___x_648_, 0);
lean_dec(v_unused_658_);
v___x_650_ = v___x_648_;
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
else
{
lean_dec(v___x_648_);
v___x_650_ = lean_box(0);
v_isShared_651_ = v_isSharedCheck_657_;
goto v_resetjp_649_;
}
v_resetjp_649_:
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_655_; 
v___x_652_ = 0;
v___x_653_ = lean_box(v___x_652_);
if (v_isShared_651_ == 0)
{
lean_ctor_set(v___x_650_, 0, v___x_653_);
v___x_655_ = v___x_650_;
goto v_reusejp_654_;
}
else
{
lean_object* v_reuseFailAlloc_656_; 
v_reuseFailAlloc_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_656_, 0, v___x_653_);
v___x_655_ = v_reuseFailAlloc_656_;
goto v_reusejp_654_;
}
v_reusejp_654_:
{
return v___x_655_;
}
}
}
else
{
lean_object* v_a_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_666_; 
v_a_659_ = lean_ctor_get(v___x_648_, 0);
v_isSharedCheck_666_ = !lean_is_exclusive(v___x_648_);
if (v_isSharedCheck_666_ == 0)
{
v___x_661_ = v___x_648_;
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_a_659_);
lean_dec(v___x_648_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_666_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_664_; 
if (v_isShared_662_ == 0)
{
v___x_664_ = v___x_661_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_665_; 
v_reuseFailAlloc_665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_665_, 0, v_a_659_);
v___x_664_ = v_reuseFailAlloc_665_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
return v___x_664_;
}
}
}
}
else
{
uint8_t v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
lean_dec(v___x_646_);
lean_dec_ref(v_fn_638_);
v___x_667_ = 1;
v___x_668_ = lean_box(v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_670_, lean_object* v_e_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_670_, v_e_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_e_671_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_679_, lean_object* v_x_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_apply_1(v_x_680_, lean_box(0));
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_689_, lean_object* v_x_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_){
_start:
{
lean_object* v_res_697_; 
v_res_697_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_689_, v_x_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
lean_dec(v___y_695_);
lean_dec_ref(v___y_694_);
lean_dec(v___y_693_);
lean_dec_ref(v___y_692_);
lean_dec(v___y_691_);
return v_res_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v_b_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_){
_start:
{
lean_object* v___x_707_; 
lean_inc(v___y_705_);
lean_inc_ref(v___y_704_);
lean_inc(v___y_703_);
lean_inc_ref(v___y_702_);
lean_inc(v___y_700_);
lean_inc(v___y_699_);
v___x_707_ = lean_apply_8(v_k_698_, v_b_701_, v___y_699_, v___y_700_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, lean_box(0));
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v_b_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_708_, v___y_709_, v___y_710_, v_b_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_718_, lean_object* v_type_719_, lean_object* v_val_720_, lean_object* v_k_721_, uint8_t v_nondep_722_, uint8_t v_kind_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v___f_731_; lean_object* v___x_732_; 
lean_inc(v___y_725_);
lean_inc(v___y_724_);
v___f_731_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_731_, 0, v_k_721_);
lean_closure_set(v___f_731_, 1, v___y_724_);
lean_closure_set(v___f_731_, 2, v___y_725_);
v___x_732_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_718_, v_type_719_, v_val_720_, v___f_731_, v_nondep_722_, v_kind_723_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
if (lean_obj_tag(v___x_732_) == 0)
{
return v___x_732_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_741_, lean_object* v_type_742_, lean_object* v_val_743_, lean_object* v_k_744_, lean_object* v_nondep_745_, lean_object* v_kind_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
uint8_t v_nondep_boxed_754_; uint8_t v_kind_boxed_755_; lean_object* v_res_756_; 
v_nondep_boxed_754_ = lean_unbox(v_nondep_745_);
v_kind_boxed_755_ = lean_unbox(v_kind_746_);
v_res_756_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_741_, v_type_742_, v_val_743_, v_k_744_, v_nondep_boxed_754_, v_kind_boxed_755_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec(v___y_747_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_757_, lean_object* v_f_758_, lean_object* v_body_759_, lean_object* v_x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
lean_object* v_res_768_; 
v_res_768_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_757_, v_f_758_, v_body_759_, v_x_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
return v_res_768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_769_, lean_object* v_fvars_770_, lean_object* v_a_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
if (lean_obj_tag(v_a_771_) == 8)
{
lean_object* v_declName_779_; lean_object* v_type_780_; lean_object* v_value_781_; lean_object* v_body_782_; lean_object* v_d_783_; lean_object* v___x_784_; 
v_declName_779_ = lean_ctor_get(v_a_771_, 0);
lean_inc(v_declName_779_);
v_type_780_ = lean_ctor_get(v_a_771_, 1);
lean_inc_ref(v_type_780_);
v_value_781_ = lean_ctor_get(v_a_771_, 2);
lean_inc_ref(v_value_781_);
v_body_782_ = lean_ctor_get(v_a_771_, 3);
lean_inc_ref(v_body_782_);
lean_dec_ref_known(v_a_771_, 4);
v_d_783_ = lean_expr_instantiate_rev(v_type_780_, v_fvars_770_);
lean_dec_ref(v_type_780_);
lean_inc_ref(v_f_769_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc(v___y_772_);
lean_inc_ref(v_d_783_);
v___x_784_ = lean_apply_8(v_f_769_, v_d_783_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_v_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_784_, 1);
v_v_785_ = lean_expr_instantiate_rev(v_value_781_, v_fvars_770_);
lean_dec_ref(v_value_781_);
lean_inc_ref(v_f_769_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc(v___y_772_);
lean_inc_ref(v_v_785_);
v___x_786_ = lean_apply_8(v_f_769_, v_v_785_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v___f_787_; uint8_t v___x_788_; uint8_t v___x_789_; lean_object* v___x_790_; 
lean_dec_ref_known(v___x_786_, 1);
v___f_787_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_787_, 0, v_fvars_770_);
lean_closure_set(v___f_787_, 1, v_f_769_);
lean_closure_set(v___f_787_, 2, v_body_782_);
v___x_788_ = 0;
v___x_789_ = 0;
v___x_790_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_779_, v_d_783_, v_v_785_, v___f_787_, v___x_788_, v___x_789_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_);
return v___x_790_;
}
else
{
lean_dec_ref(v_v_785_);
lean_dec_ref(v_d_783_);
lean_dec_ref(v_body_782_);
lean_dec(v_declName_779_);
lean_dec_ref(v_fvars_770_);
lean_dec_ref(v_f_769_);
return v___x_786_;
}
}
else
{
lean_dec_ref(v_d_783_);
lean_dec_ref(v_body_782_);
lean_dec_ref(v_value_781_);
lean_dec(v_declName_779_);
lean_dec_ref(v_fvars_770_);
lean_dec_ref(v_f_769_);
return v___x_784_;
}
}
else
{
lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_791_ = lean_expr_instantiate_rev(v_a_771_, v_fvars_770_);
lean_dec_ref(v_fvars_770_);
lean_dec_ref(v_a_771_);
lean_inc(v___y_777_);
lean_inc_ref(v___y_776_);
lean_inc(v___y_775_);
lean_inc_ref(v___y_774_);
lean_inc(v___y_773_);
lean_inc(v___y_772_);
v___x_792_ = lean_apply_8(v_f_769_, v___x_791_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, lean_box(0));
return v___x_792_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_793_, lean_object* v_f_794_, lean_object* v_body_795_, lean_object* v_x_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_){
_start:
{
lean_object* v___x_804_; lean_object* v___x_805_; 
v___x_804_ = lean_array_push(v_fvars_793_, v_x_796_);
v___x_805_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_794_, v___x_804_, v_body_795_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_);
return v___x_805_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_806_, lean_object* v_fvars_807_, lean_object* v_a_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v_res_816_; 
v_res_816_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_806_, v_fvars_807_, v_a_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec(v___y_809_);
return v_res_816_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_819_, lean_object* v_e_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_){
_start:
{
lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_828_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_829_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_819_, v___x_828_, v_e_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_830_, lean_object* v_e_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_830_, v_e_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_840_, uint8_t v_bi_841_, lean_object* v_type_842_, lean_object* v_k_843_, uint8_t v_kind_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v___f_852_; lean_object* v___x_853_; 
lean_inc(v___y_846_);
lean_inc(v___y_845_);
v___f_852_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_852_, 0, v_k_843_);
lean_closure_set(v___f_852_, 1, v___y_845_);
lean_closure_set(v___f_852_, 2, v___y_846_);
v___x_853_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_840_, v_bi_841_, v_type_842_, v___f_852_, v_kind_844_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
if (lean_obj_tag(v___x_853_) == 0)
{
return v___x_853_;
}
else
{
lean_object* v_a_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_861_; 
v_a_854_ = lean_ctor_get(v___x_853_, 0);
v_isSharedCheck_861_ = !lean_is_exclusive(v___x_853_);
if (v_isSharedCheck_861_ == 0)
{
v___x_856_ = v___x_853_;
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_a_854_);
lean_dec(v___x_853_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_861_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v___x_859_; 
if (v_isShared_857_ == 0)
{
v___x_859_ = v___x_856_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_854_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_862_, lean_object* v_bi_863_, lean_object* v_type_864_, lean_object* v_k_865_, lean_object* v_kind_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_){
_start:
{
uint8_t v_bi_boxed_874_; uint8_t v_kind_boxed_875_; lean_object* v_res_876_; 
v_bi_boxed_874_ = lean_unbox(v_bi_863_);
v_kind_boxed_875_ = lean_unbox(v_kind_866_);
v_res_876_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_862_, v_bi_boxed_874_, v_type_864_, v_k_865_, v_kind_boxed_875_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_, v___y_872_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec(v___y_867_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_877_, lean_object* v_f_878_, lean_object* v_body_879_, lean_object* v_x_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_877_, v_f_878_, v_body_879_, v_x_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec(v___y_881_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_889_, lean_object* v_fvars_890_, lean_object* v_a_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_){
_start:
{
if (lean_obj_tag(v_a_891_) == 7)
{
lean_object* v_binderName_899_; lean_object* v_binderType_900_; lean_object* v_body_901_; uint8_t v_binderInfo_902_; lean_object* v_d_903_; lean_object* v___x_904_; 
v_binderName_899_ = lean_ctor_get(v_a_891_, 0);
lean_inc(v_binderName_899_);
v_binderType_900_ = lean_ctor_get(v_a_891_, 1);
lean_inc_ref(v_binderType_900_);
v_body_901_ = lean_ctor_get(v_a_891_, 2);
lean_inc_ref(v_body_901_);
v_binderInfo_902_ = lean_ctor_get_uint8(v_a_891_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_891_, 3);
v_d_903_ = lean_expr_instantiate_rev(v_binderType_900_, v_fvars_890_);
lean_dec_ref(v_binderType_900_);
lean_inc_ref(v_f_889_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc(v___y_892_);
lean_inc_ref(v_d_903_);
v___x_904_ = lean_apply_8(v_f_889_, v_d_903_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, lean_box(0));
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___f_905_; uint8_t v___x_906_; lean_object* v___x_907_; 
lean_dec_ref_known(v___x_904_, 1);
v___f_905_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_905_, 0, v_fvars_890_);
lean_closure_set(v___f_905_, 1, v_f_889_);
lean_closure_set(v___f_905_, 2, v_body_901_);
v___x_906_ = 0;
v___x_907_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_899_, v_binderInfo_902_, v_d_903_, v___f_905_, v___x_906_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_);
return v___x_907_;
}
else
{
lean_dec_ref(v_d_903_);
lean_dec_ref(v_body_901_);
lean_dec(v_binderName_899_);
lean_dec_ref(v_fvars_890_);
lean_dec_ref(v_f_889_);
return v___x_904_;
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
v___x_908_ = lean_expr_instantiate_rev(v_a_891_, v_fvars_890_);
lean_dec_ref(v_fvars_890_);
lean_dec_ref(v_a_891_);
lean_inc(v___y_897_);
lean_inc_ref(v___y_896_);
lean_inc(v___y_895_);
lean_inc_ref(v___y_894_);
lean_inc(v___y_893_);
lean_inc(v___y_892_);
v___x_909_ = lean_apply_8(v_f_889_, v___x_908_, v___y_892_, v___y_893_, v___y_894_, v___y_895_, v___y_896_, v___y_897_, lean_box(0));
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_910_, lean_object* v_f_911_, lean_object* v_body_912_, lean_object* v_x_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_){
_start:
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_array_push(v_fvars_910_, v_x_913_);
v___x_922_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_911_, v___x_921_, v_body_912_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_);
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_923_, lean_object* v_fvars_924_, lean_object* v_a_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_923_, v_fvars_924_, v_a_925_, v___y_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
lean_dec(v___y_927_);
lean_dec(v___y_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_934_, lean_object* v_e_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_944_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_934_, v___x_943_, v_e_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
return v___x_944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_945_, lean_object* v_e_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_945_, v_e_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec(v___y_947_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_955_, lean_object* v_f_956_, lean_object* v_body_957_, lean_object* v_x_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_955_, v_f_956_, v_body_957_, v_x_958_, v___y_959_, v___y_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec_ref(v___y_961_);
lean_dec(v___y_960_);
lean_dec(v___y_959_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_967_, lean_object* v_fvars_968_, lean_object* v_a_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_){
_start:
{
if (lean_obj_tag(v_a_969_) == 6)
{
lean_object* v_binderName_977_; lean_object* v_binderType_978_; lean_object* v_body_979_; uint8_t v_binderInfo_980_; lean_object* v_d_981_; lean_object* v___x_982_; 
v_binderName_977_ = lean_ctor_get(v_a_969_, 0);
lean_inc(v_binderName_977_);
v_binderType_978_ = lean_ctor_get(v_a_969_, 1);
lean_inc_ref(v_binderType_978_);
v_body_979_ = lean_ctor_get(v_a_969_, 2);
lean_inc_ref(v_body_979_);
v_binderInfo_980_ = lean_ctor_get_uint8(v_a_969_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_969_, 3);
v_d_981_ = lean_expr_instantiate_rev(v_binderType_978_, v_fvars_968_);
lean_dec_ref(v_binderType_978_);
lean_inc_ref(v_f_967_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v_d_981_);
v___x_982_ = lean_apply_8(v_f_967_, v_d_981_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, lean_box(0));
if (lean_obj_tag(v___x_982_) == 0)
{
lean_object* v___f_983_; uint8_t v___x_984_; lean_object* v___x_985_; 
lean_dec_ref_known(v___x_982_, 1);
v___f_983_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_983_, 0, v_fvars_968_);
lean_closure_set(v___f_983_, 1, v_f_967_);
lean_closure_set(v___f_983_, 2, v_body_979_);
v___x_984_ = 0;
v___x_985_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_977_, v_binderInfo_980_, v_d_981_, v___f_983_, v___x_984_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
return v___x_985_;
}
else
{
lean_dec_ref(v_d_981_);
lean_dec_ref(v_body_979_);
lean_dec(v_binderName_977_);
lean_dec_ref(v_fvars_968_);
lean_dec_ref(v_f_967_);
return v___x_982_;
}
}
else
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = lean_expr_instantiate_rev(v_a_969_, v_fvars_968_);
lean_dec_ref(v_fvars_968_);
lean_dec_ref(v_a_969_);
lean_inc(v___y_975_);
lean_inc_ref(v___y_974_);
lean_inc(v___y_973_);
lean_inc_ref(v___y_972_);
lean_inc(v___y_971_);
lean_inc(v___y_970_);
v___x_987_ = lean_apply_8(v_f_967_, v___x_986_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, lean_box(0));
return v___x_987_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_988_, lean_object* v_f_989_, lean_object* v_body_990_, lean_object* v_x_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; lean_object* v___x_1000_; 
v___x_999_ = lean_array_push(v_fvars_988_, v_x_991_);
v___x_1000_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_989_, v___x_999_, v_body_990_, v___y_992_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1001_, lean_object* v_fvars_1002_, lean_object* v_a_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_){
_start:
{
lean_object* v_res_1011_; 
v_res_1011_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1001_, v_fvars_1002_, v_a_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
lean_dec(v___y_1009_);
lean_dec_ref(v___y_1008_);
lean_dec(v___y_1007_);
lean_dec_ref(v___y_1006_);
lean_dec(v___y_1005_);
lean_dec(v___y_1004_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1012_, lean_object* v_e_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1022_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1012_, v___x_1021_, v_e_1013_, v___y_1014_, v___y_1015_, v___y_1016_, v___y_1017_, v___y_1018_, v___y_1019_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1023_, lean_object* v_e_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_res_1032_; 
v_res_1032_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1023_, v_e_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec(v___y_1025_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1033_, lean_object* v_x_1034_){
_start:
{
if (lean_obj_tag(v_x_1034_) == 0)
{
lean_object* v___x_1035_; 
v___x_1035_ = lean_box(0);
return v___x_1035_;
}
else
{
lean_object* v_key_1036_; lean_object* v_value_1037_; lean_object* v_tail_1038_; uint8_t v___x_1039_; 
v_key_1036_ = lean_ctor_get(v_x_1034_, 0);
v_value_1037_ = lean_ctor_get(v_x_1034_, 1);
v_tail_1038_ = lean_ctor_get(v_x_1034_, 2);
v___x_1039_ = lean_expr_eqv(v_key_1036_, v_a_1033_);
if (v___x_1039_ == 0)
{
v_x_1034_ = v_tail_1038_;
goto _start;
}
else
{
lean_object* v___x_1041_; 
lean_inc(v_value_1037_);
v___x_1041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1041_, 0, v_value_1037_);
return v___x_1041_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v_res_1044_; 
v_res_1044_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1042_, v_x_1043_);
lean_dec(v_x_1043_);
lean_dec_ref(v_a_1042_);
return v_res_1044_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1045_, lean_object* v_a_1046_){
_start:
{
lean_object* v_buckets_1047_; lean_object* v___x_1048_; uint64_t v___x_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v_fold_1052_; uint64_t v___x_1053_; uint64_t v___x_1054_; uint64_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; size_t v___x_1058_; size_t v___x_1059_; size_t v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; 
v_buckets_1047_ = lean_ctor_get(v_m_1045_, 1);
v___x_1048_ = lean_array_get_size(v_buckets_1047_);
v___x_1049_ = l_Lean_Expr_hash(v_a_1046_);
v___x_1050_ = 32ULL;
v___x_1051_ = lean_uint64_shift_right(v___x_1049_, v___x_1050_);
v_fold_1052_ = lean_uint64_xor(v___x_1049_, v___x_1051_);
v___x_1053_ = 16ULL;
v___x_1054_ = lean_uint64_shift_right(v_fold_1052_, v___x_1053_);
v___x_1055_ = lean_uint64_xor(v_fold_1052_, v___x_1054_);
v___x_1056_ = lean_uint64_to_usize(v___x_1055_);
v___x_1057_ = lean_usize_of_nat(v___x_1048_);
v___x_1058_ = ((size_t)1ULL);
v___x_1059_ = lean_usize_sub(v___x_1057_, v___x_1058_);
v___x_1060_ = lean_usize_land(v___x_1056_, v___x_1059_);
v___x_1061_ = lean_array_uget_borrowed(v_buckets_1047_, v___x_1060_);
v___x_1062_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1046_, v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1063_, lean_object* v_a_1064_){
_start:
{
lean_object* v_res_1065_; 
v_res_1065_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1063_, v_a_1064_);
lean_dec_ref(v_a_1064_);
lean_dec_ref(v_m_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1066_, lean_object* v_x_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; 
v___x_1074_ = lean_apply_1(v_x_1067_, lean_box(0));
v___x_1075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1075_, 0, v___x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1076_, lean_object* v_x_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1076_, v_x_1077_, v___y_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
if (lean_obj_tag(v_x_1086_) == 0)
{
return v_x_1085_;
}
else
{
lean_object* v_key_1087_; lean_object* v_value_1088_; lean_object* v_tail_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1112_; 
v_key_1087_ = lean_ctor_get(v_x_1086_, 0);
v_value_1088_ = lean_ctor_get(v_x_1086_, 1);
v_tail_1089_ = lean_ctor_get(v_x_1086_, 2);
v_isSharedCheck_1112_ = !lean_is_exclusive(v_x_1086_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1091_ = v_x_1086_;
v_isShared_1092_ = v_isSharedCheck_1112_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_tail_1089_);
lean_inc(v_value_1088_);
lean_inc(v_key_1087_);
lean_dec(v_x_1086_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1112_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; uint64_t v___x_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v_fold_1097_; uint64_t v___x_1098_; uint64_t v___x_1099_; uint64_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; size_t v___x_1103_; size_t v___x_1104_; size_t v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1108_; 
v___x_1093_ = lean_array_get_size(v_x_1085_);
v___x_1094_ = l_Lean_Expr_hash(v_key_1087_);
v___x_1095_ = 32ULL;
v___x_1096_ = lean_uint64_shift_right(v___x_1094_, v___x_1095_);
v_fold_1097_ = lean_uint64_xor(v___x_1094_, v___x_1096_);
v___x_1098_ = 16ULL;
v___x_1099_ = lean_uint64_shift_right(v_fold_1097_, v___x_1098_);
v___x_1100_ = lean_uint64_xor(v_fold_1097_, v___x_1099_);
v___x_1101_ = lean_uint64_to_usize(v___x_1100_);
v___x_1102_ = lean_usize_of_nat(v___x_1093_);
v___x_1103_ = ((size_t)1ULL);
v___x_1104_ = lean_usize_sub(v___x_1102_, v___x_1103_);
v___x_1105_ = lean_usize_land(v___x_1101_, v___x_1104_);
v___x_1106_ = lean_array_uget_borrowed(v_x_1085_, v___x_1105_);
lean_inc(v___x_1106_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 2, v___x_1106_);
v___x_1108_ = v___x_1091_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_key_1087_);
lean_ctor_set(v_reuseFailAlloc_1111_, 1, v_value_1088_);
lean_ctor_set(v_reuseFailAlloc_1111_, 2, v___x_1106_);
v___x_1108_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_array_uset(v_x_1085_, v___x_1105_, v___x_1108_);
v_x_1085_ = v___x_1109_;
v_x_1086_ = v_tail_1089_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1113_, lean_object* v_source_1114_, lean_object* v_target_1115_){
_start:
{
lean_object* v___x_1116_; uint8_t v___x_1117_; 
v___x_1116_ = lean_array_get_size(v_source_1114_);
v___x_1117_ = lean_nat_dec_lt(v_i_1113_, v___x_1116_);
if (v___x_1117_ == 0)
{
lean_dec_ref(v_source_1114_);
lean_dec(v_i_1113_);
return v_target_1115_;
}
else
{
lean_object* v_es_1118_; lean_object* v___x_1119_; lean_object* v_source_1120_; lean_object* v_target_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_es_1118_ = lean_array_fget(v_source_1114_, v_i_1113_);
v___x_1119_ = lean_box(0);
v_source_1120_ = lean_array_fset(v_source_1114_, v_i_1113_, v___x_1119_);
v_target_1121_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1115_, v_es_1118_);
v___x_1122_ = lean_unsigned_to_nat(1u);
v___x_1123_ = lean_nat_add(v_i_1113_, v___x_1122_);
lean_dec(v_i_1113_);
v_i_1113_ = v___x_1123_;
v_source_1114_ = v_source_1120_;
v_target_1115_ = v_target_1121_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1125_){
_start:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v_nbuckets_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1126_ = lean_array_get_size(v_data_1125_);
v___x_1127_ = lean_unsigned_to_nat(2u);
v_nbuckets_1128_ = lean_nat_mul(v___x_1126_, v___x_1127_);
v___x_1129_ = lean_unsigned_to_nat(0u);
v___x_1130_ = lean_box(0);
v___x_1131_ = lean_mk_array(v_nbuckets_1128_, v___x_1130_);
v___x_1132_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1129_, v_data_1125_, v___x_1131_);
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
v___x_1215_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1214_, v_e_1211_, v_a_1212_);
v___x_1216_ = lean_st_ref_set(v_a_1210_, v___x_1215_);
v___x_1217_ = lean_box(0);
return v___x_1217_;
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
lean_dec_ref(v_fn_1233_);
v___y_1255_ = v___x_1276_;
goto v___jp_1254_;
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
lean_object* v_head_1399_; lean_object* v_tail_1400_; lean_object* v___y_1402_; lean_object* v_type_1405_; lean_object* v_ctors_1406_; lean_object* v___x_1407_; 
v_head_1399_ = lean_ctor_get(v_x_1391_, 0);
lean_inc(v_head_1399_);
v_tail_1400_ = lean_ctor_get(v_x_1391_, 1);
lean_inc(v_tail_1400_);
lean_dec_ref_known(v_x_1391_, 2);
v_type_1405_ = lean_ctor_get(v_head_1399_, 1);
lean_inc_ref(v_type_1405_);
v_ctors_1406_ = lean_ctor_get(v_head_1399_, 2);
lean_inc(v_ctors_1406_);
lean_dec(v_head_1399_);
lean_inc_ref(v_fn_1389_);
v___x_1407_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1405_, v_fn_1389_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_object* v_a_1408_; lean_object* v___x_1409_; 
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
lean_inc(v_a_1408_);
lean_dec_ref_known(v___x_1407_, 1);
lean_inc_ref(v_fn_1389_);
v___x_1409_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1389_, v_a_1408_, v_ctors_1406_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
v___y_1402_ = v___x_1409_;
goto v___jp_1401_;
}
else
{
lean_dec(v_ctors_1406_);
v___y_1402_ = v___x_1407_;
goto v___jp_1401_;
}
v___jp_1401_:
{
if (lean_obj_tag(v___y_1402_) == 0)
{
lean_object* v_a_1403_; 
v_a_1403_ = lean_ctor_get(v___y_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref_known(v___y_1402_, 1);
v_x_1390_ = v_a_1403_;
v_x_1391_ = v_tail_1400_;
goto _start;
}
else
{
lean_dec(v_tail_1400_);
lean_dec_ref(v_fn_1389_);
return v___y_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1410_, lean_object* v_x_1411_, lean_object* v_x_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v_res_1419_; 
v_res_1419_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1410_, v_x_1411_, v_x_1412_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_, v___y_1417_);
lean_dec(v___y_1417_);
lean_dec_ref(v___y_1416_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1420_, lean_object* v_x_1421_, lean_object* v_x_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_){
_start:
{
if (lean_obj_tag(v_x_1422_) == 0)
{
lean_object* v___x_1429_; 
lean_dec_ref(v_fn_1420_);
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_x_1421_);
return v___x_1429_;
}
else
{
lean_object* v_head_1430_; lean_object* v_tail_1431_; lean_object* v___y_1433_; lean_object* v_toConstantVal_1436_; lean_object* v_value_1437_; lean_object* v_type_1438_; lean_object* v___x_1439_; 
v_head_1430_ = lean_ctor_get(v_x_1422_, 0);
lean_inc(v_head_1430_);
v_tail_1431_ = lean_ctor_get(v_x_1422_, 1);
lean_inc(v_tail_1431_);
lean_dec_ref_known(v_x_1422_, 2);
v_toConstantVal_1436_ = lean_ctor_get(v_head_1430_, 0);
lean_inc_ref(v_toConstantVal_1436_);
v_value_1437_ = lean_ctor_get(v_head_1430_, 1);
lean_inc_ref(v_value_1437_);
lean_dec(v_head_1430_);
v_type_1438_ = lean_ctor_get(v_toConstantVal_1436_, 2);
lean_inc_ref(v_type_1438_);
lean_dec_ref(v_toConstantVal_1436_);
lean_inc_ref(v_fn_1420_);
v___x_1439_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1438_, v_fn_1420_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_object* v___x_1440_; 
lean_dec_ref_known(v___x_1439_, 1);
lean_inc_ref(v_fn_1420_);
v___x_1440_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1437_, v_fn_1420_, v___y_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
v___y_1433_ = v___x_1440_;
goto v___jp_1432_;
}
else
{
lean_dec_ref(v_value_1437_);
v___y_1433_ = v___x_1439_;
goto v___jp_1432_;
}
v___jp_1432_:
{
if (lean_obj_tag(v___y_1433_) == 0)
{
lean_object* v_a_1434_; 
v_a_1434_ = lean_ctor_get(v___y_1433_, 0);
lean_inc(v_a_1434_);
lean_dec_ref_known(v___y_1433_, 1);
v_x_1421_ = v_a_1434_;
v_x_1422_ = v_tail_1431_;
goto _start;
}
else
{
lean_dec(v_tail_1431_);
lean_dec_ref(v_fn_1420_);
return v___y_1433_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1441_, lean_object* v_x_1442_, lean_object* v_x_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_, lean_object* v___y_1448_, lean_object* v___y_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1441_, v_x_1442_, v_x_1443_, v___y_1444_, v___y_1445_, v___y_1446_, v___y_1447_, v___y_1448_);
lean_dec(v___y_1448_);
lean_dec_ref(v___y_1447_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1451_, lean_object* v_d_1452_, lean_object* v_a_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
switch(lean_obj_tag(v_d_1452_))
{
case 0:
{
lean_object* v_val_1460_; lean_object* v_toConstantVal_1461_; lean_object* v_type_1462_; lean_object* v___x_1463_; 
v_val_1460_ = lean_ctor_get(v_d_1452_, 0);
lean_inc_ref(v_val_1460_);
lean_dec_ref_known(v_d_1452_, 1);
v_toConstantVal_1461_ = lean_ctor_get(v_val_1460_, 0);
lean_inc_ref(v_toConstantVal_1461_);
lean_dec_ref(v_val_1460_);
v_type_1462_ = lean_ctor_get(v_toConstantVal_1461_, 2);
lean_inc_ref(v_type_1462_);
lean_dec_ref(v_toConstantVal_1461_);
v___x_1463_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1462_, v_fn_1451_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1463_;
}
case 4:
{
lean_object* v___x_1464_; 
lean_dec_ref(v_fn_1451_);
v___x_1464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1464_, 0, v_a_1453_);
return v___x_1464_;
}
case 5:
{
lean_object* v_defns_1465_; lean_object* v___x_1466_; 
v_defns_1465_ = lean_ctor_get(v_d_1452_, 0);
lean_inc(v_defns_1465_);
lean_dec_ref_known(v_d_1452_, 1);
v___x_1466_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1451_, v_a_1453_, v_defns_1465_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1466_;
}
case 6:
{
lean_object* v_types_1467_; lean_object* v___x_1468_; 
v_types_1467_ = lean_ctor_get(v_d_1452_, 2);
lean_inc(v_types_1467_);
lean_dec_ref_known(v_d_1452_, 3);
v___x_1468_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1451_, v_a_1453_, v_types_1467_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1468_;
}
default: 
{
lean_object* v_val_1469_; lean_object* v_toConstantVal_1470_; lean_object* v_value_1471_; lean_object* v_type_1472_; lean_object* v___x_1473_; 
v_val_1469_ = lean_ctor_get(v_d_1452_, 0);
lean_inc_ref(v_val_1469_);
lean_dec(v_d_1452_);
v_toConstantVal_1470_ = lean_ctor_get(v_val_1469_, 0);
lean_inc_ref(v_toConstantVal_1470_);
v_value_1471_ = lean_ctor_get(v_val_1469_, 1);
lean_inc_ref(v_value_1471_);
lean_dec_ref(v_val_1469_);
v_type_1472_ = lean_ctor_get(v_toConstantVal_1470_, 2);
lean_inc_ref(v_type_1472_);
lean_dec_ref(v_toConstantVal_1470_);
lean_inc_ref(v_fn_1451_);
v___x_1473_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1472_, v_fn_1451_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v___x_1474_; 
lean_dec_ref_known(v___x_1473_, 1);
v___x_1474_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1471_, v_fn_1451_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_, v___y_1458_);
return v___x_1474_;
}
else
{
lean_dec_ref(v_value_1471_);
lean_dec_ref(v_fn_1451_);
return v___x_1473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1475_, lean_object* v_d_1476_, lean_object* v_a_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1475_, v_d_1476_, v_a_1477_, v___y_1478_, v___y_1479_, v___y_1480_, v___y_1481_, v___y_1482_);
lean_dec(v___y_1482_);
lean_dec_ref(v___y_1481_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1485_, lean_object* v_fn_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; 
v___x_1493_ = lean_box(0);
v___x_1494_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1486_, v_decl_1485_, v___x_1493_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_, v___y_1491_);
return v___x_1494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1495_, lean_object* v_fn_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1495_, v_fn_1496_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
return v_res_1503_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__2));
v___x_1509_ = l_Lean_stringToMessageData(v___x_1508_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
v___x_1511_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__4));
v___x_1512_ = l_Lean_stringToMessageData(v___x_1511_);
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__6));
v___x_1515_ = l_Lean_stringToMessageData(v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__8(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1517_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1518_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__10(void){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1521_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__10, &l_Lean_warnIfUsesSorry___closed__10_once, _init_l_Lean_warnIfUsesSorry___closed__10);
v___x_1522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1523_ = lean_box(1);
v___x_1524_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1525_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
v___x_1526_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
lean_ctor_set(v___x_1526_, 2, v___x_1523_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1529_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1531_, 0, v___x_1530_);
lean_ctor_set(v___x_1531_, 1, v___x_1530_);
lean_ctor_set(v___x_1531_, 2, v___x_1530_);
lean_ctor_set(v___x_1531_, 3, v___x_1530_);
lean_ctor_set(v___x_1531_, 4, v___x_1529_);
lean_ctor_set(v___x_1531_, 5, v___x_1529_);
lean_ctor_set(v___x_1531_, 6, v___x_1529_);
lean_ctor_set(v___x_1531_, 7, v___x_1529_);
lean_ctor_set(v___x_1531_, 8, v___x_1529_);
lean_ctor_set(v___x_1531_, 9, v___x_1529_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
v___x_1533_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1532_);
lean_ctor_set(v___x_1533_, 2, v___x_1532_);
lean_ctor_set(v___x_1533_, 3, v___x_1532_);
lean_ctor_set(v___x_1533_, 4, v___x_1532_);
lean_ctor_set(v___x_1533_, 5, v___x_1532_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
v___x_1535_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1535_, 0, v___x_1534_);
lean_ctor_set(v___x_1535_, 1, v___x_1534_);
lean_ctor_set(v___x_1535_, 2, v___x_1534_);
lean_ctor_set(v___x_1535_, 3, v___x_1534_);
lean_ctor_set(v___x_1535_, 4, v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; 
v___x_1536_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1537_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1538_ = lean_box(1);
v___x_1539_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1540_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1541_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
lean_ctor_set(v___x_1541_, 1, v___x_1539_);
lean_ctor_set(v___x_1541_, 2, v___x_1538_);
lean_ctor_set(v___x_1541_, 3, v___x_1537_);
lean_ctor_set(v___x_1541_, 4, v___x_1536_);
return v___x_1541_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_val_1550_; lean_object* v___y_1567_; lean_object* v___y_1568_; lean_object* v_options_1574_; lean_object* v___x_1575_; uint8_t v___x_1576_; 
v_options_1574_ = lean_ctor_get(v_a_1546_, 2);
v___x_1575_ = l_Lean_warn_sorry;
v___x_1576_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1574_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
lean_dec(v_decl_1545_);
v___x_1577_ = lean_box(0);
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v___x_1577_);
return v___x_1578_;
}
else
{
lean_object* v___x_1579_; lean_object* v_messages_1580_; lean_object* v___f_1581_; uint8_t v___y_1583_; uint8_t v___x_1612_; uint8_t v___x_1613_; 
v___x_1579_ = lean_st_ref_get(v_a_1547_);
v_messages_1580_ = lean_ctor_get(v___x_1579_, 6);
lean_inc_ref(v_messages_1580_);
lean_dec(v___x_1579_);
v___f_1581_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1612_ = l_Lean_MessageLog_hasErrors(v_messages_1580_);
lean_dec_ref(v_messages_1580_);
v___x_1613_ = lean_bool_not(v___x_1612_);
if (v___x_1613_ == 0)
{
v___y_1583_ = v___x_1613_;
goto v___jp_1582_;
}
else
{
uint8_t v___x_1614_; 
v___x_1614_ = l_Lean_Declaration_hasSorry(v_decl_1545_);
v___y_1583_ = v___x_1614_;
goto v___jp_1582_;
}
v___jp_1582_:
{
if (v___y_1583_ == 0)
{
lean_object* v___x_1584_; lean_object* v___x_1585_; 
lean_dec(v_decl_1545_);
v___x_1584_ = lean_box(0);
v___x_1585_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
return v___x_1585_;
}
else
{
uint8_t v___x_1586_; uint8_t v___x_1587_; uint8_t v___x_1588_; uint8_t v___x_1589_; lean_object* v___x_1590_; uint64_t v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1586_ = 0;
v___x_1587_ = 1;
v___x_1588_ = 0;
v___x_1589_ = 2;
v___x_1590_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1590_, 0, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 1, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 2, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 3, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 4, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 5, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 6, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 7, v___x_1586_);
lean_ctor_set_uint8(v___x_1590_, 8, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 9, v___x_1587_);
lean_ctor_set_uint8(v___x_1590_, 10, v___x_1588_);
lean_ctor_set_uint8(v___x_1590_, 11, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 12, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 13, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 14, v___x_1589_);
lean_ctor_set_uint8(v___x_1590_, 15, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 16, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 17, v___y_1583_);
lean_ctor_set_uint8(v___x_1590_, 18, v___y_1583_);
v___x_1591_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1590_);
v___x_1592_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1592_, 0, v___x_1590_);
lean_ctor_set_uint64(v___x_1592_, sizeof(void*)*1, v___x_1591_);
v___x_1593_ = lean_box(1);
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
v___x_1596_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1597_ = lean_box(0);
v___x_1598_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1598_, 0, v___x_1592_);
lean_ctor_set(v___x_1598_, 1, v___x_1593_);
lean_ctor_set(v___x_1598_, 2, v___x_1595_);
lean_ctor_set(v___x_1598_, 3, v___x_1596_);
lean_ctor_set(v___x_1598_, 4, v___x_1597_);
lean_ctor_set(v___x_1598_, 5, v___x_1594_);
lean_ctor_set(v___x_1598_, 6, v___x_1597_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*7, v___x_1586_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*7 + 1, v___x_1586_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*7 + 2, v___x_1586_);
lean_ctor_set_uint8(v___x_1598_, sizeof(void*)*7 + 3, v___x_1576_);
v___x_1599_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1600_ = lean_st_mk_ref(v___x_1599_);
v___x_1601_ = lean_st_mk_ref(v___x_1596_);
v___x_1602_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1545_, v___f_1581_, v___x_1601_, v___x_1598_, v___x_1600_, v_a_1546_, v_a_1547_);
lean_dec_ref_known(v___x_1598_, 7);
if (lean_obj_tag(v___x_1602_) == 0)
{
lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; size_t v_sz_1606_; size_t v___x_1607_; lean_object* v___x_1608_; lean_object* v_fst_1609_; 
lean_dec_ref_known(v___x_1602_, 1);
v___x_1603_ = lean_st_ref_get(v___x_1601_);
lean_dec(v___x_1601_);
v___x_1604_ = lean_st_ref_get(v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v___x_1604_);
v___x_1605_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1606_ = lean_array_size(v___x_1603_);
v___x_1607_ = ((size_t)0ULL);
v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1603_, v_sz_1606_, v___x_1607_, v___x_1605_);
v_fst_1609_ = lean_ctor_get(v___x_1608_, 0);
lean_inc(v_fst_1609_);
lean_dec_ref(v___x_1608_);
if (lean_obj_tag(v_fst_1609_) == 0)
{
v___y_1567_ = v___x_1603_;
v___y_1568_ = v___x_1594_;
goto v___jp_1566_;
}
else
{
lean_object* v_val_1610_; 
v_val_1610_ = lean_ctor_get(v_fst_1609_, 0);
lean_inc(v_val_1610_);
lean_dec_ref_known(v_fst_1609_, 1);
if (lean_obj_tag(v_val_1610_) == 0)
{
v___y_1567_ = v___x_1603_;
v___y_1568_ = v___x_1594_;
goto v___jp_1566_;
}
else
{
lean_object* v_val_1611_; 
lean_dec(v___x_1603_);
v_val_1611_ = lean_ctor_get(v_val_1610_, 0);
lean_inc(v_val_1611_);
lean_dec_ref_known(v_val_1610_, 1);
v_val_1550_ = v_val_1611_;
goto v___jp_1549_;
}
}
}
else
{
lean_dec(v___x_1601_);
lean_dec(v___x_1600_);
return v___x_1602_;
}
}
}
}
v___jp_1549_:
{
lean_object* v_snd_1551_; lean_object* v___x_1553_; uint8_t v_isShared_1554_; uint8_t v_isSharedCheck_1564_; 
v_snd_1551_ = lean_ctor_get(v_val_1550_, 1);
v_isSharedCheck_1564_ = !lean_is_exclusive(v_val_1550_);
if (v_isSharedCheck_1564_ == 0)
{
lean_object* v_unused_1565_; 
v_unused_1565_ = lean_ctor_get(v_val_1550_, 0);
lean_dec(v_unused_1565_);
v___x_1553_ = v_val_1550_;
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
else
{
lean_inc(v_snd_1551_);
lean_dec(v_val_1550_);
v___x_1553_ = lean_box(0);
v_isShared_1554_ = v_isSharedCheck_1564_;
goto v_resetjp_1552_;
}
v_resetjp_1552_:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1555_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1556_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
if (v_isShared_1554_ == 0)
{
lean_ctor_set_tag(v___x_1553_, 7);
lean_ctor_set(v___x_1553_, 0, v___x_1556_);
v___x_1558_ = v___x_1553_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1563_; 
v_reuseFailAlloc_1563_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1563_, 0, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1563_, 1, v_snd_1551_);
v___x_1558_ = v_reuseFailAlloc_1563_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; 
v___x_1559_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1560_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1558_);
lean_ctor_set(v___x_1560_, 1, v___x_1559_);
v___x_1561_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1555_);
lean_ctor_set(v___x_1561_, 1, v___x_1560_);
v___x_1562_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1561_, v_a_1546_, v_a_1547_);
return v___x_1562_;
}
}
}
v___jp_1566_:
{
lean_object* v___x_1569_; uint8_t v___x_1570_; 
v___x_1569_ = lean_array_get_size(v___y_1567_);
v___x_1570_ = lean_nat_dec_lt(v___y_1568_, v___x_1569_);
if (v___x_1570_ == 0)
{
lean_object* v___x_1571_; lean_object* v___x_1572_; 
lean_dec_ref(v___y_1567_);
v___x_1571_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__8, &l_Lean_warnIfUsesSorry___closed__8_once, _init_l_Lean_warnIfUsesSorry___closed__8);
v___x_1572_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1571_, v_a_1546_, v_a_1547_);
return v___x_1572_;
}
else
{
lean_object* v___x_1573_; 
v___x_1573_ = lean_array_fget(v___y_1567_, v___y_1568_);
lean_dec_ref(v___y_1567_);
v_val_1550_ = v___x_1573_;
goto v___jp_1549_;
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
lean_object* v___x_1787_; lean_object* v_nextMacroScope_1788_; lean_object* v_ngen_1789_; lean_object* v_auxDeclNGen_1790_; lean_object* v_traceState_1791_; lean_object* v_messages_1792_; lean_object* v_infoState_1793_; lean_object* v_snapshotTasks_1794_; lean_object* v___x_1796_; uint8_t v_isShared_1797_; uint8_t v_isSharedCheck_1805_; 
v___x_1787_ = lean_st_ref_take(v___y_1785_);
v_nextMacroScope_1788_ = lean_ctor_get(v___x_1787_, 1);
v_ngen_1789_ = lean_ctor_get(v___x_1787_, 2);
v_auxDeclNGen_1790_ = lean_ctor_get(v___x_1787_, 3);
v_traceState_1791_ = lean_ctor_get(v___x_1787_, 4);
v_messages_1792_ = lean_ctor_get(v___x_1787_, 6);
v_infoState_1793_ = lean_ctor_get(v___x_1787_, 7);
v_snapshotTasks_1794_ = lean_ctor_get(v___x_1787_, 8);
v_isSharedCheck_1805_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1805_ == 0)
{
lean_object* v_unused_1806_; lean_object* v_unused_1807_; 
v_unused_1806_ = lean_ctor_get(v___x_1787_, 5);
lean_dec(v_unused_1806_);
v_unused_1807_ = lean_ctor_get(v___x_1787_, 0);
lean_dec(v_unused_1807_);
v___x_1796_ = v___x_1787_;
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
else
{
lean_inc(v_snapshotTasks_1794_);
lean_inc(v_infoState_1793_);
lean_inc(v_messages_1792_);
lean_inc(v_traceState_1791_);
lean_inc(v_auxDeclNGen_1790_);
lean_inc(v_ngen_1789_);
lean_inc(v_nextMacroScope_1788_);
lean_dec(v___x_1787_);
v___x_1796_ = lean_box(0);
v_isShared_1797_ = v_isSharedCheck_1805_;
goto v_resetjp_1795_;
}
v_resetjp_1795_:
{
lean_object* v___x_1798_; lean_object* v___x_1800_; 
v___x_1798_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1797_ == 0)
{
lean_ctor_set(v___x_1796_, 5, v___x_1798_);
lean_ctor_set(v___x_1796_, 0, v_env_1784_);
v___x_1800_ = v___x_1796_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1804_; 
v_reuseFailAlloc_1804_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1804_, 0, v_env_1784_);
lean_ctor_set(v_reuseFailAlloc_1804_, 1, v_nextMacroScope_1788_);
lean_ctor_set(v_reuseFailAlloc_1804_, 2, v_ngen_1789_);
lean_ctor_set(v_reuseFailAlloc_1804_, 3, v_auxDeclNGen_1790_);
lean_ctor_set(v_reuseFailAlloc_1804_, 4, v_traceState_1791_);
lean_ctor_set(v_reuseFailAlloc_1804_, 5, v___x_1798_);
lean_ctor_set(v_reuseFailAlloc_1804_, 6, v_messages_1792_);
lean_ctor_set(v_reuseFailAlloc_1804_, 7, v_infoState_1793_);
lean_ctor_set(v_reuseFailAlloc_1804_, 8, v_snapshotTasks_1794_);
v___x_1800_ = v_reuseFailAlloc_1804_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; 
v___x_1801_ = lean_st_ref_set(v___y_1785_, v___x_1800_);
v___x_1802_ = lean_box(0);
v___x_1803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
return v___x_1803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_){
_start:
{
lean_object* v_res_1811_; 
v_res_1811_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1808_, v___y_1809_);
lean_dec(v___y_1809_);
return v_res_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
lean_object* v___x_1816_; 
v___x_1816_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1812_, v___y_1814_);
return v___x_1816_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1817_, v___y_1818_, v___y_1819_);
lean_dec(v___y_1819_);
lean_dec_ref(v___y_1818_);
return v_res_1821_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_box(0);
v___x_1823_ = l_Lean_interruptExceptionId;
v___x_1824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1824_, 0, v___x_1823_);
lean_ctor_set(v___x_1824_, 1, v___x_1822_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1826_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_ref_1834_; lean_object* v___x_1835_; lean_object* v_a_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_1844_; 
v_ref_1834_ = lean_ctor_get(v___y_1831_, 5);
v___x_1835_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1830_, v___y_1831_, v___y_1832_);
v_a_1836_ = lean_ctor_get(v___x_1835_, 0);
v_isSharedCheck_1844_ = !lean_is_exclusive(v___x_1835_);
if (v_isSharedCheck_1844_ == 0)
{
v___x_1838_ = v___x_1835_;
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_a_1836_);
lean_dec(v___x_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_1844_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1842_; 
lean_inc(v_ref_1834_);
v___x_1840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1840_, 0, v_ref_1834_);
lean_ctor_set(v___x_1840_, 1, v_a_1836_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set_tag(v___x_1838_, 1);
lean_ctor_set(v___x_1838_, 0, v___x_1840_);
v___x_1842_ = v___x_1838_;
goto v_reusejp_1841_;
}
else
{
lean_object* v_reuseFailAlloc_1843_; 
v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1843_, 0, v___x_1840_);
v___x_1842_ = v_reuseFailAlloc_1843_;
goto v_reusejp_1841_;
}
v_reusejp_1841_:
{
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1845_, v___y_1846_, v___y_1847_);
lean_dec(v___y_1847_);
lean_dec_ref(v___y_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v___y_1855_; lean_object* v___y_1856_; 
if (lean_obj_tag(v_ex_1850_) == 16)
{
lean_object* v___x_1860_; lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
v___x_1860_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
else
{
v___y_1855_ = v___y_1851_;
v___y_1856_ = v___y_1852_;
goto v___jp_1854_;
}
v___jp_1854_:
{
lean_object* v_options_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; 
v_options_1857_ = lean_ctor_get(v___y_1855_, 2);
lean_inc_ref(v_options_1857_);
v___x_1858_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1850_, v_options_1857_);
v___x_1859_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1858_, v___y_1855_, v___y_1856_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_){
_start:
{
lean_object* v_res_1873_; 
v_res_1873_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1869_, v___y_1870_, v___y_1871_);
lean_dec(v___y_1871_);
lean_dec_ref(v___y_1870_);
return v_res_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_){
_start:
{
if (lean_obj_tag(v_x_1874_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v_x_1874_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v_x_1874_, 1);
v___x_1879_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1878_, v___y_1875_, v___y_1876_);
return v___x_1879_;
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
v_a_1880_ = lean_ctor_get(v_x_1874_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v_x_1874_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v_x_1874_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v_x_1874_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
lean_ctor_set_tag(v___x_1882_, 0);
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1888_, lean_object* v___y_1889_, lean_object* v___y_1890_, lean_object* v___y_1891_){
_start:
{
lean_object* v_res_1892_; 
v_res_1892_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1888_, v___y_1889_, v___y_1890_);
lean_dec(v___y_1890_);
lean_dec_ref(v___y_1889_);
return v_res_1892_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1893_ = lean_unsigned_to_nat(1u);
v___x_1894_ = l_Lean_Level_ofNat(v___x_1893_);
return v___x_1894_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_box(0);
v___x_1896_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1897_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
lean_ctor_set(v___x_1897_, 1, v___x_1895_);
return v___x_1897_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1905_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1906_ = l_Lean_mkConst(v___x_1905_, v___x_1904_);
return v___x_1906_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_unsigned_to_nat(0u);
v___x_1908_ = l_Lean_Level_ofNat(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; 
v___x_1909_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1910_ = l_Lean_mkSort(v___x_1909_);
return v___x_1910_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; 
v___x_1916_ = lean_box(0);
v___x_1917_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1918_ = l_Lean_mkConst(v___x_1917_, v___x_1916_);
return v___x_1918_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1919_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1920_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1921_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1922_ = l_Lean_mkAppB(v___x_1921_, v___x_1920_, v___x_1919_);
return v___x_1922_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1928_, lean_object* v_b_1929_, lean_object* v___y_1930_, lean_object* v___y_1931_){
_start:
{
if (lean_obj_tag(v_as_x27_1928_) == 0)
{
lean_object* v___x_1933_; 
v___x_1933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1933_, 0, v_b_1929_);
return v___x_1933_;
}
else
{
lean_object* v_head_1934_; lean_object* v_tail_1935_; lean_object* v___x_1936_; lean_object* v_env_1937_; lean_object* v_options_1938_; lean_object* v_cancelTk_x3f_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___y_1943_; uint8_t v___y_1944_; lean_object* v_a_1948_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
lean_dec_ref(v_b_1929_);
v_head_1934_ = lean_ctor_get(v_as_x27_1928_, 0);
v_tail_1935_ = lean_ctor_get(v_as_x27_1928_, 1);
v___x_1936_ = lean_st_ref_get(v___y_1931_);
v_env_1937_ = lean_ctor_get(v___x_1936_, 0);
lean_inc_ref(v_env_1937_);
lean_dec(v___x_1936_);
v_options_1938_ = lean_ctor_get(v___y_1930_, 2);
v_cancelTk_x3f_1939_ = lean_ctor_get(v___y_1930_, 12);
v___x_1940_ = lean_box(0);
v___x_1941_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1951_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1934_);
v___x_1952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1952_, 0, v_head_1934_);
lean_ctor_set(v___x_1952_, 1, v___x_1940_);
lean_ctor_set(v___x_1952_, 2, v___x_1951_);
v___x_1953_ = 0;
v___x_1954_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1954_, 0, v___x_1952_);
lean_ctor_set_uint8(v___x_1954_, sizeof(void*)*1, v___x_1953_);
v___x_1955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
v___x_1956_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1937_, v_options_1938_, v___x_1955_, v_cancelTk_x3f_1939_);
lean_dec_ref_known(v___x_1955_, 1);
v___x_1957_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1956_, v___y_1930_, v___y_1931_);
if (lean_obj_tag(v___x_1957_) == 0)
{
lean_object* v_a_1958_; lean_object* v___x_1959_; lean_object* v___x_1961_; uint8_t v_isShared_1962_; uint8_t v_isSharedCheck_1967_; 
v_a_1958_ = lean_ctor_get(v___x_1957_, 0);
lean_inc(v_a_1958_);
lean_dec_ref_known(v___x_1957_, 1);
v___x_1959_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1958_, v___y_1931_);
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
v_a_1948_ = v_a_1969_;
goto v___jp_1947_;
}
v___jp_1942_:
{
if (v___y_1944_ == 0)
{
lean_dec_ref(v___y_1943_);
v_as_x27_1928_ = v_tail_1935_;
v_b_1929_ = v___x_1941_;
goto _start;
}
else
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1946_, 0, v___y_1943_);
return v___x_1946_;
}
}
v___jp_1947_:
{
uint8_t v___x_1949_; 
v___x_1949_ = l_Lean_Exception_isInterrupt(v_a_1948_);
if (v___x_1949_ == 0)
{
uint8_t v___x_1950_; 
lean_inc_ref(v_a_1948_);
v___x_1950_ = l_Lean_Exception_isRuntime(v_a_1948_);
v___y_1943_ = v_a_1948_;
v___y_1944_ = v___x_1950_;
goto v___jp_1942_;
}
else
{
v___y_1943_ = v_a_1948_;
v___y_1944_ = v___x_1949_;
goto v___jp_1942_;
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
lean_object* v_val_2024_; lean_object* v___x_2025_; lean_object* v_toConstantVal_2026_; lean_object* v_env_2027_; lean_object* v_options_2028_; lean_object* v_cancelTk_x3f_2029_; uint8_t v___x_2030_; lean_object* v___x_2031_; lean_object* v_fallbackDecl_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v_val_2024_ = lean_ctor_get(v_decl_1976_, 0);
v___x_2025_ = lean_st_ref_get(v_a_1978_);
v_toConstantVal_2026_ = lean_ctor_get(v_val_2024_, 0);
v_env_2027_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_ref(v_env_2027_);
lean_dec(v___x_2025_);
v_options_2028_ = lean_ctor_get(v_a_1977_, 2);
v_cancelTk_x3f_2029_ = lean_ctor_get(v_a_1977_, 12);
v___x_2030_ = 0;
lean_inc_ref(v_toConstantVal_2026_);
v___x_2031_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2031_, 0, v_toConstantVal_2026_);
lean_ctor_set_uint8(v___x_2031_, sizeof(void*)*1, v___x_2030_);
v_fallbackDecl_2032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2032_, 0, v___x_2031_);
v___x_2033_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2027_, v_options_2028_, v_fallbackDecl_2032_, v_cancelTk_x3f_2029_);
lean_dec_ref_known(v_fallbackDecl_2032_, 1);
v___x_2034_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2033_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___x_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2044_; 
lean_dec_ref_known(v_decl_1976_, 1);
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2036_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2035_, v_a_1978_);
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
v_a_2013_ = v_a_2046_;
goto v___jp_2012_;
}
}
case 2:
{
lean_object* v_val_2047_; lean_object* v___x_2048_; lean_object* v_toConstantVal_2049_; lean_object* v_env_2050_; lean_object* v_options_2051_; lean_object* v_cancelTk_x3f_2052_; uint8_t v___x_2053_; lean_object* v___x_2054_; lean_object* v_fallbackDecl_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; 
v_val_2047_ = lean_ctor_get(v_decl_1976_, 0);
v___x_2048_ = lean_st_ref_get(v_a_1978_);
v_toConstantVal_2049_ = lean_ctor_get(v_val_2047_, 0);
v_env_2050_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_ref(v_env_2050_);
lean_dec(v___x_2048_);
v_options_2051_ = lean_ctor_get(v_a_1977_, 2);
v_cancelTk_x3f_2052_ = lean_ctor_get(v_a_1977_, 12);
v___x_2053_ = 0;
lean_inc_ref(v_toConstantVal_2049_);
v___x_2054_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2054_, 0, v_toConstantVal_2049_);
lean_ctor_set_uint8(v___x_2054_, sizeof(void*)*1, v___x_2053_);
v_fallbackDecl_2055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2055_, 0, v___x_2054_);
v___x_2056_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2050_, v_options_2051_, v_fallbackDecl_2055_, v_cancelTk_x3f_2052_);
lean_dec_ref_known(v_fallbackDecl_2055_, 1);
v___x_2057_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2056_, v_a_1977_, v_a_1978_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; lean_object* v___x_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2067_; 
lean_dec_ref_known(v_decl_1976_, 1);
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2058_, v_a_1978_);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2059_);
if (v_isSharedCheck_2067_ == 0)
{
lean_object* v_unused_2068_; 
v_unused_2068_ = lean_ctor_get(v___x_2059_, 0);
lean_dec(v_unused_2068_);
v___x_2061_ = v___x_2059_;
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
else
{
lean_dec(v___x_2059_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2067_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2063_; lean_object* v___x_2065_; 
v___x_2063_ = lean_box(0);
if (v_isShared_2062_ == 0)
{
lean_ctor_set(v___x_2061_, 0, v___x_2063_);
v___x_2065_ = v___x_2061_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
else
{
lean_object* v_a_2069_; 
v_a_2069_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2057_, 1);
v_a_2021_ = v_a_2069_;
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
v___x_1985_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2070_, lean_object* v_a_2071_, lean_object* v_a_2072_, lean_object* v_a_2073_){
_start:
{
lean_object* v_res_2074_; 
v_res_2074_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2070_, v_a_2071_, v_a_2072_);
lean_dec(v_a_2072_);
lean_dec_ref(v_a_2071_);
return v_res_2074_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2075_, lean_object* v_x_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
lean_object* v___x_2080_; 
v___x_2080_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2076_, v___y_2077_, v___y_2078_);
return v___x_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2081_, v_x_2082_, v___y_2083_, v___y_2084_);
lean_dec(v___y_2084_);
lean_dec_ref(v___y_2083_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2087_, lean_object* v_as_x27_2088_, lean_object* v_b_2089_, lean_object* v_a_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2088_, v_b_2089_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2095_, lean_object* v_as_x27_2096_, lean_object* v_b_2097_, lean_object* v_a_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v_res_2102_; 
v_res_2102_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2095_, v_as_x27_2096_, v_b_2097_, v_a_2098_, v___y_2099_, v___y_2100_);
lean_dec(v___y_2100_);
lean_dec_ref(v___y_2099_);
lean_dec(v_as_x27_2096_);
lean_dec(v_as_2095_);
return v_res_2102_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
lean_object* v___x_2107_; 
v___x_2107_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2108_, lean_object* v___y_2109_, lean_object* v___y_2110_, lean_object* v___y_2111_){
_start:
{
lean_object* v_res_2112_; 
v_res_2112_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2108_, v___y_2109_, v___y_2110_);
lean_dec(v___y_2110_);
lean_dec_ref(v___y_2109_);
return v_res_2112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2113_, lean_object* v_ex_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_){
_start:
{
lean_object* v___x_2118_; 
v___x_2118_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2114_, v___y_2115_, v___y_2116_);
return v___x_2118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2119_, lean_object* v_ex_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_res_2124_; 
v_res_2124_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2119_, v_ex_2120_, v___y_2121_, v___y_2122_);
lean_dec(v___y_2122_);
lean_dec_ref(v___y_2121_);
return v_res_2124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2125_, lean_object* v_msg_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_){
_start:
{
lean_object* v___x_2130_; 
v___x_2130_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2126_, v___y_2127_, v___y_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2131_, lean_object* v_msg_2132_, lean_object* v___y_2133_, lean_object* v___y_2134_, lean_object* v___y_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2131_, v_msg_2132_, v___y_2133_, v___y_2134_);
lean_dec(v___y_2134_);
lean_dec_ref(v___y_2133_);
return v_res_2136_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v___x_2137_ = lean_unsigned_to_nat(32u);
v___x_2138_ = lean_mk_empty_array_with_capacity(v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
return v___x_2139_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2140_ = ((size_t)5ULL);
v___x_2141_ = lean_unsigned_to_nat(0u);
v___x_2142_ = lean_unsigned_to_nat(32u);
v___x_2143_ = lean_mk_empty_array_with_capacity(v___x_2142_);
v___x_2144_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2145_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2145_, 0, v___x_2144_);
lean_ctor_set(v___x_2145_, 1, v___x_2143_);
lean_ctor_set(v___x_2145_, 2, v___x_2141_);
lean_ctor_set(v___x_2145_, 3, v___x_2141_);
lean_ctor_set_usize(v___x_2145_, 4, v___x_2140_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2146_){
_start:
{
lean_object* v___x_2148_; lean_object* v_traceState_2149_; lean_object* v_traces_2150_; lean_object* v___x_2151_; lean_object* v_traceState_2152_; lean_object* v_env_2153_; lean_object* v_nextMacroScope_2154_; lean_object* v_ngen_2155_; lean_object* v_auxDeclNGen_2156_; lean_object* v_cache_2157_; lean_object* v_messages_2158_; lean_object* v_infoState_2159_; lean_object* v_snapshotTasks_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2179_; 
v___x_2148_ = lean_st_ref_get(v___y_2146_);
v_traceState_2149_ = lean_ctor_get(v___x_2148_, 4);
lean_inc_ref(v_traceState_2149_);
lean_dec(v___x_2148_);
v_traces_2150_ = lean_ctor_get(v_traceState_2149_, 0);
lean_inc_ref(v_traces_2150_);
lean_dec_ref(v_traceState_2149_);
v___x_2151_ = lean_st_ref_take(v___y_2146_);
v_traceState_2152_ = lean_ctor_get(v___x_2151_, 4);
v_env_2153_ = lean_ctor_get(v___x_2151_, 0);
v_nextMacroScope_2154_ = lean_ctor_get(v___x_2151_, 1);
v_ngen_2155_ = lean_ctor_get(v___x_2151_, 2);
v_auxDeclNGen_2156_ = lean_ctor_get(v___x_2151_, 3);
v_cache_2157_ = lean_ctor_get(v___x_2151_, 5);
v_messages_2158_ = lean_ctor_get(v___x_2151_, 6);
v_infoState_2159_ = lean_ctor_get(v___x_2151_, 7);
v_snapshotTasks_2160_ = lean_ctor_get(v___x_2151_, 8);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2162_ = v___x_2151_;
v_isShared_2163_ = v_isSharedCheck_2179_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_snapshotTasks_2160_);
lean_inc(v_infoState_2159_);
lean_inc(v_messages_2158_);
lean_inc(v_cache_2157_);
lean_inc(v_traceState_2152_);
lean_inc(v_auxDeclNGen_2156_);
lean_inc(v_ngen_2155_);
lean_inc(v_nextMacroScope_2154_);
lean_inc(v_env_2153_);
lean_dec(v___x_2151_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2179_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
uint64_t v_tid_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2177_; 
v_tid_2164_ = lean_ctor_get_uint64(v_traceState_2152_, sizeof(void*)*1);
v_isSharedCheck_2177_ = !lean_is_exclusive(v_traceState_2152_);
if (v_isSharedCheck_2177_ == 0)
{
lean_object* v_unused_2178_; 
v_unused_2178_ = lean_ctor_get(v_traceState_2152_, 0);
lean_dec(v_unused_2178_);
v___x_2166_ = v_traceState_2152_;
v_isShared_2167_ = v_isSharedCheck_2177_;
goto v_resetjp_2165_;
}
else
{
lean_dec(v_traceState_2152_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2177_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2168_; lean_object* v___x_2170_; 
v___x_2168_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2167_ == 0)
{
lean_ctor_set(v___x_2166_, 0, v___x_2168_);
v___x_2170_ = v___x_2166_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v___x_2168_);
lean_ctor_set_uint64(v_reuseFailAlloc_2176_, sizeof(void*)*1, v_tid_2164_);
v___x_2170_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
lean_object* v___x_2172_; 
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 4, v___x_2170_);
v___x_2172_ = v___x_2162_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_env_2153_);
lean_ctor_set(v_reuseFailAlloc_2175_, 1, v_nextMacroScope_2154_);
lean_ctor_set(v_reuseFailAlloc_2175_, 2, v_ngen_2155_);
lean_ctor_set(v_reuseFailAlloc_2175_, 3, v_auxDeclNGen_2156_);
lean_ctor_set(v_reuseFailAlloc_2175_, 4, v___x_2170_);
lean_ctor_set(v_reuseFailAlloc_2175_, 5, v_cache_2157_);
lean_ctor_set(v_reuseFailAlloc_2175_, 6, v_messages_2158_);
lean_ctor_set(v_reuseFailAlloc_2175_, 7, v_infoState_2159_);
lean_ctor_set(v_reuseFailAlloc_2175_, 8, v_snapshotTasks_2160_);
v___x_2172_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2173_ = lean_st_ref_set(v___y_2146_, v___x_2172_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_traces_2150_);
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2180_, lean_object* v___y_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2180_);
lean_dec(v___y_2180_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2184_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2187_, v___y_2188_);
lean_dec(v___y_2188_);
lean_dec_ref(v___y_2187_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2191_, lean_object* v_opts_2192_, lean_object* v_act_2193_, lean_object* v_decl_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
lean_inc(v___y_2196_);
lean_inc_ref(v___y_2195_);
v___x_2198_ = lean_apply_2(v_act_2193_, v___y_2195_, v___y_2196_);
v___x_2199_ = l_Lean_profileitIOUnsafe___redArg(v_category_2191_, v_opts_2192_, v___x_2198_, v_decl_2194_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2200_, lean_object* v_opts_2201_, lean_object* v_act_2202_, lean_object* v_decl_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
lean_object* v_res_2207_; 
v_res_2207_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2200_, v_opts_2201_, v_act_2202_, v_decl_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec_ref(v_opts_2201_);
lean_dec_ref(v_category_2200_);
return v_res_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2208_, lean_object* v_category_2209_, lean_object* v_opts_2210_, lean_object* v_act_2211_, lean_object* v_decl_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v___x_2216_; 
v___x_2216_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2209_, v_opts_2210_, v_act_2211_, v_decl_2212_, v___y_2213_, v___y_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2217_, lean_object* v_category_2218_, lean_object* v_opts_2219_, lean_object* v_act_2220_, lean_object* v_decl_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2217_, v_category_2218_, v_opts_2219_, v_act_2220_, v_decl_2221_, v___y_2222_, v___y_2223_);
lean_dec(v___y_2223_);
lean_dec_ref(v___y_2222_);
lean_dec_ref(v_opts_2219_);
lean_dec_ref(v_category_2218_);
return v_res_2225_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2226_, lean_object* v_a_2227_){
_start:
{
if (lean_obj_tag(v_a_2226_) == 0)
{
lean_object* v___x_2228_; 
v___x_2228_ = l_List_reverse___redArg(v_a_2227_);
return v___x_2228_;
}
else
{
lean_object* v_head_2229_; lean_object* v_tail_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2239_; 
v_head_2229_ = lean_ctor_get(v_a_2226_, 0);
v_tail_2230_ = lean_ctor_get(v_a_2226_, 1);
v_isSharedCheck_2239_ = !lean_is_exclusive(v_a_2226_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2232_ = v_a_2226_;
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_tail_2230_);
lean_inc(v_head_2229_);
lean_dec(v_a_2226_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2239_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2236_; 
v___x_2234_ = l_Lean_MessageData_ofName(v_head_2229_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 1, v_a_2227_);
lean_ctor_set(v___x_2232_, 0, v___x_2234_);
v___x_2236_ = v___x_2232_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v___x_2234_);
lean_ctor_set(v_reuseFailAlloc_2238_, 1, v_a_2227_);
v___x_2236_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
v_a_2226_ = v_tail_2230_;
v_a_2227_ = v___x_2236_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; 
v___x_2241_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2242_ = l_Lean_stringToMessageData(v___x_2241_);
return v___x_2242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2243_, lean_object* v_x_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2248_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2249_ = l_Lean_Declaration_getTopLevelNames(v_decl_2243_);
v___x_2250_ = lean_box(0);
v___x_2251_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2249_, v___x_2250_);
v___x_2252_ = l_Lean_MessageData_ofList(v___x_2251_);
v___x_2253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2248_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2253_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2255_, lean_object* v_x_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2255_, v_x_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v_x_2256_);
return v_res_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2261_, size_t v_i_2262_, lean_object* v_bs_2263_){
_start:
{
uint8_t v___x_2264_; 
v___x_2264_ = lean_usize_dec_lt(v_i_2262_, v_sz_2261_);
if (v___x_2264_ == 0)
{
return v_bs_2263_;
}
else
{
lean_object* v_v_2265_; lean_object* v_msg_2266_; lean_object* v___x_2267_; lean_object* v_bs_x27_2268_; size_t v___x_2269_; size_t v___x_2270_; lean_object* v___x_2271_; 
v_v_2265_ = lean_array_uget_borrowed(v_bs_2263_, v_i_2262_);
v_msg_2266_ = lean_ctor_get(v_v_2265_, 1);
lean_inc_ref(v_msg_2266_);
v___x_2267_ = lean_unsigned_to_nat(0u);
v_bs_x27_2268_ = lean_array_uset(v_bs_2263_, v_i_2262_, v___x_2267_);
v___x_2269_ = ((size_t)1ULL);
v___x_2270_ = lean_usize_add(v_i_2262_, v___x_2269_);
v___x_2271_ = lean_array_uset(v_bs_x27_2268_, v_i_2262_, v_msg_2266_);
v_i_2262_ = v___x_2270_;
v_bs_2263_ = v___x_2271_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2273_, lean_object* v_i_2274_, lean_object* v_bs_2275_){
_start:
{
size_t v_sz_boxed_2276_; size_t v_i_boxed_2277_; lean_object* v_res_2278_; 
v_sz_boxed_2276_ = lean_unbox_usize(v_sz_2273_);
lean_dec(v_sz_2273_);
v_i_boxed_2277_ = lean_unbox_usize(v_i_2274_);
lean_dec(v_i_2274_);
v_res_2278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2276_, v_i_boxed_2277_, v_bs_2275_);
return v_res_2278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2279_, lean_object* v_data_2280_, lean_object* v_ref_2281_, lean_object* v_msg_2282_, lean_object* v___y_2283_, lean_object* v___y_2284_){
_start:
{
lean_object* v_fileName_2286_; lean_object* v_fileMap_2287_; lean_object* v_options_2288_; lean_object* v_currRecDepth_2289_; lean_object* v_maxRecDepth_2290_; lean_object* v_ref_2291_; lean_object* v_currNamespace_2292_; lean_object* v_openDecls_2293_; lean_object* v_initHeartbeats_2294_; lean_object* v_maxHeartbeats_2295_; lean_object* v_quotContext_2296_; lean_object* v_currMacroScope_2297_; uint8_t v_diag_2298_; lean_object* v_cancelTk_x3f_2299_; uint8_t v_suppressElabErrors_2300_; lean_object* v_inheritedTraceOptions_2301_; lean_object* v___x_2302_; lean_object* v_traceState_2303_; lean_object* v_traces_2304_; lean_object* v_ref_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; size_t v_sz_2308_; size_t v___x_2309_; lean_object* v___x_2310_; lean_object* v_msg_2311_; lean_object* v___x_2312_; lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2350_; 
v_fileName_2286_ = lean_ctor_get(v___y_2283_, 0);
v_fileMap_2287_ = lean_ctor_get(v___y_2283_, 1);
v_options_2288_ = lean_ctor_get(v___y_2283_, 2);
v_currRecDepth_2289_ = lean_ctor_get(v___y_2283_, 3);
v_maxRecDepth_2290_ = lean_ctor_get(v___y_2283_, 4);
v_ref_2291_ = lean_ctor_get(v___y_2283_, 5);
v_currNamespace_2292_ = lean_ctor_get(v___y_2283_, 6);
v_openDecls_2293_ = lean_ctor_get(v___y_2283_, 7);
v_initHeartbeats_2294_ = lean_ctor_get(v___y_2283_, 8);
v_maxHeartbeats_2295_ = lean_ctor_get(v___y_2283_, 9);
v_quotContext_2296_ = lean_ctor_get(v___y_2283_, 10);
v_currMacroScope_2297_ = lean_ctor_get(v___y_2283_, 11);
v_diag_2298_ = lean_ctor_get_uint8(v___y_2283_, sizeof(void*)*14);
v_cancelTk_x3f_2299_ = lean_ctor_get(v___y_2283_, 12);
v_suppressElabErrors_2300_ = lean_ctor_get_uint8(v___y_2283_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2301_ = lean_ctor_get(v___y_2283_, 13);
v___x_2302_ = lean_st_ref_get(v___y_2284_);
v_traceState_2303_ = lean_ctor_get(v___x_2302_, 4);
lean_inc_ref(v_traceState_2303_);
lean_dec(v___x_2302_);
v_traces_2304_ = lean_ctor_get(v_traceState_2303_, 0);
lean_inc_ref(v_traces_2304_);
lean_dec_ref(v_traceState_2303_);
v_ref_2305_ = l_Lean_replaceRef(v_ref_2281_, v_ref_2291_);
lean_inc_ref(v_inheritedTraceOptions_2301_);
lean_inc(v_cancelTk_x3f_2299_);
lean_inc(v_currMacroScope_2297_);
lean_inc(v_quotContext_2296_);
lean_inc(v_maxHeartbeats_2295_);
lean_inc(v_initHeartbeats_2294_);
lean_inc(v_openDecls_2293_);
lean_inc(v_currNamespace_2292_);
lean_inc(v_maxRecDepth_2290_);
lean_inc(v_currRecDepth_2289_);
lean_inc_ref(v_options_2288_);
lean_inc_ref(v_fileMap_2287_);
lean_inc_ref(v_fileName_2286_);
v___x_2306_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2306_, 0, v_fileName_2286_);
lean_ctor_set(v___x_2306_, 1, v_fileMap_2287_);
lean_ctor_set(v___x_2306_, 2, v_options_2288_);
lean_ctor_set(v___x_2306_, 3, v_currRecDepth_2289_);
lean_ctor_set(v___x_2306_, 4, v_maxRecDepth_2290_);
lean_ctor_set(v___x_2306_, 5, v_ref_2305_);
lean_ctor_set(v___x_2306_, 6, v_currNamespace_2292_);
lean_ctor_set(v___x_2306_, 7, v_openDecls_2293_);
lean_ctor_set(v___x_2306_, 8, v_initHeartbeats_2294_);
lean_ctor_set(v___x_2306_, 9, v_maxHeartbeats_2295_);
lean_ctor_set(v___x_2306_, 10, v_quotContext_2296_);
lean_ctor_set(v___x_2306_, 11, v_currMacroScope_2297_);
lean_ctor_set(v___x_2306_, 12, v_cancelTk_x3f_2299_);
lean_ctor_set(v___x_2306_, 13, v_inheritedTraceOptions_2301_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*14, v_diag_2298_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*14 + 1, v_suppressElabErrors_2300_);
v___x_2307_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2304_);
lean_dec_ref(v_traces_2304_);
v_sz_2308_ = lean_array_size(v___x_2307_);
v___x_2309_ = ((size_t)0ULL);
v___x_2310_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2308_, v___x_2309_, v___x_2307_);
v_msg_2311_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2311_, 0, v_data_2280_);
lean_ctor_set(v_msg_2311_, 1, v_msg_2282_);
lean_ctor_set(v_msg_2311_, 2, v___x_2310_);
v___x_2312_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2311_, v___x_2306_, v___y_2284_);
lean_dec_ref_known(v___x_2306_, 14);
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2315_ = v___x_2312_;
v_isShared_2316_ = v_isSharedCheck_2350_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2312_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2350_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v_traceState_2318_; lean_object* v_env_2319_; lean_object* v_nextMacroScope_2320_; lean_object* v_ngen_2321_; lean_object* v_auxDeclNGen_2322_; lean_object* v_cache_2323_; lean_object* v_messages_2324_; lean_object* v_infoState_2325_; lean_object* v_snapshotTasks_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2349_; 
v___x_2317_ = lean_st_ref_take(v___y_2284_);
v_traceState_2318_ = lean_ctor_get(v___x_2317_, 4);
v_env_2319_ = lean_ctor_get(v___x_2317_, 0);
v_nextMacroScope_2320_ = lean_ctor_get(v___x_2317_, 1);
v_ngen_2321_ = lean_ctor_get(v___x_2317_, 2);
v_auxDeclNGen_2322_ = lean_ctor_get(v___x_2317_, 3);
v_cache_2323_ = lean_ctor_get(v___x_2317_, 5);
v_messages_2324_ = lean_ctor_get(v___x_2317_, 6);
v_infoState_2325_ = lean_ctor_get(v___x_2317_, 7);
v_snapshotTasks_2326_ = lean_ctor_get(v___x_2317_, 8);
v_isSharedCheck_2349_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2349_ == 0)
{
v___x_2328_ = v___x_2317_;
v_isShared_2329_ = v_isSharedCheck_2349_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_snapshotTasks_2326_);
lean_inc(v_infoState_2325_);
lean_inc(v_messages_2324_);
lean_inc(v_cache_2323_);
lean_inc(v_traceState_2318_);
lean_inc(v_auxDeclNGen_2322_);
lean_inc(v_ngen_2321_);
lean_inc(v_nextMacroScope_2320_);
lean_inc(v_env_2319_);
lean_dec(v___x_2317_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2349_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
uint64_t v_tid_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2347_; 
v_tid_2330_ = lean_ctor_get_uint64(v_traceState_2318_, sizeof(void*)*1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_traceState_2318_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_traceState_2318_, 0);
lean_dec(v_unused_2348_);
v___x_2332_ = v_traceState_2318_;
v_isShared_2333_ = v_isSharedCheck_2347_;
goto v_resetjp_2331_;
}
else
{
lean_dec(v_traceState_2318_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2347_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v_ref_2281_);
lean_ctor_set(v___x_2334_, 1, v_a_2313_);
v___x_2335_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2279_, v___x_2334_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v___x_2335_);
v___x_2337_ = v___x_2332_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v___x_2335_);
lean_ctor_set_uint64(v_reuseFailAlloc_2346_, sizeof(void*)*1, v_tid_2330_);
v___x_2337_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
lean_object* v___x_2339_; 
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 4, v___x_2337_);
v___x_2339_ = v___x_2328_;
goto v_reusejp_2338_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_env_2319_);
lean_ctor_set(v_reuseFailAlloc_2345_, 1, v_nextMacroScope_2320_);
lean_ctor_set(v_reuseFailAlloc_2345_, 2, v_ngen_2321_);
lean_ctor_set(v_reuseFailAlloc_2345_, 3, v_auxDeclNGen_2322_);
lean_ctor_set(v_reuseFailAlloc_2345_, 4, v___x_2337_);
lean_ctor_set(v_reuseFailAlloc_2345_, 5, v_cache_2323_);
lean_ctor_set(v_reuseFailAlloc_2345_, 6, v_messages_2324_);
lean_ctor_set(v_reuseFailAlloc_2345_, 7, v_infoState_2325_);
lean_ctor_set(v_reuseFailAlloc_2345_, 8, v_snapshotTasks_2326_);
v___x_2339_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2338_;
}
v_reusejp_2338_:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2343_; 
v___x_2340_ = lean_st_ref_set(v___y_2284_, v___x_2339_);
v___x_2341_ = lean_box(0);
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2341_);
v___x_2343_ = v___x_2315_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2344_; 
v_reuseFailAlloc_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2344_, 0, v___x_2341_);
v___x_2343_ = v_reuseFailAlloc_2344_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
return v___x_2343_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2351_, lean_object* v_data_2352_, lean_object* v_ref_2353_, lean_object* v_msg_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2351_, v_data_2352_, v_ref_2353_, v_msg_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2359_){
_start:
{
if (lean_obj_tag(v_x_2359_) == 0)
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
v_a_2361_ = lean_ctor_get(v_x_2359_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v_x_2359_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v_x_2359_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v_x_2359_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
lean_ctor_set_tag(v___x_2363_, 1);
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
v_a_2369_ = lean_ctor_get(v_x_2359_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v_x_2359_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v_x_2359_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v_x_2359_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
lean_ctor_set_tag(v___x_2371_, 0);
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2377_);
return v_res_2379_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2380_){
_start:
{
if (lean_obj_tag(v_e_2380_) == 0)
{
uint8_t v___x_2381_; 
v___x_2381_ = 2;
return v___x_2381_;
}
else
{
uint8_t v___x_2382_; 
v___x_2382_ = 0;
return v___x_2382_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2383_){
_start:
{
uint8_t v_res_2384_; lean_object* v_r_2385_; 
v_res_2384_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2383_);
lean_dec_ref(v_e_2383_);
v_r_2385_ = lean_box(v_res_2384_);
return v_r_2385_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2386_; double v___x_2387_; 
v___x_2386_ = lean_unsigned_to_nat(0u);
v___x_2387_ = lean_float_of_nat(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2389_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2390_ = l_Lean_stringToMessageData(v___x_2389_);
return v___x_2390_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2391_; double v___x_2392_; 
v___x_2391_ = lean_unsigned_to_nat(1000u);
v___x_2392_ = lean_float_of_nat(v___x_2391_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2393_, uint8_t v_collapsed_2394_, lean_object* v_tag_2395_, lean_object* v_opts_2396_, uint8_t v_clsEnabled_2397_, lean_object* v_oldTraces_2398_, lean_object* v_msg_2399_, lean_object* v_resStartStop_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
lean_object* v_fst_2404_; lean_object* v_snd_2405_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v_data_2409_; lean_object* v_fst_2412_; lean_object* v_snd_2413_; lean_object* v___x_2414_; uint8_t v___x_2415_; lean_object* v___y_2417_; lean_object* v_a_2418_; uint8_t v___y_2433_; double v___y_2464_; 
v_fst_2404_ = lean_ctor_get(v_resStartStop_2400_, 0);
lean_inc(v_fst_2404_);
v_snd_2405_ = lean_ctor_get(v_resStartStop_2400_, 1);
lean_inc(v_snd_2405_);
lean_dec_ref(v_resStartStop_2400_);
v_fst_2412_ = lean_ctor_get(v_snd_2405_, 0);
lean_inc(v_fst_2412_);
v_snd_2413_ = lean_ctor_get(v_snd_2405_, 1);
lean_inc(v_snd_2413_);
lean_dec(v_snd_2405_);
v___x_2414_ = l_Lean_trace_profiler;
v___x_2415_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2396_, v___x_2414_);
if (v___x_2415_ == 0)
{
v___y_2433_ = v___x_2415_;
goto v___jp_2432_;
}
else
{
lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2469_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2470_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2396_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; double v___x_2473_; double v___x_2474_; double v___x_2475_; 
v___x_2471_ = l_Lean_trace_profiler_threshold;
v___x_2472_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2396_, v___x_2471_);
v___x_2473_ = lean_float_of_nat(v___x_2472_);
v___x_2474_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2475_ = lean_float_div(v___x_2473_, v___x_2474_);
v___y_2464_ = v___x_2475_;
goto v___jp_2463_;
}
else
{
lean_object* v___x_2476_; lean_object* v___x_2477_; double v___x_2478_; 
v___x_2476_ = l_Lean_trace_profiler_threshold;
v___x_2477_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2396_, v___x_2476_);
v___x_2478_ = lean_float_of_nat(v___x_2477_);
v___y_2464_ = v___x_2478_;
goto v___jp_2463_;
}
}
v___jp_2406_:
{
lean_object* v___x_2410_; 
lean_inc(v___y_2407_);
v___x_2410_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2398_, v_data_2409_, v___y_2407_, v___y_2408_, v___y_2401_, v___y_2402_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v___x_2411_; 
lean_dec_ref_known(v___x_2410_, 1);
v___x_2411_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2404_);
return v___x_2411_;
}
else
{
lean_dec(v_fst_2404_);
return v___x_2410_;
}
}
v___jp_2416_:
{
uint8_t v_result_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; double v___x_2422_; lean_object* v_data_2423_; 
v_result_2419_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2404_);
v___x_2420_ = lean_box(v_result_2419_);
v___x_2421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
v___x_2422_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2395_);
lean_inc_ref(v___x_2421_);
lean_inc(v_cls_2393_);
v_data_2423_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2423_, 0, v_cls_2393_);
lean_ctor_set(v_data_2423_, 1, v___x_2421_);
lean_ctor_set(v_data_2423_, 2, v_tag_2395_);
lean_ctor_set_float(v_data_2423_, sizeof(void*)*3, v___x_2422_);
lean_ctor_set_float(v_data_2423_, sizeof(void*)*3 + 8, v___x_2422_);
lean_ctor_set_uint8(v_data_2423_, sizeof(void*)*3 + 16, v_collapsed_2394_);
if (v___x_2415_ == 0)
{
lean_dec_ref_known(v___x_2421_, 1);
lean_dec(v_snd_2413_);
lean_dec(v_fst_2412_);
lean_dec_ref(v_tag_2395_);
lean_dec(v_cls_2393_);
v___y_2407_ = v___y_2417_;
v___y_2408_ = v_a_2418_;
v_data_2409_ = v_data_2423_;
goto v___jp_2406_;
}
else
{
lean_object* v_data_2424_; double v___x_2425_; double v___x_2426_; 
lean_dec_ref_known(v_data_2423_, 3);
v_data_2424_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2424_, 0, v_cls_2393_);
lean_ctor_set(v_data_2424_, 1, v___x_2421_);
lean_ctor_set(v_data_2424_, 2, v_tag_2395_);
v___x_2425_ = lean_unbox_float(v_fst_2412_);
lean_dec(v_fst_2412_);
lean_ctor_set_float(v_data_2424_, sizeof(void*)*3, v___x_2425_);
v___x_2426_ = lean_unbox_float(v_snd_2413_);
lean_dec(v_snd_2413_);
lean_ctor_set_float(v_data_2424_, sizeof(void*)*3 + 8, v___x_2426_);
lean_ctor_set_uint8(v_data_2424_, sizeof(void*)*3 + 16, v_collapsed_2394_);
v___y_2407_ = v___y_2417_;
v___y_2408_ = v_a_2418_;
v_data_2409_ = v_data_2424_;
goto v___jp_2406_;
}
}
v___jp_2427_:
{
lean_object* v_ref_2428_; lean_object* v___x_2429_; 
v_ref_2428_ = lean_ctor_get(v___y_2401_, 5);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
lean_inc(v_fst_2404_);
v___x_2429_ = lean_apply_4(v_msg_2399_, v_fst_2404_, v___y_2401_, v___y_2402_, lean_box(0));
if (lean_obj_tag(v___x_2429_) == 0)
{
lean_object* v_a_2430_; 
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
lean_inc(v_a_2430_);
lean_dec_ref_known(v___x_2429_, 1);
v___y_2417_ = v_ref_2428_;
v_a_2418_ = v_a_2430_;
goto v___jp_2416_;
}
else
{
lean_object* v___x_2431_; 
lean_dec_ref_known(v___x_2429_, 1);
v___x_2431_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2417_ = v_ref_2428_;
v_a_2418_ = v___x_2431_;
goto v___jp_2416_;
}
}
v___jp_2432_:
{
if (v_clsEnabled_2397_ == 0)
{
if (v___y_2433_ == 0)
{
lean_object* v___x_2434_; lean_object* v_traceState_2435_; lean_object* v_env_2436_; lean_object* v_nextMacroScope_2437_; lean_object* v_ngen_2438_; lean_object* v_auxDeclNGen_2439_; lean_object* v_cache_2440_; lean_object* v_messages_2441_; lean_object* v_infoState_2442_; lean_object* v_snapshotTasks_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_snd_2413_);
lean_dec(v_fst_2412_);
lean_dec_ref(v_msg_2399_);
lean_dec_ref(v_tag_2395_);
lean_dec(v_cls_2393_);
v___x_2434_ = lean_st_ref_take(v___y_2402_);
v_traceState_2435_ = lean_ctor_get(v___x_2434_, 4);
v_env_2436_ = lean_ctor_get(v___x_2434_, 0);
v_nextMacroScope_2437_ = lean_ctor_get(v___x_2434_, 1);
v_ngen_2438_ = lean_ctor_get(v___x_2434_, 2);
v_auxDeclNGen_2439_ = lean_ctor_get(v___x_2434_, 3);
v_cache_2440_ = lean_ctor_get(v___x_2434_, 5);
v_messages_2441_ = lean_ctor_get(v___x_2434_, 6);
v_infoState_2442_ = lean_ctor_get(v___x_2434_, 7);
v_snapshotTasks_2443_ = lean_ctor_get(v___x_2434_, 8);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2445_ = v___x_2434_;
v_isShared_2446_ = v_isSharedCheck_2462_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_snapshotTasks_2443_);
lean_inc(v_infoState_2442_);
lean_inc(v_messages_2441_);
lean_inc(v_cache_2440_);
lean_inc(v_traceState_2435_);
lean_inc(v_auxDeclNGen_2439_);
lean_inc(v_ngen_2438_);
lean_inc(v_nextMacroScope_2437_);
lean_inc(v_env_2436_);
lean_dec(v___x_2434_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2462_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
uint64_t v_tid_2447_; lean_object* v_traces_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2461_; 
v_tid_2447_ = lean_ctor_get_uint64(v_traceState_2435_, sizeof(void*)*1);
v_traces_2448_ = lean_ctor_get(v_traceState_2435_, 0);
v_isSharedCheck_2461_ = !lean_is_exclusive(v_traceState_2435_);
if (v_isSharedCheck_2461_ == 0)
{
v___x_2450_ = v_traceState_2435_;
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_traces_2448_);
lean_dec(v_traceState_2435_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2461_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2452_; lean_object* v___x_2454_; 
v___x_2452_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2398_, v_traces_2448_);
lean_dec_ref(v_traces_2448_);
if (v_isShared_2451_ == 0)
{
lean_ctor_set(v___x_2450_, 0, v___x_2452_);
v___x_2454_ = v___x_2450_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2452_);
lean_ctor_set_uint64(v_reuseFailAlloc_2460_, sizeof(void*)*1, v_tid_2447_);
v___x_2454_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
lean_object* v___x_2456_; 
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 4, v___x_2454_);
v___x_2456_ = v___x_2445_;
goto v_reusejp_2455_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_env_2436_);
lean_ctor_set(v_reuseFailAlloc_2459_, 1, v_nextMacroScope_2437_);
lean_ctor_set(v_reuseFailAlloc_2459_, 2, v_ngen_2438_);
lean_ctor_set(v_reuseFailAlloc_2459_, 3, v_auxDeclNGen_2439_);
lean_ctor_set(v_reuseFailAlloc_2459_, 4, v___x_2454_);
lean_ctor_set(v_reuseFailAlloc_2459_, 5, v_cache_2440_);
lean_ctor_set(v_reuseFailAlloc_2459_, 6, v_messages_2441_);
lean_ctor_set(v_reuseFailAlloc_2459_, 7, v_infoState_2442_);
lean_ctor_set(v_reuseFailAlloc_2459_, 8, v_snapshotTasks_2443_);
v___x_2456_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2455_;
}
v_reusejp_2455_:
{
lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2457_ = lean_st_ref_set(v___y_2402_, v___x_2456_);
v___x_2458_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2404_);
return v___x_2458_;
}
}
}
}
}
else
{
goto v___jp_2427_;
}
}
else
{
goto v___jp_2427_;
}
}
v___jp_2463_:
{
double v___x_2465_; double v___x_2466_; double v___x_2467_; uint8_t v___x_2468_; 
v___x_2465_ = lean_unbox_float(v_snd_2413_);
v___x_2466_ = lean_unbox_float(v_fst_2412_);
v___x_2467_ = lean_float_sub(v___x_2465_, v___x_2466_);
v___x_2468_ = lean_float_decLt(v___y_2464_, v___x_2467_);
v___y_2433_ = v___x_2468_;
goto v___jp_2432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2479_, lean_object* v_collapsed_2480_, lean_object* v_tag_2481_, lean_object* v_opts_2482_, lean_object* v_clsEnabled_2483_, lean_object* v_oldTraces_2484_, lean_object* v_msg_2485_, lean_object* v_resStartStop_2486_, lean_object* v___y_2487_, lean_object* v___y_2488_, lean_object* v___y_2489_){
_start:
{
uint8_t v_collapsed_boxed_2490_; uint8_t v_clsEnabled_boxed_2491_; lean_object* v_res_2492_; 
v_collapsed_boxed_2490_ = lean_unbox(v_collapsed_2480_);
v_clsEnabled_boxed_2491_ = lean_unbox(v_clsEnabled_2483_);
v_res_2492_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2479_, v_collapsed_boxed_2490_, v_tag_2481_, v_opts_2482_, v_clsEnabled_boxed_2491_, v_oldTraces_2484_, v_msg_2485_, v_resStartStop_2486_, v___y_2487_, v___y_2488_);
lean_dec(v___y_2488_);
lean_dec_ref(v___y_2487_);
lean_dec_ref(v_opts_2482_);
return v_res_2492_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2493_; double v___x_2494_; 
v___x_2493_ = lean_unsigned_to_nat(1000000000u);
v___x_2494_ = lean_float_of_nat(v___x_2493_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2497_, lean_object* v___x_2498_, uint8_t v___x_2499_, lean_object* v___x_2500_, lean_object* v___f_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
lean_object* v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2508_; lean_object* v___y_2519_; lean_object* v_a_2520_; lean_object* v___y_2524_; lean_object* v___y_2525_; uint8_t v___y_2526_; lean_object* v___y_2537_; lean_object* v_a_2538_; lean_object* v_options_2541_; lean_object* v_cancelTk_x3f_2542_; lean_object* v_inheritedTraceOptions_2543_; lean_object* v___y_2545_; uint8_t v___y_2546_; lean_object* v___y_2547_; lean_object* v_a_2548_; uint8_t v___y_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v_a_2564_; uint8_t v___y_2567_; lean_object* v___y_2568_; lean_object* v___y_2569_; lean_object* v_a_2570_; lean_object* v___y_2573_; uint8_t v___y_2574_; lean_object* v___y_2575_; lean_object* v___y_2576_; lean_object* v___y_2580_; lean_object* v___y_2581_; uint8_t v___y_2582_; lean_object* v___y_2583_; uint8_t v___y_2584_; uint8_t v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v_a_2590_; lean_object* v___y_2594_; uint8_t v___y_2595_; lean_object* v___y_2596_; lean_object* v_a_2597_; uint8_t v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2609_; lean_object* v_a_2610_; uint8_t v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v_a_2616_; lean_object* v___y_2619_; uint8_t v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2626_; lean_object* v___y_2627_; uint8_t v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; uint8_t v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v_a_2636_; uint8_t v___y_2640_; uint8_t v_a_2666_; uint8_t v_hasTrace_2684_; uint8_t v___x_2685_; 
v_options_2541_ = lean_ctor_get(v___y_2502_, 2);
v_cancelTk_x3f_2542_ = lean_ctor_get(v___y_2502_, 12);
v_inheritedTraceOptions_2543_ = lean_ctor_get(v___y_2502_, 13);
v_hasTrace_2684_ = lean_ctor_get_uint8(v_options_2541_, sizeof(void*)*1);
v___x_2685_ = lean_bool_not(v_hasTrace_2684_);
if (v___x_2685_ == 0)
{
if (v_hasTrace_2684_ == 0)
{
v_a_2666_ = v_hasTrace_2684_;
goto v___jp_2665_;
}
else
{
lean_object* v___x_2686_; lean_object* v___x_2687_; uint8_t v___x_2688_; 
v___x_2686_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v___x_2498_);
v___x_2687_ = l_Lean_Name_append(v___x_2686_, v___x_2498_);
v___x_2688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2543_, v_options_2541_, v___x_2687_);
lean_dec(v___x_2687_);
if (v___x_2688_ == 0)
{
v_a_2666_ = v___x_2688_;
goto v___jp_2665_;
}
else
{
v___y_2640_ = v___x_2688_;
goto v___jp_2639_;
}
}
}
else
{
lean_object* v___x_2689_; 
lean_dec_ref(v___f_2501_);
lean_dec_ref(v___x_2500_);
lean_dec(v___x_2498_);
lean_inc(v_decl_2497_);
v___x_2689_ = l_Lean_warnIfUsesSorry(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v___x_2690_; lean_object* v_env_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
lean_dec_ref_known(v___x_2689_, 1);
v___x_2690_ = lean_st_ref_get(v___y_2503_);
v_env_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc_ref(v_env_2691_);
lean_dec(v___x_2690_);
v___x_2692_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2691_, v_options_2541_, v_decl_2497_, v_cancelTk_x3f_2542_);
v___x_2693_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2692_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; 
lean_dec(v_decl_2497_);
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
v___x_2695_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2694_, v___y_2503_);
return v___x_2695_;
}
else
{
lean_object* v_a_2696_; lean_object* v___x_2698_; uint8_t v_isShared_2699_; uint8_t v_isSharedCheck_2703_; 
v_a_2696_ = lean_ctor_get(v___x_2693_, 0);
v_isSharedCheck_2703_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2703_ == 0)
{
v___x_2698_ = v___x_2693_;
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
else
{
lean_inc(v_a_2696_);
lean_dec(v___x_2693_);
v___x_2698_ = lean_box(0);
v_isShared_2699_ = v_isSharedCheck_2703_;
goto v_resetjp_2697_;
}
v_resetjp_2697_:
{
lean_object* v___x_2701_; 
lean_inc(v_a_2696_);
if (v_isShared_2699_ == 0)
{
v___x_2701_ = v___x_2698_;
goto v_reusejp_2700_;
}
else
{
lean_object* v_reuseFailAlloc_2702_; 
v_reuseFailAlloc_2702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_a_2696_);
v___x_2701_ = v_reuseFailAlloc_2702_;
goto v_reusejp_2700_;
}
v_reusejp_2700_:
{
v___y_2519_ = v___x_2701_;
v_a_2520_ = v_a_2696_;
goto v___jp_2518_;
}
}
}
}
else
{
lean_dec(v_decl_2497_);
return v___x_2689_;
}
}
v___jp_2505_:
{
if (v___y_2508_ == 0)
{
lean_object* v___x_2509_; 
lean_dec_ref(v___y_2507_);
v___x_2509_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2509_) == 0)
{
lean_object* v___x_2511_; uint8_t v_isShared_2512_; uint8_t v_isSharedCheck_2516_; 
v_isSharedCheck_2516_ = !lean_is_exclusive(v___x_2509_);
if (v_isSharedCheck_2516_ == 0)
{
lean_object* v_unused_2517_; 
v_unused_2517_ = lean_ctor_get(v___x_2509_, 0);
lean_dec(v_unused_2517_);
v___x_2511_ = v___x_2509_;
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
else
{
lean_dec(v___x_2509_);
v___x_2511_ = lean_box(0);
v_isShared_2512_ = v_isSharedCheck_2516_;
goto v_resetjp_2510_;
}
v_resetjp_2510_:
{
lean_object* v___x_2514_; 
if (v_isShared_2512_ == 0)
{
lean_ctor_set_tag(v___x_2511_, 1);
lean_ctor_set(v___x_2511_, 0, v___y_2506_);
v___x_2514_ = v___x_2511_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2515_; 
v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2515_, 0, v___y_2506_);
v___x_2514_ = v_reuseFailAlloc_2515_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
return v___x_2514_;
}
}
}
else
{
lean_dec_ref(v___y_2506_);
return v___x_2509_;
}
}
else
{
lean_dec_ref(v___y_2506_);
lean_dec(v_decl_2497_);
return v___y_2507_;
}
}
v___jp_2518_:
{
uint8_t v___x_2521_; 
v___x_2521_ = l_Lean_Exception_isInterrupt(v_a_2520_);
if (v___x_2521_ == 0)
{
uint8_t v___x_2522_; 
lean_inc_ref(v_a_2520_);
v___x_2522_ = l_Lean_Exception_isRuntime(v_a_2520_);
v___y_2506_ = v_a_2520_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___x_2522_;
goto v___jp_2505_;
}
else
{
v___y_2506_ = v_a_2520_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___x_2521_;
goto v___jp_2505_;
}
}
v___jp_2523_:
{
if (v___y_2526_ == 0)
{
lean_object* v___x_2527_; 
lean_dec_ref(v___y_2524_);
v___x_2527_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2527_);
if (v_isSharedCheck_2534_ == 0)
{
lean_object* v_unused_2535_; 
v_unused_2535_ = lean_ctor_get(v___x_2527_, 0);
lean_dec(v_unused_2535_);
v___x_2529_ = v___x_2527_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_dec(v___x_2527_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
lean_ctor_set_tag(v___x_2529_, 1);
lean_ctor_set(v___x_2529_, 0, v___y_2525_);
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___y_2525_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
else
{
lean_dec_ref(v___y_2525_);
return v___x_2527_;
}
}
else
{
lean_dec_ref(v___y_2525_);
lean_dec(v_decl_2497_);
return v___y_2524_;
}
}
v___jp_2536_:
{
uint8_t v___x_2539_; 
v___x_2539_ = l_Lean_Exception_isInterrupt(v_a_2538_);
if (v___x_2539_ == 0)
{
uint8_t v___x_2540_; 
lean_inc_ref(v_a_2538_);
v___x_2540_ = l_Lean_Exception_isRuntime(v_a_2538_);
v___y_2524_ = v___y_2537_;
v___y_2525_ = v_a_2538_;
v___y_2526_ = v___x_2540_;
goto v___jp_2523_;
}
else
{
v___y_2524_ = v___y_2537_;
v___y_2525_ = v_a_2538_;
v___y_2526_ = v___x_2539_;
goto v___jp_2523_;
}
}
v___jp_2544_:
{
lean_object* v___x_2549_; double v___x_2550_; double v___x_2551_; double v___x_2552_; double v___x_2553_; double v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2549_ = lean_io_mono_nanos_now();
v___x_2550_ = lean_float_of_nat(v___y_2547_);
v___x_2551_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0);
v___x_2552_ = lean_float_div(v___x_2550_, v___x_2551_);
v___x_2553_ = lean_float_of_nat(v___x_2549_);
v___x_2554_ = lean_float_div(v___x_2553_, v___x_2551_);
v___x_2555_ = lean_box_float(v___x_2552_);
v___x_2556_ = lean_box_float(v___x_2554_);
v___x_2557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2557_, 0, v___x_2555_);
lean_ctor_set(v___x_2557_, 1, v___x_2556_);
v___x_2558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2558_, 0, v_a_2548_);
lean_ctor_set(v___x_2558_, 1, v___x_2557_);
v___x_2559_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2498_, v___x_2499_, v___x_2500_, v_options_2541_, v___y_2546_, v___y_2545_, v___f_2501_, v___x_2558_, v___y_2502_, v___y_2503_);
return v___x_2559_;
}
v___jp_2560_:
{
lean_object* v___x_2565_; 
v___x_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2565_, 0, v_a_2564_);
v___y_2545_ = v___y_2562_;
v___y_2546_ = v___y_2561_;
v___y_2547_ = v___y_2563_;
v_a_2548_ = v___x_2565_;
goto v___jp_2544_;
}
v___jp_2566_:
{
lean_object* v___x_2571_; 
v___x_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2571_, 0, v_a_2570_);
v___y_2545_ = v___y_2568_;
v___y_2546_ = v___y_2567_;
v___y_2547_ = v___y_2569_;
v_a_2548_ = v___x_2571_;
goto v___jp_2544_;
}
v___jp_2572_:
{
if (lean_obj_tag(v___y_2576_) == 0)
{
lean_object* v_a_2577_; 
v_a_2577_ = lean_ctor_get(v___y_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___y_2576_, 1);
v___y_2567_ = v___y_2574_;
v___y_2568_ = v___y_2573_;
v___y_2569_ = v___y_2575_;
v_a_2570_ = v_a_2577_;
goto v___jp_2566_;
}
else
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___y_2576_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___y_2576_, 1);
v___y_2561_ = v___y_2574_;
v___y_2562_ = v___y_2573_;
v___y_2563_ = v___y_2575_;
v_a_2564_ = v_a_2578_;
goto v___jp_2560_;
}
}
v___jp_2579_:
{
if (v___y_2584_ == 0)
{
lean_object* v___x_2585_; 
v___x_2585_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_dec_ref_known(v___x_2585_, 1);
v___y_2561_ = v___y_2582_;
v___y_2562_ = v___y_2581_;
v___y_2563_ = v___y_2583_;
v_a_2564_ = v___y_2580_;
goto v___jp_2560_;
}
else
{
lean_dec_ref(v___y_2580_);
v___y_2573_ = v___y_2581_;
v___y_2574_ = v___y_2582_;
v___y_2575_ = v___y_2583_;
v___y_2576_ = v___x_2585_;
goto v___jp_2572_;
}
}
else
{
lean_dec(v_decl_2497_);
v___y_2561_ = v___y_2582_;
v___y_2562_ = v___y_2581_;
v___y_2563_ = v___y_2583_;
v_a_2564_ = v___y_2580_;
goto v___jp_2560_;
}
}
v___jp_2586_:
{
uint8_t v___x_2591_; 
v___x_2591_ = l_Lean_Exception_isInterrupt(v_a_2590_);
if (v___x_2591_ == 0)
{
uint8_t v___x_2592_; 
lean_inc_ref(v_a_2590_);
v___x_2592_ = l_Lean_Exception_isRuntime(v_a_2590_);
v___y_2580_ = v_a_2590_;
v___y_2581_ = v___y_2588_;
v___y_2582_ = v___y_2587_;
v___y_2583_ = v___y_2589_;
v___y_2584_ = v___x_2592_;
goto v___jp_2579_;
}
else
{
v___y_2580_ = v_a_2590_;
v___y_2581_ = v___y_2588_;
v___y_2582_ = v___y_2587_;
v___y_2583_ = v___y_2589_;
v___y_2584_ = v___x_2591_;
goto v___jp_2579_;
}
}
v___jp_2593_:
{
lean_object* v___x_2598_; double v___x_2599_; double v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; 
v___x_2598_ = lean_io_get_num_heartbeats();
v___x_2599_ = lean_float_of_nat(v___y_2596_);
v___x_2600_ = lean_float_of_nat(v___x_2598_);
v___x_2601_ = lean_box_float(v___x_2599_);
v___x_2602_ = lean_box_float(v___x_2600_);
v___x_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v_a_2597_);
lean_ctor_set(v___x_2604_, 1, v___x_2603_);
v___x_2605_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2498_, v___x_2499_, v___x_2500_, v_options_2541_, v___y_2595_, v___y_2594_, v___f_2501_, v___x_2604_, v___y_2502_, v___y_2503_);
return v___x_2605_;
}
v___jp_2606_:
{
lean_object* v___x_2611_; 
v___x_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2611_, 0, v_a_2610_);
v___y_2594_ = v___y_2608_;
v___y_2595_ = v___y_2607_;
v___y_2596_ = v___y_2609_;
v_a_2597_ = v___x_2611_;
goto v___jp_2593_;
}
v___jp_2612_:
{
lean_object* v___x_2617_; 
v___x_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2617_, 0, v_a_2616_);
v___y_2594_ = v___y_2614_;
v___y_2595_ = v___y_2613_;
v___y_2596_ = v___y_2615_;
v_a_2597_ = v___x_2617_;
goto v___jp_2593_;
}
v___jp_2618_:
{
if (lean_obj_tag(v___y_2622_) == 0)
{
lean_object* v_a_2623_; 
v_a_2623_ = lean_ctor_get(v___y_2622_, 0);
lean_inc(v_a_2623_);
lean_dec_ref_known(v___y_2622_, 1);
v___y_2613_ = v___y_2620_;
v___y_2614_ = v___y_2619_;
v___y_2615_ = v___y_2621_;
v_a_2616_ = v_a_2623_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___y_2622_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___y_2622_, 1);
v___y_2607_ = v___y_2620_;
v___y_2608_ = v___y_2619_;
v___y_2609_ = v___y_2621_;
v_a_2610_ = v_a_2624_;
goto v___jp_2606_;
}
}
v___jp_2625_:
{
if (v___y_2630_ == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref_known(v___x_2631_, 1);
v___y_2607_ = v___y_2628_;
v___y_2608_ = v___y_2627_;
v___y_2609_ = v___y_2629_;
v_a_2610_ = v___y_2626_;
goto v___jp_2606_;
}
else
{
lean_dec_ref(v___y_2626_);
v___y_2619_ = v___y_2627_;
v___y_2620_ = v___y_2628_;
v___y_2621_ = v___y_2629_;
v___y_2622_ = v___x_2631_;
goto v___jp_2618_;
}
}
else
{
lean_dec(v_decl_2497_);
v___y_2607_ = v___y_2628_;
v___y_2608_ = v___y_2627_;
v___y_2609_ = v___y_2629_;
v_a_2610_ = v___y_2626_;
goto v___jp_2606_;
}
}
v___jp_2632_:
{
uint8_t v___x_2637_; 
v___x_2637_ = l_Lean_Exception_isInterrupt(v_a_2636_);
if (v___x_2637_ == 0)
{
uint8_t v___x_2638_; 
lean_inc_ref(v_a_2636_);
v___x_2638_ = l_Lean_Exception_isRuntime(v_a_2636_);
v___y_2626_ = v_a_2636_;
v___y_2627_ = v___y_2634_;
v___y_2628_ = v___y_2633_;
v___y_2629_ = v___y_2635_;
v___y_2630_ = v___x_2638_;
goto v___jp_2625_;
}
else
{
v___y_2626_ = v_a_2636_;
v___y_2627_ = v___y_2634_;
v___y_2628_ = v___y_2633_;
v___y_2629_ = v___y_2635_;
v___y_2630_ = v___x_2637_;
goto v___jp_2625_;
}
}
v___jp_2639_:
{
lean_object* v___x_2641_; lean_object* v_a_2642_; lean_object* v___x_2643_; uint8_t v___x_2644_; 
v___x_2641_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2503_);
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref(v___x_2641_);
v___x_2643_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2644_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2541_, v___x_2643_);
if (v___x_2644_ == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2497_);
v___x_2646_ = l_Lean_warnIfUsesSorry(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v___x_2647_; lean_object* v_env_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; 
lean_dec_ref_known(v___x_2646_, 1);
v___x_2647_ = lean_st_ref_get(v___y_2503_);
v_env_2648_ = lean_ctor_get(v___x_2647_, 0);
lean_inc_ref(v_env_2648_);
lean_dec(v___x_2647_);
v___x_2649_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2648_, v_options_2541_, v_decl_2497_, v_cancelTk_x3f_2542_);
v___x_2650_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2649_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2650_) == 0)
{
lean_object* v_a_2651_; lean_object* v___x_2652_; lean_object* v_a_2653_; 
lean_dec(v_decl_2497_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref_known(v___x_2650_, 1);
v___x_2652_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2651_, v___y_2503_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___y_2567_ = v___y_2640_;
v___y_2568_ = v_a_2642_;
v___y_2569_ = v___x_2645_;
v_a_2570_ = v_a_2653_;
goto v___jp_2566_;
}
else
{
lean_object* v_a_2654_; 
v_a_2654_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2654_);
lean_dec_ref_known(v___x_2650_, 1);
v___y_2587_ = v___y_2640_;
v___y_2588_ = v_a_2642_;
v___y_2589_ = v___x_2645_;
v_a_2590_ = v_a_2654_;
goto v___jp_2586_;
}
}
else
{
lean_dec(v_decl_2497_);
v___y_2573_ = v_a_2642_;
v___y_2574_ = v___y_2640_;
v___y_2575_ = v___x_2645_;
v___y_2576_ = v___x_2646_;
goto v___jp_2572_;
}
}
else
{
lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2655_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2497_);
v___x_2656_ = l_Lean_warnIfUsesSorry(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v___x_2657_; lean_object* v_env_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref_known(v___x_2656_, 1);
v___x_2657_ = lean_st_ref_get(v___y_2503_);
v_env_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_ref(v_env_2658_);
lean_dec(v___x_2657_);
v___x_2659_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2658_, v_options_2541_, v_decl_2497_, v_cancelTk_x3f_2542_);
v___x_2660_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2659_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; lean_object* v_a_2663_; 
lean_dec(v_decl_2497_);
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v___x_2662_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2661_, v___y_2503_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2662_);
v___y_2613_ = v___y_2640_;
v___y_2614_ = v_a_2642_;
v___y_2615_ = v___x_2655_;
v_a_2616_ = v_a_2663_;
goto v___jp_2612_;
}
else
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2660_, 1);
v___y_2633_ = v___y_2640_;
v___y_2634_ = v_a_2642_;
v___y_2635_ = v___x_2655_;
v_a_2636_ = v_a_2664_;
goto v___jp_2632_;
}
}
else
{
lean_dec(v_decl_2497_);
v___y_2619_ = v_a_2642_;
v___y_2620_ = v___y_2640_;
v___y_2621_ = v___x_2655_;
v___y_2622_ = v___x_2656_;
goto v___jp_2618_;
}
}
}
v___jp_2665_:
{
lean_object* v___x_2667_; uint8_t v___x_2668_; 
v___x_2667_ = l_Lean_trace_profiler;
v___x_2668_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2541_, v___x_2667_);
if (v___x_2668_ == 0)
{
lean_object* v___x_2669_; 
lean_dec_ref(v___f_2501_);
lean_dec_ref(v___x_2500_);
lean_dec(v___x_2498_);
lean_inc(v_decl_2497_);
v___x_2669_ = l_Lean_warnIfUsesSorry(v_decl_2497_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v___x_2670_; lean_object* v_env_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
lean_dec_ref_known(v___x_2669_, 1);
v___x_2670_ = lean_st_ref_get(v___y_2503_);
v_env_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc_ref(v_env_2671_);
lean_dec(v___x_2670_);
v___x_2672_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2671_, v_options_2541_, v_decl_2497_, v_cancelTk_x3f_2542_);
v___x_2673_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2672_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; 
lean_dec(v_decl_2497_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2674_, v___y_2503_);
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
v___y_2537_ = v___x_2681_;
v_a_2538_ = v_a_2676_;
goto v___jp_2536_;
}
}
}
}
else
{
lean_dec(v_decl_2497_);
return v___x_2669_;
}
}
else
{
v___y_2640_ = v_a_2666_;
goto v___jp_2639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2704_, lean_object* v___x_2705_, lean_object* v___x_2706_, lean_object* v___x_2707_, lean_object* v___f_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
uint8_t v___x_7828__boxed_2712_; lean_object* v_res_2713_; 
v___x_7828__boxed_2712_ = lean_unbox(v___x_2706_);
v_res_2713_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2704_, v___x_2705_, v___x_7828__boxed_2712_, v___x_2707_, v___f_2708_, v___y_2709_, v___y_2710_);
lean_dec(v___y_2710_);
lean_dec_ref(v___y_2709_);
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2718_, lean_object* v_a_2719_, lean_object* v_a_2720_){
_start:
{
lean_object* v_options_2722_; lean_object* v___f_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___f_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_options_2722_ = lean_ctor_get(v_a_2719_, 2);
lean_inc(v_decl_2718_);
v___f_2723_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2723_, 0, v_decl_2718_);
v___x_2724_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2725_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2726_ = 1;
v___x_2727_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2728_ = lean_box(v___x_2726_);
v___f_2729_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2729_, 0, v_decl_2718_);
lean_closure_set(v___f_2729_, 1, v___x_2725_);
lean_closure_set(v___f_2729_, 2, v___x_2728_);
lean_closure_set(v___f_2729_, 3, v___x_2727_);
lean_closure_set(v___f_2729_, 4, v___f_2723_);
v___x_2730_ = lean_box(0);
v___x_2731_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2724_, v_options_2722_, v___f_2729_, v___x_2730_, v_a_2719_, v_a_2720_);
return v___x_2731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2732_, lean_object* v_a_2733_, lean_object* v_a_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2732_, v_a_2733_, v_a_2734_);
lean_dec(v_a_2734_);
lean_dec_ref(v_a_2733_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2737_, lean_object* v_x_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2738_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_x_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2743_, v_x_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2748_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__0));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v_decl_2752_, lean_object* v_x_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2757_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___closed__1);
v___x_2758_ = l_Lean_Declaration_getNames(v_decl_2752_);
v___x_2759_ = lean_box(0);
v___x_2760_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2758_, v___x_2759_);
v___x_2761_ = l_Lean_MessageData_ofList(v___x_2760_);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2757_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2762_);
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v_decl_2764_, lean_object* v_x_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_, lean_object* v___y_2768_){
_start:
{
lean_object* v_res_2769_; 
v_res_2769_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v_decl_2764_, v_x_2765_, v___y_2766_, v___y_2767_);
lean_dec(v___y_2767_);
lean_dec_ref(v___y_2766_);
lean_dec_ref(v_x_2765_);
return v_res_2769_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2772_, lean_object* v_msg_2773_, lean_object* v___y_2774_, lean_object* v___y_2775_){
_start:
{
lean_object* v_ref_2777_; lean_object* v___x_2778_; lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2823_; 
v_ref_2777_ = lean_ctor_get(v___y_2774_, 5);
v___x_2778_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2773_, v___y_2774_, v___y_2775_);
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2781_ = v___x_2778_;
v_isShared_2782_ = v_isSharedCheck_2823_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2778_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2823_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v_traceState_2784_; lean_object* v_env_2785_; lean_object* v_nextMacroScope_2786_; lean_object* v_ngen_2787_; lean_object* v_auxDeclNGen_2788_; lean_object* v_cache_2789_; lean_object* v_messages_2790_; lean_object* v_infoState_2791_; lean_object* v_snapshotTasks_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2822_; 
v___x_2783_ = lean_st_ref_take(v___y_2775_);
v_traceState_2784_ = lean_ctor_get(v___x_2783_, 4);
v_env_2785_ = lean_ctor_get(v___x_2783_, 0);
v_nextMacroScope_2786_ = lean_ctor_get(v___x_2783_, 1);
v_ngen_2787_ = lean_ctor_get(v___x_2783_, 2);
v_auxDeclNGen_2788_ = lean_ctor_get(v___x_2783_, 3);
v_cache_2789_ = lean_ctor_get(v___x_2783_, 5);
v_messages_2790_ = lean_ctor_get(v___x_2783_, 6);
v_infoState_2791_ = lean_ctor_get(v___x_2783_, 7);
v_snapshotTasks_2792_ = lean_ctor_get(v___x_2783_, 8);
v_isSharedCheck_2822_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2794_ = v___x_2783_;
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_snapshotTasks_2792_);
lean_inc(v_infoState_2791_);
lean_inc(v_messages_2790_);
lean_inc(v_cache_2789_);
lean_inc(v_traceState_2784_);
lean_inc(v_auxDeclNGen_2788_);
lean_inc(v_ngen_2787_);
lean_inc(v_nextMacroScope_2786_);
lean_inc(v_env_2785_);
lean_dec(v___x_2783_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2822_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
uint64_t v_tid_2796_; lean_object* v_traces_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2821_; 
v_tid_2796_ = lean_ctor_get_uint64(v_traceState_2784_, sizeof(void*)*1);
v_traces_2797_ = lean_ctor_get(v_traceState_2784_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v_traceState_2784_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2799_ = v_traceState_2784_;
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
else
{
lean_inc(v_traces_2797_);
lean_dec(v_traceState_2784_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2821_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; double v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2811_; 
v___x_2801_ = lean_box(0);
v___x_2802_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2803_ = 0;
v___x_2804_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2805_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2805_, 0, v_cls_2772_);
lean_ctor_set(v___x_2805_, 1, v___x_2801_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
lean_ctor_set_float(v___x_2805_, sizeof(void*)*3, v___x_2802_);
lean_ctor_set_float(v___x_2805_, sizeof(void*)*3 + 8, v___x_2802_);
lean_ctor_set_uint8(v___x_2805_, sizeof(void*)*3 + 16, v___x_2803_);
v___x_2806_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2807_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2807_, 0, v___x_2805_);
lean_ctor_set(v___x_2807_, 1, v_a_2779_);
lean_ctor_set(v___x_2807_, 2, v___x_2806_);
lean_inc(v_ref_2777_);
v___x_2808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2808_, 0, v_ref_2777_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_PersistentArray_push___redArg(v_traces_2797_, v___x_2808_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 0, v___x_2809_);
v___x_2811_ = v___x_2799_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v___x_2809_);
lean_ctor_set_uint64(v_reuseFailAlloc_2820_, sizeof(void*)*1, v_tid_2796_);
v___x_2811_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2813_; 
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 4, v___x_2811_);
v___x_2813_ = v___x_2794_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_env_2785_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_nextMacroScope_2786_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_ngen_2787_);
lean_ctor_set(v_reuseFailAlloc_2819_, 3, v_auxDeclNGen_2788_);
lean_ctor_set(v_reuseFailAlloc_2819_, 4, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2819_, 5, v_cache_2789_);
lean_ctor_set(v_reuseFailAlloc_2819_, 6, v_messages_2790_);
lean_ctor_set(v_reuseFailAlloc_2819_, 7, v_infoState_2791_);
lean_ctor_set(v_reuseFailAlloc_2819_, 8, v_snapshotTasks_2792_);
v___x_2813_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2814_ = lean_st_ref_set(v___y_2775_, v___x_2813_);
v___x_2815_ = lean_box(0);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2815_);
v___x_2817_ = v___x_2781_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v___x_2815_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2824_, lean_object* v_msg_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v_res_2829_; 
v_res_2829_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2824_, v_msg_2825_, v___y_2826_, v___y_2827_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
return v_res_2829_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2833_, lean_object* v_cls_2834_, lean_object* v_x_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_){
_start:
{
lean_object* v_options_2839_; uint8_t v_hasTrace_2840_; 
v_options_2839_ = lean_ctor_get(v___y_2836_, 2);
v_hasTrace_2840_ = lean_ctor_get_uint8(v_options_2839_, sizeof(void*)*1);
if (v_hasTrace_2840_ == 0)
{
lean_object* v___x_2841_; 
lean_dec(v_cls_2834_);
v___x_2841_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2833_, v___y_2836_, v___y_2837_);
return v___x_2841_;
}
else
{
lean_object* v_inheritedTraceOptions_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; uint8_t v___x_2845_; 
v_inheritedTraceOptions_2842_ = lean_ctor_get(v___y_2836_, 13);
v___x_2843_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_2834_);
v___x_2844_ = l_Lean_Name_append(v___x_2843_, v_cls_2834_);
v___x_2845_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2842_, v_options_2839_, v___x_2844_);
lean_dec(v___x_2844_);
if (v___x_2845_ == 0)
{
lean_object* v___x_2846_; 
lean_dec(v_cls_2834_);
v___x_2846_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2833_, v___y_2836_, v___y_2837_);
return v___x_2846_;
}
else
{
lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2847_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2848_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2834_, v___x_2847_, v___y_2836_, v___y_2837_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v___x_2849_; 
lean_dec_ref_known(v___x_2848_, 1);
v___x_2849_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2833_, v___y_2836_, v___y_2837_);
return v___x_2849_;
}
else
{
lean_dec(v_decl_2833_);
return v___x_2848_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2850_, lean_object* v_cls_2851_, lean_object* v_x_2852_, lean_object* v___y_2853_, lean_object* v___y_2854_, lean_object* v___y_2855_){
_start:
{
lean_object* v_res_2856_; 
v_res_2856_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2850_, v_cls_2851_, v_x_2852_, v___y_2853_, v___y_2854_);
lean_dec(v___y_2854_);
lean_dec_ref(v___y_2853_);
lean_dec(v_x_2852_);
return v_res_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v___y_2857_, lean_object* v_a_2858_, lean_object* v___y_2859_, lean_object* v_a_x3f_2860_){
_start:
{
lean_object* v___x_2862_; lean_object* v_env_2863_; lean_object* v___x_2864_; 
v___x_2862_ = lean_st_ref_get(v___y_2857_);
v_env_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc_ref(v_env_2863_);
lean_dec(v___x_2862_);
v___x_2864_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2858_, v_env_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2872_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2872_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2872_ == 0)
{
v___x_2867_ = v___x_2864_;
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_a_2865_);
lean_dec(v___x_2864_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2872_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2870_; 
if (v_isShared_2868_ == 0)
{
v___x_2870_ = v___x_2867_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2871_; 
v_reuseFailAlloc_2871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2871_, 0, v_a_2865_);
v___x_2870_ = v_reuseFailAlloc_2871_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
return v___x_2870_;
}
}
}
else
{
lean_object* v_a_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2885_; 
v_a_2873_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2875_ = v___x_2864_;
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_a_2873_);
lean_dec(v___x_2864_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2885_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v_ref_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2883_; 
v_ref_2877_ = lean_ctor_get(v___y_2859_, 5);
v___x_2878_ = lean_io_error_to_string(v_a_2873_);
v___x_2879_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2878_);
v___x_2880_ = l_Lean_MessageData_ofFormat(v___x_2879_);
lean_inc(v_ref_2877_);
v___x_2881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2881_, 0, v_ref_2877_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2881_);
v___x_2883_ = v___x_2875_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v___y_2886_, lean_object* v_a_2887_, lean_object* v___y_2888_, lean_object* v_a_x3f_2889_, lean_object* v___y_2890_){
_start:
{
lean_object* v_res_2891_; 
v_res_2891_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v___y_2886_, v_a_2887_, v___y_2888_, v_a_x3f_2889_);
lean_dec(v_a_x3f_2889_);
lean_dec_ref(v___y_2888_);
lean_dec(v___y_2886_);
return v_res_2891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_asyncEnv_2892_, lean_object* v_a_2893_, lean_object* v_decl_2894_, lean_object* v_x_2895_, lean_object* v___y_2896_, lean_object* v___y_2897_){
_start:
{
lean_object* v___x_2899_; lean_object* v_r_2900_; 
v___x_2899_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2892_, v___y_2897_);
lean_dec_ref(v___x_2899_);
v_r_2900_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2894_, v___y_2896_, v___y_2897_);
if (lean_obj_tag(v_r_2900_) == 0)
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2917_; 
v_a_2901_ = lean_ctor_get(v_r_2900_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v_r_2900_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2903_ = v_r_2900_;
v_isShared_2904_ = v_isSharedCheck_2917_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v_r_2900_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2917_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
lean_inc(v_a_2901_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set_tag(v___x_2903_, 1);
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2907_; 
v___x_2907_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v___y_2897_, v_a_2893_, v___y_2896_, v___x_2906_);
lean_dec_ref(v___x_2906_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v___x_2907_, 0);
lean_dec(v_unused_2915_);
v___x_2909_ = v___x_2907_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_dec(v___x_2907_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
lean_ctor_set(v___x_2909_, 0, v_a_2901_);
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2901_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
else
{
lean_dec(v_a_2901_);
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
v_a_2918_ = lean_ctor_get(v_r_2900_, 0);
lean_inc(v_a_2918_);
lean_dec_ref_known(v_r_2900_, 1);
v___x_2919_ = lean_box(0);
v___x_2920_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v___y_2897_, v_a_2893_, v___y_2896_, v___x_2919_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2927_ == 0)
{
lean_object* v_unused_2928_; 
v_unused_2928_ = lean_ctor_get(v___x_2920_, 0);
lean_dec(v_unused_2928_);
v___x_2922_ = v___x_2920_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_dec(v___x_2920_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
lean_ctor_set_tag(v___x_2922_, 1);
lean_ctor_set(v___x_2922_, 0, v_a_2918_);
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2918_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
else
{
lean_dec(v_a_2918_);
return v___x_2920_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_asyncEnv_2929_, lean_object* v_a_2930_, lean_object* v_decl_2931_, lean_object* v_x_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_){
_start:
{
lean_object* v_res_2936_; 
v_res_2936_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_asyncEnv_2929_, v_a_2930_, v_decl_2931_, v_x_2932_, v___y_2933_, v___y_2934_);
lean_dec(v___y_2934_);
lean_dec_ref(v___y_2933_);
lean_dec_ref(v_x_2932_);
return v_res_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2937_, lean_object* v___y_2938_){
_start:
{
lean_object* v_options_2940_; uint8_t v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v_options_2940_ = lean_ctor_get(v___y_2938_, 2);
v___x_2941_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2940_, v_opt_2937_);
v___x_2942_ = lean_box(v___x_2941_);
v___x_2943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2943_, 0, v___x_2942_);
return v___x_2943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2944_, lean_object* v___y_2945_, lean_object* v___y_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2944_, v___y_2945_);
lean_dec_ref(v___y_2945_);
lean_dec_ref(v_opt_2944_);
return v_res_2947_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2948_){
_start:
{
if (lean_obj_tag(v_x_2948_) == 0)
{
uint8_t v___x_2949_; 
v___x_2949_ = 1;
return v___x_2949_;
}
else
{
lean_object* v_head_2950_; lean_object* v_tail_2951_; uint8_t v___x_2952_; 
v_head_2950_ = lean_ctor_get(v_x_2948_, 0);
v_tail_2951_ = lean_ctor_get(v_x_2948_, 1);
v___x_2952_ = l_Lean_isPrivateName(v_head_2950_);
if (v___x_2952_ == 0)
{
return v___x_2952_;
}
else
{
v_x_2948_ = v_tail_2951_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2954_){
_start:
{
uint8_t v_res_2955_; lean_object* v_r_2956_; 
v_res_2955_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2954_);
lean_dec(v_x_2954_);
v_r_2956_ = lean_box(v_res_2955_);
return v_r_2956_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3(void){
_start:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2962_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__2));
v___x_2963_ = l_Lean_stringToMessageData(v___x_2962_);
return v___x_2963_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5(void){
_start:
{
lean_object* v___x_2965_; lean_object* v___x_2966_; 
v___x_2965_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__4));
v___x_2966_ = l_Lean_stringToMessageData(v___x_2965_);
return v___x_2966_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7(void){
_start:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; 
v___x_2968_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__6));
v___x_2969_ = l_Lean_stringToMessageData(v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_decl_2970_, uint8_t v___x_2971_, uint8_t v___x_2972_, lean_object* v___x_2973_, lean_object* v_cls_2974_, lean_object* v___x_2975_, lean_object* v_____x_2976_, lean_object* v_exportedInfo_x3f_2977_, lean_object* v___y_2978_, lean_object* v___y_2979_){
_start:
{
lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v_a_2984_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v_a_2997_; lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v___y_3012_; lean_object* v___y_3013_; lean_object* v___y_3014_; lean_object* v___y_3015_; lean_object* v___y_3016_; lean_object* v___y_3017_; lean_object* v_snd_3080_; lean_object* v_fst_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3208_; 
v_snd_3080_ = lean_ctor_get(v_____x_2976_, 1);
v_fst_3081_ = lean_ctor_get(v_____x_2976_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v_____x_2976_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3083_ = v_____x_2976_;
v_isShared_3084_ = v_isSharedCheck_3208_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_snd_3080_);
lean_inc(v_fst_3081_);
lean_dec(v_____x_2976_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3208_;
goto v_resetjp_3082_;
}
v___jp_2981_:
{
lean_object* v___x_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
v___x_2985_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2982_, v___y_2983_);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_2992_ == 0)
{
lean_object* v_unused_2993_; 
v_unused_2993_ = lean_ctor_get(v___x_2985_, 0);
lean_dec(v_unused_2993_);
v___x_2987_ = v___x_2985_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v___x_2985_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
lean_ctor_set_tag(v___x_2987_, 1);
lean_ctor_set(v___x_2987_, 0, v_a_2984_);
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2984_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
v___jp_2994_:
{
lean_object* v___x_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v___x_2998_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2995_, v___y_2996_);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3005_ == 0)
{
lean_object* v_unused_3006_; 
v_unused_3006_ = lean_ctor_get(v___x_2998_, 0);
lean_dec(v_unused_3006_);
v___x_3000_ = v___x_2998_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_dec(v___x_2998_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
lean_ctor_set(v___x_3000_, 0, v_a_2997_);
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2997_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
v___jp_3007_:
{
lean_object* v___x_3018_; 
lean_inc_ref(v___y_3012_);
v___x_3018_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3014_, v___y_3012_, v___y_3013_, v___y_3017_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref_known(v___x_3018_, 1);
lean_inc_ref(v___y_3009_);
v___x_3019_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3009_, v___y_3015_);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3065_ == 0)
{
lean_object* v_unused_3066_; 
v_unused_3066_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3066_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3065_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v_options_3023_; lean_object* v___x_3024_; uint8_t v___x_3025_; 
v_options_3023_ = lean_ctor_get(v___y_3016_, 2);
v___x_3024_ = l_Lean_Elab_async;
v___x_3025_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3023_, v___x_3024_);
if (v___x_3025_ == 0)
{
lean_object* v___x_3026_; lean_object* v_r_3027_; 
lean_del_object(v___x_3021_);
lean_dec_ref(v___y_3011_);
lean_dec_ref(v___y_3008_);
v___x_3026_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3012_, v___y_3015_);
lean_dec_ref(v___x_3026_);
v_r_3027_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2970_, v___y_3016_, v___y_3015_);
if (lean_obj_tag(v_r_3027_) == 0)
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3037_; 
v_a_3028_ = lean_ctor_get(v_r_3027_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_r_3027_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3030_ = v_r_3027_;
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v_r_3027_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3037_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
lean_inc(v_a_3028_);
if (v_isShared_3031_ == 0)
{
lean_ctor_set_tag(v___x_3030_, 1);
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
lean_object* v___x_3034_; 
v___x_3034_ = lean_apply_2(v___y_3010_, v___x_3033_, lean_box(0));
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_dec_ref_known(v___x_3034_, 1);
v___y_2995_ = v___y_3009_;
v___y_2996_ = v___y_3015_;
v_a_2997_ = v_a_3028_;
goto v___jp_2994_;
}
else
{
lean_object* v_a_3035_; 
lean_dec(v_a_3028_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
lean_inc(v_a_3035_);
lean_dec_ref_known(v___x_3034_, 1);
v___y_2982_ = v___y_3009_;
v___y_2983_ = v___y_3015_;
v_a_2984_ = v_a_3035_;
goto v___jp_2981_;
}
}
}
}
else
{
lean_object* v_a_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; 
v_a_3038_ = lean_ctor_get(v_r_3027_, 0);
lean_inc(v_a_3038_);
lean_dec_ref_known(v_r_3027_, 1);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_apply_2(v___y_3010_, v___x_3039_, lean_box(0));
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_dec_ref_known(v___x_3040_, 1);
v___y_2982_ = v___y_3009_;
v___y_2983_ = v___y_3015_;
v_a_2984_ = v_a_3038_;
goto v___jp_2981_;
}
else
{
lean_object* v_a_3041_; 
lean_dec(v_a_3038_);
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
lean_dec_ref_known(v___x_3040_, 1);
v___y_2982_ = v___y_3009_;
v___y_2983_ = v___y_3015_;
v_a_2984_ = v_a_3041_;
goto v___jp_2981_;
}
}
}
else
{
lean_object* v___x_3042_; lean_object* v___x_3044_; 
lean_dec_ref(v___y_3012_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec(v_decl_2970_);
v___x_3042_ = l_IO_CancelToken_new();
if (v_isShared_3022_ == 0)
{
lean_ctor_set_tag(v___x_3021_, 1);
lean_ctor_set(v___x_3021_, 0, v___x_3042_);
v___x_3044_ = v___x_3021_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3042_);
v___x_3044_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3045_ = lean_unsigned_to_nat(0u);
v___x_3046_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1));
v___x_3047_ = l_Lean_Name_toString(v___x_3046_, v___x_2971_);
lean_inc_ref(v___x_3044_);
v___x_3048_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3008_, v___x_3044_, v___x_3047_, v___y_3016_, v___y_3015_);
if (lean_obj_tag(v___x_3048_) == 0)
{
lean_object* v_a_3049_; lean_object* v_checked_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; 
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref_known(v___x_3048_, 1);
v_checked_3050_ = lean_ctor_get(v___y_3011_, 2);
lean_inc_ref(v_checked_3050_);
lean_dec_ref(v___y_3011_);
v___x_3051_ = lean_io_map_task(v_a_3049_, v_checked_3050_, v___x_3045_, v___x_2972_);
v___x_3052_ = lean_box(0);
v___x_3053_ = lean_box(2);
v___x_3054_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
lean_ctor_set(v___x_3054_, 2, v___x_3044_);
lean_ctor_set(v___x_3054_, 3, v___x_3051_);
v___x_3055_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3054_, v___y_3015_);
return v___x_3055_;
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v___x_3044_);
lean_dec_ref(v___y_3011_);
v_a_3056_ = lean_ctor_get(v___x_3048_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3048_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3048_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3048_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v___y_3012_);
lean_dec_ref(v___y_3011_);
lean_dec_ref(v___y_3010_);
lean_dec_ref(v___y_3009_);
lean_dec_ref(v___y_3008_);
lean_dec(v_decl_2970_);
v_a_3067_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3069_ = v___x_3018_;
v_isShared_3070_ = v_isSharedCheck_3079_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_3018_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3079_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v_ref_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3077_; 
v_ref_3071_ = lean_ctor_get(v___y_3016_, 5);
v___x_3072_ = lean_io_error_to_string(v_a_3067_);
v___x_3073_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
v___x_3074_ = l_Lean_MessageData_ofFormat(v___x_3073_);
lean_inc(v_ref_3071_);
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v_ref_3071_);
lean_ctor_set(v___x_3075_, 1, v___x_3074_);
if (v_isShared_3070_ == 0)
{
lean_ctor_set(v___x_3069_, 0, v___x_3075_);
v___x_3077_ = v___x_3069_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
v___x_3077_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3076_;
}
v_reusejp_3076_:
{
return v___x_3077_;
}
}
}
}
v_resetjp_3082_:
{
lean_object* v_fst_3085_; lean_object* v_snd_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3207_; 
v_fst_3085_ = lean_ctor_get(v_snd_3080_, 0);
v_snd_3086_ = lean_ctor_get(v_snd_3080_, 1);
v_isSharedCheck_3207_ = !lean_is_exclusive(v_snd_3080_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3088_ = v_snd_3080_;
v_isShared_3089_ = v_isSharedCheck_3207_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_snd_3086_);
lean_inc(v_fst_3085_);
lean_dec(v_snd_3080_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3207_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___y_3091_; lean_object* v___y_3092_; lean_object* v___y_3093_; lean_object* v___y_3094_; lean_object* v___y_3095_; lean_object* v___y_3096_; lean_object* v___y_3097_; lean_object* v_exportedInfo_x3f_3122_; lean_object* v___y_3123_; lean_object* v___y_3124_; lean_object* v___y_3134_; lean_object* v___y_3135_; lean_object* v___y_3138_; lean_object* v___y_3139_; lean_object* v___y_3142_; lean_object* v___y_3143_; lean_object* v___y_3165_; lean_object* v___y_3166_; lean_object* v___x_3197_; lean_object* v_env_3198_; uint8_t v___x_3199_; 
v___x_3197_ = lean_st_ref_get(v___y_2979_);
v_env_3198_ = lean_ctor_get(v___x_3197_, 0);
lean_inc_ref(v_env_3198_);
lean_dec(v___x_3197_);
v___x_3199_ = l_Lean_Environment_containsOnBranch(v_env_3198_, v_fst_3081_);
lean_dec_ref(v_env_3198_);
if (v___x_3199_ == 0)
{
lean_del_object(v___x_3083_);
v___y_3165_ = v___y_2978_;
v___y_3166_ = v___y_2979_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3200_; lean_object* v_env_3201_; lean_object* v___x_3202_; lean_object* v___x_3204_; 
lean_del_object(v___x_3088_);
lean_dec(v_snd_3086_);
lean_dec(v_fst_3085_);
lean_dec(v_exportedInfo_x3f_2977_);
lean_dec(v___x_2975_);
lean_dec(v_cls_2974_);
lean_dec_ref(v___x_2973_);
lean_dec(v_decl_2970_);
v___x_3200_ = lean_st_ref_get(v___y_2979_);
v_env_3201_ = lean_ctor_get(v___x_3200_, 0);
lean_inc_ref(v_env_3201_);
lean_dec(v___x_3200_);
v___x_3202_ = lean_elab_environment_to_kernel_env(v_env_3201_);
if (v_isShared_3084_ == 0)
{
lean_ctor_set_tag(v___x_3083_, 1);
lean_ctor_set(v___x_3083_, 1, v_fst_3081_);
lean_ctor_set(v___x_3083_, 0, v___x_3202_);
v___x_3204_ = v___x_3083_;
goto v_reusejp_3203_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v___x_3202_);
lean_ctor_set(v_reuseFailAlloc_3206_, 1, v_fst_3081_);
v___x_3204_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3203_;
}
v_reusejp_3203_:
{
lean_object* v___x_3205_; 
v___x_3205_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3204_, v___y_2978_, v___y_2979_);
return v___x_3205_;
}
}
v___jp_3090_:
{
uint8_t v___x_3098_; lean_object* v___x_3099_; 
v___x_3098_ = lean_unbox(v_snd_3086_);
lean_dec(v_snd_3086_);
lean_inc_ref(v___y_3092_);
v___x_3099_ = l_Lean_Environment_addConstAsync(v___y_3092_, v_fst_3081_, v___x_3098_, v___y_3097_, v___x_2972_, v___x_2971_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v_mainEnv_3101_; lean_object* v_asyncEnv_3102_; lean_object* v___f_3103_; lean_object* v___f_3104_; lean_object* v___x_3105_; 
lean_del_object(v___x_3088_);
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc_n(v_a_3100_, 3);
lean_dec_ref_known(v___x_3099_, 1);
v_mainEnv_3101_ = lean_ctor_get(v_a_3100_, 0);
lean_inc_ref(v_mainEnv_3101_);
v_asyncEnv_3102_ = lean_ctor_get(v_a_3100_, 1);
lean_inc_ref_n(v_asyncEnv_3102_, 2);
lean_inc_ref(v___y_3091_);
lean_inc(v___y_3093_);
v___f_3103_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3103_, 0, v___y_3093_);
lean_closure_set(v___f_3103_, 1, v_a_3100_);
lean_closure_set(v___f_3103_, 2, v___y_3091_);
lean_inc(v_decl_2970_);
v___f_3104_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed), 7, 3);
lean_closure_set(v___f_3104_, 0, v_asyncEnv_3102_);
lean_closure_set(v___f_3104_, 1, v_a_3100_);
lean_closure_set(v___f_3104_, 2, v_decl_2970_);
v___x_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3105_, 0, v_fst_3085_);
if (lean_obj_tag(v___y_3094_) == 0)
{
lean_inc_ref(v___x_3105_);
v___y_3008_ = v___f_3104_;
v___y_3009_ = v_mainEnv_3101_;
v___y_3010_ = v___f_3103_;
v___y_3011_ = v___y_3092_;
v___y_3012_ = v_asyncEnv_3102_;
v___y_3013_ = v___x_3105_;
v___y_3014_ = v_a_3100_;
v___y_3015_ = v___y_3095_;
v___y_3016_ = v___y_3096_;
v___y_3017_ = v___x_3105_;
goto v___jp_3007_;
}
else
{
v___y_3008_ = v___f_3104_;
v___y_3009_ = v_mainEnv_3101_;
v___y_3010_ = v___f_3103_;
v___y_3011_ = v___y_3092_;
v___y_3012_ = v_asyncEnv_3102_;
v___y_3013_ = v___x_3105_;
v___y_3014_ = v_a_3100_;
v___y_3015_ = v___y_3095_;
v___y_3016_ = v___y_3096_;
v___y_3017_ = v___y_3094_;
goto v___jp_3007_;
}
}
else
{
lean_object* v_a_3106_; lean_object* v___x_3108_; uint8_t v_isShared_3109_; uint8_t v_isSharedCheck_3120_; 
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3092_);
lean_dec(v_fst_3085_);
lean_dec(v_decl_2970_);
v_a_3106_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_3108_ = v___x_3099_;
v_isShared_3109_ = v_isSharedCheck_3120_;
goto v_resetjp_3107_;
}
else
{
lean_inc(v_a_3106_);
lean_dec(v___x_3099_);
v___x_3108_ = lean_box(0);
v_isShared_3109_ = v_isSharedCheck_3120_;
goto v_resetjp_3107_;
}
v_resetjp_3107_:
{
lean_object* v_ref_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3115_; 
v_ref_3110_ = lean_ctor_get(v___y_3096_, 5);
v___x_3111_ = lean_io_error_to_string(v_a_3106_);
v___x_3112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3111_);
v___x_3113_ = l_Lean_MessageData_ofFormat(v___x_3112_);
lean_inc(v_ref_3110_);
if (v_isShared_3089_ == 0)
{
lean_ctor_set(v___x_3088_, 1, v___x_3113_);
lean_ctor_set(v___x_3088_, 0, v_ref_3110_);
v___x_3115_ = v___x_3088_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3119_; 
v_reuseFailAlloc_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3119_, 0, v_ref_3110_);
lean_ctor_set(v_reuseFailAlloc_3119_, 1, v___x_3113_);
v___x_3115_ = v_reuseFailAlloc_3119_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
lean_object* v___x_3117_; 
if (v_isShared_3109_ == 0)
{
lean_ctor_set(v___x_3108_, 0, v___x_3115_);
v___x_3117_ = v___x_3108_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v___x_3115_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
}
}
v___jp_3121_:
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_st_ref_get(v___y_3124_);
if (lean_obj_tag(v_exportedInfo_x3f_3122_) == 0)
{
lean_object* v_env_3126_; lean_object* v___x_3127_; 
v_env_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc_ref(v_env_3126_);
lean_dec(v___x_3125_);
v___x_3127_ = lean_box(0);
v___y_3091_ = v___y_3123_;
v___y_3092_ = v_env_3126_;
v___y_3093_ = v___y_3124_;
v___y_3094_ = v_exportedInfo_x3f_3122_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___x_3127_;
goto v___jp_3090_;
}
else
{
lean_object* v_env_3128_; lean_object* v_val_3129_; uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; 
v_env_3128_ = lean_ctor_get(v___x_3125_, 0);
lean_inc_ref(v_env_3128_);
lean_dec(v___x_3125_);
v_val_3129_ = lean_ctor_get(v_exportedInfo_x3f_3122_, 0);
v___x_3130_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3129_);
v___x_3131_ = lean_box(v___x_3130_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v___x_3131_);
v___y_3091_ = v___y_3123_;
v___y_3092_ = v_env_3128_;
v___y_3093_ = v___y_3124_;
v___y_3094_ = v_exportedInfo_x3f_3122_;
v___y_3095_ = v___y_3124_;
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___x_3132_;
goto v___jp_3090_;
}
}
v___jp_3133_:
{
lean_object* v___x_3136_; 
lean_inc(v_fst_3085_);
v___x_3136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_fst_3085_);
v_exportedInfo_x3f_3122_ = v___x_3136_;
v___y_3123_ = v___y_3134_;
v___y_3124_ = v___y_3135_;
goto v___jp_3121_;
}
v___jp_3137_:
{
lean_object* v___x_3140_; 
lean_inc(v_fst_3085_);
v___x_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3140_, 0, v_fst_3085_);
v_exportedInfo_x3f_3122_ = v___x_3140_;
v___y_3123_ = v___y_3138_;
v___y_3124_ = v___y_3139_;
goto v___jp_3121_;
}
v___jp_3141_:
{
lean_object* v___x_3144_; lean_object* v_env_3145_; lean_object* v_nextMacroScope_3146_; lean_object* v_ngen_3147_; lean_object* v_auxDeclNGen_3148_; lean_object* v_traceState_3149_; lean_object* v_messages_3150_; lean_object* v_infoState_3151_; lean_object* v_snapshotTasks_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3162_; 
v___x_3144_ = lean_st_ref_take(v___y_3142_);
v_env_3145_ = lean_ctor_get(v___x_3144_, 0);
v_nextMacroScope_3146_ = lean_ctor_get(v___x_3144_, 1);
v_ngen_3147_ = lean_ctor_get(v___x_3144_, 2);
v_auxDeclNGen_3148_ = lean_ctor_get(v___x_3144_, 3);
v_traceState_3149_ = lean_ctor_get(v___x_3144_, 4);
v_messages_3150_ = lean_ctor_get(v___x_3144_, 6);
v_infoState_3151_ = lean_ctor_get(v___x_3144_, 7);
v_snapshotTasks_3152_ = lean_ctor_get(v___x_3144_, 8);
v_isSharedCheck_3162_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3162_ == 0)
{
lean_object* v_unused_3163_; 
v_unused_3163_ = lean_ctor_get(v___x_3144_, 5);
lean_dec(v_unused_3163_);
v___x_3154_ = v___x_3144_;
v_isShared_3155_ = v_isSharedCheck_3162_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snapshotTasks_3152_);
lean_inc(v_infoState_3151_);
lean_inc(v_messages_3150_);
lean_inc(v_traceState_3149_);
lean_inc(v_auxDeclNGen_3148_);
lean_inc(v_ngen_3147_);
lean_inc(v_nextMacroScope_3146_);
lean_inc(v_env_3145_);
lean_dec(v___x_3144_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3162_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3156_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3086_);
lean_inc(v_fst_3081_);
v___x_3157_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3156_, v_env_3145_, v_fst_3081_, v_snd_3086_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 5, v___x_2973_);
lean_ctor_set(v___x_3154_, 0, v___x_3157_);
v___x_3159_ = v___x_3154_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_nextMacroScope_3146_);
lean_ctor_set(v_reuseFailAlloc_3161_, 2, v_ngen_3147_);
lean_ctor_set(v_reuseFailAlloc_3161_, 3, v_auxDeclNGen_3148_);
lean_ctor_set(v_reuseFailAlloc_3161_, 4, v_traceState_3149_);
lean_ctor_set(v_reuseFailAlloc_3161_, 5, v___x_2973_);
lean_ctor_set(v_reuseFailAlloc_3161_, 6, v_messages_3150_);
lean_ctor_set(v_reuseFailAlloc_3161_, 7, v_infoState_3151_);
lean_ctor_set(v_reuseFailAlloc_3161_, 8, v_snapshotTasks_3152_);
v___x_3159_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_st_ref_set(v___y_3142_, v___x_3159_);
v_exportedInfo_x3f_3122_ = v_exportedInfo_x3f_2977_;
v___y_3123_ = v___y_3143_;
v___y_3124_ = v___y_3142_;
goto v___jp_3121_;
}
}
}
v___jp_3164_:
{
lean_object* v___x_3167_; uint8_t v___x_3168_; 
lean_inc(v_decl_2970_);
v___x_3167_ = l_Lean_Declaration_getTopLevelNames(v_decl_2970_);
v___x_3168_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3167_);
lean_dec(v___x_3167_);
if (v___x_3168_ == 0)
{
lean_dec(v___x_2975_);
if (lean_obj_tag(v_exportedInfo_x3f_2977_) == 0)
{
if (v___x_2972_ == 0)
{
lean_object* v_options_3169_; uint8_t v_hasTrace_3170_; 
lean_dec_ref(v___x_2973_);
v_options_3169_ = lean_ctor_get(v___y_3165_, 2);
v_hasTrace_3170_ = lean_ctor_get_uint8(v_options_3169_, sizeof(void*)*1);
if (v_hasTrace_3170_ == 0)
{
lean_dec(v_cls_2974_);
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
goto v___jp_3133_;
}
else
{
lean_object* v_inheritedTraceOptions_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; uint8_t v___x_3174_; 
v_inheritedTraceOptions_3171_ = lean_ctor_get(v___y_3165_, 13);
v___x_3172_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_2974_);
v___x_3173_ = l_Lean_Name_append(v___x_3172_, v_cls_2974_);
v___x_3174_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3171_, v_options_3169_, v___x_3173_);
lean_dec(v___x_3173_);
if (v___x_3174_ == 0)
{
lean_dec(v_cls_2974_);
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
goto v___jp_3133_;
}
else
{
lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3175_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3);
v___x_3176_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2974_, v___x_3175_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3176_) == 0)
{
lean_dec_ref_known(v___x_3176_, 1);
v___y_3134_ = v___y_3165_;
v___y_3135_ = v___y_3166_;
goto v___jp_3133_;
}
else
{
lean_del_object(v___x_3088_);
lean_dec(v_snd_3086_);
lean_dec(v_fst_3085_);
lean_dec(v_fst_3081_);
lean_dec(v_decl_2970_);
return v___x_3176_;
}
}
}
}
else
{
lean_dec(v_cls_2974_);
v___y_3142_ = v___y_3166_;
v___y_3143_ = v___y_3165_;
goto v___jp_3141_;
}
}
else
{
lean_dec(v_cls_2974_);
v___y_3142_ = v___y_3166_;
v___y_3143_ = v___y_3165_;
goto v___jp_3141_;
}
}
else
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v_a_3179_; uint8_t v___x_3180_; 
lean_dec(v_exportedInfo_x3f_2977_);
lean_dec_ref(v___x_2973_);
v___x_3177_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3178_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3177_, v___y_3165_);
v_a_3179_ = lean_ctor_get(v___x_3178_, 0);
lean_inc(v_a_3179_);
lean_dec_ref(v___x_3178_);
v___x_3180_ = lean_unbox(v_a_3179_);
lean_dec(v_a_3179_);
if (v___x_3180_ == 0)
{
lean_object* v_options_3181_; uint8_t v_hasTrace_3182_; 
v_options_3181_ = lean_ctor_get(v___y_3165_, 2);
v_hasTrace_3182_ = lean_ctor_get_uint8(v_options_3181_, sizeof(void*)*1);
if (v_hasTrace_3182_ == 0)
{
lean_dec(v_cls_2974_);
v_exportedInfo_x3f_3122_ = v___x_2975_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
goto v___jp_3121_;
}
else
{
lean_object* v_inheritedTraceOptions_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v___x_3186_; 
v_inheritedTraceOptions_3183_ = lean_ctor_get(v___y_3165_, 13);
v___x_3184_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_2974_);
v___x_3185_ = l_Lean_Name_append(v___x_3184_, v_cls_2974_);
v___x_3186_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3183_, v_options_3181_, v___x_3185_);
lean_dec(v___x_3185_);
if (v___x_3186_ == 0)
{
lean_dec(v_cls_2974_);
v_exportedInfo_x3f_3122_ = v___x_2975_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
goto v___jp_3121_;
}
else
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5);
v___x_3188_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2974_, v___x_3187_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3188_) == 0)
{
lean_dec_ref_known(v___x_3188_, 1);
v_exportedInfo_x3f_3122_ = v___x_2975_;
v___y_3123_ = v___y_3165_;
v___y_3124_ = v___y_3166_;
goto v___jp_3121_;
}
else
{
lean_del_object(v___x_3088_);
lean_dec(v_snd_3086_);
lean_dec(v_fst_3085_);
lean_dec(v_fst_3081_);
lean_dec(v___x_2975_);
lean_dec(v_decl_2970_);
return v___x_3188_;
}
}
}
}
else
{
lean_object* v_options_3189_; uint8_t v_hasTrace_3190_; 
lean_dec(v___x_2975_);
v_options_3189_ = lean_ctor_get(v___y_3165_, 2);
v_hasTrace_3190_ = lean_ctor_get_uint8(v_options_3189_, sizeof(void*)*1);
if (v_hasTrace_3190_ == 0)
{
lean_dec(v_cls_2974_);
v___y_3138_ = v___y_3165_;
v___y_3139_ = v___y_3166_;
goto v___jp_3137_;
}
else
{
lean_object* v_inheritedTraceOptions_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; uint8_t v___x_3194_; 
v_inheritedTraceOptions_3191_ = lean_ctor_get(v___y_3165_, 13);
v___x_3192_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_2974_);
v___x_3193_ = l_Lean_Name_append(v___x_3192_, v_cls_2974_);
v___x_3194_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3191_, v_options_3189_, v___x_3193_);
lean_dec(v___x_3193_);
if (v___x_3194_ == 0)
{
lean_dec(v_cls_2974_);
v___y_3138_ = v___y_3165_;
v___y_3139_ = v___y_3166_;
goto v___jp_3137_;
}
else
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7);
v___x_3196_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2974_, v___x_3195_, v___y_3165_, v___y_3166_);
if (lean_obj_tag(v___x_3196_) == 0)
{
lean_dec_ref_known(v___x_3196_, 1);
v___y_3138_ = v___y_3165_;
v___y_3139_ = v___y_3166_;
goto v___jp_3137_;
}
else
{
lean_del_object(v___x_3088_);
lean_dec(v_snd_3086_);
lean_dec(v_fst_3085_);
lean_dec(v_fst_3081_);
lean_dec(v_decl_2970_);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_decl_3209_, lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v___x_3212_, lean_object* v_cls_3213_, lean_object* v___x_3214_, lean_object* v_____x_3215_, lean_object* v_exportedInfo_x3f_3216_, lean_object* v___y_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
uint8_t v___x_60465__boxed_3220_; uint8_t v___x_60466__boxed_3221_; lean_object* v_res_3222_; 
v___x_60465__boxed_3220_ = lean_unbox(v___x_3210_);
v___x_60466__boxed_3221_ = lean_unbox(v___x_3211_);
v_res_3222_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_decl_3209_, v___x_60465__boxed_3220_, v___x_60466__boxed_3221_, v___x_3212_, v_cls_3213_, v___x_3214_, v_____x_3215_, v_exportedInfo_x3f_3216_, v___y_3217_, v___y_3218_);
lean_dec(v___y_3218_);
lean_dec_ref(v___y_3217_);
return v_res_3222_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__0));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; 
v___x_3227_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__2));
v___x_3228_ = l_Lean_stringToMessageData(v___x_3227_);
return v___x_3228_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v___f_3229_, lean_object* v___x_3230_, lean_object* v_cls_3231_, uint8_t v_forceExpose_3232_, lean_object* v_defn_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v_exportedInfo_x3f_3238_; lean_object* v___y_3239_; lean_object* v___y_3240_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v_env_3261_; uint8_t v___y_3263_; uint8_t v___x_3280_; 
v___x_3259_ = lean_st_ref_get(v___y_3235_);
v___x_3260_ = lean_st_ref_get(v___y_3235_);
v_env_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc_ref(v_env_3261_);
lean_dec(v___x_3260_);
v___x_3280_ = lean_bool_not(v_forceExpose_3232_);
if (v___x_3280_ == 0)
{
lean_dec(v___x_3259_);
v___y_3263_ = v___x_3280_;
goto v___jp_3262_;
}
else
{
lean_object* v_env_3281_; lean_object* v___x_3282_; uint8_t v_isModule_3283_; 
v_env_3281_ = lean_ctor_get(v___x_3259_, 0);
lean_inc_ref(v_env_3281_);
lean_dec(v___x_3259_);
v___x_3282_ = l_Lean_Environment_header(v_env_3281_);
lean_dec_ref(v_env_3281_);
v_isModule_3283_ = lean_ctor_get_uint8(v___x_3282_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3282_);
v___y_3263_ = v_isModule_3283_;
goto v___jp_3262_;
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
v___x_3248_ = lean_apply_5(v___f_3229_, v___x_3247_, v_exportedInfo_x3f_3238_, v___y_3239_, v___y_3240_, lean_box(0));
return v___x_3248_;
}
v___jp_3249_:
{
lean_object* v_toConstantVal_3252_; uint8_t v_safety_3253_; uint8_t v___x_3254_; uint8_t v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_toConstantVal_3252_ = lean_ctor_get(v_defn_3233_, 0);
v_safety_3253_ = lean_ctor_get_uint8(v_defn_3233_, sizeof(void*)*4);
v___x_3254_ = 0;
v___x_3255_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3253_, v___x_3254_);
lean_inc_ref(v_toConstantVal_3252_);
v___x_3256_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3256_, 0, v_toConstantVal_3252_);
lean_ctor_set_uint8(v___x_3256_, sizeof(void*)*1, v___x_3255_);
v___x_3257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
v___x_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3258_, 0, v___x_3257_);
v_exportedInfo_x3f_3238_ = v___x_3258_;
v___y_3239_ = v___y_3250_;
v___y_3240_ = v___y_3251_;
goto v___jp_3237_;
}
v___jp_3262_:
{
if (v___y_3263_ == 0)
{
lean_dec_ref(v_env_3261_);
lean_dec(v_cls_3231_);
v_exportedInfo_x3f_3238_ = v___x_3230_;
v___y_3239_ = v___y_3234_;
v___y_3240_ = v___y_3235_;
goto v___jp_3237_;
}
else
{
uint8_t v_isExporting_3264_; uint8_t v___x_3265_; 
v_isExporting_3264_ = lean_ctor_get_uint8(v_env_3261_, sizeof(void*)*8);
lean_dec_ref(v_env_3261_);
v___x_3265_ = lean_bool_not(v_isExporting_3264_);
if (v___x_3265_ == 0)
{
lean_dec(v_cls_3231_);
v_exportedInfo_x3f_3238_ = v___x_3230_;
v___y_3239_ = v___y_3234_;
v___y_3240_ = v___y_3235_;
goto v___jp_3237_;
}
else
{
lean_object* v_options_3266_; uint8_t v_hasTrace_3267_; 
lean_dec(v___x_3230_);
v_options_3266_ = lean_ctor_get(v___y_3234_, 2);
v_hasTrace_3267_ = lean_ctor_get_uint8(v_options_3266_, sizeof(void*)*1);
if (v_hasTrace_3267_ == 0)
{
lean_dec(v_cls_3231_);
v___y_3250_ = v___y_3234_;
v___y_3251_ = v___y_3235_;
goto v___jp_3249_;
}
else
{
lean_object* v_inheritedTraceOptions_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; 
v_inheritedTraceOptions_3268_ = lean_ctor_get(v___y_3234_, 13);
v___x_3269_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_3231_);
v___x_3270_ = l_Lean_Name_append(v___x_3269_, v_cls_3231_);
v___x_3271_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3268_, v_options_3266_, v___x_3270_);
lean_dec(v___x_3270_);
if (v___x_3271_ == 0)
{
lean_dec(v_cls_3231_);
v___y_3250_ = v___y_3234_;
v___y_3251_ = v___y_3235_;
goto v___jp_3249_;
}
else
{
lean_object* v_toConstantVal_3272_; lean_object* v_name_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; 
v_toConstantVal_3272_ = lean_ctor_get(v_defn_3233_, 0);
v_name_3273_ = lean_ctor_get(v_toConstantVal_3272_, 0);
v___x_3274_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1);
lean_inc(v_name_3273_);
v___x_3275_ = l_Lean_MessageData_ofName(v_name_3273_);
v___x_3276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3274_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_3278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3276_);
lean_ctor_set(v___x_3278_, 1, v___x_3277_);
v___x_3279_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3231_, v___x_3278_, v___y_3234_, v___y_3235_);
if (lean_obj_tag(v___x_3279_) == 0)
{
lean_dec_ref_known(v___x_3279_, 1);
v___y_3250_ = v___y_3234_;
v___y_3251_ = v___y_3235_;
goto v___jp_3249_;
}
else
{
lean_dec_ref(v_defn_3233_);
lean_dec_ref(v___f_3229_);
return v___x_3279_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v___f_3284_, lean_object* v___x_3285_, lean_object* v_cls_3286_, lean_object* v_forceExpose_3287_, lean_object* v_defn_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
uint8_t v_forceExpose_boxed_3292_; lean_object* v_res_3293_; 
v_forceExpose_boxed_3292_ = lean_unbox(v_forceExpose_3287_);
v_res_3293_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v___f_3284_, v___x_3285_, v_cls_3286_, v_forceExpose_boxed_3292_, v_defn_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3294_, lean_object* v___f_3295_, lean_object* v_____r_3296_, lean_object* v_exportedInfo_x3f_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_toConstantVal_3301_; lean_object* v_name_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v_toConstantVal_3301_ = lean_ctor_get(v_val_3294_, 0);
v_name_3302_ = lean_ctor_get(v_toConstantVal_3301_, 0);
lean_inc(v_name_3302_);
v___x_3303_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3303_, 0, v_val_3294_);
v___x_3304_ = 1;
v___x_3305_ = lean_box(v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v___x_3303_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
v___x_3307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3307_, 0, v_name_3302_);
lean_ctor_set(v___x_3307_, 1, v___x_3306_);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
v___x_3308_ = lean_apply_5(v___f_3295_, v___x_3307_, v_exportedInfo_x3f_3297_, v___y_3298_, v___y_3299_, lean_box(0));
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3309_, lean_object* v___f_3310_, lean_object* v_____r_3311_, lean_object* v_exportedInfo_x3f_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_){
_start:
{
lean_object* v_res_3316_; 
v_res_3316_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3309_, v___f_3310_, v_____r_3311_, v_exportedInfo_x3f_3312_, v___y_3313_, v___y_3314_);
lean_dec(v___y_3314_);
lean_dec_ref(v___y_3313_);
return v_res_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3317_, uint8_t v___x_3318_, lean_object* v___f_3319_, lean_object* v_____r_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_){
_start:
{
lean_object* v_toConstantVal_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_toConstantVal_3324_ = lean_ctor_get(v_val_3317_, 0);
lean_inc_ref(v_toConstantVal_3324_);
v___x_3325_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3325_, 0, v_toConstantVal_3324_);
lean_ctor_set_uint8(v___x_3325_, sizeof(void*)*1, v___x_3318_);
v___x_3326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
v___x_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3326_);
v___x_3328_ = lean_box(0);
lean_inc(v___y_3322_);
lean_inc_ref(v___y_3321_);
v___x_3329_ = lean_apply_5(v___f_3319_, v___x_3328_, v___x_3327_, v___y_3321_, v___y_3322_, lean_box(0));
return v___x_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3330_, lean_object* v___x_3331_, lean_object* v___f_3332_, lean_object* v_____r_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
uint8_t v___x_61062__boxed_3337_; lean_object* v_res_3338_; 
v___x_61062__boxed_3337_ = lean_unbox(v___x_3331_);
v_res_3338_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3330_, v___x_61062__boxed_3337_, v___f_3332_, v_____r_3333_, v___y_3334_, v___y_3335_);
lean_dec(v___y_3335_);
lean_dec_ref(v___y_3334_);
lean_dec_ref(v_val_3330_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3339_, lean_object* v___f_3340_, lean_object* v_____r_3341_, lean_object* v_exportedInfo_x3f_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_toConstantVal_3346_; lean_object* v_name_3347_; lean_object* v___x_3348_; uint8_t v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_toConstantVal_3346_ = lean_ctor_get(v_val_3339_, 0);
v_name_3347_ = lean_ctor_get(v_toConstantVal_3346_, 0);
lean_inc(v_name_3347_);
v___x_3348_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3348_, 0, v_val_3339_);
v___x_3349_ = 3;
v___x_3350_ = lean_box(v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3348_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
v___x_3352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3352_, 0, v_name_3347_);
lean_ctor_set(v___x_3352_, 1, v___x_3351_);
lean_inc(v___y_3344_);
lean_inc_ref(v___y_3343_);
v___x_3353_ = lean_apply_5(v___f_3340_, v___x_3352_, v_exportedInfo_x3f_3342_, v___y_3343_, v___y_3344_, lean_box(0));
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3354_, lean_object* v___f_3355_, lean_object* v_____r_3356_, lean_object* v_exportedInfo_x3f_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
lean_object* v_res_3361_; 
v_res_3361_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3354_, v___f_3355_, v_____r_3356_, v_exportedInfo_x3f_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
return v_res_3361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3362_, lean_object* v___f_3363_, lean_object* v_____r_3364_, lean_object* v___y_3365_, lean_object* v___y_3366_){
_start:
{
lean_object* v_toConstantVal_3368_; uint8_t v_isUnsafe_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_toConstantVal_3368_ = lean_ctor_get(v_val_3362_, 0);
v_isUnsafe_3369_ = lean_ctor_get_uint8(v_val_3362_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3368_);
v___x_3370_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3370_, 0, v_toConstantVal_3368_);
lean_ctor_set_uint8(v___x_3370_, sizeof(void*)*1, v_isUnsafe_3369_);
v___x_3371_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
v___x_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3371_);
v___x_3373_ = lean_box(0);
lean_inc(v___y_3366_);
lean_inc_ref(v___y_3365_);
v___x_3374_ = lean_apply_5(v___f_3363_, v___x_3373_, v___x_3372_, v___y_3365_, v___y_3366_, lean_box(0));
return v___x_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3375_, lean_object* v___f_3376_, lean_object* v_____r_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_res_3381_; 
v_res_3381_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3375_, v___f_3376_, v_____r_3377_, v___y_3378_, v___y_3379_);
lean_dec(v___y_3379_);
lean_dec_ref(v___y_3378_);
lean_dec_ref(v_val_3375_);
return v_res_3381_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3382_, uint8_t v___x_3383_, uint8_t v___x_3384_, lean_object* v_cls_3385_, lean_object* v___x_3386_, lean_object* v___x_3387_, lean_object* v_____x_3388_, lean_object* v_exportedInfo_x3f_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_){
_start:
{
lean_object* v___y_3394_; lean_object* v___y_3395_; lean_object* v_a_3396_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v_a_3409_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v___y_3429_; lean_object* v_snd_3492_; lean_object* v_fst_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3621_; 
v_snd_3492_ = lean_ctor_get(v_____x_3388_, 1);
v_fst_3493_ = lean_ctor_get(v_____x_3388_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_____x_3388_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3495_ = v_____x_3388_;
v_isShared_3496_ = v_isSharedCheck_3621_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_snd_3492_);
lean_inc(v_fst_3493_);
lean_dec(v_____x_3388_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3621_;
goto v_resetjp_3494_;
}
v___jp_3393_:
{
lean_object* v___x_3397_; lean_object* v___x_3399_; uint8_t v_isShared_3400_; uint8_t v_isSharedCheck_3404_; 
v___x_3397_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3394_, v___y_3395_);
v_isSharedCheck_3404_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3404_ == 0)
{
lean_object* v_unused_3405_; 
v_unused_3405_ = lean_ctor_get(v___x_3397_, 0);
lean_dec(v_unused_3405_);
v___x_3399_ = v___x_3397_;
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
else
{
lean_dec(v___x_3397_);
v___x_3399_ = lean_box(0);
v_isShared_3400_ = v_isSharedCheck_3404_;
goto v_resetjp_3398_;
}
v_resetjp_3398_:
{
lean_object* v___x_3402_; 
if (v_isShared_3400_ == 0)
{
lean_ctor_set_tag(v___x_3399_, 1);
lean_ctor_set(v___x_3399_, 0, v_a_3396_);
v___x_3402_ = v___x_3399_;
goto v_reusejp_3401_;
}
else
{
lean_object* v_reuseFailAlloc_3403_; 
v_reuseFailAlloc_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3403_, 0, v_a_3396_);
v___x_3402_ = v_reuseFailAlloc_3403_;
goto v_reusejp_3401_;
}
v_reusejp_3401_:
{
return v___x_3402_;
}
}
}
v___jp_3406_:
{
lean_object* v___x_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
v___x_3410_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3407_, v___y_3408_);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3410_);
if (v_isSharedCheck_3417_ == 0)
{
lean_object* v_unused_3418_; 
v_unused_3418_ = lean_ctor_get(v___x_3410_, 0);
lean_dec(v_unused_3418_);
v___x_3412_ = v___x_3410_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_dec(v___x_3410_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
lean_ctor_set(v___x_3412_, 0, v_a_3409_);
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3409_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
v___jp_3419_:
{
lean_object* v___x_3430_; 
lean_inc_ref(v___y_3424_);
v___x_3430_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3425_, v___y_3424_, v___y_3427_, v___y_3429_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v___x_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref_known(v___x_3430_, 1);
lean_inc_ref(v___y_3421_);
v___x_3431_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3421_, v___y_3428_);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3431_, 0);
lean_dec(v_unused_3478_);
v___x_3433_ = v___x_3431_;
v_isShared_3434_ = v_isSharedCheck_3477_;
goto v_resetjp_3432_;
}
else
{
lean_dec(v___x_3431_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3477_;
goto v_resetjp_3432_;
}
v_resetjp_3432_:
{
lean_object* v_options_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_options_3435_ = lean_ctor_get(v___y_3423_, 2);
v___x_3436_ = l_Lean_Elab_async;
v___x_3437_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v_r_3439_; 
lean_del_object(v___x_3433_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3420_);
v___x_3438_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3424_, v___y_3428_);
lean_dec_ref(v___x_3438_);
v_r_3439_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3382_, v___y_3423_, v___y_3428_);
if (lean_obj_tag(v_r_3439_) == 0)
{
lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3449_; 
v_a_3440_ = lean_ctor_get(v_r_3439_, 0);
v_isSharedCheck_3449_ = !lean_is_exclusive(v_r_3439_);
if (v_isSharedCheck_3449_ == 0)
{
v___x_3442_ = v_r_3439_;
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_dec(v_r_3439_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3449_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3445_; 
lean_inc(v_a_3440_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set_tag(v___x_3442_, 1);
v___x_3445_ = v___x_3442_;
goto v_reusejp_3444_;
}
else
{
lean_object* v_reuseFailAlloc_3448_; 
v_reuseFailAlloc_3448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3448_, 0, v_a_3440_);
v___x_3445_ = v_reuseFailAlloc_3448_;
goto v_reusejp_3444_;
}
v_reusejp_3444_:
{
lean_object* v___x_3446_; 
v___x_3446_ = lean_apply_2(v___y_3426_, v___x_3445_, lean_box(0));
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_dec_ref_known(v___x_3446_, 1);
v___y_3407_ = v___y_3421_;
v___y_3408_ = v___y_3428_;
v_a_3409_ = v_a_3440_;
goto v___jp_3406_;
}
else
{
lean_object* v_a_3447_; 
lean_dec(v_a_3440_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___y_3394_ = v___y_3421_;
v___y_3395_ = v___y_3428_;
v_a_3396_ = v_a_3447_;
goto v___jp_3393_;
}
}
}
}
else
{
lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v_r_3439_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v_r_3439_, 1);
v___x_3451_ = lean_box(0);
v___x_3452_ = lean_apply_2(v___y_3426_, v___x_3451_, lean_box(0));
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_dec_ref_known(v___x_3452_, 1);
v___y_3394_ = v___y_3421_;
v___y_3395_ = v___y_3428_;
v_a_3396_ = v_a_3450_;
goto v___jp_3393_;
}
else
{
lean_object* v_a_3453_; 
lean_dec(v_a_3450_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___y_3394_ = v___y_3421_;
v___y_3395_ = v___y_3428_;
v_a_3396_ = v_a_3453_;
goto v___jp_3393_;
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_dec_ref(v___y_3426_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v___y_3421_);
lean_dec(v_decl_3382_);
v___x_3454_ = l_IO_CancelToken_new();
if (v_isShared_3434_ == 0)
{
lean_ctor_set_tag(v___x_3433_, 1);
lean_ctor_set(v___x_3433_, 0, v___x_3454_);
v___x_3456_ = v___x_3433_;
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
v___x_3458_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1));
v___x_3459_ = l_Lean_Name_toString(v___x_3458_, v___x_3383_);
lean_inc_ref(v___x_3456_);
v___x_3460_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3420_, v___x_3456_, v___x_3459_, v___y_3423_, v___y_3428_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_checked_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v_checked_3462_ = lean_ctor_get(v___y_3422_, 2);
lean_inc_ref(v_checked_3462_);
lean_dec_ref(v___y_3422_);
v___x_3463_ = lean_io_map_task(v_a_3461_, v_checked_3462_, v___x_3457_, v___x_3384_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_box(2);
v___x_3466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_ctor_set(v___x_3466_, 2, v___x_3456_);
lean_ctor_set(v___x_3466_, 3, v___x_3463_);
v___x_3467_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3466_, v___y_3428_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___y_3422_);
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
lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v___y_3426_);
lean_dec_ref(v___y_3424_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v_decl_3382_);
v_a_3479_ = lean_ctor_get(v___x_3430_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3481_ = v___x_3430_;
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3430_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_ref_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v_ref_3483_ = lean_ctor_get(v___y_3423_, 5);
v___x_3484_ = lean_io_error_to_string(v_a_3479_);
v___x_3485_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
v___x_3486_ = l_Lean_MessageData_ofFormat(v___x_3485_);
lean_inc(v_ref_3483_);
v___x_3487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3487_, 0, v_ref_3483_);
lean_ctor_set(v___x_3487_, 1, v___x_3486_);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3487_);
v___x_3489_ = v___x_3481_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
v_resetjp_3494_:
{
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3620_; 
v_fst_3497_ = lean_ctor_get(v_snd_3492_, 0);
v_snd_3498_ = lean_ctor_get(v_snd_3492_, 1);
v_isSharedCheck_3620_ = !lean_is_exclusive(v_snd_3492_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3500_ = v_snd_3492_;
v_isShared_3501_ = v_isSharedCheck_3620_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_snd_3492_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3620_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v_exportedInfo_x3f_3534_; lean_object* v___y_3535_; lean_object* v___y_3536_; lean_object* v___y_3546_; lean_object* v___y_3547_; lean_object* v___y_3550_; lean_object* v___y_3551_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___y_3556_; lean_object* v___y_3586_; lean_object* v___y_3587_; lean_object* v___x_3610_; lean_object* v_env_3611_; uint8_t v___x_3612_; 
v___x_3610_ = lean_st_ref_get(v___y_3391_);
v_env_3611_ = lean_ctor_get(v___x_3610_, 0);
lean_inc_ref(v_env_3611_);
lean_dec(v___x_3610_);
v___x_3612_ = l_Lean_Environment_containsOnBranch(v_env_3611_, v_fst_3493_);
lean_dec_ref(v_env_3611_);
if (v___x_3612_ == 0)
{
lean_del_object(v___x_3495_);
v___y_3586_ = v___y_3390_;
v___y_3587_ = v___y_3391_;
goto v___jp_3585_;
}
else
{
lean_object* v___x_3613_; lean_object* v_env_3614_; lean_object* v___x_3615_; lean_object* v___x_3617_; 
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_exportedInfo_x3f_3389_);
lean_dec(v___x_3387_);
lean_dec_ref(v___x_3386_);
lean_dec(v_cls_3385_);
lean_dec(v_decl_3382_);
v___x_3613_ = lean_st_ref_get(v___y_3391_);
v_env_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc_ref(v_env_3614_);
lean_dec(v___x_3613_);
v___x_3615_ = lean_elab_environment_to_kernel_env(v_env_3614_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 1);
lean_ctor_set(v___x_3495_, 1, v_fst_3493_);
lean_ctor_set(v___x_3495_, 0, v___x_3615_);
v___x_3617_ = v___x_3495_;
goto v_reusejp_3616_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3615_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_fst_3493_);
v___x_3617_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3616_;
}
v_reusejp_3616_:
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3617_, v___y_3390_, v___y_3391_);
return v___x_3618_;
}
}
v___jp_3502_:
{
uint8_t v___x_3510_; lean_object* v___x_3511_; 
v___x_3510_ = lean_unbox(v_snd_3498_);
lean_dec(v_snd_3498_);
lean_inc_ref(v___y_3505_);
v___x_3511_ = l_Lean_Environment_addConstAsync(v___y_3505_, v_fst_3493_, v___x_3510_, v___y_3509_, v___x_3384_, v___x_3383_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v_mainEnv_3513_; lean_object* v_asyncEnv_3514_; lean_object* v___f_3515_; lean_object* v___f_3516_; lean_object* v___x_3517_; 
lean_del_object(v___x_3500_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc_n(v_a_3512_, 3);
lean_dec_ref_known(v___x_3511_, 1);
v_mainEnv_3513_ = lean_ctor_get(v_a_3512_, 0);
lean_inc_ref(v_mainEnv_3513_);
v_asyncEnv_3514_ = lean_ctor_get(v_a_3512_, 1);
lean_inc_ref_n(v_asyncEnv_3514_, 2);
lean_inc_ref(v___y_3503_);
lean_inc(v___y_3504_);
v___f_3515_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3515_, 0, v___y_3504_);
lean_closure_set(v___f_3515_, 1, v_a_3512_);
lean_closure_set(v___f_3515_, 2, v___y_3503_);
lean_inc(v_decl_3382_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed), 7, 3);
lean_closure_set(v___f_3516_, 0, v_asyncEnv_3514_);
lean_closure_set(v___f_3516_, 1, v_a_3512_);
lean_closure_set(v___f_3516_, 2, v_decl_3382_);
v___x_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3517_, 0, v_fst_3497_);
if (lean_obj_tag(v___y_3506_) == 0)
{
lean_inc_ref(v___x_3517_);
v___y_3420_ = v___f_3516_;
v___y_3421_ = v_mainEnv_3513_;
v___y_3422_ = v___y_3505_;
v___y_3423_ = v___y_3507_;
v___y_3424_ = v_asyncEnv_3514_;
v___y_3425_ = v_a_3512_;
v___y_3426_ = v___f_3515_;
v___y_3427_ = v___x_3517_;
v___y_3428_ = v___y_3508_;
v___y_3429_ = v___x_3517_;
goto v___jp_3419_;
}
else
{
v___y_3420_ = v___f_3516_;
v___y_3421_ = v_mainEnv_3513_;
v___y_3422_ = v___y_3505_;
v___y_3423_ = v___y_3507_;
v___y_3424_ = v_asyncEnv_3514_;
v___y_3425_ = v_a_3512_;
v___y_3426_ = v___f_3515_;
v___y_3427_ = v___x_3517_;
v___y_3428_ = v___y_3508_;
v___y_3429_ = v___y_3506_;
goto v___jp_3419_;
}
}
else
{
lean_object* v_a_3518_; lean_object* v___x_3520_; uint8_t v_isShared_3521_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v___y_3506_);
lean_dec_ref(v___y_3505_);
lean_dec(v_fst_3497_);
lean_dec(v_decl_3382_);
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
v_ref_3522_ = lean_ctor_get(v___y_3507_, 5);
v___x_3523_ = lean_io_error_to_string(v_a_3518_);
v___x_3524_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
v___x_3525_ = l_Lean_MessageData_ofFormat(v___x_3524_);
lean_inc(v_ref_3522_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3525_);
lean_ctor_set(v___x_3500_, 0, v_ref_3522_);
v___x_3527_ = v___x_3500_;
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
v___y_3503_ = v___y_3535_;
v___y_3504_ = v___y_3536_;
v___y_3505_ = v_env_3538_;
v___y_3506_ = v_exportedInfo_x3f_3534_;
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___x_3539_;
goto v___jp_3502_;
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
v___y_3503_ = v___y_3535_;
v___y_3504_ = v___y_3536_;
v___y_3505_ = v_env_3540_;
v___y_3506_ = v_exportedInfo_x3f_3534_;
v___y_3507_ = v___y_3535_;
v___y_3508_ = v___y_3536_;
v___y_3509_ = v___x_3544_;
goto v___jp_3502_;
}
}
v___jp_3545_:
{
lean_object* v___x_3548_; 
lean_inc(v_fst_3497_);
v___x_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_fst_3497_);
v_exportedInfo_x3f_3534_ = v___x_3548_;
v___y_3535_ = v___y_3546_;
v___y_3536_ = v___y_3547_;
goto v___jp_3533_;
}
v___jp_3549_:
{
lean_object* v___x_3552_; 
lean_inc(v_fst_3497_);
v___x_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3552_, 0, v_fst_3497_);
v_exportedInfo_x3f_3534_ = v___x_3552_;
v___y_3535_ = v___y_3550_;
v___y_3536_ = v___y_3551_;
goto v___jp_3533_;
}
v___jp_3553_:
{
if (v___y_3556_ == 0)
{
lean_object* v_options_3557_; uint8_t v_hasTrace_3558_; 
lean_dec(v_exportedInfo_x3f_3389_);
lean_dec_ref(v___x_3386_);
v_options_3557_ = lean_ctor_get(v___y_3554_, 2);
v_hasTrace_3558_ = lean_ctor_get_uint8(v_options_3557_, sizeof(void*)*1);
if (v_hasTrace_3558_ == 0)
{
lean_dec(v_cls_3385_);
v___y_3546_ = v___y_3554_;
v___y_3547_ = v___y_3555_;
goto v___jp_3545_;
}
else
{
lean_object* v_inheritedTraceOptions_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; uint8_t v___x_3562_; 
v_inheritedTraceOptions_3559_ = lean_ctor_get(v___y_3554_, 13);
v___x_3560_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_3385_);
v___x_3561_ = l_Lean_Name_append(v___x_3560_, v_cls_3385_);
v___x_3562_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3559_, v_options_3557_, v___x_3561_);
lean_dec(v___x_3561_);
if (v___x_3562_ == 0)
{
lean_dec(v_cls_3385_);
v___y_3546_ = v___y_3554_;
v___y_3547_ = v___y_3555_;
goto v___jp_3545_;
}
else
{
lean_object* v___x_3563_; lean_object* v___x_3564_; 
v___x_3563_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3);
v___x_3564_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3385_, v___x_3563_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3564_) == 0)
{
lean_dec_ref_known(v___x_3564_, 1);
v___y_3546_ = v___y_3554_;
v___y_3547_ = v___y_3555_;
goto v___jp_3545_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v_decl_3382_);
return v___x_3564_;
}
}
}
}
else
{
lean_object* v___x_3565_; lean_object* v_env_3566_; lean_object* v_nextMacroScope_3567_; lean_object* v_ngen_3568_; lean_object* v_auxDeclNGen_3569_; lean_object* v_traceState_3570_; lean_object* v_messages_3571_; lean_object* v_infoState_3572_; lean_object* v_snapshotTasks_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_cls_3385_);
v___x_3565_ = lean_st_ref_take(v___y_3555_);
v_env_3566_ = lean_ctor_get(v___x_3565_, 0);
v_nextMacroScope_3567_ = lean_ctor_get(v___x_3565_, 1);
v_ngen_3568_ = lean_ctor_get(v___x_3565_, 2);
v_auxDeclNGen_3569_ = lean_ctor_get(v___x_3565_, 3);
v_traceState_3570_ = lean_ctor_get(v___x_3565_, 4);
v_messages_3571_ = lean_ctor_get(v___x_3565_, 6);
v_infoState_3572_ = lean_ctor_get(v___x_3565_, 7);
v_snapshotTasks_3573_ = lean_ctor_get(v___x_3565_, 8);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; 
v_unused_3584_ = lean_ctor_get(v___x_3565_, 5);
lean_dec(v_unused_3584_);
v___x_3575_ = v___x_3565_;
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_snapshotTasks_3573_);
lean_inc(v_infoState_3572_);
lean_inc(v_messages_3571_);
lean_inc(v_traceState_3570_);
lean_inc(v_auxDeclNGen_3569_);
lean_inc(v_ngen_3568_);
lean_inc(v_nextMacroScope_3567_);
lean_inc(v_env_3566_);
lean_dec(v___x_3565_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3583_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3580_; 
v___x_3577_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3498_);
lean_inc(v_fst_3493_);
v___x_3578_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3577_, v_env_3566_, v_fst_3493_, v_snd_3498_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 5, v___x_3386_);
lean_ctor_set(v___x_3575_, 0, v___x_3578_);
v___x_3580_ = v___x_3575_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_nextMacroScope_3567_);
lean_ctor_set(v_reuseFailAlloc_3582_, 2, v_ngen_3568_);
lean_ctor_set(v_reuseFailAlloc_3582_, 3, v_auxDeclNGen_3569_);
lean_ctor_set(v_reuseFailAlloc_3582_, 4, v_traceState_3570_);
lean_ctor_set(v_reuseFailAlloc_3582_, 5, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3582_, 6, v_messages_3571_);
lean_ctor_set(v_reuseFailAlloc_3582_, 7, v_infoState_3572_);
lean_ctor_set(v_reuseFailAlloc_3582_, 8, v_snapshotTasks_3573_);
v___x_3580_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
lean_object* v___x_3581_; 
v___x_3581_ = lean_st_ref_set(v___y_3555_, v___x_3580_);
v_exportedInfo_x3f_3534_ = v_exportedInfo_x3f_3389_;
v___y_3535_ = v___y_3554_;
v___y_3536_ = v___y_3555_;
goto v___jp_3533_;
}
}
}
}
v___jp_3585_:
{
lean_object* v___x_3588_; uint8_t v___x_3589_; 
lean_inc(v_decl_3382_);
v___x_3588_ = l_Lean_Declaration_getTopLevelNames(v_decl_3382_);
v___x_3589_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3588_);
lean_dec(v___x_3588_);
if (v___x_3589_ == 0)
{
lean_dec(v___x_3387_);
if (lean_obj_tag(v_exportedInfo_x3f_3389_) == 0)
{
v___y_3554_ = v___y_3586_;
v___y_3555_ = v___y_3587_;
v___y_3556_ = v___x_3384_;
goto v___jp_3553_;
}
else
{
v___y_3554_ = v___y_3586_;
v___y_3555_ = v___y_3587_;
v___y_3556_ = v___x_3383_;
goto v___jp_3553_;
}
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v_a_3592_; uint8_t v___x_3593_; 
lean_dec(v_exportedInfo_x3f_3389_);
lean_dec_ref(v___x_3386_);
v___x_3590_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3591_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3590_, v___y_3586_);
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc(v_a_3592_);
lean_dec_ref(v___x_3591_);
v___x_3593_ = lean_unbox(v_a_3592_);
lean_dec(v_a_3592_);
if (v___x_3593_ == 0)
{
lean_object* v_options_3594_; uint8_t v_hasTrace_3595_; 
v_options_3594_ = lean_ctor_get(v___y_3586_, 2);
v_hasTrace_3595_ = lean_ctor_get_uint8(v_options_3594_, sizeof(void*)*1);
if (v_hasTrace_3595_ == 0)
{
lean_dec(v_cls_3385_);
v_exportedInfo_x3f_3534_ = v___x_3387_;
v___y_3535_ = v___y_3586_;
v___y_3536_ = v___y_3587_;
goto v___jp_3533_;
}
else
{
lean_object* v_inheritedTraceOptions_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_inheritedTraceOptions_3596_ = lean_ctor_get(v___y_3586_, 13);
v___x_3597_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_3385_);
v___x_3598_ = l_Lean_Name_append(v___x_3597_, v_cls_3385_);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3596_, v_options_3594_, v___x_3598_);
lean_dec(v___x_3598_);
if (v___x_3599_ == 0)
{
lean_dec(v_cls_3385_);
v_exportedInfo_x3f_3534_ = v___x_3387_;
v___y_3535_ = v___y_3586_;
v___y_3536_ = v___y_3587_;
goto v___jp_3533_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5);
v___x_3601_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3385_, v___x_3600_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_dec_ref_known(v___x_3601_, 1);
v_exportedInfo_x3f_3534_ = v___x_3387_;
v___y_3535_ = v___y_3586_;
v___y_3536_ = v___y_3587_;
goto v___jp_3533_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v___x_3387_);
lean_dec(v_decl_3382_);
return v___x_3601_;
}
}
}
}
else
{
lean_object* v_options_3602_; uint8_t v_hasTrace_3603_; 
lean_dec(v___x_3387_);
v_options_3602_ = lean_ctor_get(v___y_3586_, 2);
v_hasTrace_3603_ = lean_ctor_get_uint8(v_options_3602_, sizeof(void*)*1);
if (v_hasTrace_3603_ == 0)
{
lean_dec(v_cls_3385_);
v___y_3550_ = v___y_3586_;
v___y_3551_ = v___y_3587_;
goto v___jp_3549_;
}
else
{
lean_object* v_inheritedTraceOptions_3604_; lean_object* v___x_3605_; lean_object* v___x_3606_; uint8_t v___x_3607_; 
v_inheritedTraceOptions_3604_ = lean_ctor_get(v___y_3586_, 13);
v___x_3605_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
lean_inc(v_cls_3385_);
v___x_3606_ = l_Lean_Name_append(v___x_3605_, v_cls_3385_);
v___x_3607_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3604_, v_options_3602_, v___x_3606_);
lean_dec(v___x_3606_);
if (v___x_3607_ == 0)
{
lean_dec(v_cls_3385_);
v___y_3550_ = v___y_3586_;
v___y_3551_ = v___y_3587_;
goto v___jp_3549_;
}
else
{
lean_object* v___x_3608_; lean_object* v___x_3609_; 
v___x_3608_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7);
v___x_3609_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3385_, v___x_3608_, v___y_3586_, v___y_3587_);
if (lean_obj_tag(v___x_3609_) == 0)
{
lean_dec_ref_known(v___x_3609_, 1);
v___y_3550_ = v___y_3586_;
v___y_3551_ = v___y_3587_;
goto v___jp_3549_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v_decl_3382_);
return v___x_3609_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3622_, lean_object* v___x_3623_, lean_object* v___x_3624_, lean_object* v_cls_3625_, lean_object* v___x_3626_, lean_object* v___x_3627_, lean_object* v_____x_3628_, lean_object* v_exportedInfo_x3f_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
uint8_t v___x_61193__boxed_3633_; uint8_t v___x_61194__boxed_3634_; lean_object* v_res_3635_; 
v___x_61193__boxed_3633_ = lean_unbox(v___x_3623_);
v___x_61194__boxed_3634_ = lean_unbox(v___x_3624_);
v_res_3635_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3622_, v___x_61193__boxed_3633_, v___x_61194__boxed_3634_, v_cls_3625_, v___x_3626_, v___x_3627_, v_____x_3628_, v_exportedInfo_x3f_3629_, v___y_3630_, v___y_3631_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
return v_res_3635_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3636_, lean_object* v_x_3637_){
_start:
{
if (lean_obj_tag(v_x_3637_) == 0)
{
return v_x_3636_;
}
else
{
lean_object* v_head_3638_; lean_object* v_tail_3639_; lean_object* v___x_3640_; 
v_head_3638_ = lean_ctor_get(v_x_3637_, 0);
lean_inc(v_head_3638_);
v_tail_3639_ = lean_ctor_get(v_x_3637_, 1);
lean_inc(v_tail_3639_);
lean_dec_ref_known(v_x_3637_, 2);
v___x_3640_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3636_, v_head_3638_);
v_x_3636_ = v___x_3640_;
v_x_3637_ = v_tail_3639_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v_cls_3642_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3643_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1));
v___x_3644_ = l_Lean_Name_append(v___x_3643_, v_cls_3642_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1(void){
_start:
{
uint8_t v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = 1;
v___x_3646_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1));
v___x_3647_ = l_Lean_Name_toString(v___x_3646_, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3654_, uint8_t v_forceExpose_3655_, lean_object* v_a_3656_, lean_object* v_a_3657_){
_start:
{
lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v_a_3662_; lean_object* v___y_3673_; lean_object* v___y_3674_; lean_object* v_a_3675_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v_a_3688_; lean_object* v___y_3699_; lean_object* v___y_3700_; lean_object* v_a_3701_; lean_object* v_options_3711_; lean_object* v_inheritedTraceOptions_3712_; uint8_t v_hasTrace_3713_; lean_object* v_cls_3714_; lean_object* v___y_3716_; lean_object* v_options_3717_; uint8_t v_hasTrace_3718_; lean_object* v_inheritedTraceOptions_3719_; lean_object* v___y_3720_; uint8_t v___x_3728_; lean_object* v___y_3730_; lean_object* v___y_3731_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v___y_3734_; lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3804_; lean_object* v___y_3805_; lean_object* v___y_3806_; lean_object* v___y_3807_; lean_object* v___y_3808_; lean_object* v___y_3809_; lean_object* v___y_3810_; uint8_t v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3836_; uint8_t v___y_3837_; lean_object* v___y_3838_; lean_object* v_exportedInfo_x3f_3839_; lean_object* v___y_3840_; lean_object* v___y_3841_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3858_; uint8_t v___y_3859_; lean_object* v___y_3860_; lean_object* v___y_3861_; lean_object* v___y_3862_; 
v_options_3711_ = lean_ctor_get(v_a_3656_, 2);
v_inheritedTraceOptions_3712_ = lean_ctor_get(v_a_3656_, 13);
v_hasTrace_3713_ = lean_ctor_get_uint8(v_options_3711_, sizeof(void*)*1);
v_cls_3714_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3728_ = lean_bool_not(v_hasTrace_3713_);
if (v___x_3728_ == 0)
{
lean_object* v___f_3864_; uint8_t v___x_3865_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; uint8_t v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; lean_object* v___y_3877_; lean_object* v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; lean_object* v___y_3945_; uint8_t v___y_3946_; lean_object* v___y_3947_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3972_; uint8_t v___y_3973_; uint8_t v___y_3974_; lean_object* v___y_3975_; lean_object* v_exportedInfo_x3f_3976_; lean_object* v___y_3977_; lean_object* v___y_3978_; lean_object* v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_4018_; uint8_t v___y_4019_; uint8_t v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4022_; lean_object* v___y_4023_; lean_object* v___y_4026_; uint8_t v___y_4027_; uint8_t v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; lean_object* v___y_4034_; uint8_t v___y_4035_; uint8_t v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4042_; uint8_t v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v_fst_4074_; lean_object* v_fst_4075_; uint8_t v_snd_4076_; lean_object* v_exportedInfo_x3f_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4089_; lean_object* v___y_4090_; lean_object* v_toConstantVal_4091_; lean_object* v___y_4092_; lean_object* v___y_4093_; lean_object* v_exportedInfo_x3f_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4101_; lean_object* v___y_4102_; lean_object* v_toConstantVal_4103_; uint8_t v_isUnsafe_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v___y_4118_; uint8_t v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v_exportedInfo_x3f_4126_; lean_object* v___y_4127_; lean_object* v___y_4128_; lean_object* v___y_4131_; uint8_t v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; uint8_t v___y_4136_; lean_object* v___y_4151_; lean_object* v_toConstantVal_4152_; uint8_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v_exportedInfo_x3f_4156_; lean_object* v___y_4157_; lean_object* v___y_4158_; lean_object* v___y_4163_; lean_object* v_toConstantVal_4164_; uint8_t v___y_4165_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4174_; uint8_t v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4177_; lean_object* v___y_4178_; lean_object* v___y_4179_; lean_object* v___y_4182_; uint8_t v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; uint8_t v___y_4186_; lean_object* v___y_4199_; lean_object* v_toConstantVal_4200_; uint8_t v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v_exportedInfo_x3f_4204_; lean_object* v___y_4205_; lean_object* v___y_4206_; lean_object* v___y_4211_; uint8_t v___y_4212_; lean_object* v___y_4213_; lean_object* v___y_4214_; lean_object* v_exportedInfo_x3f_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4220_; lean_object* v_toConstantVal_4221_; uint8_t v_safety_4222_; uint8_t v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4234_; uint8_t v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4243_; uint8_t v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; uint8_t v___y_4250_; uint8_t v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v_defn_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___x_4281_; lean_object* v___y_4283_; uint8_t v___y_4284_; lean_object* v___y_4285_; lean_object* v_a_4286_; lean_object* v___y_4296_; uint8_t v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4317_; lean_object* v___y_4318_; uint8_t v___y_4319_; lean_object* v___y_4320_; lean_object* v___y_4321_; lean_object* v___y_4325_; uint8_t v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4328_; lean_object* v___y_4332_; lean_object* v___y_4333_; uint8_t v___y_4334_; lean_object* v___y_4335_; lean_object* v___y_4336_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; uint8_t v___y_4340_; lean_object* v___y_4356_; lean_object* v___y_4357_; uint8_t v___y_4358_; lean_object* v___y_4359_; lean_object* v___y_4363_; lean_object* v___y_4364_; uint8_t v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; uint8_t v___y_4370_; lean_object* v___y_4386_; uint8_t v___y_4387_; lean_object* v___y_4388_; lean_object* v_a_4389_; lean_object* v___y_4402_; uint8_t v___y_4403_; lean_object* v___y_4404_; lean_object* v___y_4405_; lean_object* v___y_4423_; uint8_t v___y_4424_; lean_object* v___y_4425_; lean_object* v___y_4426_; lean_object* v___y_4430_; lean_object* v___y_4431_; lean_object* v___y_4432_; uint8_t v___y_4433_; lean_object* v___y_4434_; lean_object* v___y_4435_; lean_object* v___y_4436_; uint8_t v___y_4437_; lean_object* v___y_4453_; uint8_t v___y_4454_; lean_object* v___y_4455_; lean_object* v___y_4456_; lean_object* v___y_4460_; lean_object* v___y_4461_; lean_object* v___y_4462_; uint8_t v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4471_; lean_object* v___y_4472_; uint8_t v___y_4473_; lean_object* v___y_4474_; lean_object* v___y_4475_; uint8_t v___y_4476_; uint8_t v___y_4492_; uint8_t v_a_4632_; 
lean_inc(v_decl_3654_);
v___f_3864_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 1);
lean_closure_set(v___f_3864_, 0, v_decl_3654_);
v___x_3865_ = 1;
v___x_4281_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v_hasTrace_3713_ == 0)
{
v_a_4632_ = v_hasTrace_3713_;
goto v___jp_4631_;
}
else
{
lean_object* v___x_4680_; uint8_t v___x_4681_; 
v___x_4680_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4680_);
if (v___x_4681_ == 0)
{
v_a_4632_ = v___x_4681_;
goto v___jp_4631_;
}
else
{
v___y_4492_ = v___x_4681_;
goto v___jp_4491_;
}
}
v___jp_3866_:
{
lean_object* v___x_3878_; 
lean_inc_ref(v___y_3867_);
v___x_3878_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3868_, v___y_3867_, v___y_3873_, v___y_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v___x_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3924_; 
lean_dec_ref_known(v___x_3878_, 1);
lean_inc_ref(v___y_3871_);
v___x_3879_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3871_, v___y_3876_);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3924_ == 0)
{
lean_object* v_unused_3925_; 
v_unused_3925_ = lean_ctor_get(v___x_3879_, 0);
lean_dec(v_unused_3925_);
v___x_3881_ = v___x_3879_;
v_isShared_3882_ = v_isSharedCheck_3924_;
goto v_resetjp_3880_;
}
else
{
lean_dec(v___x_3879_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3924_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v_options_3883_; lean_object* v___x_3884_; uint8_t v___x_3885_; 
v_options_3883_ = lean_ctor_get(v___y_3870_, 2);
v___x_3884_ = l_Lean_Elab_async;
v___x_3885_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3883_, v___x_3884_);
if (v___x_3885_ == 0)
{
lean_object* v___x_3886_; lean_object* v_r_3887_; 
lean_del_object(v___x_3881_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3869_);
v___x_3886_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3867_, v___y_3876_);
lean_dec_ref(v___x_3886_);
v_r_3887_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_3870_, v___y_3876_);
if (lean_obj_tag(v_r_3887_) == 0)
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3897_; 
v_a_3888_ = lean_ctor_get(v_r_3887_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v_r_3887_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3890_ = v_r_3887_;
v_isShared_3891_ = v_isSharedCheck_3897_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v_r_3887_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3897_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
lean_inc(v_a_3888_);
if (v_isShared_3891_ == 0)
{
lean_ctor_set_tag(v___x_3890_, 1);
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_apply_2(v___y_3875_, v___x_3893_, lean_box(0));
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_dec_ref_known(v___x_3894_, 1);
v___y_3660_ = v___y_3871_;
v___y_3661_ = v___y_3876_;
v_a_3662_ = v_a_3888_;
goto v___jp_3659_;
}
else
{
lean_object* v_a_3895_; 
lean_dec(v_a_3888_);
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
lean_inc(v_a_3895_);
lean_dec_ref_known(v___x_3894_, 1);
v___y_3673_ = v___y_3871_;
v___y_3674_ = v___y_3876_;
v_a_3675_ = v_a_3895_;
goto v___jp_3672_;
}
}
}
}
else
{
lean_object* v_a_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v_a_3898_ = lean_ctor_get(v_r_3887_, 0);
lean_inc(v_a_3898_);
lean_dec_ref_known(v_r_3887_, 1);
v___x_3899_ = lean_box(0);
v___x_3900_ = lean_apply_2(v___y_3875_, v___x_3899_, lean_box(0));
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_dec_ref_known(v___x_3900_, 1);
v___y_3673_ = v___y_3871_;
v___y_3674_ = v___y_3876_;
v_a_3675_ = v_a_3898_;
goto v___jp_3672_;
}
else
{
lean_object* v_a_3901_; 
lean_dec(v_a_3898_);
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
lean_inc(v_a_3901_);
lean_dec_ref_known(v___x_3900_, 1);
v___y_3673_ = v___y_3871_;
v___y_3674_ = v___y_3876_;
v_a_3675_ = v_a_3901_;
goto v___jp_3672_;
}
}
}
else
{
lean_object* v___x_3902_; lean_object* v___x_3904_; 
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v___y_3867_);
lean_dec(v_decl_3654_);
v___x_3902_ = l_IO_CancelToken_new();
if (v_isShared_3882_ == 0)
{
lean_ctor_set_tag(v___x_3881_, 1);
lean_ctor_set(v___x_3881_, 0, v___x_3902_);
v___x_3904_ = v___x_3881_;
goto v_reusejp_3903_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v___x_3902_);
v___x_3904_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3903_;
}
v_reusejp_3903_:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3905_ = lean_unsigned_to_nat(0u);
v___x_3906_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1);
lean_inc_ref(v___x_3904_);
v___x_3907_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3874_, v___x_3904_, v___x_3906_, v___y_3870_, v___y_3876_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v_checked_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v_checked_3909_ = lean_ctor_get(v___y_3869_, 2);
lean_inc_ref(v_checked_3909_);
lean_dec_ref(v___y_3869_);
v___x_3910_ = lean_io_map_task(v_a_3908_, v_checked_3909_, v___x_3905_, v___y_3872_);
v___x_3911_ = lean_box(0);
v___x_3912_ = lean_box(2);
v___x_3913_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3911_);
lean_ctor_set(v___x_3913_, 1, v___x_3912_);
lean_ctor_set(v___x_3913_, 2, v___x_3904_);
lean_ctor_set(v___x_3913_, 3, v___x_3910_);
v___x_3914_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3913_, v___y_3876_);
return v___x_3914_;
}
else
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3922_; 
lean_dec_ref(v___x_3904_);
lean_dec_ref(v___y_3869_);
v_a_3915_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3917_ = v___x_3907_;
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3907_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3922_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v___x_3920_; 
if (v_isShared_3918_ == 0)
{
v___x_3920_ = v___x_3917_;
goto v_reusejp_3919_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3915_);
v___x_3920_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3919_;
}
v_reusejp_3919_:
{
return v___x_3920_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3938_; 
lean_dec_ref(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v___y_3869_);
lean_dec_ref(v___y_3867_);
lean_dec(v_decl_3654_);
v_a_3926_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3928_ = v___x_3878_;
v_isShared_3929_ = v_isSharedCheck_3938_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3878_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3938_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v_ref_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v_ref_3930_ = lean_ctor_get(v___y_3870_, 5);
v___x_3931_ = lean_io_error_to_string(v_a_3926_);
v___x_3932_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3931_);
v___x_3933_ = l_Lean_MessageData_ofFormat(v___x_3932_);
lean_inc(v_ref_3930_);
v___x_3934_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3934_, 0, v_ref_3930_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3934_);
v___x_3936_ = v___x_3928_;
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
lean_object* v___x_3951_; 
lean_inc_ref(v___y_3940_);
v___x_3951_ = l_Lean_Environment_addConstAsync(v___y_3940_, v___y_3943_, v___y_3948_, v___y_3950_, v___y_3946_, v___x_3865_);
if (lean_obj_tag(v___x_3951_) == 0)
{
lean_object* v_a_3952_; lean_object* v_mainEnv_3953_; lean_object* v_asyncEnv_3954_; lean_object* v___f_3955_; lean_object* v___f_3956_; lean_object* v___x_3957_; 
v_a_3952_ = lean_ctor_get(v___x_3951_, 0);
lean_inc_n(v_a_3952_, 3);
lean_dec_ref_known(v___x_3951_, 1);
v_mainEnv_3953_ = lean_ctor_get(v_a_3952_, 0);
lean_inc_ref(v_mainEnv_3953_);
v_asyncEnv_3954_ = lean_ctor_get(v_a_3952_, 1);
lean_inc_ref_n(v_asyncEnv_3954_, 2);
lean_inc_ref(v___y_3941_);
lean_inc(v___y_3942_);
v___f_3955_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3955_, 0, v___y_3942_);
lean_closure_set(v___f_3955_, 1, v_a_3952_);
lean_closure_set(v___f_3955_, 2, v___y_3941_);
lean_inc(v_decl_3654_);
v___f_3956_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed), 7, 3);
lean_closure_set(v___f_3956_, 0, v_asyncEnv_3954_);
lean_closure_set(v___f_3956_, 1, v_a_3952_);
lean_closure_set(v___f_3956_, 2, v_decl_3654_);
v___x_3957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3957_, 0, v___y_3947_);
if (lean_obj_tag(v___y_3945_) == 0)
{
lean_inc_ref(v___x_3957_);
v___y_3867_ = v_asyncEnv_3954_;
v___y_3868_ = v_a_3952_;
v___y_3869_ = v___y_3940_;
v___y_3870_ = v___y_3944_;
v___y_3871_ = v_mainEnv_3953_;
v___y_3872_ = v___y_3946_;
v___y_3873_ = v___x_3957_;
v___y_3874_ = v___f_3956_;
v___y_3875_ = v___f_3955_;
v___y_3876_ = v___y_3949_;
v___y_3877_ = v___x_3957_;
goto v___jp_3866_;
}
else
{
v___y_3867_ = v_asyncEnv_3954_;
v___y_3868_ = v_a_3952_;
v___y_3869_ = v___y_3940_;
v___y_3870_ = v___y_3944_;
v___y_3871_ = v_mainEnv_3953_;
v___y_3872_ = v___y_3946_;
v___y_3873_ = v___x_3957_;
v___y_3874_ = v___f_3956_;
v___y_3875_ = v___f_3955_;
v___y_3876_ = v___y_3949_;
v___y_3877_ = v___y_3945_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3970_; 
lean_dec_ref(v___y_3947_);
lean_dec(v___y_3945_);
lean_dec_ref(v___y_3940_);
lean_dec(v_decl_3654_);
v_a_3958_ = lean_ctor_get(v___x_3951_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3951_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3960_ = v___x_3951_;
v_isShared_3961_ = v_isSharedCheck_3970_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3951_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3970_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v_ref_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3968_; 
v_ref_3962_ = lean_ctor_get(v___y_3944_, 5);
v___x_3963_ = lean_io_error_to_string(v_a_3958_);
v___x_3964_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v___x_3965_ = l_Lean_MessageData_ofFormat(v___x_3964_);
lean_inc(v_ref_3962_);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v_ref_3962_);
lean_ctor_set(v___x_3966_, 1, v___x_3965_);
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 0, v___x_3966_);
v___x_3968_ = v___x_3960_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
v___jp_3971_:
{
lean_object* v___x_3979_; 
v___x_3979_ = lean_st_ref_get(v___y_3978_);
if (lean_obj_tag(v_exportedInfo_x3f_3976_) == 0)
{
lean_object* v_env_3980_; lean_object* v___x_3981_; 
v_env_3980_ = lean_ctor_get(v___x_3979_, 0);
lean_inc_ref(v_env_3980_);
lean_dec(v___x_3979_);
v___x_3981_ = lean_box(0);
v___y_3940_ = v_env_3980_;
v___y_3941_ = v___y_3977_;
v___y_3942_ = v___y_3978_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3977_;
v___y_3945_ = v_exportedInfo_x3f_3976_;
v___y_3946_ = v___y_3973_;
v___y_3947_ = v___y_3975_;
v___y_3948_ = v___y_3974_;
v___y_3949_ = v___y_3978_;
v___y_3950_ = v___x_3981_;
goto v___jp_3939_;
}
else
{
lean_object* v_env_3982_; lean_object* v_val_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; lean_object* v___x_3986_; 
v_env_3982_ = lean_ctor_get(v___x_3979_, 0);
lean_inc_ref(v_env_3982_);
lean_dec(v___x_3979_);
v_val_3983_ = lean_ctor_get(v_exportedInfo_x3f_3976_, 0);
v___x_3984_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3983_);
v___x_3985_ = lean_box(v___x_3984_);
v___x_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3985_);
v___y_3940_ = v_env_3982_;
v___y_3941_ = v___y_3977_;
v___y_3942_ = v___y_3978_;
v___y_3943_ = v___y_3972_;
v___y_3944_ = v___y_3977_;
v___y_3945_ = v_exportedInfo_x3f_3976_;
v___y_3946_ = v___y_3973_;
v___y_3947_ = v___y_3975_;
v___y_3948_ = v___y_3974_;
v___y_3949_ = v___y_3978_;
v___y_3950_ = v___x_3986_;
goto v___jp_3939_;
}
}
v___jp_3987_:
{
lean_object* v___x_3996_; lean_object* v_env_3997_; lean_object* v_nextMacroScope_3998_; lean_object* v_ngen_3999_; lean_object* v_auxDeclNGen_4000_; lean_object* v_traceState_4001_; lean_object* v_messages_4002_; lean_object* v_infoState_4003_; lean_object* v_snapshotTasks_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4015_; 
v___x_3996_ = lean_st_ref_take(v___y_3995_);
v_env_3997_ = lean_ctor_get(v___x_3996_, 0);
v_nextMacroScope_3998_ = lean_ctor_get(v___x_3996_, 1);
v_ngen_3999_ = lean_ctor_get(v___x_3996_, 2);
v_auxDeclNGen_4000_ = lean_ctor_get(v___x_3996_, 3);
v_traceState_4001_ = lean_ctor_get(v___x_3996_, 4);
v_messages_4002_ = lean_ctor_get(v___x_3996_, 6);
v_infoState_4003_ = lean_ctor_get(v___x_3996_, 7);
v_snapshotTasks_4004_ = lean_ctor_get(v___x_3996_, 8);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3996_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; 
v_unused_4016_ = lean_ctor_get(v___x_3996_, 5);
lean_dec(v_unused_4016_);
v___x_4006_ = v___x_3996_;
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_snapshotTasks_4004_);
lean_inc(v_infoState_4003_);
lean_inc(v_messages_4002_);
lean_inc(v_traceState_4001_);
lean_inc(v_auxDeclNGen_4000_);
lean_inc(v_ngen_3999_);
lean_inc(v_nextMacroScope_3998_);
lean_inc(v_env_3997_);
lean_dec(v___x_3996_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4008_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4009_ = lean_box(v___y_3991_);
lean_inc(v___y_3988_);
v___x_4010_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4008_, v_env_3997_, v___y_3988_, v___x_4009_);
lean_inc_ref(v___y_3992_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 5, v___y_3992_);
lean_ctor_set(v___x_4006_, 0, v___x_4010_);
v___x_4012_ = v___x_4006_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_nextMacroScope_3998_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_ngen_3999_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_auxDeclNGen_4000_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_traceState_4001_);
lean_ctor_set(v_reuseFailAlloc_4014_, 5, v___y_3992_);
lean_ctor_set(v_reuseFailAlloc_4014_, 6, v_messages_4002_);
lean_ctor_set(v_reuseFailAlloc_4014_, 7, v_infoState_4003_);
lean_ctor_set(v_reuseFailAlloc_4014_, 8, v_snapshotTasks_4004_);
v___x_4012_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_st_ref_set(v___y_3995_, v___x_4012_);
v___y_3972_ = v___y_3988_;
v___y_3973_ = v___y_3989_;
v___y_3974_ = v___y_3991_;
v___y_3975_ = v___y_3990_;
v_exportedInfo_x3f_3976_ = v___y_3993_;
v___y_3977_ = v___y_3994_;
v___y_3978_ = v___y_3995_;
goto v___jp_3971_;
}
}
}
v___jp_4017_:
{
lean_object* v___x_4024_; 
lean_inc_ref(v___y_4021_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___y_4021_);
v___y_3972_ = v___y_4018_;
v___y_3973_ = v___y_4019_;
v___y_3974_ = v___y_4020_;
v___y_3975_ = v___y_4021_;
v_exportedInfo_x3f_3976_ = v___x_4024_;
v___y_3977_ = v___y_4022_;
v___y_3978_ = v___y_4023_;
goto v___jp_3971_;
}
v___jp_4025_:
{
lean_object* v___x_4032_; 
lean_inc_ref(v___y_4029_);
v___x_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4032_, 0, v___y_4029_);
v___y_3972_ = v___y_4026_;
v___y_3973_ = v___y_4027_;
v___y_3974_ = v___y_4028_;
v___y_3975_ = v___y_4029_;
v_exportedInfo_x3f_3976_ = v___x_4032_;
v___y_3977_ = v___y_4030_;
v___y_3978_ = v___y_4031_;
goto v___jp_3971_;
}
v___jp_4033_:
{
lean_object* v___x_4043_; uint8_t v___x_4044_; 
lean_inc(v_decl_3654_);
v___x_4043_ = l_Lean_Declaration_getTopLevelNames(v_decl_3654_);
v___x_4044_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4043_);
lean_dec(v___x_4043_);
if (v___x_4044_ == 0)
{
lean_dec(v___y_4038_);
if (lean_obj_tag(v___y_4040_) == 0)
{
if (v___y_4035_ == 0)
{
lean_object* v_options_4045_; uint8_t v_hasTrace_4046_; 
v_options_4045_ = lean_ctor_get(v___y_4041_, 2);
v_hasTrace_4046_ = lean_ctor_get_uint8(v_options_4045_, sizeof(void*)*1);
if (v_hasTrace_4046_ == 0)
{
v___y_4026_ = v___y_4034_;
v___y_4027_ = v___y_4035_;
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4037_;
v___y_4030_ = v___y_4041_;
v___y_4031_ = v___y_4042_;
goto v___jp_4025_;
}
else
{
lean_object* v_inheritedTraceOptions_4047_; lean_object* v___x_4048_; uint8_t v___x_4049_; 
v_inheritedTraceOptions_4047_ = lean_ctor_get(v___y_4041_, 13);
v___x_4048_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4049_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4047_, v_options_4045_, v___x_4048_);
if (v___x_4049_ == 0)
{
v___y_4026_ = v___y_4034_;
v___y_4027_ = v___y_4035_;
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4037_;
v___y_4030_ = v___y_4041_;
v___y_4031_ = v___y_4042_;
goto v___jp_4025_;
}
else
{
lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4050_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3);
v___x_4051_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4050_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_dec_ref_known(v___x_4051_, 1);
v___y_4026_ = v___y_4034_;
v___y_4027_ = v___y_4035_;
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4037_;
v___y_4030_ = v___y_4041_;
v___y_4031_ = v___y_4042_;
goto v___jp_4025_;
}
else
{
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4034_);
lean_dec(v_decl_3654_);
return v___x_4051_;
}
}
}
}
else
{
v___y_3988_ = v___y_4034_;
v___y_3989_ = v___y_4035_;
v___y_3990_ = v___y_4037_;
v___y_3991_ = v___y_4036_;
v___y_3992_ = v___y_4039_;
v___y_3993_ = v___y_4040_;
v___y_3994_ = v___y_4041_;
v___y_3995_ = v___y_4042_;
goto v___jp_3987_;
}
}
else
{
v___y_3988_ = v___y_4034_;
v___y_3989_ = v___y_4035_;
v___y_3990_ = v___y_4037_;
v___y_3991_ = v___y_4036_;
v___y_3992_ = v___y_4039_;
v___y_3993_ = v___y_4040_;
v___y_3994_ = v___y_4041_;
v___y_3995_ = v___y_4042_;
goto v___jp_3987_;
}
}
else
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v_a_4054_; uint8_t v___x_4055_; 
lean_dec(v___y_4040_);
v___x_4052_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4053_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4052_, v___y_4041_);
v_a_4054_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4054_);
lean_dec_ref(v___x_4053_);
v___x_4055_ = lean_unbox(v_a_4054_);
lean_dec(v_a_4054_);
if (v___x_4055_ == 0)
{
lean_object* v_options_4056_; uint8_t v_hasTrace_4057_; 
v_options_4056_ = lean_ctor_get(v___y_4041_, 2);
v_hasTrace_4057_ = lean_ctor_get_uint8(v_options_4056_, sizeof(void*)*1);
if (v_hasTrace_4057_ == 0)
{
v___y_3972_ = v___y_4034_;
v___y_3973_ = v___y_4035_;
v___y_3974_ = v___y_4036_;
v___y_3975_ = v___y_4037_;
v_exportedInfo_x3f_3976_ = v___y_4038_;
v___y_3977_ = v___y_4041_;
v___y_3978_ = v___y_4042_;
goto v___jp_3971_;
}
else
{
lean_object* v_inheritedTraceOptions_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_inheritedTraceOptions_4058_ = lean_ctor_get(v___y_4041_, 13);
v___x_4059_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4058_, v_options_4056_, v___x_4059_);
if (v___x_4060_ == 0)
{
v___y_3972_ = v___y_4034_;
v___y_3973_ = v___y_4035_;
v___y_3974_ = v___y_4036_;
v___y_3975_ = v___y_4037_;
v_exportedInfo_x3f_3976_ = v___y_4038_;
v___y_3977_ = v___y_4041_;
v___y_3978_ = v___y_4042_;
goto v___jp_3971_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5);
v___x_4062_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4061_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_dec_ref_known(v___x_4062_, 1);
v___y_3972_ = v___y_4034_;
v___y_3973_ = v___y_4035_;
v___y_3974_ = v___y_4036_;
v___y_3975_ = v___y_4037_;
v_exportedInfo_x3f_3976_ = v___y_4038_;
v___y_3977_ = v___y_4041_;
v___y_3978_ = v___y_4042_;
goto v___jp_3971_;
}
else
{
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4034_);
lean_dec(v_decl_3654_);
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_options_4063_; uint8_t v_hasTrace_4064_; 
lean_dec(v___y_4038_);
v_options_4063_ = lean_ctor_get(v___y_4041_, 2);
v_hasTrace_4064_ = lean_ctor_get_uint8(v_options_4063_, sizeof(void*)*1);
if (v_hasTrace_4064_ == 0)
{
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4035_;
v___y_4020_ = v___y_4036_;
v___y_4021_ = v___y_4037_;
v___y_4022_ = v___y_4041_;
v___y_4023_ = v___y_4042_;
goto v___jp_4017_;
}
else
{
lean_object* v_inheritedTraceOptions_4065_; lean_object* v___x_4066_; uint8_t v___x_4067_; 
v_inheritedTraceOptions_4065_ = lean_ctor_get(v___y_4041_, 13);
v___x_4066_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4067_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4065_, v_options_4063_, v___x_4066_);
if (v___x_4067_ == 0)
{
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4035_;
v___y_4020_ = v___y_4036_;
v___y_4021_ = v___y_4037_;
v___y_4022_ = v___y_4041_;
v___y_4023_ = v___y_4042_;
goto v___jp_4017_;
}
else
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7);
v___x_4069_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4068_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4069_) == 0)
{
lean_dec_ref_known(v___x_4069_, 1);
v___y_4018_ = v___y_4034_;
v___y_4019_ = v___y_4035_;
v___y_4020_ = v___y_4036_;
v___y_4021_ = v___y_4037_;
v___y_4022_ = v___y_4041_;
v___y_4023_ = v___y_4042_;
goto v___jp_4017_;
}
else
{
lean_dec_ref(v___y_4037_);
lean_dec(v___y_4034_);
lean_dec(v_decl_3654_);
return v___x_4069_;
}
}
}
}
}
}
v___jp_4070_:
{
lean_object* v___x_4080_; lean_object* v_env_4081_; uint8_t v___x_4082_; 
v___x_4080_ = lean_st_ref_get(v___y_4079_);
v_env_4081_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4081_);
lean_dec(v___x_4080_);
v___x_4082_ = l_Lean_Environment_containsOnBranch(v_env_4081_, v_fst_4074_);
lean_dec_ref(v_env_4081_);
if (v___x_4082_ == 0)
{
v___y_4034_ = v_fst_4074_;
v___y_4035_ = v___y_4071_;
v___y_4036_ = v_snd_4076_;
v___y_4037_ = v_fst_4075_;
v___y_4038_ = v___y_4072_;
v___y_4039_ = v___y_4073_;
v___y_4040_ = v_exportedInfo_x3f_4077_;
v___y_4041_ = v___y_4078_;
v___y_4042_ = v___y_4079_;
goto v___jp_4033_;
}
else
{
lean_object* v___x_4083_; lean_object* v_env_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; 
lean_dec(v_exportedInfo_x3f_4077_);
lean_dec_ref(v_fst_4075_);
lean_dec(v___y_4072_);
lean_dec(v_decl_3654_);
v___x_4083_ = lean_st_ref_get(v___y_4079_);
v_env_4084_ = lean_ctor_get(v___x_4083_, 0);
lean_inc_ref(v_env_4084_);
lean_dec(v___x_4083_);
v___x_4085_ = lean_elab_environment_to_kernel_env(v_env_4084_);
v___x_4086_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4086_, 0, v___x_4085_);
lean_ctor_set(v___x_4086_, 1, v_fst_4074_);
v___x_4087_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4086_, v___y_4078_, v___y_4079_);
return v___x_4087_;
}
}
v___jp_4088_:
{
lean_object* v_name_4097_; lean_object* v___x_4098_; uint8_t v___x_4099_; 
v_name_4097_ = lean_ctor_get(v_toConstantVal_4091_, 0);
lean_inc(v_name_4097_);
lean_dec_ref(v_toConstantVal_4091_);
v___x_4098_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___y_4090_);
v___x_4099_ = 3;
v___y_4071_ = v___y_4089_;
v___y_4072_ = v___y_4092_;
v___y_4073_ = v___y_4093_;
v_fst_4074_ = v_name_4097_;
v_fst_4075_ = v___x_4098_;
v_snd_4076_ = v___x_4099_;
v_exportedInfo_x3f_4077_ = v_exportedInfo_x3f_4094_;
v___y_4078_ = v___y_4095_;
v___y_4079_ = v___y_4096_;
goto v___jp_4070_;
}
v___jp_4100_:
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_inc_ref(v_toConstantVal_4103_);
v___x_4109_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4109_, 0, v_toConstantVal_4103_);
lean_ctor_set_uint8(v___x_4109_, sizeof(void*)*1, v_isUnsafe_4104_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
v___x_4111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
v___y_4089_ = v___y_4101_;
v___y_4090_ = v___y_4102_;
v_toConstantVal_4091_ = v_toConstantVal_4103_;
v___y_4092_ = v___y_4105_;
v___y_4093_ = v___y_4106_;
v_exportedInfo_x3f_4094_ = v___x_4111_;
v___y_4095_ = v___y_4107_;
v___y_4096_ = v___y_4108_;
goto v___jp_4088_;
}
v___jp_4112_:
{
lean_object* v_toConstantVal_4119_; uint8_t v_isUnsafe_4120_; 
v_toConstantVal_4119_ = lean_ctor_get(v___y_4114_, 0);
lean_inc_ref(v_toConstantVal_4119_);
v_isUnsafe_4120_ = lean_ctor_get_uint8(v___y_4114_, sizeof(void*)*3);
v___y_4101_ = v___y_4113_;
v___y_4102_ = v___y_4114_;
v_toConstantVal_4103_ = v_toConstantVal_4119_;
v_isUnsafe_4104_ = v_isUnsafe_4120_;
v___y_4105_ = v___y_4115_;
v___y_4106_ = v___y_4116_;
v___y_4107_ = v___y_4117_;
v___y_4108_ = v___y_4118_;
goto v___jp_4100_;
}
v___jp_4121_:
{
lean_object* v_toConstantVal_4129_; 
v_toConstantVal_4129_ = lean_ctor_get(v___y_4123_, 0);
lean_inc_ref(v_toConstantVal_4129_);
v___y_4089_ = v___y_4122_;
v___y_4090_ = v___y_4123_;
v_toConstantVal_4091_ = v_toConstantVal_4129_;
v___y_4092_ = v___y_4124_;
v___y_4093_ = v___y_4125_;
v_exportedInfo_x3f_4094_ = v_exportedInfo_x3f_4126_;
v___y_4095_ = v___y_4127_;
v___y_4096_ = v___y_4128_;
goto v___jp_4088_;
}
v___jp_4130_:
{
if (v___y_4136_ == 0)
{
lean_dec_ref(v___y_4131_);
lean_inc(v___y_4134_);
v___y_4122_ = v___y_4132_;
v___y_4123_ = v___y_4133_;
v___y_4124_ = v___y_4134_;
v___y_4125_ = v___y_4135_;
v_exportedInfo_x3f_4126_ = v___y_4134_;
v___y_4127_ = v_a_3656_;
v___y_4128_ = v_a_3657_;
goto v___jp_4121_;
}
else
{
uint8_t v_isExporting_4137_; uint8_t v___x_4138_; 
v_isExporting_4137_ = lean_ctor_get_uint8(v___y_4131_, sizeof(void*)*8);
lean_dec_ref(v___y_4131_);
v___x_4138_ = lean_bool_not(v_isExporting_4137_);
if (v___x_4138_ == 0)
{
lean_inc(v___y_4134_);
v___y_4122_ = v___y_4132_;
v___y_4123_ = v___y_4133_;
v___y_4124_ = v___y_4134_;
v___y_4125_ = v___y_4135_;
v_exportedInfo_x3f_4126_ = v___y_4134_;
v___y_4127_ = v_a_3656_;
v___y_4128_ = v_a_3657_;
goto v___jp_4121_;
}
else
{
if (v_hasTrace_3713_ == 0)
{
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4133_;
v___y_4115_ = v___y_4134_;
v___y_4116_ = v___y_4135_;
v___y_4117_ = v_a_3656_;
v___y_4118_ = v_a_3657_;
goto v___jp_4112_;
}
else
{
lean_object* v___x_4139_; uint8_t v___x_4140_; 
v___x_4139_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4140_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4139_);
if (v___x_4140_ == 0)
{
v___y_4113_ = v___y_4132_;
v___y_4114_ = v___y_4133_;
v___y_4115_ = v___y_4134_;
v___y_4116_ = v___y_4135_;
v___y_4117_ = v_a_3656_;
v___y_4118_ = v_a_3657_;
goto v___jp_4112_;
}
else
{
lean_object* v_toConstantVal_4141_; uint8_t v_isUnsafe_4142_; lean_object* v_name_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_toConstantVal_4141_ = lean_ctor_get(v___y_4133_, 0);
lean_inc_ref(v_toConstantVal_4141_);
v_isUnsafe_4142_ = lean_ctor_get_uint8(v___y_4133_, sizeof(void*)*3);
v_name_4143_ = lean_ctor_get(v_toConstantVal_4141_, 0);
v___x_4144_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3);
lean_inc(v_name_4143_);
v___x_4145_ = l_Lean_MessageData_ofName(v_name_4143_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v___x_4144_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
v___x_4147_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4148_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4146_);
lean_ctor_set(v___x_4148_, 1, v___x_4147_);
v___x_4149_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4148_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_dec_ref_known(v___x_4149_, 1);
v___y_4101_ = v___y_4132_;
v___y_4102_ = v___y_4133_;
v_toConstantVal_4103_ = v_toConstantVal_4141_;
v_isUnsafe_4104_ = v_isUnsafe_4142_;
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4135_;
v___y_4107_ = v_a_3656_;
v___y_4108_ = v_a_3657_;
goto v___jp_4100_;
}
else
{
lean_dec_ref(v_toConstantVal_4141_);
lean_dec(v___y_4134_);
lean_dec_ref(v___y_4133_);
lean_dec(v_decl_3654_);
return v___x_4149_;
}
}
}
}
}
}
v___jp_4150_:
{
lean_object* v_name_4159_; lean_object* v___x_4160_; uint8_t v___x_4161_; 
v_name_4159_ = lean_ctor_get(v_toConstantVal_4152_, 0);
lean_inc(v_name_4159_);
lean_dec_ref(v_toConstantVal_4152_);
v___x_4160_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4160_, 0, v___y_4151_);
v___x_4161_ = 1;
v___y_4071_ = v___y_4153_;
v___y_4072_ = v___y_4154_;
v___y_4073_ = v___y_4155_;
v_fst_4074_ = v_name_4159_;
v_fst_4075_ = v___x_4160_;
v_snd_4076_ = v___x_4161_;
v_exportedInfo_x3f_4077_ = v_exportedInfo_x3f_4156_;
v___y_4078_ = v___y_4157_;
v___y_4079_ = v___y_4158_;
goto v___jp_4070_;
}
v___jp_4162_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
lean_inc_ref(v_toConstantVal_4164_);
v___x_4170_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4170_, 0, v_toConstantVal_4164_);
lean_ctor_set_uint8(v___x_4170_, sizeof(void*)*1, v___y_4165_);
v___x_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4170_);
v___x_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
v___y_4151_ = v___y_4163_;
v_toConstantVal_4152_ = v_toConstantVal_4164_;
v___y_4153_ = v___y_4165_;
v___y_4154_ = v___y_4166_;
v___y_4155_ = v___y_4167_;
v_exportedInfo_x3f_4156_ = v___x_4172_;
v___y_4157_ = v___y_4168_;
v___y_4158_ = v___y_4169_;
goto v___jp_4150_;
}
v___jp_4173_:
{
lean_object* v_toConstantVal_4180_; 
v_toConstantVal_4180_ = lean_ctor_get(v___y_4174_, 0);
lean_inc_ref(v_toConstantVal_4180_);
v___y_4163_ = v___y_4174_;
v_toConstantVal_4164_ = v_toConstantVal_4180_;
v___y_4165_ = v___y_4175_;
v___y_4166_ = v___y_4176_;
v___y_4167_ = v___y_4177_;
v___y_4168_ = v___y_4178_;
v___y_4169_ = v___y_4179_;
goto v___jp_4162_;
}
v___jp_4181_:
{
if (v___y_4186_ == 0)
{
lean_object* v_toConstantVal_4187_; 
v_toConstantVal_4187_ = lean_ctor_get(v___y_4182_, 0);
lean_inc_ref(v_toConstantVal_4187_);
lean_inc(v___y_4184_);
v___y_4151_ = v___y_4182_;
v_toConstantVal_4152_ = v_toConstantVal_4187_;
v___y_4153_ = v___y_4183_;
v___y_4154_ = v___y_4184_;
v___y_4155_ = v___y_4185_;
v_exportedInfo_x3f_4156_ = v___y_4184_;
v___y_4157_ = v_a_3656_;
v___y_4158_ = v_a_3657_;
goto v___jp_4150_;
}
else
{
if (v_hasTrace_3713_ == 0)
{
v___y_4174_ = v___y_4182_;
v___y_4175_ = v___y_4183_;
v___y_4176_ = v___y_4184_;
v___y_4177_ = v___y_4185_;
v___y_4178_ = v_a_3656_;
v___y_4179_ = v_a_3657_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4188_; uint8_t v___x_4189_; 
v___x_4188_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4188_);
if (v___x_4189_ == 0)
{
v___y_4174_ = v___y_4182_;
v___y_4175_ = v___y_4183_;
v___y_4176_ = v___y_4184_;
v___y_4177_ = v___y_4185_;
v___y_4178_ = v_a_3656_;
v___y_4179_ = v_a_3657_;
goto v___jp_4173_;
}
else
{
lean_object* v_toConstantVal_4190_; lean_object* v_name_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; 
v_toConstantVal_4190_ = lean_ctor_get(v___y_4182_, 0);
lean_inc_ref(v_toConstantVal_4190_);
v_name_4191_ = lean_ctor_get(v_toConstantVal_4190_, 0);
v___x_4192_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5);
lean_inc(v_name_4191_);
v___x_4193_ = l_Lean_MessageData_ofName(v_name_4191_);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4194_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4196_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_dec_ref_known(v___x_4197_, 1);
v___y_4163_ = v___y_4182_;
v_toConstantVal_4164_ = v_toConstantVal_4190_;
v___y_4165_ = v___y_4183_;
v___y_4166_ = v___y_4184_;
v___y_4167_ = v___y_4185_;
v___y_4168_ = v_a_3656_;
v___y_4169_ = v_a_3657_;
goto v___jp_4162_;
}
else
{
lean_dec_ref(v_toConstantVal_4190_);
lean_dec(v___y_4184_);
lean_dec_ref(v___y_4182_);
lean_dec(v_decl_3654_);
return v___x_4197_;
}
}
}
}
}
v___jp_4198_:
{
lean_object* v_name_4207_; lean_object* v___x_4208_; uint8_t v___x_4209_; 
v_name_4207_ = lean_ctor_get(v_toConstantVal_4200_, 0);
lean_inc(v_name_4207_);
lean_dec_ref(v_toConstantVal_4200_);
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___y_4199_);
v___x_4209_ = 0;
v___y_4071_ = v___y_4201_;
v___y_4072_ = v___y_4202_;
v___y_4073_ = v___y_4203_;
v_fst_4074_ = v_name_4207_;
v_fst_4075_ = v___x_4208_;
v_snd_4076_ = v___x_4209_;
v_exportedInfo_x3f_4077_ = v_exportedInfo_x3f_4204_;
v___y_4078_ = v___y_4205_;
v___y_4079_ = v___y_4206_;
goto v___jp_4070_;
}
v___jp_4210_:
{
lean_object* v_toConstantVal_4218_; 
v_toConstantVal_4218_ = lean_ctor_get(v___y_4211_, 0);
lean_inc_ref(v_toConstantVal_4218_);
v___y_4199_ = v___y_4211_;
v_toConstantVal_4200_ = v_toConstantVal_4218_;
v___y_4201_ = v___y_4212_;
v___y_4202_ = v___y_4213_;
v___y_4203_ = v___y_4214_;
v_exportedInfo_x3f_4204_ = v_exportedInfo_x3f_4215_;
v___y_4205_ = v___y_4216_;
v___y_4206_ = v___y_4217_;
goto v___jp_4198_;
}
v___jp_4219_:
{
uint8_t v___x_4228_; uint8_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4228_ = 0;
v___x_4229_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4222_, v___x_4228_);
lean_inc_ref(v_toConstantVal_4221_);
v___x_4230_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4230_, 0, v_toConstantVal_4221_);
lean_ctor_set_uint8(v___x_4230_, sizeof(void*)*1, v___x_4229_);
v___x_4231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4231_, 0, v___x_4230_);
v___x_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4231_);
v___y_4199_ = v___y_4220_;
v_toConstantVal_4200_ = v_toConstantVal_4221_;
v___y_4201_ = v___y_4223_;
v___y_4202_ = v___y_4224_;
v___y_4203_ = v___y_4225_;
v_exportedInfo_x3f_4204_ = v___x_4232_;
v___y_4205_ = v___y_4226_;
v___y_4206_ = v___y_4227_;
goto v___jp_4198_;
}
v___jp_4233_:
{
lean_object* v_toConstantVal_4240_; uint8_t v_safety_4241_; 
v_toConstantVal_4240_ = lean_ctor_get(v___y_4234_, 0);
lean_inc_ref(v_toConstantVal_4240_);
v_safety_4241_ = lean_ctor_get_uint8(v___y_4234_, sizeof(void*)*4);
v___y_4220_ = v___y_4234_;
v_toConstantVal_4221_ = v_toConstantVal_4240_;
v_safety_4222_ = v_safety_4241_;
v___y_4223_ = v___y_4235_;
v___y_4224_ = v___y_4236_;
v___y_4225_ = v___y_4237_;
v___y_4226_ = v___y_4238_;
v___y_4227_ = v___y_4239_;
goto v___jp_4219_;
}
v___jp_4242_:
{
if (v___y_4250_ == 0)
{
lean_dec_ref(v___y_4247_);
lean_inc(v___y_4245_);
v___y_4211_ = v___y_4243_;
v___y_4212_ = v___y_4244_;
v___y_4213_ = v___y_4245_;
v___y_4214_ = v___y_4246_;
v_exportedInfo_x3f_4215_ = v___y_4245_;
v___y_4216_ = v___y_4249_;
v___y_4217_ = v___y_4248_;
goto v___jp_4210_;
}
else
{
uint8_t v_isExporting_4251_; uint8_t v___x_4252_; 
v_isExporting_4251_ = lean_ctor_get_uint8(v___y_4247_, sizeof(void*)*8);
lean_dec_ref(v___y_4247_);
v___x_4252_ = lean_bool_not(v_isExporting_4251_);
if (v___x_4252_ == 0)
{
lean_inc(v___y_4245_);
v___y_4211_ = v___y_4243_;
v___y_4212_ = v___y_4244_;
v___y_4213_ = v___y_4245_;
v___y_4214_ = v___y_4246_;
v_exportedInfo_x3f_4215_ = v___y_4245_;
v___y_4216_ = v___y_4249_;
v___y_4217_ = v___y_4248_;
goto v___jp_4210_;
}
else
{
lean_object* v_options_4253_; uint8_t v_hasTrace_4254_; 
v_options_4253_ = lean_ctor_get(v___y_4249_, 2);
v_hasTrace_4254_ = lean_ctor_get_uint8(v_options_4253_, sizeof(void*)*1);
if (v_hasTrace_4254_ == 0)
{
v___y_4234_ = v___y_4243_;
v___y_4235_ = v___y_4244_;
v___y_4236_ = v___y_4245_;
v___y_4237_ = v___y_4246_;
v___y_4238_ = v___y_4249_;
v___y_4239_ = v___y_4248_;
goto v___jp_4233_;
}
else
{
lean_object* v_inheritedTraceOptions_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v_inheritedTraceOptions_4255_ = lean_ctor_get(v___y_4249_, 13);
v___x_4256_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4257_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4255_, v_options_4253_, v___x_4256_);
if (v___x_4257_ == 0)
{
v___y_4234_ = v___y_4243_;
v___y_4235_ = v___y_4244_;
v___y_4236_ = v___y_4245_;
v___y_4237_ = v___y_4246_;
v___y_4238_ = v___y_4249_;
v___y_4239_ = v___y_4248_;
goto v___jp_4233_;
}
else
{
lean_object* v_toConstantVal_4258_; uint8_t v_safety_4259_; lean_object* v_name_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; 
v_toConstantVal_4258_ = lean_ctor_get(v___y_4243_, 0);
lean_inc_ref(v_toConstantVal_4258_);
v_safety_4259_ = lean_ctor_get_uint8(v___y_4243_, sizeof(void*)*4);
v_name_4260_ = lean_ctor_get(v_toConstantVal_4258_, 0);
v___x_4261_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1);
lean_inc(v_name_4260_);
v___x_4262_ = l_Lean_MessageData_ofName(v_name_4260_);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4265_, v___y_4249_, v___y_4248_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_dec_ref_known(v___x_4266_, 1);
v___y_4220_ = v___y_4243_;
v_toConstantVal_4221_ = v_toConstantVal_4258_;
v_safety_4222_ = v_safety_4259_;
v___y_4223_ = v___y_4244_;
v___y_4224_ = v___y_4245_;
v___y_4225_ = v___y_4246_;
v___y_4226_ = v___y_4249_;
v___y_4227_ = v___y_4248_;
goto v___jp_4219_;
}
else
{
lean_dec_ref(v_toConstantVal_4258_);
lean_dec(v___y_4245_);
lean_dec_ref(v___y_4243_);
lean_dec(v_decl_3654_);
return v___x_4266_;
}
}
}
}
}
}
v___jp_4267_:
{
lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v_env_4276_; uint8_t v___x_4277_; 
v___x_4274_ = lean_st_ref_get(v___y_4273_);
v___x_4275_ = lean_st_ref_get(v___y_4273_);
v_env_4276_ = lean_ctor_get(v___x_4275_, 0);
lean_inc_ref(v_env_4276_);
lean_dec(v___x_4275_);
v___x_4277_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4277_ == 0)
{
lean_dec(v___x_4274_);
v___y_4243_ = v_defn_4271_;
v___y_4244_ = v___y_4268_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4270_;
v___y_4247_ = v_env_4276_;
v___y_4248_ = v___y_4273_;
v___y_4249_ = v___y_4272_;
v___y_4250_ = v___x_4277_;
goto v___jp_4242_;
}
else
{
lean_object* v_env_4278_; lean_object* v___x_4279_; uint8_t v_isModule_4280_; 
v_env_4278_ = lean_ctor_get(v___x_4274_, 0);
lean_inc_ref(v_env_4278_);
lean_dec(v___x_4274_);
v___x_4279_ = l_Lean_Environment_header(v_env_4278_);
lean_dec_ref(v_env_4278_);
v_isModule_4280_ = lean_ctor_get_uint8(v___x_4279_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4279_);
v___y_4243_ = v_defn_4271_;
v___y_4244_ = v___y_4268_;
v___y_4245_ = v___y_4269_;
v___y_4246_ = v___y_4270_;
v___y_4247_ = v_env_4276_;
v___y_4248_ = v___y_4273_;
v___y_4249_ = v___y_4272_;
v___y_4250_ = v_isModule_4280_;
goto v___jp_4242_;
}
}
v___jp_4282_:
{
lean_object* v___x_4287_; double v___x_4288_; double v___x_4289_; lean_object* v___x_4290_; lean_object* v___x_4291_; lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4294_; 
v___x_4287_ = lean_io_get_num_heartbeats();
v___x_4288_ = lean_float_of_nat(v___y_4283_);
v___x_4289_ = lean_float_of_nat(v___x_4287_);
v___x_4290_ = lean_box_float(v___x_4288_);
v___x_4291_ = lean_box_float(v___x_4289_);
v___x_4292_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4292_, 0, v___x_4290_);
lean_ctor_set(v___x_4292_, 1, v___x_4291_);
v___x_4293_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4293_, 0, v_a_4286_);
lean_ctor_set(v___x_4293_, 1, v___x_4292_);
v___x_4294_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3714_, v___x_3865_, v___x_4281_, v_options_3711_, v___y_4284_, v___y_4285_, v___f_3864_, v___x_4293_, v_a_3656_, v_a_3657_);
return v___x_4294_;
}
v___jp_4295_:
{
if (lean_obj_tag(v___y_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
v_a_4300_ = lean_ctor_get(v___y_4299_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___y_4299_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___y_4299_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___y_4299_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
lean_ctor_set_tag(v___x_4302_, 1);
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
v___y_4283_ = v___y_4296_;
v___y_4284_ = v___y_4297_;
v___y_4285_ = v___y_4298_;
v_a_4286_ = v___x_4305_;
goto v___jp_4282_;
}
}
}
else
{
lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4315_; 
v_a_4308_ = lean_ctor_get(v___y_4299_, 0);
v_isSharedCheck_4315_ = !lean_is_exclusive(v___y_4299_);
if (v_isSharedCheck_4315_ == 0)
{
v___x_4310_ = v___y_4299_;
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___y_4299_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4315_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4313_; 
if (v_isShared_4311_ == 0)
{
lean_ctor_set_tag(v___x_4310_, 0);
v___x_4313_ = v___x_4310_;
goto v_reusejp_4312_;
}
else
{
lean_object* v_reuseFailAlloc_4314_; 
v_reuseFailAlloc_4314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4314_, 0, v_a_4308_);
v___x_4313_ = v_reuseFailAlloc_4314_;
goto v_reusejp_4312_;
}
v_reusejp_4312_:
{
v___y_4283_ = v___y_4296_;
v___y_4284_ = v___y_4297_;
v___y_4285_ = v___y_4298_;
v_a_4286_ = v___x_4313_;
goto v___jp_4282_;
}
}
}
}
v___jp_4316_:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4323_ = lean_apply_5(v___y_4317_, v___x_4322_, v___y_4320_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4318_;
v___y_4297_ = v___y_4319_;
v___y_4298_ = v___y_4321_;
v___y_4299_ = v___x_4323_;
goto v___jp_4295_;
}
v___jp_4324_:
{
lean_object* v___x_4329_; lean_object* v___x_4330_; 
v___x_4329_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4330_ = lean_apply_4(v___y_4327_, v___x_4329_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4325_;
v___y_4297_ = v___y_4326_;
v___y_4298_ = v___y_4328_;
v___y_4299_ = v___x_4330_;
goto v___jp_4295_;
}
v___jp_4331_:
{
if (v___y_4340_ == 0)
{
lean_dec_ref(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec_ref(v___y_4336_);
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4333_;
v___y_4319_ = v___y_4334_;
v___y_4320_ = v___y_4335_;
v___y_4321_ = v___y_4339_;
goto v___jp_4316_;
}
else
{
uint8_t v_isExporting_4341_; uint8_t v___x_4342_; 
v_isExporting_4341_ = lean_ctor_get_uint8(v___y_4338_, sizeof(void*)*8);
lean_dec_ref(v___y_4338_);
v___x_4342_ = lean_bool_not(v_isExporting_4341_);
if (v___x_4342_ == 0)
{
lean_dec_ref(v___y_4337_);
lean_dec_ref(v___y_4336_);
v___y_4317_ = v___y_4332_;
v___y_4318_ = v___y_4333_;
v___y_4319_ = v___y_4334_;
v___y_4320_ = v___y_4335_;
v___y_4321_ = v___y_4339_;
goto v___jp_4316_;
}
else
{
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4332_);
if (v_hasTrace_3713_ == 0)
{
lean_dec_ref(v___y_4336_);
v___y_4325_ = v___y_4333_;
v___y_4326_ = v___y_4334_;
v___y_4327_ = v___y_4337_;
v___y_4328_ = v___y_4339_;
goto v___jp_4324_;
}
else
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4344_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_dec_ref(v___y_4336_);
v___y_4325_ = v___y_4333_;
v___y_4326_ = v___y_4334_;
v___y_4327_ = v___y_4337_;
v___y_4328_ = v___y_4339_;
goto v___jp_4324_;
}
else
{
lean_object* v_toConstantVal_4345_; lean_object* v_name_4346_; lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v_toConstantVal_4345_ = lean_ctor_get(v___y_4336_, 0);
lean_inc_ref(v_toConstantVal_4345_);
lean_dec_ref(v___y_4336_);
v_name_4346_ = lean_ctor_get(v_toConstantVal_4345_, 0);
lean_inc(v_name_4346_);
lean_dec_ref(v_toConstantVal_4345_);
v___x_4347_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3);
v___x_4348_ = l_Lean_MessageData_ofName(v_name_4346_);
v___x_4349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4347_);
lean_ctor_set(v___x_4349_, 1, v___x_4348_);
v___x_4350_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4351_, 0, v___x_4349_);
lean_ctor_set(v___x_4351_, 1, v___x_4350_);
v___x_4352_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4351_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4354_ = lean_apply_4(v___y_4337_, v_a_4353_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4333_;
v___y_4297_ = v___y_4334_;
v___y_4298_ = v___y_4339_;
v___y_4299_ = v___x_4354_;
goto v___jp_4295_;
}
else
{
lean_dec_ref(v___y_4337_);
v___y_4296_ = v___y_4333_;
v___y_4297_ = v___y_4334_;
v___y_4298_ = v___y_4339_;
v___y_4299_ = v___x_4352_;
goto v___jp_4295_;
}
}
}
}
}
}
v___jp_4355_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; 
v___x_4360_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4361_ = lean_apply_4(v___y_4357_, v___x_4360_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4356_;
v___y_4297_ = v___y_4358_;
v___y_4298_ = v___y_4359_;
v___y_4299_ = v___x_4361_;
goto v___jp_4295_;
}
v___jp_4362_:
{
if (v___y_4370_ == 0)
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
lean_dec_ref(v___y_4366_);
lean_dec_ref(v___y_4363_);
v___x_4371_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4372_ = lean_apply_5(v___y_4368_, v___x_4371_, v___y_4367_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4364_;
v___y_4297_ = v___y_4365_;
v___y_4298_ = v___y_4369_;
v___y_4299_ = v___x_4372_;
goto v___jp_4295_;
}
else
{
lean_dec_ref(v___y_4368_);
lean_dec(v___y_4367_);
if (v_hasTrace_3713_ == 0)
{
lean_dec_ref(v___y_4366_);
v___y_4356_ = v___y_4364_;
v___y_4357_ = v___y_4363_;
v___y_4358_ = v___y_4365_;
v___y_4359_ = v___y_4369_;
goto v___jp_4355_;
}
else
{
lean_object* v___x_4373_; uint8_t v___x_4374_; 
v___x_4373_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4374_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4373_);
if (v___x_4374_ == 0)
{
lean_dec_ref(v___y_4366_);
v___y_4356_ = v___y_4364_;
v___y_4357_ = v___y_4363_;
v___y_4358_ = v___y_4365_;
v___y_4359_ = v___y_4369_;
goto v___jp_4355_;
}
else
{
lean_object* v_toConstantVal_4375_; lean_object* v_name_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; 
v_toConstantVal_4375_ = lean_ctor_get(v___y_4366_, 0);
lean_inc_ref(v_toConstantVal_4375_);
lean_dec_ref(v___y_4366_);
v_name_4376_ = lean_ctor_get(v_toConstantVal_4375_, 0);
lean_inc(v_name_4376_);
lean_dec_ref(v_toConstantVal_4375_);
v___x_4377_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5);
v___x_4378_ = l_Lean_MessageData_ofName(v_name_4376_);
v___x_4379_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4379_, 0, v___x_4377_);
lean_ctor_set(v___x_4379_, 1, v___x_4378_);
v___x_4380_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4381_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4382_) == 0)
{
lean_object* v_a_4383_; lean_object* v___x_4384_; 
v_a_4383_ = lean_ctor_get(v___x_4382_, 0);
lean_inc(v_a_4383_);
lean_dec_ref_known(v___x_4382_, 1);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4384_ = lean_apply_4(v___y_4363_, v_a_4383_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4296_ = v___y_4364_;
v___y_4297_ = v___y_4365_;
v___y_4298_ = v___y_4369_;
v___y_4299_ = v___x_4384_;
goto v___jp_4295_;
}
else
{
lean_dec_ref(v___y_4363_);
v___y_4296_ = v___y_4364_;
v___y_4297_ = v___y_4365_;
v___y_4298_ = v___y_4369_;
v___y_4299_ = v___x_4382_;
goto v___jp_4295_;
}
}
}
}
}
v___jp_4385_:
{
lean_object* v___x_4390_; double v___x_4391_; double v___x_4392_; double v___x_4393_; double v___x_4394_; double v___x_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4390_ = lean_io_mono_nanos_now();
v___x_4391_ = lean_float_of_nat(v___y_4386_);
v___x_4392_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0);
v___x_4393_ = lean_float_div(v___x_4391_, v___x_4392_);
v___x_4394_ = lean_float_of_nat(v___x_4390_);
v___x_4395_ = lean_float_div(v___x_4394_, v___x_4392_);
v___x_4396_ = lean_box_float(v___x_4393_);
v___x_4397_ = lean_box_float(v___x_4395_);
v___x_4398_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4398_, 0, v___x_4396_);
lean_ctor_set(v___x_4398_, 1, v___x_4397_);
v___x_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4399_, 0, v_a_4389_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
v___x_4400_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3714_, v___x_3865_, v___x_4281_, v_options_3711_, v___y_4387_, v___y_4388_, v___f_3864_, v___x_4399_, v_a_3656_, v_a_3657_);
return v___x_4400_;
}
v___jp_4401_:
{
if (lean_obj_tag(v___y_4405_) == 0)
{
lean_object* v_a_4406_; lean_object* v___x_4408_; uint8_t v_isShared_4409_; uint8_t v_isSharedCheck_4413_; 
v_a_4406_ = lean_ctor_get(v___y_4405_, 0);
v_isSharedCheck_4413_ = !lean_is_exclusive(v___y_4405_);
if (v_isSharedCheck_4413_ == 0)
{
v___x_4408_ = v___y_4405_;
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
else
{
lean_inc(v_a_4406_);
lean_dec(v___y_4405_);
v___x_4408_ = lean_box(0);
v_isShared_4409_ = v_isSharedCheck_4413_;
goto v_resetjp_4407_;
}
v_resetjp_4407_:
{
lean_object* v___x_4411_; 
if (v_isShared_4409_ == 0)
{
lean_ctor_set_tag(v___x_4408_, 1);
v___x_4411_ = v___x_4408_;
goto v_reusejp_4410_;
}
else
{
lean_object* v_reuseFailAlloc_4412_; 
v_reuseFailAlloc_4412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4412_, 0, v_a_4406_);
v___x_4411_ = v_reuseFailAlloc_4412_;
goto v_reusejp_4410_;
}
v_reusejp_4410_:
{
v___y_4386_ = v___y_4402_;
v___y_4387_ = v___y_4403_;
v___y_4388_ = v___y_4404_;
v_a_4389_ = v___x_4411_;
goto v___jp_4385_;
}
}
}
else
{
lean_object* v_a_4414_; lean_object* v___x_4416_; uint8_t v_isShared_4417_; uint8_t v_isSharedCheck_4421_; 
v_a_4414_ = lean_ctor_get(v___y_4405_, 0);
v_isSharedCheck_4421_ = !lean_is_exclusive(v___y_4405_);
if (v_isSharedCheck_4421_ == 0)
{
v___x_4416_ = v___y_4405_;
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
else
{
lean_inc(v_a_4414_);
lean_dec(v___y_4405_);
v___x_4416_ = lean_box(0);
v_isShared_4417_ = v_isSharedCheck_4421_;
goto v_resetjp_4415_;
}
v_resetjp_4415_:
{
lean_object* v___x_4419_; 
if (v_isShared_4417_ == 0)
{
lean_ctor_set_tag(v___x_4416_, 0);
v___x_4419_ = v___x_4416_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4420_; 
v_reuseFailAlloc_4420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4420_, 0, v_a_4414_);
v___x_4419_ = v_reuseFailAlloc_4420_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
v___y_4386_ = v___y_4402_;
v___y_4387_ = v___y_4403_;
v___y_4388_ = v___y_4404_;
v_a_4389_ = v___x_4419_;
goto v___jp_4385_;
}
}
}
}
v___jp_4422_:
{
lean_object* v___x_4427_; lean_object* v___x_4428_; 
v___x_4427_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4428_ = lean_apply_4(v___y_4425_, v___x_4427_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4423_;
v___y_4403_ = v___y_4424_;
v___y_4404_ = v___y_4426_;
v___y_4405_ = v___x_4428_;
goto v___jp_4401_;
}
v___jp_4429_:
{
if (v___y_4437_ == 0)
{
lean_object* v___x_4438_; lean_object* v___x_4439_; 
lean_dec_ref(v___y_4435_);
lean_dec_ref(v___y_4434_);
v___x_4438_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4439_ = lean_apply_5(v___y_4430_, v___x_4438_, v___y_4431_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4433_;
v___y_4404_ = v___y_4436_;
v___y_4405_ = v___x_4439_;
goto v___jp_4401_;
}
else
{
lean_dec(v___y_4431_);
lean_dec_ref(v___y_4430_);
if (v_hasTrace_3713_ == 0)
{
lean_dec_ref(v___y_4435_);
v___y_4423_ = v___y_4432_;
v___y_4424_ = v___y_4433_;
v___y_4425_ = v___y_4434_;
v___y_4426_ = v___y_4436_;
goto v___jp_4422_;
}
else
{
lean_object* v___x_4440_; uint8_t v___x_4441_; 
v___x_4440_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4441_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4440_);
if (v___x_4441_ == 0)
{
lean_dec_ref(v___y_4435_);
v___y_4423_ = v___y_4432_;
v___y_4424_ = v___y_4433_;
v___y_4425_ = v___y_4434_;
v___y_4426_ = v___y_4436_;
goto v___jp_4422_;
}
else
{
lean_object* v_toConstantVal_4442_; lean_object* v_name_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; 
v_toConstantVal_4442_ = lean_ctor_get(v___y_4435_, 0);
lean_inc_ref(v_toConstantVal_4442_);
lean_dec_ref(v___y_4435_);
v_name_4443_ = lean_ctor_get(v_toConstantVal_4442_, 0);
lean_inc(v_name_4443_);
lean_dec_ref(v_toConstantVal_4442_);
v___x_4444_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5);
v___x_4445_ = l_Lean_MessageData_ofName(v_name_4443_);
v___x_4446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4444_);
lean_ctor_set(v___x_4446_, 1, v___x_4445_);
v___x_4447_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4448_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4446_);
lean_ctor_set(v___x_4448_, 1, v___x_4447_);
v___x_4449_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4448_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4449_) == 0)
{
lean_object* v_a_4450_; lean_object* v___x_4451_; 
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref_known(v___x_4449_, 1);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4451_ = lean_apply_4(v___y_4434_, v_a_4450_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4433_;
v___y_4404_ = v___y_4436_;
v___y_4405_ = v___x_4451_;
goto v___jp_4401_;
}
else
{
lean_dec_ref(v___y_4434_);
v___y_4402_ = v___y_4432_;
v___y_4403_ = v___y_4433_;
v___y_4404_ = v___y_4436_;
v___y_4405_ = v___x_4449_;
goto v___jp_4401_;
}
}
}
}
}
v___jp_4452_:
{
lean_object* v___x_4457_; lean_object* v___x_4458_; 
v___x_4457_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4458_ = lean_apply_4(v___y_4455_, v___x_4457_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4453_;
v___y_4403_ = v___y_4454_;
v___y_4404_ = v___y_4456_;
v___y_4405_ = v___x_4458_;
goto v___jp_4401_;
}
v___jp_4459_:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_box(0);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4466_ = lean_apply_5(v___y_4461_, v___x_4465_, v___y_4460_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4462_;
v___y_4403_ = v___y_4463_;
v___y_4404_ = v___y_4464_;
v___y_4405_ = v___x_4466_;
goto v___jp_4401_;
}
v___jp_4467_:
{
if (v___y_4476_ == 0)
{
lean_dec_ref(v___y_4474_);
lean_dec_ref(v___y_4471_);
lean_dec_ref(v___y_4468_);
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___y_4469_;
v___y_4462_ = v___y_4472_;
v___y_4463_ = v___y_4473_;
v___y_4464_ = v___y_4475_;
goto v___jp_4459_;
}
else
{
uint8_t v_isExporting_4477_; uint8_t v___x_4478_; 
v_isExporting_4477_ = lean_ctor_get_uint8(v___y_4468_, sizeof(void*)*8);
lean_dec_ref(v___y_4468_);
v___x_4478_ = lean_bool_not(v_isExporting_4477_);
if (v___x_4478_ == 0)
{
lean_dec_ref(v___y_4474_);
lean_dec_ref(v___y_4471_);
v___y_4460_ = v___y_4470_;
v___y_4461_ = v___y_4469_;
v___y_4462_ = v___y_4472_;
v___y_4463_ = v___y_4473_;
v___y_4464_ = v___y_4475_;
goto v___jp_4459_;
}
else
{
lean_dec(v___y_4470_);
lean_dec_ref(v___y_4469_);
if (v_hasTrace_3713_ == 0)
{
lean_dec_ref(v___y_4471_);
v___y_4453_ = v___y_4472_;
v___y_4454_ = v___y_4473_;
v___y_4455_ = v___y_4474_;
v___y_4456_ = v___y_4475_;
goto v___jp_4452_;
}
else
{
lean_object* v___x_4479_; uint8_t v___x_4480_; 
v___x_4479_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4480_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4479_);
if (v___x_4480_ == 0)
{
lean_dec_ref(v___y_4471_);
v___y_4453_ = v___y_4472_;
v___y_4454_ = v___y_4473_;
v___y_4455_ = v___y_4474_;
v___y_4456_ = v___y_4475_;
goto v___jp_4452_;
}
else
{
lean_object* v_toConstantVal_4481_; lean_object* v_name_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; lean_object* v___x_4487_; lean_object* v___x_4488_; 
v_toConstantVal_4481_ = lean_ctor_get(v___y_4471_, 0);
lean_inc_ref(v_toConstantVal_4481_);
lean_dec_ref(v___y_4471_);
v_name_4482_ = lean_ctor_get(v_toConstantVal_4481_, 0);
lean_inc(v_name_4482_);
lean_dec_ref(v_toConstantVal_4481_);
v___x_4483_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3);
v___x_4484_ = l_Lean_MessageData_ofName(v_name_4482_);
v___x_4485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4485_, 0, v___x_4483_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4487_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4485_);
lean_ctor_set(v___x_4487_, 1, v___x_4486_);
v___x_4488_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4487_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_object* v_a_4489_; lean_object* v___x_4490_; 
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
lean_inc(v_a_3657_);
lean_inc_ref(v_a_3656_);
v___x_4490_ = lean_apply_4(v___y_4474_, v_a_4489_, v_a_3656_, v_a_3657_, lean_box(0));
v___y_4402_ = v___y_4472_;
v___y_4403_ = v___y_4473_;
v___y_4404_ = v___y_4475_;
v___y_4405_ = v___x_4490_;
goto v___jp_4401_;
}
else
{
lean_dec_ref(v___y_4474_);
v___y_4402_ = v___y_4472_;
v___y_4403_ = v___y_4473_;
v___y_4404_ = v___y_4475_;
v___y_4405_ = v___x_4488_;
goto v___jp_4401_;
}
}
}
}
}
}
v___jp_4491_:
{
lean_object* v___x_4493_; lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4630_; 
v___x_4493_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3657_);
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4496_ = v___x_4493_;
v_isShared_4497_ = v_isSharedCheck_4630_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4493_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4630_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4498_; uint8_t v___x_4499_; 
v___x_4498_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4499_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3711_, v___x_4498_);
if (v___x_4499_ == 0)
{
lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v_env_4502_; lean_object* v_nextMacroScope_4503_; lean_object* v_ngen_4504_; lean_object* v_auxDeclNGen_4505_; lean_object* v_traceState_4506_; lean_object* v_messages_4507_; lean_object* v_infoState_4508_; lean_object* v_snapshotTasks_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4563_; 
v___x_4500_ = lean_io_mono_nanos_now();
v___x_4501_ = lean_st_ref_take(v_a_3657_);
v_env_4502_ = lean_ctor_get(v___x_4501_, 0);
v_nextMacroScope_4503_ = lean_ctor_get(v___x_4501_, 1);
v_ngen_4504_ = lean_ctor_get(v___x_4501_, 2);
v_auxDeclNGen_4505_ = lean_ctor_get(v___x_4501_, 3);
v_traceState_4506_ = lean_ctor_get(v___x_4501_, 4);
v_messages_4507_ = lean_ctor_get(v___x_4501_, 6);
v_infoState_4508_ = lean_ctor_get(v___x_4501_, 7);
v_snapshotTasks_4509_ = lean_ctor_get(v___x_4501_, 8);
v_isSharedCheck_4563_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4563_ == 0)
{
lean_object* v_unused_4564_; 
v_unused_4564_ = lean_ctor_get(v___x_4501_, 5);
lean_dec(v_unused_4564_);
v___x_4511_ = v___x_4501_;
v_isShared_4512_ = v_isSharedCheck_4563_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_snapshotTasks_4509_);
lean_inc(v_infoState_4508_);
lean_inc(v_messages_4507_);
lean_inc(v_traceState_4506_);
lean_inc(v_auxDeclNGen_4505_);
lean_inc(v_ngen_4504_);
lean_inc(v_nextMacroScope_4503_);
lean_inc(v_env_4502_);
lean_dec(v___x_4501_);
v___x_4511_ = lean_box(0);
v_isShared_4512_ = v_isSharedCheck_4563_;
goto v_resetjp_4510_;
}
v_resetjp_4510_:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; lean_object* v___x_4515_; lean_object* v___x_4517_; 
lean_inc(v_decl_3654_);
v___x_4513_ = l_Lean_Declaration_getNames(v_decl_3654_);
v___x_4514_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4502_, v___x_4513_);
v___x_4515_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4512_ == 0)
{
lean_ctor_set(v___x_4511_, 5, v___x_4515_);
lean_ctor_set(v___x_4511_, 0, v___x_4514_);
v___x_4517_ = v___x_4511_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4562_; 
v_reuseFailAlloc_4562_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4562_, 0, v___x_4514_);
lean_ctor_set(v_reuseFailAlloc_4562_, 1, v_nextMacroScope_4503_);
lean_ctor_set(v_reuseFailAlloc_4562_, 2, v_ngen_4504_);
lean_ctor_set(v_reuseFailAlloc_4562_, 3, v_auxDeclNGen_4505_);
lean_ctor_set(v_reuseFailAlloc_4562_, 4, v_traceState_4506_);
lean_ctor_set(v_reuseFailAlloc_4562_, 5, v___x_4515_);
lean_ctor_set(v_reuseFailAlloc_4562_, 6, v_messages_4507_);
lean_ctor_set(v_reuseFailAlloc_4562_, 7, v_infoState_4508_);
lean_ctor_set(v_reuseFailAlloc_4562_, 8, v_snapshotTasks_4509_);
v___x_4517_ = v_reuseFailAlloc_4562_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; lean_object* v___x_4521_; lean_object* v___f_4522_; 
v___x_4518_ = lean_st_ref_set(v_a_3657_, v___x_4517_);
v___x_4519_ = lean_box(0);
v___x_4520_ = lean_box(v___x_3865_);
v___x_4521_ = lean_box(v___x_4499_);
lean_inc(v_decl_3654_);
v___f_4522_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 11, 6);
lean_closure_set(v___f_4522_, 0, v_decl_3654_);
lean_closure_set(v___f_4522_, 1, v___x_4520_);
lean_closure_set(v___f_4522_, 2, v___x_4521_);
lean_closure_set(v___f_4522_, 3, v___x_4515_);
lean_closure_set(v___f_4522_, 4, v_cls_3714_);
lean_closure_set(v___f_4522_, 5, v___x_4519_);
switch(lean_obj_tag(v_decl_3654_))
{
case 2:
{
lean_object* v_val_4523_; lean_object* v___x_4524_; lean_object* v___f_4525_; lean_object* v___x_4526_; lean_object* v___f_4527_; uint8_t v___x_4528_; 
lean_del_object(v___x_4496_);
v_val_4523_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref_n(v_val_4523_, 3);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4524_ = lean_st_ref_get(v_a_3657_);
v___f_4525_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4525_, 0, v_val_4523_);
lean_closure_set(v___f_4525_, 1, v___f_4522_);
v___x_4526_ = lean_box(v___x_4499_);
lean_inc_ref(v___f_4525_);
v___f_4527_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4527_, 0, v_val_4523_);
lean_closure_set(v___f_4527_, 1, v___x_4526_);
lean_closure_set(v___f_4527_, 2, v___f_4525_);
v___x_4528_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4528_ == 0)
{
lean_dec(v___x_4524_);
v___y_4430_ = v___f_4525_;
v___y_4431_ = v___x_4519_;
v___y_4432_ = v___x_4500_;
v___y_4433_ = v___y_4492_;
v___y_4434_ = v___f_4527_;
v___y_4435_ = v_val_4523_;
v___y_4436_ = v_a_4494_;
v___y_4437_ = v___x_4528_;
goto v___jp_4429_;
}
else
{
lean_object* v_env_4529_; lean_object* v___x_4530_; uint8_t v_isModule_4531_; 
v_env_4529_ = lean_ctor_get(v___x_4524_, 0);
lean_inc_ref(v_env_4529_);
lean_dec(v___x_4524_);
v___x_4530_ = l_Lean_Environment_header(v_env_4529_);
lean_dec_ref(v_env_4529_);
v_isModule_4531_ = lean_ctor_get_uint8(v___x_4530_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4530_);
v___y_4430_ = v___f_4525_;
v___y_4431_ = v___x_4519_;
v___y_4432_ = v___x_4500_;
v___y_4433_ = v___y_4492_;
v___y_4434_ = v___f_4527_;
v___y_4435_ = v_val_4523_;
v___y_4436_ = v_a_4494_;
v___y_4437_ = v_isModule_4531_;
goto v___jp_4429_;
}
}
case 1:
{
lean_object* v_val_4532_; lean_object* v___x_4533_; 
lean_del_object(v___x_4496_);
v_val_4532_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref(v_val_4532_);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4533_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v___f_4522_, v___x_4519_, v_cls_3714_, v_forceExpose_3655_, v_val_4532_, v_a_3656_, v_a_3657_);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4533_;
goto v___jp_4401_;
}
case 5:
{
lean_object* v_defns_4534_; 
lean_del_object(v___x_4496_);
v_defns_4534_ = lean_ctor_get(v_decl_3654_, 0);
if (lean_obj_tag(v_defns_4534_) == 1)
{
lean_object* v_tail_4535_; 
v_tail_4535_ = lean_ctor_get(v_defns_4534_, 1);
if (lean_obj_tag(v_tail_4535_) == 0)
{
lean_object* v_head_4536_; lean_object* v___x_4537_; 
lean_inc_ref(v_defns_4534_);
lean_dec_ref_known(v_decl_3654_, 1);
v_head_4536_ = lean_ctor_get(v_defns_4534_, 0);
lean_inc(v_head_4536_);
lean_dec_ref_known(v_defns_4534_, 2);
v___x_4537_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v___f_4522_, v___x_4519_, v_cls_3714_, v_forceExpose_3655_, v_head_4536_, v_a_3656_, v_a_3657_);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4537_;
goto v___jp_4401_;
}
else
{
lean_object* v___x_4538_; 
lean_dec_ref(v___f_4522_);
lean_inc_ref(v_decl_3654_);
v___x_4538_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec_ref_known(v_decl_3654_, 1);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4538_;
goto v___jp_4401_;
}
}
else
{
lean_object* v___x_4539_; 
lean_dec_ref(v___f_4522_);
lean_inc_ref(v_decl_3654_);
v___x_4539_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec_ref_known(v_decl_3654_, 1);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4539_;
goto v___jp_4401_;
}
}
case 3:
{
lean_object* v_val_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v_env_4543_; lean_object* v___f_4544_; lean_object* v___f_4545_; uint8_t v___x_4546_; 
lean_del_object(v___x_4496_);
v_val_4540_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref_n(v_val_4540_, 3);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4541_ = lean_st_ref_get(v_a_3657_);
v___x_4542_ = lean_st_ref_get(v_a_3657_);
v_env_4543_ = lean_ctor_get(v___x_4542_, 0);
lean_inc_ref(v_env_4543_);
lean_dec(v___x_4542_);
v___f_4544_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4544_, 0, v_val_4540_);
lean_closure_set(v___f_4544_, 1, v___f_4522_);
lean_inc_ref(v___f_4544_);
v___f_4545_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4545_, 0, v_val_4540_);
lean_closure_set(v___f_4545_, 1, v___f_4544_);
v___x_4546_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4546_ == 0)
{
lean_dec(v___x_4541_);
v___y_4468_ = v_env_4543_;
v___y_4469_ = v___f_4544_;
v___y_4470_ = v___x_4519_;
v___y_4471_ = v_val_4540_;
v___y_4472_ = v___x_4500_;
v___y_4473_ = v___y_4492_;
v___y_4474_ = v___f_4545_;
v___y_4475_ = v_a_4494_;
v___y_4476_ = v___x_4546_;
goto v___jp_4467_;
}
else
{
lean_object* v_env_4547_; lean_object* v___x_4548_; uint8_t v_isModule_4549_; 
v_env_4547_ = lean_ctor_get(v___x_4541_, 0);
lean_inc_ref(v_env_4547_);
lean_dec(v___x_4541_);
v___x_4548_ = l_Lean_Environment_header(v_env_4547_);
lean_dec_ref(v_env_4547_);
v_isModule_4549_ = lean_ctor_get_uint8(v___x_4548_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4548_);
v___y_4468_ = v_env_4543_;
v___y_4469_ = v___f_4544_;
v___y_4470_ = v___x_4519_;
v___y_4471_ = v_val_4540_;
v___y_4472_ = v___x_4500_;
v___y_4473_ = v___y_4492_;
v___y_4474_ = v___f_4545_;
v___y_4475_ = v_a_4494_;
v___y_4476_ = v_isModule_4549_;
goto v___jp_4467_;
}
}
case 0:
{
lean_object* v_val_4550_; lean_object* v_toConstantVal_4551_; lean_object* v_name_4552_; lean_object* v___x_4554_; 
lean_dec_ref(v___f_4522_);
v_val_4550_ = lean_ctor_get(v_decl_3654_, 0);
v_toConstantVal_4551_ = lean_ctor_get(v_val_4550_, 0);
v_name_4552_ = lean_ctor_get(v_toConstantVal_4551_, 0);
lean_inc_ref(v_val_4550_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_val_4550_);
v___x_4554_ = v___x_4496_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_val_4550_);
v___x_4554_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
uint8_t v___x_4555_; lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; 
v___x_4555_ = 2;
v___x_4556_ = lean_box(v___x_4555_);
v___x_4557_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4557_, 0, v___x_4554_);
lean_ctor_set(v___x_4557_, 1, v___x_4556_);
lean_inc(v_name_4552_);
v___x_4558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4558_, 0, v_name_4552_);
lean_ctor_set(v___x_4558_, 1, v___x_4557_);
v___x_4559_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_decl_3654_, v___x_3865_, v___x_4499_, v___x_4515_, v_cls_3714_, v___x_4519_, v___x_4558_, v___x_4519_, v_a_3656_, v_a_3657_);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4559_;
goto v___jp_4401_;
}
}
default: 
{
lean_object* v___x_4561_; 
lean_dec_ref(v___f_4522_);
lean_del_object(v___x_4496_);
lean_inc(v_decl_3654_);
v___x_4561_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec(v_decl_3654_);
v___y_4402_ = v___x_4500_;
v___y_4403_ = v___y_4492_;
v___y_4404_ = v_a_4494_;
v___y_4405_ = v___x_4561_;
goto v___jp_4401_;
}
}
}
}
}
else
{
lean_object* v___x_4565_; lean_object* v___x_4566_; lean_object* v_env_4567_; lean_object* v_nextMacroScope_4568_; lean_object* v_ngen_4569_; lean_object* v_auxDeclNGen_4570_; lean_object* v_traceState_4571_; lean_object* v_messages_4572_; lean_object* v_infoState_4573_; lean_object* v_snapshotTasks_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4628_; 
v___x_4565_ = lean_io_get_num_heartbeats();
v___x_4566_ = lean_st_ref_take(v_a_3657_);
v_env_4567_ = lean_ctor_get(v___x_4566_, 0);
v_nextMacroScope_4568_ = lean_ctor_get(v___x_4566_, 1);
v_ngen_4569_ = lean_ctor_get(v___x_4566_, 2);
v_auxDeclNGen_4570_ = lean_ctor_get(v___x_4566_, 3);
v_traceState_4571_ = lean_ctor_get(v___x_4566_, 4);
v_messages_4572_ = lean_ctor_get(v___x_4566_, 6);
v_infoState_4573_ = lean_ctor_get(v___x_4566_, 7);
v_snapshotTasks_4574_ = lean_ctor_get(v___x_4566_, 8);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v___x_4566_, 5);
lean_dec(v_unused_4629_);
v___x_4576_ = v___x_4566_;
v_isShared_4577_ = v_isSharedCheck_4628_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snapshotTasks_4574_);
lean_inc(v_infoState_4573_);
lean_inc(v_messages_4572_);
lean_inc(v_traceState_4571_);
lean_inc(v_auxDeclNGen_4570_);
lean_inc(v_ngen_4569_);
lean_inc(v_nextMacroScope_4568_);
lean_inc(v_env_4567_);
lean_dec(v___x_4566_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4628_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
lean_inc(v_decl_3654_);
v___x_4578_ = l_Lean_Declaration_getNames(v_decl_3654_);
v___x_4579_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4567_, v___x_4578_);
v___x_4580_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 5, v___x_4580_);
lean_ctor_set(v___x_4576_, 0, v___x_4579_);
v___x_4582_ = v___x_4576_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v_nextMacroScope_4568_);
lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_ngen_4569_);
lean_ctor_set(v_reuseFailAlloc_4627_, 3, v_auxDeclNGen_4570_);
lean_ctor_set(v_reuseFailAlloc_4627_, 4, v_traceState_4571_);
lean_ctor_set(v_reuseFailAlloc_4627_, 5, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4627_, 6, v_messages_4572_);
lean_ctor_set(v_reuseFailAlloc_4627_, 7, v_infoState_4573_);
lean_ctor_set(v_reuseFailAlloc_4627_, 8, v_snapshotTasks_4574_);
v___x_4582_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v___x_4586_; lean_object* v___f_4587_; 
v___x_4583_ = lean_st_ref_set(v_a_3657_, v___x_4582_);
v___x_4584_ = lean_box(0);
v___x_4585_ = lean_box(v___x_4499_);
v___x_4586_ = lean_box(v___x_3728_);
lean_inc(v_decl_3654_);
v___f_4587_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 11, 6);
lean_closure_set(v___f_4587_, 0, v_decl_3654_);
lean_closure_set(v___f_4587_, 1, v___x_4585_);
lean_closure_set(v___f_4587_, 2, v___x_4586_);
lean_closure_set(v___f_4587_, 3, v_cls_3714_);
lean_closure_set(v___f_4587_, 4, v___x_4580_);
lean_closure_set(v___f_4587_, 5, v___x_4584_);
switch(lean_obj_tag(v_decl_3654_))
{
case 2:
{
lean_object* v_val_4588_; lean_object* v___x_4589_; lean_object* v___f_4590_; lean_object* v___x_4591_; lean_object* v___f_4592_; uint8_t v___x_4593_; 
lean_del_object(v___x_4496_);
v_val_4588_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref_n(v_val_4588_, 3);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4589_ = lean_st_ref_get(v_a_3657_);
v___f_4590_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4590_, 0, v_val_4588_);
lean_closure_set(v___f_4590_, 1, v___f_4587_);
v___x_4591_ = lean_box(v___x_3728_);
lean_inc_ref(v___f_4590_);
v___f_4592_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4592_, 0, v_val_4588_);
lean_closure_set(v___f_4592_, 1, v___x_4591_);
lean_closure_set(v___f_4592_, 2, v___f_4590_);
v___x_4593_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4593_ == 0)
{
lean_dec(v___x_4589_);
v___y_4363_ = v___f_4592_;
v___y_4364_ = v___x_4565_;
v___y_4365_ = v___y_4492_;
v___y_4366_ = v_val_4588_;
v___y_4367_ = v___x_4584_;
v___y_4368_ = v___f_4590_;
v___y_4369_ = v_a_4494_;
v___y_4370_ = v___x_4593_;
goto v___jp_4362_;
}
else
{
lean_object* v_env_4594_; lean_object* v___x_4595_; uint8_t v_isModule_4596_; 
v_env_4594_ = lean_ctor_get(v___x_4589_, 0);
lean_inc_ref(v_env_4594_);
lean_dec(v___x_4589_);
v___x_4595_ = l_Lean_Environment_header(v_env_4594_);
lean_dec_ref(v_env_4594_);
v_isModule_4596_ = lean_ctor_get_uint8(v___x_4595_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4595_);
v___y_4363_ = v___f_4592_;
v___y_4364_ = v___x_4565_;
v___y_4365_ = v___y_4492_;
v___y_4366_ = v_val_4588_;
v___y_4367_ = v___x_4584_;
v___y_4368_ = v___f_4590_;
v___y_4369_ = v_a_4494_;
v___y_4370_ = v_isModule_4596_;
goto v___jp_4362_;
}
}
case 1:
{
lean_object* v_val_4597_; lean_object* v___x_4598_; 
lean_del_object(v___x_4496_);
v_val_4597_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref(v_val_4597_);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4598_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v___f_4587_, v___x_4584_, v_cls_3714_, v_forceExpose_3655_, v_val_4597_, v_a_3656_, v_a_3657_);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4598_;
goto v___jp_4295_;
}
case 5:
{
lean_object* v_defns_4599_; 
lean_del_object(v___x_4496_);
v_defns_4599_ = lean_ctor_get(v_decl_3654_, 0);
if (lean_obj_tag(v_defns_4599_) == 1)
{
lean_object* v_tail_4600_; 
v_tail_4600_ = lean_ctor_get(v_defns_4599_, 1);
if (lean_obj_tag(v_tail_4600_) == 0)
{
lean_object* v_head_4601_; lean_object* v___x_4602_; 
lean_inc_ref(v_defns_4599_);
lean_dec_ref_known(v_decl_3654_, 1);
v_head_4601_ = lean_ctor_get(v_defns_4599_, 0);
lean_inc(v_head_4601_);
lean_dec_ref_known(v_defns_4599_, 2);
v___x_4602_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v___f_4587_, v___x_4584_, v_cls_3714_, v_forceExpose_3655_, v_head_4601_, v_a_3656_, v_a_3657_);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4602_;
goto v___jp_4295_;
}
else
{
lean_object* v___x_4603_; 
lean_dec_ref(v___f_4587_);
lean_inc_ref(v_decl_3654_);
v___x_4603_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec_ref_known(v_decl_3654_, 1);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4603_;
goto v___jp_4295_;
}
}
else
{
lean_object* v___x_4604_; 
lean_dec_ref(v___f_4587_);
lean_inc_ref(v_decl_3654_);
v___x_4604_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec_ref_known(v_decl_3654_, 1);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4604_;
goto v___jp_4295_;
}
}
case 3:
{
lean_object* v_val_4605_; lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v_env_4608_; lean_object* v___f_4609_; lean_object* v___f_4610_; uint8_t v___x_4611_; 
lean_del_object(v___x_4496_);
v_val_4605_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref_n(v_val_4605_, 3);
lean_dec_ref_known(v_decl_3654_, 1);
v___x_4606_ = lean_st_ref_get(v_a_3657_);
v___x_4607_ = lean_st_ref_get(v_a_3657_);
v_env_4608_ = lean_ctor_get(v___x_4607_, 0);
lean_inc_ref(v_env_4608_);
lean_dec(v___x_4607_);
v___f_4609_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4609_, 0, v_val_4605_);
lean_closure_set(v___f_4609_, 1, v___f_4587_);
lean_inc_ref(v___f_4609_);
v___f_4610_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4610_, 0, v_val_4605_);
lean_closure_set(v___f_4610_, 1, v___f_4609_);
v___x_4611_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4611_ == 0)
{
lean_dec(v___x_4606_);
v___y_4332_ = v___f_4609_;
v___y_4333_ = v___x_4565_;
v___y_4334_ = v___y_4492_;
v___y_4335_ = v___x_4584_;
v___y_4336_ = v_val_4605_;
v___y_4337_ = v___f_4610_;
v___y_4338_ = v_env_4608_;
v___y_4339_ = v_a_4494_;
v___y_4340_ = v___x_4611_;
goto v___jp_4331_;
}
else
{
lean_object* v_env_4612_; lean_object* v___x_4613_; uint8_t v_isModule_4614_; 
v_env_4612_ = lean_ctor_get(v___x_4606_, 0);
lean_inc_ref(v_env_4612_);
lean_dec(v___x_4606_);
v___x_4613_ = l_Lean_Environment_header(v_env_4612_);
lean_dec_ref(v_env_4612_);
v_isModule_4614_ = lean_ctor_get_uint8(v___x_4613_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4613_);
v___y_4332_ = v___f_4609_;
v___y_4333_ = v___x_4565_;
v___y_4334_ = v___y_4492_;
v___y_4335_ = v___x_4584_;
v___y_4336_ = v_val_4605_;
v___y_4337_ = v___f_4610_;
v___y_4338_ = v_env_4608_;
v___y_4339_ = v_a_4494_;
v___y_4340_ = v_isModule_4614_;
goto v___jp_4331_;
}
}
case 0:
{
lean_object* v_val_4615_; lean_object* v_toConstantVal_4616_; lean_object* v_name_4617_; lean_object* v___x_4619_; 
lean_dec_ref(v___f_4587_);
v_val_4615_ = lean_ctor_get(v_decl_3654_, 0);
v_toConstantVal_4616_ = lean_ctor_get(v_val_4615_, 0);
v_name_4617_ = lean_ctor_get(v_toConstantVal_4616_, 0);
lean_inc_ref(v_val_4615_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v_val_4615_);
v___x_4619_ = v___x_4496_;
goto v_reusejp_4618_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_val_4615_);
v___x_4619_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4618_;
}
v_reusejp_4618_:
{
uint8_t v___x_4620_; lean_object* v___x_4621_; lean_object* v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4620_ = 2;
v___x_4621_ = lean_box(v___x_4620_);
v___x_4622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4622_, 0, v___x_4619_);
lean_ctor_set(v___x_4622_, 1, v___x_4621_);
lean_inc(v_name_4617_);
v___x_4623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4623_, 0, v_name_4617_);
lean_ctor_set(v___x_4623_, 1, v___x_4622_);
v___x_4624_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3654_, v___x_4499_, v___x_3728_, v_cls_3714_, v___x_4580_, v___x_4584_, v___x_4623_, v___x_4584_, v_a_3656_, v_a_3657_);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4624_;
goto v___jp_4295_;
}
}
default: 
{
lean_object* v___x_4626_; 
lean_dec_ref(v___f_4587_);
lean_del_object(v___x_4496_);
lean_inc(v_decl_3654_);
v___x_4626_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_3654_, v_cls_3714_, v_decl_3654_, v_a_3656_, v_a_3657_);
lean_dec(v_decl_3654_);
v___y_4296_ = v___x_4565_;
v___y_4297_ = v___y_4492_;
v___y_4298_ = v_a_4494_;
v___y_4299_ = v___x_4626_;
goto v___jp_4295_;
}
}
}
}
}
}
}
v___jp_4631_:
{
lean_object* v___x_4633_; uint8_t v___x_4634_; 
v___x_4633_ = l_Lean_trace_profiler;
v___x_4634_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3711_, v___x_4633_);
if (v___x_4634_ == 0)
{
lean_object* v___x_4635_; lean_object* v_env_4636_; lean_object* v_nextMacroScope_4637_; lean_object* v_ngen_4638_; lean_object* v_auxDeclNGen_4639_; lean_object* v_traceState_4640_; lean_object* v_messages_4641_; lean_object* v_infoState_4642_; lean_object* v_snapshotTasks_4643_; lean_object* v___x_4645_; uint8_t v_isShared_4646_; uint8_t v_isSharedCheck_4678_; 
lean_dec_ref(v___f_3864_);
v___x_4635_ = lean_st_ref_take(v_a_3657_);
v_env_4636_ = lean_ctor_get(v___x_4635_, 0);
v_nextMacroScope_4637_ = lean_ctor_get(v___x_4635_, 1);
v_ngen_4638_ = lean_ctor_get(v___x_4635_, 2);
v_auxDeclNGen_4639_ = lean_ctor_get(v___x_4635_, 3);
v_traceState_4640_ = lean_ctor_get(v___x_4635_, 4);
v_messages_4641_ = lean_ctor_get(v___x_4635_, 6);
v_infoState_4642_ = lean_ctor_get(v___x_4635_, 7);
v_snapshotTasks_4643_ = lean_ctor_get(v___x_4635_, 8);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4635_);
if (v_isSharedCheck_4678_ == 0)
{
lean_object* v_unused_4679_; 
v_unused_4679_ = lean_ctor_get(v___x_4635_, 5);
lean_dec(v_unused_4679_);
v___x_4645_ = v___x_4635_;
v_isShared_4646_ = v_isSharedCheck_4678_;
goto v_resetjp_4644_;
}
else
{
lean_inc(v_snapshotTasks_4643_);
lean_inc(v_infoState_4642_);
lean_inc(v_messages_4641_);
lean_inc(v_traceState_4640_);
lean_inc(v_auxDeclNGen_4639_);
lean_inc(v_ngen_4638_);
lean_inc(v_nextMacroScope_4637_);
lean_inc(v_env_4636_);
lean_dec(v___x_4635_);
v___x_4645_ = lean_box(0);
v_isShared_4646_ = v_isSharedCheck_4678_;
goto v_resetjp_4644_;
}
v_resetjp_4644_:
{
lean_object* v___x_4647_; lean_object* v___x_4648_; lean_object* v___x_4649_; lean_object* v___x_4651_; 
lean_inc(v_decl_3654_);
v___x_4647_ = l_Lean_Declaration_getNames(v_decl_3654_);
v___x_4648_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4636_, v___x_4647_);
v___x_4649_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4646_ == 0)
{
lean_ctor_set(v___x_4645_, 5, v___x_4649_);
lean_ctor_set(v___x_4645_, 0, v___x_4648_);
v___x_4651_ = v___x_4645_;
goto v_reusejp_4650_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4648_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_nextMacroScope_4637_);
lean_ctor_set(v_reuseFailAlloc_4677_, 2, v_ngen_4638_);
lean_ctor_set(v_reuseFailAlloc_4677_, 3, v_auxDeclNGen_4639_);
lean_ctor_set(v_reuseFailAlloc_4677_, 4, v_traceState_4640_);
lean_ctor_set(v_reuseFailAlloc_4677_, 5, v___x_4649_);
lean_ctor_set(v_reuseFailAlloc_4677_, 6, v_messages_4641_);
lean_ctor_set(v_reuseFailAlloc_4677_, 7, v_infoState_4642_);
lean_ctor_set(v_reuseFailAlloc_4677_, 8, v_snapshotTasks_4643_);
v___x_4651_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4650_;
}
v_reusejp_4650_:
{
lean_object* v___x_4652_; lean_object* v___x_4653_; 
v___x_4652_ = lean_st_ref_set(v_a_3657_, v___x_4651_);
v___x_4653_ = lean_box(0);
switch(lean_obj_tag(v_decl_3654_))
{
case 2:
{
lean_object* v_val_4654_; lean_object* v___x_4655_; uint8_t v___x_4656_; 
v_val_4654_ = lean_ctor_get(v_decl_3654_, 0);
v___x_4655_ = lean_st_ref_get(v_a_3657_);
v___x_4656_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4656_ == 0)
{
lean_dec(v___x_4655_);
lean_inc_ref(v_val_4654_);
v___y_4182_ = v_val_4654_;
v___y_4183_ = v___x_4634_;
v___y_4184_ = v___x_4653_;
v___y_4185_ = v___x_4649_;
v___y_4186_ = v___x_4656_;
goto v___jp_4181_;
}
else
{
lean_object* v_env_4657_; lean_object* v___x_4658_; uint8_t v_isModule_4659_; 
v_env_4657_ = lean_ctor_get(v___x_4655_, 0);
lean_inc_ref(v_env_4657_);
lean_dec(v___x_4655_);
v___x_4658_ = l_Lean_Environment_header(v_env_4657_);
lean_dec_ref(v_env_4657_);
v_isModule_4659_ = lean_ctor_get_uint8(v___x_4658_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4658_);
lean_inc_ref(v_val_4654_);
v___y_4182_ = v_val_4654_;
v___y_4183_ = v___x_4634_;
v___y_4184_ = v___x_4653_;
v___y_4185_ = v___x_4649_;
v___y_4186_ = v_isModule_4659_;
goto v___jp_4181_;
}
}
case 1:
{
lean_object* v_val_4660_; 
v_val_4660_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref(v_val_4660_);
v___y_4268_ = v___x_4634_;
v___y_4269_ = v___x_4653_;
v___y_4270_ = v___x_4649_;
v_defn_4271_ = v_val_4660_;
v___y_4272_ = v_a_3656_;
v___y_4273_ = v_a_3657_;
goto v___jp_4267_;
}
case 5:
{
lean_object* v_defns_4661_; 
v_defns_4661_ = lean_ctor_get(v_decl_3654_, 0);
if (lean_obj_tag(v_defns_4661_) == 1)
{
lean_object* v_tail_4662_; 
v_tail_4662_ = lean_ctor_get(v_defns_4661_, 1);
if (lean_obj_tag(v_tail_4662_) == 0)
{
lean_object* v_head_4663_; 
v_head_4663_ = lean_ctor_get(v_defns_4661_, 0);
lean_inc(v_head_4663_);
v___y_4268_ = v___x_4634_;
v___y_4269_ = v___x_4653_;
v___y_4270_ = v___x_4649_;
v_defn_4271_ = v_head_4663_;
v___y_4272_ = v_a_3656_;
v___y_4273_ = v_a_3657_;
goto v___jp_4267_;
}
else
{
v___y_3716_ = v_a_3656_;
v_options_3717_ = v_options_3711_;
v_hasTrace_3718_ = v_hasTrace_3713_;
v_inheritedTraceOptions_3719_ = v_inheritedTraceOptions_3712_;
v___y_3720_ = v_a_3657_;
goto v___jp_3715_;
}
}
else
{
v___y_3716_ = v_a_3656_;
v_options_3717_ = v_options_3711_;
v_hasTrace_3718_ = v_hasTrace_3713_;
v_inheritedTraceOptions_3719_ = v_inheritedTraceOptions_3712_;
v___y_3720_ = v_a_3657_;
goto v___jp_3715_;
}
}
case 3:
{
lean_object* v_val_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v_env_4667_; uint8_t v___x_4668_; 
v_val_4664_ = lean_ctor_get(v_decl_3654_, 0);
v___x_4665_ = lean_st_ref_get(v_a_3657_);
v___x_4666_ = lean_st_ref_get(v_a_3657_);
v_env_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc_ref(v_env_4667_);
lean_dec(v___x_4666_);
v___x_4668_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4668_ == 0)
{
lean_dec(v___x_4665_);
lean_inc_ref(v_val_4664_);
v___y_4131_ = v_env_4667_;
v___y_4132_ = v___x_4634_;
v___y_4133_ = v_val_4664_;
v___y_4134_ = v___x_4653_;
v___y_4135_ = v___x_4649_;
v___y_4136_ = v___x_4668_;
goto v___jp_4130_;
}
else
{
lean_object* v_env_4669_; lean_object* v___x_4670_; uint8_t v_isModule_4671_; 
v_env_4669_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_ref(v_env_4669_);
lean_dec(v___x_4665_);
v___x_4670_ = l_Lean_Environment_header(v_env_4669_);
lean_dec_ref(v_env_4669_);
v_isModule_4671_ = lean_ctor_get_uint8(v___x_4670_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4670_);
lean_inc_ref(v_val_4664_);
v___y_4131_ = v_env_4667_;
v___y_4132_ = v___x_4634_;
v___y_4133_ = v_val_4664_;
v___y_4134_ = v___x_4653_;
v___y_4135_ = v___x_4649_;
v___y_4136_ = v_isModule_4671_;
goto v___jp_4130_;
}
}
case 0:
{
lean_object* v_val_4672_; lean_object* v_toConstantVal_4673_; lean_object* v_name_4674_; lean_object* v___x_4675_; uint8_t v___x_4676_; 
v_val_4672_ = lean_ctor_get(v_decl_3654_, 0);
v_toConstantVal_4673_ = lean_ctor_get(v_val_4672_, 0);
v_name_4674_ = lean_ctor_get(v_toConstantVal_4673_, 0);
lean_inc_ref(v_val_4672_);
v___x_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4675_, 0, v_val_4672_);
v___x_4676_ = 2;
lean_inc(v_name_4674_);
v___y_4071_ = v___x_4634_;
v___y_4072_ = v___x_4653_;
v___y_4073_ = v___x_4649_;
v_fst_4074_ = v_name_4674_;
v_fst_4075_ = v___x_4675_;
v_snd_4076_ = v___x_4676_;
v_exportedInfo_x3f_4077_ = v___x_4653_;
v___y_4078_ = v_a_3656_;
v___y_4079_ = v_a_3657_;
goto v___jp_4070_;
}
default: 
{
v___y_3716_ = v_a_3656_;
v_options_3717_ = v_options_3711_;
v_hasTrace_3718_ = v_hasTrace_3713_;
v_inheritedTraceOptions_3719_ = v_inheritedTraceOptions_3712_;
v___y_3720_ = v_a_3657_;
goto v___jp_3715_;
}
}
}
}
}
else
{
v___y_4492_ = v_a_4632_;
goto v___jp_4491_;
}
}
}
else
{
lean_object* v___x_4682_; lean_object* v_env_4683_; lean_object* v_nextMacroScope_4684_; lean_object* v_ngen_4685_; lean_object* v_auxDeclNGen_4686_; lean_object* v_traceState_4687_; lean_object* v_messages_4688_; lean_object* v_infoState_4689_; lean_object* v_snapshotTasks_4690_; lean_object* v___x_4692_; uint8_t v_isShared_4693_; uint8_t v_isSharedCheck_4939_; 
v___x_4682_ = lean_st_ref_take(v_a_3657_);
v_env_4683_ = lean_ctor_get(v___x_4682_, 0);
v_nextMacroScope_4684_ = lean_ctor_get(v___x_4682_, 1);
v_ngen_4685_ = lean_ctor_get(v___x_4682_, 2);
v_auxDeclNGen_4686_ = lean_ctor_get(v___x_4682_, 3);
v_traceState_4687_ = lean_ctor_get(v___x_4682_, 4);
v_messages_4688_ = lean_ctor_get(v___x_4682_, 6);
v_infoState_4689_ = lean_ctor_get(v___x_4682_, 7);
v_snapshotTasks_4690_ = lean_ctor_get(v___x_4682_, 8);
v_isSharedCheck_4939_ = !lean_is_exclusive(v___x_4682_);
if (v_isSharedCheck_4939_ == 0)
{
lean_object* v_unused_4940_; 
v_unused_4940_ = lean_ctor_get(v___x_4682_, 5);
lean_dec(v_unused_4940_);
v___x_4692_ = v___x_4682_;
v_isShared_4693_ = v_isSharedCheck_4939_;
goto v_resetjp_4691_;
}
else
{
lean_inc(v_snapshotTasks_4690_);
lean_inc(v_infoState_4689_);
lean_inc(v_messages_4688_);
lean_inc(v_traceState_4687_);
lean_inc(v_auxDeclNGen_4686_);
lean_inc(v_ngen_4685_);
lean_inc(v_nextMacroScope_4684_);
lean_inc(v_env_4683_);
lean_dec(v___x_4682_);
v___x_4692_ = lean_box(0);
v_isShared_4693_ = v_isSharedCheck_4939_;
goto v_resetjp_4691_;
}
v_resetjp_4691_:
{
lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4700_; uint8_t v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; uint8_t v___y_4704_; lean_object* v___x_4734_; 
lean_inc(v_decl_3654_);
v___x_4694_ = l_Lean_Declaration_getNames(v_decl_3654_);
v___x_4695_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4683_, v___x_4694_);
v___x_4696_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4693_ == 0)
{
lean_ctor_set(v___x_4692_, 5, v___x_4696_);
lean_ctor_set(v___x_4692_, 0, v___x_4695_);
v___x_4734_ = v___x_4692_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4938_; 
v_reuseFailAlloc_4938_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4938_, 0, v___x_4695_);
lean_ctor_set(v_reuseFailAlloc_4938_, 1, v_nextMacroScope_4684_);
lean_ctor_set(v_reuseFailAlloc_4938_, 2, v_ngen_4685_);
lean_ctor_set(v_reuseFailAlloc_4938_, 3, v_auxDeclNGen_4686_);
lean_ctor_set(v_reuseFailAlloc_4938_, 4, v_traceState_4687_);
lean_ctor_set(v_reuseFailAlloc_4938_, 5, v___x_4696_);
lean_ctor_set(v_reuseFailAlloc_4938_, 6, v_messages_4688_);
lean_ctor_set(v_reuseFailAlloc_4938_, 7, v_infoState_4689_);
lean_ctor_set(v_reuseFailAlloc_4938_, 8, v_snapshotTasks_4690_);
v___x_4734_ = v_reuseFailAlloc_4938_;
goto v_reusejp_4733_;
}
v___jp_4697_:
{
if (v___y_4704_ == 0)
{
lean_object* v_options_4705_; uint8_t v_hasTrace_4706_; 
lean_dec(v___y_4699_);
v_options_4705_ = lean_ctor_get(v___y_4698_, 2);
v_hasTrace_4706_ = lean_ctor_get_uint8(v_options_4705_, sizeof(void*)*1);
if (v_hasTrace_4706_ == 0)
{
v___y_3858_ = v___y_4700_;
v___y_3859_ = v___y_4701_;
v___y_3860_ = v___y_4702_;
v___y_3861_ = v___y_4698_;
v___y_3862_ = v___y_4703_;
goto v___jp_3857_;
}
else
{
lean_object* v_inheritedTraceOptions_4707_; lean_object* v___x_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4707_ = lean_ctor_get(v___y_4698_, 13);
v___x_4708_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4707_, v_options_4705_, v___x_4708_);
if (v___x_4709_ == 0)
{
v___y_3858_ = v___y_4700_;
v___y_3859_ = v___y_4701_;
v___y_3860_ = v___y_4702_;
v___y_3861_ = v___y_4698_;
v___y_3862_ = v___y_4703_;
goto v___jp_3857_;
}
else
{
lean_object* v___x_4710_; lean_object* v___x_4711_; 
v___x_4710_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__3);
v___x_4711_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4710_, v___y_4698_, v___y_4703_);
if (lean_obj_tag(v___x_4711_) == 0)
{
lean_dec_ref_known(v___x_4711_, 1);
v___y_3858_ = v___y_4700_;
v___y_3859_ = v___y_4701_;
v___y_3860_ = v___y_4702_;
v___y_3861_ = v___y_4698_;
v___y_3862_ = v___y_4703_;
goto v___jp_3857_;
}
else
{
lean_dec_ref(v___y_4702_);
lean_dec(v___y_4700_);
lean_dec(v_decl_3654_);
return v___x_4711_;
}
}
}
}
else
{
lean_object* v___x_4712_; lean_object* v_env_4713_; lean_object* v_nextMacroScope_4714_; lean_object* v_ngen_4715_; lean_object* v_auxDeclNGen_4716_; lean_object* v_traceState_4717_; lean_object* v_messages_4718_; lean_object* v_infoState_4719_; lean_object* v_snapshotTasks_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4731_; 
v___x_4712_ = lean_st_ref_take(v___y_4703_);
v_env_4713_ = lean_ctor_get(v___x_4712_, 0);
v_nextMacroScope_4714_ = lean_ctor_get(v___x_4712_, 1);
v_ngen_4715_ = lean_ctor_get(v___x_4712_, 2);
v_auxDeclNGen_4716_ = lean_ctor_get(v___x_4712_, 3);
v_traceState_4717_ = lean_ctor_get(v___x_4712_, 4);
v_messages_4718_ = lean_ctor_get(v___x_4712_, 6);
v_infoState_4719_ = lean_ctor_get(v___x_4712_, 7);
v_snapshotTasks_4720_ = lean_ctor_get(v___x_4712_, 8);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4731_ == 0)
{
lean_object* v_unused_4732_; 
v_unused_4732_ = lean_ctor_get(v___x_4712_, 5);
lean_dec(v_unused_4732_);
v___x_4722_ = v___x_4712_;
v_isShared_4723_ = v_isSharedCheck_4731_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_snapshotTasks_4720_);
lean_inc(v_infoState_4719_);
lean_inc(v_messages_4718_);
lean_inc(v_traceState_4717_);
lean_inc(v_auxDeclNGen_4716_);
lean_inc(v_ngen_4715_);
lean_inc(v_nextMacroScope_4714_);
lean_inc(v_env_4713_);
lean_dec(v___x_4712_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4731_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4728_; 
v___x_4724_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4725_ = lean_box(v___y_4701_);
lean_inc(v___y_4700_);
v___x_4726_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4724_, v_env_4713_, v___y_4700_, v___x_4725_);
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 5, v___x_4696_);
lean_ctor_set(v___x_4722_, 0, v___x_4726_);
v___x_4728_ = v___x_4722_;
goto v_reusejp_4727_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v___x_4726_);
lean_ctor_set(v_reuseFailAlloc_4730_, 1, v_nextMacroScope_4714_);
lean_ctor_set(v_reuseFailAlloc_4730_, 2, v_ngen_4715_);
lean_ctor_set(v_reuseFailAlloc_4730_, 3, v_auxDeclNGen_4716_);
lean_ctor_set(v_reuseFailAlloc_4730_, 4, v_traceState_4717_);
lean_ctor_set(v_reuseFailAlloc_4730_, 5, v___x_4696_);
lean_ctor_set(v_reuseFailAlloc_4730_, 6, v_messages_4718_);
lean_ctor_set(v_reuseFailAlloc_4730_, 7, v_infoState_4719_);
lean_ctor_set(v_reuseFailAlloc_4730_, 8, v_snapshotTasks_4720_);
v___x_4728_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4727_;
}
v_reusejp_4727_:
{
lean_object* v___x_4729_; 
v___x_4729_ = lean_st_ref_set(v___y_4703_, v___x_4728_);
v___y_3836_ = v___y_4700_;
v___y_3837_ = v___y_4701_;
v___y_3838_ = v___y_4702_;
v_exportedInfo_x3f_3839_ = v___y_4699_;
v___y_3840_ = v___y_4698_;
v___y_3841_ = v___y_4703_;
goto v___jp_3835_;
}
}
}
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; lean_object* v___y_4737_; lean_object* v_options_4738_; uint8_t v_hasTrace_4739_; lean_object* v_inheritedTraceOptions_4740_; lean_object* v___y_4741_; lean_object* v___x_4749_; lean_object* v___y_4751_; lean_object* v___y_4752_; uint8_t v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v_fst_4778_; lean_object* v_fst_4779_; uint8_t v_snd_4780_; lean_object* v_exportedInfo_x3f_4781_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___y_4793_; lean_object* v_toConstantVal_4794_; lean_object* v_exportedInfo_x3f_4795_; lean_object* v___y_4796_; lean_object* v___y_4797_; lean_object* v___y_4802_; lean_object* v_exportedInfo_x3f_4803_; lean_object* v___y_4804_; lean_object* v___y_4805_; lean_object* v___y_4808_; lean_object* v_toConstantVal_4809_; uint8_t v_safety_4810_; lean_object* v___y_4811_; lean_object* v___y_4812_; lean_object* v___y_4819_; lean_object* v___y_4820_; lean_object* v___y_4821_; lean_object* v___y_4825_; lean_object* v___y_4826_; lean_object* v___y_4827_; lean_object* v___y_4828_; uint8_t v___y_4829_; lean_object* v_defn_4847_; lean_object* v___y_4848_; lean_object* v___y_4849_; 
v___x_4735_ = lean_st_ref_set(v_a_3657_, v___x_4734_);
v___x_4749_ = lean_box(0);
switch(lean_obj_tag(v_decl_3654_))
{
case 2:
{
lean_object* v_val_4857_; lean_object* v_exportedInfo_x3f_4859_; lean_object* v___y_4860_; lean_object* v___y_4861_; lean_object* v___y_4867_; lean_object* v___y_4868_; lean_object* v___x_4874_; uint8_t v___y_4876_; uint8_t v___x_4887_; 
v_val_4857_ = lean_ctor_get(v_decl_3654_, 0);
v___x_4874_ = lean_st_ref_get(v_a_3657_);
v___x_4887_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4887_ == 0)
{
lean_dec(v___x_4874_);
v___y_4876_ = v___x_4887_;
goto v___jp_4875_;
}
else
{
lean_object* v_env_4888_; lean_object* v___x_4889_; uint8_t v_isModule_4890_; 
v_env_4888_ = lean_ctor_get(v___x_4874_, 0);
lean_inc_ref(v_env_4888_);
lean_dec(v___x_4874_);
v___x_4889_ = l_Lean_Environment_header(v_env_4888_);
lean_dec_ref(v_env_4888_);
v_isModule_4890_ = lean_ctor_get_uint8(v___x_4889_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4889_);
v___y_4876_ = v_isModule_4890_;
goto v___jp_4875_;
}
v___jp_4858_:
{
lean_object* v_toConstantVal_4862_; lean_object* v_name_4863_; lean_object* v___x_4864_; uint8_t v___x_4865_; 
v_toConstantVal_4862_ = lean_ctor_get(v_val_4857_, 0);
v_name_4863_ = lean_ctor_get(v_toConstantVal_4862_, 0);
lean_inc_ref(v_val_4857_);
v___x_4864_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4864_, 0, v_val_4857_);
v___x_4865_ = 1;
lean_inc(v_name_4863_);
v_fst_4778_ = v_name_4863_;
v_fst_4779_ = v___x_4864_;
v_snd_4780_ = v___x_4865_;
v_exportedInfo_x3f_4781_ = v_exportedInfo_x3f_4859_;
v___y_4782_ = v___y_4860_;
v___y_4783_ = v___y_4861_;
goto v___jp_4777_;
}
v___jp_4866_:
{
lean_object* v_toConstantVal_4869_; uint8_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; 
v_toConstantVal_4869_ = lean_ctor_get(v_val_4857_, 0);
v___x_4870_ = 0;
lean_inc_ref(v_toConstantVal_4869_);
v___x_4871_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4871_, 0, v_toConstantVal_4869_);
lean_ctor_set_uint8(v___x_4871_, sizeof(void*)*1, v___x_4870_);
v___x_4872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4871_);
v___x_4873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4872_);
v_exportedInfo_x3f_4859_ = v___x_4873_;
v___y_4860_ = v___y_4867_;
v___y_4861_ = v___y_4868_;
goto v___jp_4858_;
}
v___jp_4875_:
{
if (v___y_4876_ == 0)
{
v_exportedInfo_x3f_4859_ = v___x_4749_;
v___y_4860_ = v_a_3656_;
v___y_4861_ = v_a_3657_;
goto v___jp_4858_;
}
else
{
if (v_hasTrace_3713_ == 0)
{
v___y_4867_ = v_a_3656_;
v___y_4868_ = v_a_3657_;
goto v___jp_4866_;
}
else
{
lean_object* v___x_4877_; uint8_t v___x_4878_; 
v___x_4877_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4878_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4877_);
if (v___x_4878_ == 0)
{
v___y_4867_ = v_a_3656_;
v___y_4868_ = v_a_3657_;
goto v___jp_4866_;
}
else
{
lean_object* v_toConstantVal_4879_; lean_object* v_name_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; 
v_toConstantVal_4879_ = lean_ctor_get(v_val_4857_, 0);
v_name_4880_ = lean_ctor_get(v_toConstantVal_4879_, 0);
v___x_4881_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__5);
lean_inc(v_name_4880_);
v___x_4882_ = l_Lean_MessageData_ofName(v_name_4880_);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4885_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4885_, 0, v___x_4883_);
lean_ctor_set(v___x_4885_, 1, v___x_4884_);
v___x_4886_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4885_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_dec_ref_known(v___x_4886_, 1);
v___y_4867_ = v_a_3656_;
v___y_4868_ = v_a_3657_;
goto v___jp_4866_;
}
else
{
lean_dec_ref_known(v_decl_3654_, 1);
return v___x_4886_;
}
}
}
}
}
}
case 1:
{
lean_object* v_val_4891_; 
v_val_4891_ = lean_ctor_get(v_decl_3654_, 0);
lean_inc_ref(v_val_4891_);
v_defn_4847_ = v_val_4891_;
v___y_4848_ = v_a_3656_;
v___y_4849_ = v_a_3657_;
goto v___jp_4846_;
}
case 5:
{
lean_object* v_defns_4892_; 
v_defns_4892_ = lean_ctor_get(v_decl_3654_, 0);
if (lean_obj_tag(v_defns_4892_) == 1)
{
lean_object* v_tail_4893_; 
v_tail_4893_ = lean_ctor_get(v_defns_4892_, 1);
if (lean_obj_tag(v_tail_4893_) == 0)
{
lean_object* v_head_4894_; 
v_head_4894_ = lean_ctor_get(v_defns_4892_, 0);
lean_inc(v_head_4894_);
v_defn_4847_ = v_head_4894_;
v___y_4848_ = v_a_3656_;
v___y_4849_ = v_a_3657_;
goto v___jp_4846_;
}
else
{
v___y_4737_ = v_a_3656_;
v_options_4738_ = v_options_3711_;
v_hasTrace_4739_ = v_hasTrace_3713_;
v_inheritedTraceOptions_4740_ = v_inheritedTraceOptions_3712_;
v___y_4741_ = v_a_3657_;
goto v___jp_4736_;
}
}
else
{
v___y_4737_ = v_a_3656_;
v_options_4738_ = v_options_3711_;
v_hasTrace_4739_ = v_hasTrace_3713_;
v_inheritedTraceOptions_4740_ = v_inheritedTraceOptions_3712_;
v___y_4741_ = v_a_3657_;
goto v___jp_4736_;
}
}
case 3:
{
lean_object* v_val_4895_; lean_object* v_exportedInfo_x3f_4897_; lean_object* v___y_4898_; lean_object* v___y_4899_; lean_object* v___y_4905_; lean_object* v___y_4906_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v_env_4914_; uint8_t v___y_4916_; uint8_t v___x_4929_; 
v_val_4895_ = lean_ctor_get(v_decl_3654_, 0);
v___x_4912_ = lean_st_ref_get(v_a_3657_);
v___x_4913_ = lean_st_ref_get(v_a_3657_);
v_env_4914_ = lean_ctor_get(v___x_4913_, 0);
lean_inc_ref(v_env_4914_);
lean_dec(v___x_4913_);
v___x_4929_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4929_ == 0)
{
lean_dec(v___x_4912_);
v___y_4916_ = v___x_4929_;
goto v___jp_4915_;
}
else
{
lean_object* v_env_4930_; lean_object* v___x_4931_; uint8_t v_isModule_4932_; 
v_env_4930_ = lean_ctor_get(v___x_4912_, 0);
lean_inc_ref(v_env_4930_);
lean_dec(v___x_4912_);
v___x_4931_ = l_Lean_Environment_header(v_env_4930_);
lean_dec_ref(v_env_4930_);
v_isModule_4932_ = lean_ctor_get_uint8(v___x_4931_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4931_);
v___y_4916_ = v_isModule_4932_;
goto v___jp_4915_;
}
v___jp_4896_:
{
lean_object* v_toConstantVal_4900_; lean_object* v_name_4901_; lean_object* v___x_4902_; uint8_t v___x_4903_; 
v_toConstantVal_4900_ = lean_ctor_get(v_val_4895_, 0);
v_name_4901_ = lean_ctor_get(v_toConstantVal_4900_, 0);
lean_inc_ref(v_val_4895_);
v___x_4902_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4902_, 0, v_val_4895_);
v___x_4903_ = 3;
lean_inc(v_name_4901_);
v_fst_4778_ = v_name_4901_;
v_fst_4779_ = v___x_4902_;
v_snd_4780_ = v___x_4903_;
v_exportedInfo_x3f_4781_ = v_exportedInfo_x3f_4897_;
v___y_4782_ = v___y_4898_;
v___y_4783_ = v___y_4899_;
goto v___jp_4777_;
}
v___jp_4904_:
{
lean_object* v_toConstantVal_4907_; uint8_t v_isUnsafe_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; 
v_toConstantVal_4907_ = lean_ctor_get(v_val_4895_, 0);
v_isUnsafe_4908_ = lean_ctor_get_uint8(v_val_4895_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4907_);
v___x_4909_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4909_, 0, v_toConstantVal_4907_);
lean_ctor_set_uint8(v___x_4909_, sizeof(void*)*1, v_isUnsafe_4908_);
v___x_4910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4910_, 0, v___x_4909_);
v___x_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4911_, 0, v___x_4910_);
v_exportedInfo_x3f_4897_ = v___x_4911_;
v___y_4898_ = v___y_4905_;
v___y_4899_ = v___y_4906_;
goto v___jp_4896_;
}
v___jp_4915_:
{
if (v___y_4916_ == 0)
{
lean_dec_ref(v_env_4914_);
v_exportedInfo_x3f_4897_ = v___x_4749_;
v___y_4898_ = v_a_3656_;
v___y_4899_ = v_a_3657_;
goto v___jp_4896_;
}
else
{
uint8_t v_isExporting_4917_; uint8_t v___x_4918_; 
v_isExporting_4917_ = lean_ctor_get_uint8(v_env_4914_, sizeof(void*)*8);
lean_dec_ref(v_env_4914_);
v___x_4918_ = lean_bool_not(v_isExporting_4917_);
if (v___x_4918_ == 0)
{
v_exportedInfo_x3f_4897_ = v___x_4749_;
v___y_4898_ = v_a_3656_;
v___y_4899_ = v_a_3657_;
goto v___jp_4896_;
}
else
{
if (v_hasTrace_3713_ == 0)
{
v___y_4905_ = v_a_3656_;
v___y_4906_ = v_a_3657_;
goto v___jp_4904_;
}
else
{
lean_object* v___x_4919_; uint8_t v___x_4920_; 
v___x_4919_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3712_, v_options_3711_, v___x_4919_);
if (v___x_4920_ == 0)
{
v___y_4905_ = v_a_3656_;
v___y_4906_ = v_a_3657_;
goto v___jp_4904_;
}
else
{
lean_object* v_toConstantVal_4921_; lean_object* v_name_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; 
v_toConstantVal_4921_ = lean_ctor_get(v_val_4895_, 0);
v_name_4922_ = lean_ctor_get(v_toConstantVal_4921_, 0);
v___x_4923_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3);
lean_inc(v_name_4922_);
v___x_4924_ = l_Lean_MessageData_ofName(v_name_4922_);
v___x_4925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4923_);
lean_ctor_set(v___x_4925_, 1, v___x_4924_);
v___x_4926_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4927_, 0, v___x_4925_);
lean_ctor_set(v___x_4927_, 1, v___x_4926_);
v___x_4928_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4927_, v_a_3656_, v_a_3657_);
if (lean_obj_tag(v___x_4928_) == 0)
{
lean_dec_ref_known(v___x_4928_, 1);
v___y_4905_ = v_a_3656_;
v___y_4906_ = v_a_3657_;
goto v___jp_4904_;
}
else
{
lean_dec_ref_known(v_decl_3654_, 1);
return v___x_4928_;
}
}
}
}
}
}
}
case 0:
{
lean_object* v_val_4933_; lean_object* v_toConstantVal_4934_; lean_object* v_name_4935_; lean_object* v___x_4936_; uint8_t v___x_4937_; 
v_val_4933_ = lean_ctor_get(v_decl_3654_, 0);
v_toConstantVal_4934_ = lean_ctor_get(v_val_4933_, 0);
v_name_4935_ = lean_ctor_get(v_toConstantVal_4934_, 0);
lean_inc_ref(v_val_4933_);
v___x_4936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4936_, 0, v_val_4933_);
v___x_4937_ = 2;
lean_inc(v_name_4935_);
v_fst_4778_ = v_name_4935_;
v_fst_4779_ = v___x_4936_;
v_snd_4780_ = v___x_4937_;
v_exportedInfo_x3f_4781_ = v___x_4749_;
v___y_4782_ = v_a_3656_;
v___y_4783_ = v_a_3657_;
goto v___jp_4777_;
}
default: 
{
v___y_4737_ = v_a_3656_;
v_options_4738_ = v_options_3711_;
v_hasTrace_4739_ = v_hasTrace_3713_;
v_inheritedTraceOptions_4740_ = v_inheritedTraceOptions_3712_;
v___y_4741_ = v_a_3657_;
goto v___jp_4736_;
}
}
v___jp_4736_:
{
if (v_hasTrace_4739_ == 0)
{
lean_object* v___x_4742_; 
v___x_4742_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_4737_, v___y_4741_);
return v___x_4742_;
}
else
{
lean_object* v___x_4743_; uint8_t v___x_4744_; 
v___x_4743_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4744_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4740_, v_options_4738_, v___x_4743_);
if (v___x_4744_ == 0)
{
lean_object* v___x_4745_; 
v___x_4745_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_4737_, v___y_4741_);
return v___x_4745_;
}
else
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_4747_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4746_, v___y_4737_, v___y_4741_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_object* v___x_4748_; 
lean_dec_ref_known(v___x_4747_, 1);
v___x_4748_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_4737_, v___y_4741_);
return v___x_4748_;
}
else
{
lean_dec(v_decl_3654_);
return v___x_4747_;
}
}
}
}
v___jp_4750_:
{
lean_object* v___x_4757_; uint8_t v___x_4758_; 
lean_inc(v_decl_3654_);
v___x_4757_ = l_Lean_Declaration_getTopLevelNames(v_decl_3654_);
v___x_4758_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4757_);
lean_dec(v___x_4757_);
if (v___x_4758_ == 0)
{
if (lean_obj_tag(v___y_4751_) == 0)
{
v___y_4698_ = v___y_4755_;
v___y_4699_ = v___y_4751_;
v___y_4700_ = v___y_4752_;
v___y_4701_ = v___y_4753_;
v___y_4702_ = v___y_4754_;
v___y_4703_ = v___y_4756_;
v___y_4704_ = v___x_4758_;
goto v___jp_4697_;
}
else
{
v___y_4698_ = v___y_4755_;
v___y_4699_ = v___y_4751_;
v___y_4700_ = v___y_4752_;
v___y_4701_ = v___y_4753_;
v___y_4702_ = v___y_4754_;
v___y_4703_ = v___y_4756_;
v___y_4704_ = v___x_3728_;
goto v___jp_4697_;
}
}
else
{
lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v_a_4761_; uint8_t v___x_4762_; 
lean_dec(v___y_4751_);
v___x_4759_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4760_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4759_, v___y_4755_);
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
lean_inc(v_a_4761_);
lean_dec_ref(v___x_4760_);
v___x_4762_ = lean_unbox(v_a_4761_);
lean_dec(v_a_4761_);
if (v___x_4762_ == 0)
{
lean_object* v_options_4763_; uint8_t v_hasTrace_4764_; 
v_options_4763_ = lean_ctor_get(v___y_4755_, 2);
v_hasTrace_4764_ = lean_ctor_get_uint8(v_options_4763_, sizeof(void*)*1);
if (v_hasTrace_4764_ == 0)
{
v___y_3836_ = v___y_4752_;
v___y_3837_ = v___y_4753_;
v___y_3838_ = v___y_4754_;
v_exportedInfo_x3f_3839_ = v___x_4749_;
v___y_3840_ = v___y_4755_;
v___y_3841_ = v___y_4756_;
goto v___jp_3835_;
}
else
{
lean_object* v_inheritedTraceOptions_4765_; lean_object* v___x_4766_; uint8_t v___x_4767_; 
v_inheritedTraceOptions_4765_ = lean_ctor_get(v___y_4755_, 13);
v___x_4766_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4765_, v_options_4763_, v___x_4766_);
if (v___x_4767_ == 0)
{
v___y_3836_ = v___y_4752_;
v___y_3837_ = v___y_4753_;
v___y_3838_ = v___y_4754_;
v_exportedInfo_x3f_3839_ = v___x_4749_;
v___y_3840_ = v___y_4755_;
v___y_3841_ = v___y_4756_;
goto v___jp_3835_;
}
else
{
lean_object* v___x_4768_; lean_object* v___x_4769_; 
v___x_4768_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__5);
v___x_4769_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4768_, v___y_4755_, v___y_4756_);
if (lean_obj_tag(v___x_4769_) == 0)
{
lean_dec_ref_known(v___x_4769_, 1);
v___y_3836_ = v___y_4752_;
v___y_3837_ = v___y_4753_;
v___y_3838_ = v___y_4754_;
v_exportedInfo_x3f_3839_ = v___x_4749_;
v___y_3840_ = v___y_4755_;
v___y_3841_ = v___y_4756_;
goto v___jp_3835_;
}
else
{
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4752_);
lean_dec(v_decl_3654_);
return v___x_4769_;
}
}
}
}
else
{
lean_object* v_options_4770_; uint8_t v_hasTrace_4771_; 
v_options_4770_ = lean_ctor_get(v___y_4755_, 2);
v_hasTrace_4771_ = lean_ctor_get_uint8(v_options_4770_, sizeof(void*)*1);
if (v_hasTrace_4771_ == 0)
{
v___y_3851_ = v___y_4752_;
v___y_3852_ = v___y_4753_;
v___y_3853_ = v___y_4754_;
v___y_3854_ = v___y_4755_;
v___y_3855_ = v___y_4756_;
goto v___jp_3850_;
}
else
{
lean_object* v_inheritedTraceOptions_4772_; lean_object* v___x_4773_; uint8_t v___x_4774_; 
v_inheritedTraceOptions_4772_ = lean_ctor_get(v___y_4755_, 13);
v___x_4773_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4774_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4772_, v_options_4770_, v___x_4773_);
if (v___x_4774_ == 0)
{
v___y_3851_ = v___y_4752_;
v___y_3852_ = v___y_4753_;
v___y_3853_ = v___y_4754_;
v___y_3854_ = v___y_4755_;
v___y_3855_ = v___y_4756_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_4775_; lean_object* v___x_4776_; 
v___x_4775_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__7);
v___x_4776_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4775_, v___y_4755_, v___y_4756_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_dec_ref_known(v___x_4776_, 1);
v___y_3851_ = v___y_4752_;
v___y_3852_ = v___y_4753_;
v___y_3853_ = v___y_4754_;
v___y_3854_ = v___y_4755_;
v___y_3855_ = v___y_4756_;
goto v___jp_3850_;
}
else
{
lean_dec_ref(v___y_4754_);
lean_dec(v___y_4752_);
lean_dec(v_decl_3654_);
return v___x_4776_;
}
}
}
}
}
}
v___jp_4777_:
{
lean_object* v___x_4784_; lean_object* v_env_4785_; uint8_t v___x_4786_; 
v___x_4784_ = lean_st_ref_get(v___y_4783_);
v_env_4785_ = lean_ctor_get(v___x_4784_, 0);
lean_inc_ref(v_env_4785_);
lean_dec(v___x_4784_);
v___x_4786_ = l_Lean_Environment_containsOnBranch(v_env_4785_, v_fst_4778_);
lean_dec_ref(v_env_4785_);
if (v___x_4786_ == 0)
{
v___y_4751_ = v_exportedInfo_x3f_4781_;
v___y_4752_ = v_fst_4778_;
v___y_4753_ = v_snd_4780_;
v___y_4754_ = v_fst_4779_;
v___y_4755_ = v___y_4782_;
v___y_4756_ = v___y_4783_;
goto v___jp_4750_;
}
else
{
lean_object* v___x_4787_; lean_object* v_env_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
lean_dec(v_exportedInfo_x3f_4781_);
lean_dec_ref(v_fst_4779_);
lean_dec(v_decl_3654_);
v___x_4787_ = lean_st_ref_get(v___y_4783_);
v_env_4788_ = lean_ctor_get(v___x_4787_, 0);
lean_inc_ref(v_env_4788_);
lean_dec(v___x_4787_);
v___x_4789_ = lean_elab_environment_to_kernel_env(v_env_4788_);
v___x_4790_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
lean_ctor_set(v___x_4790_, 1, v_fst_4778_);
v___x_4791_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4790_, v___y_4782_, v___y_4783_);
return v___x_4791_;
}
}
v___jp_4792_:
{
lean_object* v_name_4798_; lean_object* v___x_4799_; uint8_t v___x_4800_; 
v_name_4798_ = lean_ctor_get(v_toConstantVal_4794_, 0);
lean_inc(v_name_4798_);
lean_dec_ref(v_toConstantVal_4794_);
v___x_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4799_, 0, v___y_4793_);
v___x_4800_ = 0;
v_fst_4778_ = v_name_4798_;
v_fst_4779_ = v___x_4799_;
v_snd_4780_ = v___x_4800_;
v_exportedInfo_x3f_4781_ = v_exportedInfo_x3f_4795_;
v___y_4782_ = v___y_4796_;
v___y_4783_ = v___y_4797_;
goto v___jp_4777_;
}
v___jp_4801_:
{
lean_object* v_toConstantVal_4806_; 
v_toConstantVal_4806_ = lean_ctor_get(v___y_4802_, 0);
lean_inc_ref(v_toConstantVal_4806_);
v___y_4793_ = v___y_4802_;
v_toConstantVal_4794_ = v_toConstantVal_4806_;
v_exportedInfo_x3f_4795_ = v_exportedInfo_x3f_4803_;
v___y_4796_ = v___y_4804_;
v___y_4797_ = v___y_4805_;
goto v___jp_4792_;
}
v___jp_4807_:
{
uint8_t v___x_4813_; uint8_t v___x_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
v___x_4813_ = 0;
v___x_4814_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4810_, v___x_4813_);
lean_inc_ref(v_toConstantVal_4809_);
v___x_4815_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4815_, 0, v_toConstantVal_4809_);
lean_ctor_set_uint8(v___x_4815_, sizeof(void*)*1, v___x_4814_);
v___x_4816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4816_, 0, v___x_4815_);
v___x_4817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4817_, 0, v___x_4816_);
v___y_4793_ = v___y_4808_;
v_toConstantVal_4794_ = v_toConstantVal_4809_;
v_exportedInfo_x3f_4795_ = v___x_4817_;
v___y_4796_ = v___y_4811_;
v___y_4797_ = v___y_4812_;
goto v___jp_4792_;
}
v___jp_4818_:
{
lean_object* v_toConstantVal_4822_; uint8_t v_safety_4823_; 
v_toConstantVal_4822_ = lean_ctor_get(v___y_4819_, 0);
lean_inc_ref(v_toConstantVal_4822_);
v_safety_4823_ = lean_ctor_get_uint8(v___y_4819_, sizeof(void*)*4);
v___y_4808_ = v___y_4819_;
v_toConstantVal_4809_ = v_toConstantVal_4822_;
v_safety_4810_ = v_safety_4823_;
v___y_4811_ = v___y_4820_;
v___y_4812_ = v___y_4821_;
goto v___jp_4807_;
}
v___jp_4824_:
{
if (v___y_4829_ == 0)
{
lean_dec_ref(v___y_4826_);
v___y_4802_ = v___y_4828_;
v_exportedInfo_x3f_4803_ = v___x_4749_;
v___y_4804_ = v___y_4827_;
v___y_4805_ = v___y_4825_;
goto v___jp_4801_;
}
else
{
uint8_t v_isExporting_4830_; uint8_t v___x_4831_; 
v_isExporting_4830_ = lean_ctor_get_uint8(v___y_4826_, sizeof(void*)*8);
lean_dec_ref(v___y_4826_);
v___x_4831_ = lean_bool_not(v_isExporting_4830_);
if (v___x_4831_ == 0)
{
v___y_4802_ = v___y_4828_;
v_exportedInfo_x3f_4803_ = v___x_4749_;
v___y_4804_ = v___y_4827_;
v___y_4805_ = v___y_4825_;
goto v___jp_4801_;
}
else
{
lean_object* v_options_4832_; uint8_t v_hasTrace_4833_; 
v_options_4832_ = lean_ctor_get(v___y_4827_, 2);
v_hasTrace_4833_ = lean_ctor_get_uint8(v_options_4832_, sizeof(void*)*1);
if (v_hasTrace_4833_ == 0)
{
v___y_4819_ = v___y_4828_;
v___y_4820_ = v___y_4827_;
v___y_4821_ = v___y_4825_;
goto v___jp_4818_;
}
else
{
lean_object* v_inheritedTraceOptions_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_inheritedTraceOptions_4834_ = lean_ctor_get(v___y_4827_, 13);
v___x_4835_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4834_, v_options_4832_, v___x_4835_);
if (v___x_4836_ == 0)
{
v___y_4819_ = v___y_4828_;
v___y_4820_ = v___y_4827_;
v___y_4821_ = v___y_4825_;
goto v___jp_4818_;
}
else
{
lean_object* v_toConstantVal_4837_; uint8_t v_safety_4838_; lean_object* v_name_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v_toConstantVal_4837_ = lean_ctor_get(v___y_4828_, 0);
lean_inc_ref(v_toConstantVal_4837_);
v_safety_4838_ = lean_ctor_get_uint8(v___y_4828_, sizeof(void*)*4);
v_name_4839_ = lean_ctor_get(v_toConstantVal_4837_, 0);
v___x_4840_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__1);
lean_inc(v_name_4839_);
v___x_4841_ = l_Lean_MessageData_ofName(v_name_4839_);
v___x_4842_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4842_, 0, v___x_4840_);
lean_ctor_set(v___x_4842_, 1, v___x_4841_);
v___x_4843_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___closed__3);
v___x_4844_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4842_);
lean_ctor_set(v___x_4844_, 1, v___x_4843_);
v___x_4845_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_4844_, v___y_4827_, v___y_4825_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_dec_ref_known(v___x_4845_, 1);
v___y_4808_ = v___y_4828_;
v_toConstantVal_4809_ = v_toConstantVal_4837_;
v_safety_4810_ = v_safety_4838_;
v___y_4811_ = v___y_4827_;
v___y_4812_ = v___y_4825_;
goto v___jp_4807_;
}
else
{
lean_dec_ref(v_toConstantVal_4837_);
lean_dec_ref(v___y_4828_);
lean_dec(v_decl_3654_);
return v___x_4845_;
}
}
}
}
}
}
v___jp_4846_:
{
lean_object* v___x_4850_; lean_object* v___x_4851_; lean_object* v_env_4852_; uint8_t v___x_4853_; 
v___x_4850_ = lean_st_ref_get(v___y_4849_);
v___x_4851_ = lean_st_ref_get(v___y_4849_);
v_env_4852_ = lean_ctor_get(v___x_4851_, 0);
lean_inc_ref(v_env_4852_);
lean_dec(v___x_4851_);
v___x_4853_ = lean_bool_not(v_forceExpose_3655_);
if (v___x_4853_ == 0)
{
lean_dec(v___x_4850_);
v___y_4825_ = v___y_4849_;
v___y_4826_ = v_env_4852_;
v___y_4827_ = v___y_4848_;
v___y_4828_ = v_defn_4847_;
v___y_4829_ = v___x_4853_;
goto v___jp_4824_;
}
else
{
lean_object* v_env_4854_; lean_object* v___x_4855_; uint8_t v_isModule_4856_; 
v_env_4854_ = lean_ctor_get(v___x_4850_, 0);
lean_inc_ref(v_env_4854_);
lean_dec(v___x_4850_);
v___x_4855_ = l_Lean_Environment_header(v_env_4854_);
lean_dec_ref(v_env_4854_);
v_isModule_4856_ = lean_ctor_get_uint8(v___x_4855_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4855_);
v___y_4825_ = v___y_4849_;
v___y_4826_ = v_env_4852_;
v___y_4827_ = v___y_4848_;
v___y_4828_ = v_defn_4847_;
v___y_4829_ = v_isModule_4856_;
goto v___jp_4824_;
}
}
}
}
}
v___jp_3659_:
{
lean_object* v___x_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3670_; 
v___x_3663_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3660_, v___y_3661_);
v_isSharedCheck_3670_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3670_ == 0)
{
lean_object* v_unused_3671_; 
v_unused_3671_ = lean_ctor_get(v___x_3663_, 0);
lean_dec(v_unused_3671_);
v___x_3665_ = v___x_3663_;
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
else
{
lean_dec(v___x_3663_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3670_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v___x_3668_; 
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v_a_3662_);
v___x_3668_ = v___x_3665_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3662_);
v___x_3668_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
return v___x_3668_;
}
}
}
v___jp_3672_:
{
lean_object* v___x_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
v___x_3676_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3673_, v___y_3674_);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3676_);
if (v_isSharedCheck_3683_ == 0)
{
lean_object* v_unused_3684_; 
v_unused_3684_ = lean_ctor_get(v___x_3676_, 0);
lean_dec(v_unused_3684_);
v___x_3678_ = v___x_3676_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v___x_3676_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 1);
lean_ctor_set(v___x_3678_, 0, v_a_3675_);
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3675_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
v___jp_3685_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
v___x_3689_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3687_, v___y_3686_);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3689_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v___x_3689_, 0);
lean_dec(v_unused_3697_);
v___x_3691_ = v___x_3689_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_dec(v___x_3689_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
lean_ctor_set_tag(v___x_3691_, 1);
lean_ctor_set(v___x_3691_, 0, v_a_3688_);
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3688_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
v___jp_3698_:
{
lean_object* v___x_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
v___x_3702_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3700_, v___y_3699_);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3702_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v___x_3702_, 0);
lean_dec(v_unused_3710_);
v___x_3704_ = v___x_3702_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_dec(v___x_3702_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v_a_3701_);
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3701_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
v___jp_3715_:
{
if (v_hasTrace_3718_ == 0)
{
lean_object* v___x_3721_; 
v___x_3721_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_3716_, v___y_3720_);
return v___x_3721_;
}
else
{
lean_object* v___x_3722_; uint8_t v___x_3723_; 
v___x_3722_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3719_, v_options_3717_, v___x_3722_);
if (v___x_3723_ == 0)
{
lean_object* v___x_3724_; 
v___x_3724_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_3716_, v___y_3720_);
return v___x_3724_;
}
else
{
lean_object* v___x_3725_; lean_object* v___x_3726_; 
v___x_3725_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_3726_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3714_, v___x_3725_, v___y_3716_, v___y_3720_);
if (lean_obj_tag(v___x_3726_) == 0)
{
lean_object* v___x_3727_; 
lean_dec_ref_known(v___x_3726_, 1);
v___x_3727_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_3716_, v___y_3720_);
return v___x_3727_;
}
else
{
lean_dec(v_decl_3654_);
return v___x_3726_;
}
}
}
}
v___jp_3729_:
{
lean_object* v___x_3741_; 
lean_inc_ref(v___y_3730_);
v___x_3741_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3736_, v___y_3730_, v___y_3732_, v___y_3740_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v___x_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3788_; 
lean_dec_ref_known(v___x_3741_, 1);
lean_inc_ref(v___y_3734_);
v___x_3742_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3734_, v___y_3731_);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3788_ == 0)
{
lean_object* v_unused_3789_; 
v_unused_3789_ = lean_ctor_get(v___x_3742_, 0);
lean_dec(v_unused_3789_);
v___x_3744_ = v___x_3742_;
v_isShared_3745_ = v_isSharedCheck_3788_;
goto v_resetjp_3743_;
}
else
{
lean_dec(v___x_3742_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3788_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_options_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
v_options_3746_ = lean_ctor_get(v___y_3737_, 2);
v___x_3747_ = l_Lean_Elab_async;
v___x_3748_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3746_, v___x_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v_r_3750_; 
lean_del_object(v___x_3744_);
lean_dec_ref(v___y_3739_);
lean_dec_ref(v___y_3733_);
v___x_3749_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3730_, v___y_3731_);
lean_dec_ref(v___x_3749_);
v_r_3750_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3654_, v___y_3737_, v___y_3731_);
if (lean_obj_tag(v_r_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3760_; 
v_a_3751_ = lean_ctor_get(v_r_3750_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v_r_3750_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3753_ = v_r_3750_;
v_isShared_3754_ = v_isSharedCheck_3760_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v_r_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3760_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
lean_inc(v_a_3751_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set_tag(v___x_3753_, 1);
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3751_);
v___x_3756_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; 
v___x_3757_ = lean_apply_2(v___y_3735_, v___x_3756_, lean_box(0));
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_dec_ref_known(v___x_3757_, 1);
v___y_3699_ = v___y_3731_;
v___y_3700_ = v___y_3734_;
v_a_3701_ = v_a_3751_;
goto v___jp_3698_;
}
else
{
lean_object* v_a_3758_; 
lean_dec(v_a_3751_);
v_a_3758_ = lean_ctor_get(v___x_3757_, 0);
lean_inc(v_a_3758_);
lean_dec_ref_known(v___x_3757_, 1);
v___y_3686_ = v___y_3731_;
v___y_3687_ = v___y_3734_;
v_a_3688_ = v_a_3758_;
goto v___jp_3685_;
}
}
}
}
else
{
lean_object* v_a_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; 
v_a_3761_ = lean_ctor_get(v_r_3750_, 0);
lean_inc(v_a_3761_);
lean_dec_ref_known(v_r_3750_, 1);
v___x_3762_ = lean_box(0);
v___x_3763_ = lean_apply_2(v___y_3735_, v___x_3762_, lean_box(0));
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_dec_ref_known(v___x_3763_, 1);
v___y_3686_ = v___y_3731_;
v___y_3687_ = v___y_3734_;
v_a_3688_ = v_a_3761_;
goto v___jp_3685_;
}
else
{
lean_object* v_a_3764_; 
lean_dec(v_a_3761_);
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
lean_inc(v_a_3764_);
lean_dec_ref_known(v___x_3763_, 1);
v___y_3686_ = v___y_3731_;
v___y_3687_ = v___y_3734_;
v_a_3688_ = v_a_3764_;
goto v___jp_3685_;
}
}
}
else
{
lean_object* v___x_3765_; lean_object* v___x_3767_; 
lean_dec_ref(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec_ref(v___y_3730_);
lean_dec(v_decl_3654_);
v___x_3765_ = l_IO_CancelToken_new();
if (v_isShared_3745_ == 0)
{
lean_ctor_set_tag(v___x_3744_, 1);
lean_ctor_set(v___x_3744_, 0, v___x_3765_);
v___x_3767_ = v___x_3744_;
goto v_reusejp_3766_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3765_);
v___x_3767_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3766_;
}
v_reusejp_3766_:
{
lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; 
v___x_3768_ = lean_unsigned_to_nat(0u);
v___x_3769_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___closed__1));
v___x_3770_ = l_Lean_Name_toString(v___x_3769_, v___x_3728_);
lean_inc_ref(v___x_3767_);
v___x_3771_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3733_, v___x_3767_, v___x_3770_, v___y_3737_, v___y_3731_);
if (lean_obj_tag(v___x_3771_) == 0)
{
lean_object* v_a_3772_; lean_object* v_checked_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_a_3772_ = lean_ctor_get(v___x_3771_, 0);
lean_inc(v_a_3772_);
lean_dec_ref_known(v___x_3771_, 1);
v_checked_3773_ = lean_ctor_get(v___y_3739_, 2);
lean_inc_ref(v_checked_3773_);
lean_dec_ref(v___y_3739_);
v___x_3774_ = lean_io_map_task(v_a_3772_, v_checked_3773_, v___x_3768_, v___y_3738_);
v___x_3775_ = lean_box(0);
v___x_3776_ = lean_box(2);
v___x_3777_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3775_);
lean_ctor_set(v___x_3777_, 1, v___x_3776_);
lean_ctor_set(v___x_3777_, 2, v___x_3767_);
lean_ctor_set(v___x_3777_, 3, v___x_3774_);
v___x_3778_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3777_, v___y_3731_);
return v___x_3778_;
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
lean_dec_ref(v___x_3767_);
lean_dec_ref(v___y_3739_);
v_a_3779_ = lean_ctor_get(v___x_3771_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3771_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3771_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3771_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3802_; 
lean_dec_ref(v___y_3739_);
lean_dec_ref(v___y_3735_);
lean_dec_ref(v___y_3734_);
lean_dec_ref(v___y_3733_);
lean_dec_ref(v___y_3730_);
lean_dec(v_decl_3654_);
v_a_3790_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3792_ = v___x_3741_;
v_isShared_3793_ = v_isSharedCheck_3802_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3741_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3802_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v_ref_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3800_; 
v_ref_3794_ = lean_ctor_get(v___y_3737_, 5);
v___x_3795_ = lean_io_error_to_string(v_a_3790_);
v___x_3796_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3796_, 0, v___x_3795_);
v___x_3797_ = l_Lean_MessageData_ofFormat(v___x_3796_);
lean_inc(v_ref_3794_);
v___x_3798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3798_, 0, v_ref_3794_);
lean_ctor_set(v___x_3798_, 1, v___x_3797_);
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v___x_3798_);
v___x_3800_ = v___x_3792_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3801_; 
v_reuseFailAlloc_3801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3801_, 0, v___x_3798_);
v___x_3800_ = v_reuseFailAlloc_3801_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
return v___x_3800_;
}
}
}
}
v___jp_3803_:
{
uint8_t v___x_3814_; lean_object* v___x_3815_; 
v___x_3814_ = 0;
lean_inc_ref(v___y_3806_);
v___x_3815_ = l_Lean_Environment_addConstAsync(v___y_3806_, v___y_3810_, v___y_3811_, v___y_3813_, v___x_3814_, v___x_3728_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v_mainEnv_3817_; lean_object* v_asyncEnv_3818_; lean_object* v___f_3819_; lean_object* v___f_3820_; lean_object* v___x_3821_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc_n(v_a_3816_, 3);
lean_dec_ref_known(v___x_3815_, 1);
v_mainEnv_3817_ = lean_ctor_get(v_a_3816_, 0);
lean_inc_ref(v_mainEnv_3817_);
v_asyncEnv_3818_ = lean_ctor_get(v_a_3816_, 1);
lean_inc_ref_n(v_asyncEnv_3818_, 2);
lean_inc_ref(v___y_3805_);
lean_inc(v___y_3804_);
v___f_3819_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 3);
lean_closure_set(v___f_3819_, 0, v___y_3804_);
lean_closure_set(v___f_3819_, 1, v_a_3816_);
lean_closure_set(v___f_3819_, 2, v___y_3805_);
lean_inc(v_decl_3654_);
v___f_3820_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed), 7, 3);
lean_closure_set(v___f_3820_, 0, v_asyncEnv_3818_);
lean_closure_set(v___f_3820_, 1, v_a_3816_);
lean_closure_set(v___f_3820_, 2, v_decl_3654_);
v___x_3821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3821_, 0, v___y_3812_);
if (lean_obj_tag(v___y_3807_) == 0)
{
lean_inc_ref(v___x_3821_);
v___y_3730_ = v_asyncEnv_3818_;
v___y_3731_ = v___y_3808_;
v___y_3732_ = v___x_3821_;
v___y_3733_ = v___f_3820_;
v___y_3734_ = v_mainEnv_3817_;
v___y_3735_ = v___f_3819_;
v___y_3736_ = v_a_3816_;
v___y_3737_ = v___y_3809_;
v___y_3738_ = v___x_3814_;
v___y_3739_ = v___y_3806_;
v___y_3740_ = v___x_3821_;
goto v___jp_3729_;
}
else
{
v___y_3730_ = v_asyncEnv_3818_;
v___y_3731_ = v___y_3808_;
v___y_3732_ = v___x_3821_;
v___y_3733_ = v___f_3820_;
v___y_3734_ = v_mainEnv_3817_;
v___y_3735_ = v___f_3819_;
v___y_3736_ = v_a_3816_;
v___y_3737_ = v___y_3809_;
v___y_3738_ = v___x_3814_;
v___y_3739_ = v___y_3806_;
v___y_3740_ = v___y_3807_;
goto v___jp_3729_;
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3834_; 
lean_dec_ref(v___y_3812_);
lean_dec(v___y_3807_);
lean_dec_ref(v___y_3806_);
lean_dec(v_decl_3654_);
v_a_3822_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3834_ == 0)
{
v___x_3824_ = v___x_3815_;
v_isShared_3825_ = v_isSharedCheck_3834_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3815_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3834_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_ref_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3832_; 
v_ref_3826_ = lean_ctor_get(v___y_3809_, 5);
v___x_3827_ = lean_io_error_to_string(v_a_3822_);
v___x_3828_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3828_, 0, v___x_3827_);
v___x_3829_ = l_Lean_MessageData_ofFormat(v___x_3828_);
lean_inc(v_ref_3826_);
v___x_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3830_, 0, v_ref_3826_);
lean_ctor_set(v___x_3830_, 1, v___x_3829_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3830_);
v___x_3832_ = v___x_3824_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v___x_3830_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
}
v___jp_3835_:
{
lean_object* v___x_3842_; 
v___x_3842_ = lean_st_ref_get(v___y_3841_);
if (lean_obj_tag(v_exportedInfo_x3f_3839_) == 0)
{
lean_object* v_env_3843_; lean_object* v___x_3844_; 
v_env_3843_ = lean_ctor_get(v___x_3842_, 0);
lean_inc_ref(v_env_3843_);
lean_dec(v___x_3842_);
v___x_3844_ = lean_box(0);
v___y_3804_ = v___y_3841_;
v___y_3805_ = v___y_3840_;
v___y_3806_ = v_env_3843_;
v___y_3807_ = v_exportedInfo_x3f_3839_;
v___y_3808_ = v___y_3841_;
v___y_3809_ = v___y_3840_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___x_3844_;
goto v___jp_3803_;
}
else
{
lean_object* v_env_3845_; lean_object* v_val_3846_; uint8_t v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v_env_3845_ = lean_ctor_get(v___x_3842_, 0);
lean_inc_ref(v_env_3845_);
lean_dec(v___x_3842_);
v_val_3846_ = lean_ctor_get(v_exportedInfo_x3f_3839_, 0);
v___x_3847_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3846_);
v___x_3848_ = lean_box(v___x_3847_);
v___x_3849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3848_);
v___y_3804_ = v___y_3841_;
v___y_3805_ = v___y_3840_;
v___y_3806_ = v_env_3845_;
v___y_3807_ = v_exportedInfo_x3f_3839_;
v___y_3808_ = v___y_3841_;
v___y_3809_ = v___y_3840_;
v___y_3810_ = v___y_3836_;
v___y_3811_ = v___y_3837_;
v___y_3812_ = v___y_3838_;
v___y_3813_ = v___x_3849_;
goto v___jp_3803_;
}
}
v___jp_3850_:
{
lean_object* v___x_3856_; 
lean_inc_ref(v___y_3853_);
v___x_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3856_, 0, v___y_3853_);
v___y_3836_ = v___y_3851_;
v___y_3837_ = v___y_3852_;
v___y_3838_ = v___y_3853_;
v_exportedInfo_x3f_3839_ = v___x_3856_;
v___y_3840_ = v___y_3854_;
v___y_3841_ = v___y_3855_;
goto v___jp_3835_;
}
v___jp_3857_:
{
lean_object* v___x_3863_; 
lean_inc_ref(v___y_3860_);
v___x_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3863_, 0, v___y_3860_);
v___y_3836_ = v___y_3858_;
v___y_3837_ = v___y_3859_;
v___y_3838_ = v___y_3860_;
v_exportedInfo_x3f_3839_ = v___x_3863_;
v___y_3840_ = v___y_3861_;
v___y_3841_ = v___y_3862_;
goto v___jp_3835_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4941_, lean_object* v_forceExpose_4942_, lean_object* v_a_4943_, lean_object* v_a_4944_, lean_object* v_a_4945_){
_start:
{
uint8_t v_forceExpose_boxed_4946_; lean_object* v_res_4947_; 
v_forceExpose_boxed_4946_ = lean_unbox(v_forceExpose_4942_);
v_res_4947_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4941_, v_forceExpose_boxed_4946_, v_a_4943_, v_a_4944_);
lean_dec(v_a_4944_);
lean_dec_ref(v_a_4943_);
return v_res_4947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_){
_start:
{
lean_object* v___x_4952_; 
v___x_4952_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4948_, v___y_4949_);
return v___x_4952_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4953_, v___y_4954_, v___y_4955_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v_opt_4953_);
return v_res_4957_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4958_, lean_object* v_x_4959_, lean_object* v___y_4960_, lean_object* v___y_4961_){
_start:
{
if (lean_obj_tag(v_x_4958_) == 0)
{
lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4963_ = l_List_reverse___redArg(v_x_4959_);
v___x_4964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4964_, 0, v___x_4963_);
return v___x_4964_;
}
else
{
lean_object* v_head_4965_; lean_object* v_tail_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_4984_; 
v_head_4965_ = lean_ctor_get(v_x_4958_, 0);
v_tail_4966_ = lean_ctor_get(v_x_4958_, 1);
v_isSharedCheck_4984_ = !lean_is_exclusive(v_x_4958_);
if (v_isSharedCheck_4984_ == 0)
{
v___x_4968_ = v_x_4958_;
v_isShared_4969_ = v_isSharedCheck_4984_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_tail_4966_);
lean_inc(v_head_4965_);
lean_dec(v_x_4958_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_4984_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v___x_4970_; 
v___x_4970_ = l_Lean_snapshotEnvLinterOptions(v_head_4965_, v___y_4960_, v___y_4961_);
if (lean_obj_tag(v___x_4970_) == 0)
{
lean_object* v_a_4971_; lean_object* v___x_4973_; 
v_a_4971_ = lean_ctor_get(v___x_4970_, 0);
lean_inc(v_a_4971_);
lean_dec_ref_known(v___x_4970_, 1);
if (v_isShared_4969_ == 0)
{
lean_ctor_set(v___x_4968_, 1, v_x_4959_);
lean_ctor_set(v___x_4968_, 0, v_a_4971_);
v___x_4973_ = v___x_4968_;
goto v_reusejp_4972_;
}
else
{
lean_object* v_reuseFailAlloc_4975_; 
v_reuseFailAlloc_4975_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4975_, 0, v_a_4971_);
lean_ctor_set(v_reuseFailAlloc_4975_, 1, v_x_4959_);
v___x_4973_ = v_reuseFailAlloc_4975_;
goto v_reusejp_4972_;
}
v_reusejp_4972_:
{
v_x_4958_ = v_tail_4966_;
v_x_4959_ = v___x_4973_;
goto _start;
}
}
else
{
lean_object* v_a_4976_; lean_object* v___x_4978_; uint8_t v_isShared_4979_; uint8_t v_isSharedCheck_4983_; 
lean_del_object(v___x_4968_);
lean_dec(v_tail_4966_);
lean_dec(v_x_4959_);
v_a_4976_ = lean_ctor_get(v___x_4970_, 0);
v_isSharedCheck_4983_ = !lean_is_exclusive(v___x_4970_);
if (v_isSharedCheck_4983_ == 0)
{
v___x_4978_ = v___x_4970_;
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
else
{
lean_inc(v_a_4976_);
lean_dec(v___x_4970_);
v___x_4978_ = lean_box(0);
v_isShared_4979_ = v_isSharedCheck_4983_;
goto v_resetjp_4977_;
}
v_resetjp_4977_:
{
lean_object* v___x_4981_; 
if (v_isShared_4979_ == 0)
{
v___x_4981_ = v___x_4978_;
goto v_reusejp_4980_;
}
else
{
lean_object* v_reuseFailAlloc_4982_; 
v_reuseFailAlloc_4982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4982_, 0, v_a_4976_);
v___x_4981_ = v_reuseFailAlloc_4982_;
goto v_reusejp_4980_;
}
v_reusejp_4980_:
{
return v___x_4981_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4985_, lean_object* v_x_4986_, lean_object* v___y_4987_, lean_object* v___y_4988_, lean_object* v___y_4989_){
_start:
{
lean_object* v_res_4990_; 
v_res_4990_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4985_, v_x_4986_, v___y_4987_, v___y_4988_);
lean_dec(v___y_4988_);
lean_dec_ref(v___y_4987_);
return v_res_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4991_, uint8_t v_forceExpose_4992_, lean_object* v_a_4993_, lean_object* v_a_4994_){
_start:
{
lean_object* v___x_4996_; 
lean_inc(v_decl_4991_);
v___x_4996_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4991_, v_forceExpose_4992_, v_a_4993_, v_a_4994_);
if (lean_obj_tag(v___x_4996_) == 0)
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; 
lean_dec_ref_known(v___x_4996_, 1);
v___x_4997_ = l_Lean_Declaration_getTopLevelNames(v_decl_4991_);
v___x_4998_ = lean_box(0);
v___x_4999_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4997_, v___x_4998_, v_a_4993_, v_a_4994_);
if (lean_obj_tag(v___x_4999_) == 0)
{
lean_object* v___x_5001_; uint8_t v_isShared_5002_; uint8_t v_isSharedCheck_5007_; 
v_isSharedCheck_5007_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5007_ == 0)
{
lean_object* v_unused_5008_; 
v_unused_5008_ = lean_ctor_get(v___x_4999_, 0);
lean_dec(v_unused_5008_);
v___x_5001_ = v___x_4999_;
v_isShared_5002_ = v_isSharedCheck_5007_;
goto v_resetjp_5000_;
}
else
{
lean_dec(v___x_4999_);
v___x_5001_ = lean_box(0);
v_isShared_5002_ = v_isSharedCheck_5007_;
goto v_resetjp_5000_;
}
v_resetjp_5000_:
{
lean_object* v___x_5003_; lean_object* v___x_5005_; 
v___x_5003_ = lean_box(0);
if (v_isShared_5002_ == 0)
{
lean_ctor_set(v___x_5001_, 0, v___x_5003_);
v___x_5005_ = v___x_5001_;
goto v_reusejp_5004_;
}
else
{
lean_object* v_reuseFailAlloc_5006_; 
v_reuseFailAlloc_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5006_, 0, v___x_5003_);
v___x_5005_ = v_reuseFailAlloc_5006_;
goto v_reusejp_5004_;
}
v_reusejp_5004_:
{
return v___x_5005_;
}
}
}
else
{
lean_object* v_a_5009_; lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5016_; 
v_a_5009_ = lean_ctor_get(v___x_4999_, 0);
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_4999_);
if (v_isSharedCheck_5016_ == 0)
{
v___x_5011_ = v___x_4999_;
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
else
{
lean_inc(v_a_5009_);
lean_dec(v___x_4999_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5016_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5014_; 
if (v_isShared_5012_ == 0)
{
v___x_5014_ = v___x_5011_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v_a_5009_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
}
else
{
lean_dec(v_decl_4991_);
return v___x_4996_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_5017_, lean_object* v_forceExpose_5018_, lean_object* v_a_5019_, lean_object* v_a_5020_, lean_object* v_a_5021_){
_start:
{
uint8_t v_forceExpose_boxed_5022_; lean_object* v_res_5023_; 
v_forceExpose_boxed_5022_ = lean_unbox(v_forceExpose_5018_);
v_res_5023_ = l_Lean_addDecl(v_decl_5017_, v_forceExpose_boxed_5022_, v_a_5019_, v_a_5020_);
lean_dec(v_a_5020_);
lean_dec_ref(v_a_5019_);
return v_res_5023_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_5024_, lean_object* v_b_5025_, lean_object* v___y_5026_){
_start:
{
if (lean_obj_tag(v_as_x27_5024_) == 0)
{
lean_object* v___x_5028_; 
v___x_5028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5028_, 0, v_b_5025_);
return v___x_5028_;
}
else
{
lean_object* v_head_5029_; lean_object* v_tail_5030_; lean_object* v___x_5031_; lean_object* v_env_5032_; lean_object* v_nextMacroScope_5033_; lean_object* v_ngen_5034_; lean_object* v_auxDeclNGen_5035_; lean_object* v_traceState_5036_; lean_object* v_messages_5037_; lean_object* v_infoState_5038_; lean_object* v_snapshotTasks_5039_; lean_object* v___x_5041_; uint8_t v_isShared_5042_; uint8_t v_isSharedCheck_5051_; 
v_head_5029_ = lean_ctor_get(v_as_x27_5024_, 0);
v_tail_5030_ = lean_ctor_get(v_as_x27_5024_, 1);
v___x_5031_ = lean_st_ref_take(v___y_5026_);
v_env_5032_ = lean_ctor_get(v___x_5031_, 0);
v_nextMacroScope_5033_ = lean_ctor_get(v___x_5031_, 1);
v_ngen_5034_ = lean_ctor_get(v___x_5031_, 2);
v_auxDeclNGen_5035_ = lean_ctor_get(v___x_5031_, 3);
v_traceState_5036_ = lean_ctor_get(v___x_5031_, 4);
v_messages_5037_ = lean_ctor_get(v___x_5031_, 6);
v_infoState_5038_ = lean_ctor_get(v___x_5031_, 7);
v_snapshotTasks_5039_ = lean_ctor_get(v___x_5031_, 8);
v_isSharedCheck_5051_ = !lean_is_exclusive(v___x_5031_);
if (v_isSharedCheck_5051_ == 0)
{
lean_object* v_unused_5052_; 
v_unused_5052_ = lean_ctor_get(v___x_5031_, 5);
lean_dec(v_unused_5052_);
v___x_5041_ = v___x_5031_;
v_isShared_5042_ = v_isSharedCheck_5051_;
goto v_resetjp_5040_;
}
else
{
lean_inc(v_snapshotTasks_5039_);
lean_inc(v_infoState_5038_);
lean_inc(v_messages_5037_);
lean_inc(v_traceState_5036_);
lean_inc(v_auxDeclNGen_5035_);
lean_inc(v_ngen_5034_);
lean_inc(v_nextMacroScope_5033_);
lean_inc(v_env_5032_);
lean_dec(v___x_5031_);
v___x_5041_ = lean_box(0);
v_isShared_5042_ = v_isSharedCheck_5051_;
goto v_resetjp_5040_;
}
v_resetjp_5040_:
{
lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5046_; 
lean_inc(v_head_5029_);
v___x_5043_ = l_Lean_markMeta(v_env_5032_, v_head_5029_);
v___x_5044_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_5042_ == 0)
{
lean_ctor_set(v___x_5041_, 5, v___x_5044_);
lean_ctor_set(v___x_5041_, 0, v___x_5043_);
v___x_5046_ = v___x_5041_;
goto v_reusejp_5045_;
}
else
{
lean_object* v_reuseFailAlloc_5050_; 
v_reuseFailAlloc_5050_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5050_, 0, v___x_5043_);
lean_ctor_set(v_reuseFailAlloc_5050_, 1, v_nextMacroScope_5033_);
lean_ctor_set(v_reuseFailAlloc_5050_, 2, v_ngen_5034_);
lean_ctor_set(v_reuseFailAlloc_5050_, 3, v_auxDeclNGen_5035_);
lean_ctor_set(v_reuseFailAlloc_5050_, 4, v_traceState_5036_);
lean_ctor_set(v_reuseFailAlloc_5050_, 5, v___x_5044_);
lean_ctor_set(v_reuseFailAlloc_5050_, 6, v_messages_5037_);
lean_ctor_set(v_reuseFailAlloc_5050_, 7, v_infoState_5038_);
lean_ctor_set(v_reuseFailAlloc_5050_, 8, v_snapshotTasks_5039_);
v___x_5046_ = v_reuseFailAlloc_5050_;
goto v_reusejp_5045_;
}
v_reusejp_5045_:
{
lean_object* v___x_5047_; lean_object* v___x_5048_; 
v___x_5047_ = lean_st_ref_set(v___y_5026_, v___x_5046_);
v___x_5048_ = lean_box(0);
v_as_x27_5024_ = v_tail_5030_;
v_b_5025_ = v___x_5048_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_5053_, lean_object* v_b_5054_, lean_object* v___y_5055_, lean_object* v___y_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5053_, v_b_5054_, v___y_5055_);
lean_dec(v___y_5055_);
lean_dec(v_as_x27_5053_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_5058_, uint8_t v_logCompileErrors_5059_, uint8_t v_markMeta_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
uint8_t v___x_5064_; lean_object* v___x_5065_; 
v___x_5064_ = 0;
lean_inc(v_decl_5058_);
v___x_5065_ = l_Lean_addDecl(v_decl_5058_, v___x_5064_, v_a_5061_, v_a_5062_);
if (lean_obj_tag(v___x_5065_) == 0)
{
lean_dec_ref_known(v___x_5065_, 1);
if (v_markMeta_5060_ == 0)
{
lean_object* v___x_5066_; 
v___x_5066_ = l_Lean_compileDecl(v_decl_5058_, v_logCompileErrors_5059_, v_a_5061_, v_a_5062_);
return v___x_5066_;
}
else
{
lean_object* v___x_5067_; lean_object* v___x_5068_; lean_object* v___x_5069_; lean_object* v___x_5070_; 
lean_inc(v_decl_5058_);
v___x_5067_ = l_Lean_Declaration_getNames(v_decl_5058_);
v___x_5068_ = lean_box(0);
v___x_5069_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5067_, v___x_5068_, v_a_5062_);
lean_dec(v___x_5067_);
lean_dec_ref(v___x_5069_);
v___x_5070_ = l_Lean_compileDecl(v_decl_5058_, v_logCompileErrors_5059_, v_a_5061_, v_a_5062_);
return v___x_5070_;
}
}
else
{
lean_dec(v_decl_5058_);
return v___x_5065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5071_, lean_object* v_logCompileErrors_5072_, lean_object* v_markMeta_5073_, lean_object* v_a_5074_, lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
uint8_t v_logCompileErrors_boxed_5077_; uint8_t v_markMeta_boxed_5078_; lean_object* v_res_5079_; 
v_logCompileErrors_boxed_5077_ = lean_unbox(v_logCompileErrors_5072_);
v_markMeta_boxed_5078_ = lean_unbox(v_markMeta_5073_);
v_res_5079_ = l_Lean_addAndCompile(v_decl_5071_, v_logCompileErrors_boxed_5077_, v_markMeta_boxed_5078_, v_a_5074_, v_a_5075_);
lean_dec(v_a_5075_);
lean_dec_ref(v_a_5074_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5080_, lean_object* v_as_x27_5081_, lean_object* v_b_5082_, lean_object* v_a_5083_, lean_object* v___y_5084_, lean_object* v___y_5085_){
_start:
{
lean_object* v___x_5087_; 
v___x_5087_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5081_, v_b_5082_, v___y_5085_);
return v___x_5087_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5088_, lean_object* v_as_x27_5089_, lean_object* v_b_5090_, lean_object* v_a_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v_res_5095_; 
v_res_5095_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5088_, v_as_x27_5089_, v_b_5090_, v_a_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___y_5093_);
lean_dec_ref(v___y_5092_);
lean_dec(v_as_x27_5089_);
lean_dec(v_as_5088_);
return v_res_5095_;
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
