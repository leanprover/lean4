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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___y_15948__boxed_416_; uint8_t v_suppressElabErrors_boxed_417_; uint8_t v_res_418_; lean_object* v_r_419_; 
v___y_15948__boxed_416_ = lean_unbox(v___y_413_);
v_suppressElabErrors_boxed_417_ = lean_unbox(v_suppressElabErrors_414_);
v_res_418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15948__boxed_416_, v_suppressElabErrors_boxed_417_, v_x_415_);
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
uint8_t v___y_465_; lean_object* v___y_466_; lean_object* v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; lean_object* v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v___y_501_; uint8_t v___y_502_; uint8_t v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; lean_object* v___y_507_; lean_object* v___y_508_; lean_object* v___y_526_; uint8_t v___y_527_; lean_object* v___y_528_; uint8_t v___y_529_; lean_object* v___y_530_; uint8_t v___y_531_; lean_object* v___y_532_; lean_object* v___y_533_; lean_object* v___y_537_; lean_object* v___y_538_; uint8_t v___y_539_; lean_object* v___y_540_; uint8_t v___y_541_; lean_object* v___y_542_; uint8_t v___y_543_; uint8_t v___x_548_; lean_object* v___y_550_; lean_object* v___y_551_; uint8_t v___y_552_; lean_object* v___y_553_; lean_object* v___y_554_; uint8_t v___y_555_; uint8_t v___y_556_; uint8_t v___y_558_; uint8_t v___x_573_; 
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
lean_ctor_set(v___x_490_, 1, v___y_468_);
lean_inc_ref(v___y_470_);
lean_inc_ref(v___y_467_);
v___x_491_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_491_, 0, v___y_467_);
lean_ctor_set(v___x_491_, 1, v___y_471_);
lean_ctor_set(v___x_491_, 2, v___y_466_);
lean_ctor_set(v___x_491_, 3, v___y_470_);
lean_ctor_set(v___x_491_, 4, v___x_490_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5, v___y_469_);
lean_ctor_set_uint8(v___x_491_, sizeof(void*)*5 + 1, v___y_465_);
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
lean_inc_ref_n(v___y_507_, 2);
v___x_515_ = l_Lean_FileMap_toPosition(v___y_507_, v___y_504_);
lean_dec(v___y_504_);
v___x_516_ = l_Lean_FileMap_toPosition(v___y_507_, v___y_508_);
lean_dec(v___y_508_);
v___x_517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_517_, 0, v___x_516_);
v___x_518_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_503_ == 0)
{
lean_del_object(v___x_513_);
lean_dec_ref(v___y_501_);
v___y_465_ = v___y_502_;
v___y_466_ = v___x_517_;
v___y_467_ = v___y_505_;
v___y_468_ = v_a_511_;
v___y_469_ = v___y_506_;
v___y_470_ = v___x_518_;
v___y_471_ = v___x_515_;
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
v___y_465_ = v___y_502_;
v___y_466_ = v___x_517_;
v___y_467_ = v___y_505_;
v___y_468_ = v_a_511_;
v___y_469_ = v___y_506_;
v___y_470_ = v___x_518_;
v___y_471_ = v___x_515_;
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
v___x_534_ = l_Lean_Syntax_getTailPos_x3f(v___y_528_, v___y_531_);
lean_dec(v___y_528_);
if (lean_obj_tag(v___x_534_) == 0)
{
lean_inc(v___y_533_);
v___y_501_ = v___y_526_;
v___y_502_ = v___y_527_;
v___y_503_ = v___y_529_;
v___y_504_ = v___y_533_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
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
v___y_503_ = v___y_529_;
v___y_504_ = v___y_533_;
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_532_;
v___y_508_ = v_val_535_;
goto v___jp_500_;
}
}
v___jp_536_:
{
lean_object* v_ref_544_; lean_object* v___x_545_; 
v_ref_544_ = l_Lean_replaceRef(v_ref_457_, v___y_538_);
v___x_545_ = l_Lean_Syntax_getPos_x3f(v_ref_544_, v___y_541_);
if (lean_obj_tag(v___x_545_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___y_526_ = v___y_537_;
v___y_527_ = v___y_543_;
v___y_528_ = v_ref_544_;
v___y_529_ = v___y_539_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_542_;
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
v___y_527_ = v___y_543_;
v___y_528_ = v_ref_544_;
v___y_529_ = v___y_539_;
v___y_530_ = v___y_540_;
v___y_531_ = v___y_541_;
v___y_532_ = v___y_542_;
v___y_533_ = v_val_547_;
goto v___jp_525_;
}
}
v___jp_549_:
{
if (v___y_556_ == 0)
{
v___y_537_ = v___y_550_;
v___y_538_ = v___y_551_;
v___y_539_ = v___y_552_;
v___y_540_ = v___y_553_;
v___y_541_ = v___y_555_;
v___y_542_ = v___y_554_;
v___y_543_ = v_severity_459_;
goto v___jp_536_;
}
else
{
v___y_537_ = v___y_550_;
v___y_538_ = v___y_551_;
v___y_539_ = v___y_552_;
v___y_540_ = v___y_553_;
v___y_541_ = v___y_555_;
v___y_542_ = v___y_554_;
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
v___y_550_ = v___f_566_;
v___y_551_ = v_ref_562_;
v___y_552_ = v_suppressElabErrors_563_;
v___y_553_ = v_fileName_559_;
v___y_554_ = v_fileMap_560_;
v___y_555_ = v___y_558_;
v___y_556_ = v___x_568_;
goto v___jp_549_;
}
else
{
lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_569_ = l_Lean_warningAsError;
v___x_570_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_561_, v___x_569_);
v___y_550_ = v___f_566_;
v___y_551_ = v_ref_562_;
v___y_552_ = v_suppressElabErrors_563_;
v___y_553_ = v_fileName_559_;
v___y_554_ = v_fileMap_560_;
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
v___x_1566_ = lean_alloc_ctor(0, 0, 20);
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
lean_ctor_set_uint8(v___x_1566_, 19, v___x_1561_);
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
lean_inc(v___y_2404_);
v___x_2407_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2395_, v_data_2406_, v___y_2404_, v___y_2405_, v___y_2398_, v___y_2399_);
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
v___y_2404_ = v___y_2414_;
v___y_2405_ = v_a_2415_;
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
v___y_2404_ = v___y_2414_;
v___y_2405_ = v_a_2415_;
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
v___x_2575_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2538_, v___x_2560_, v___y_2563_, v___f_2498_, v___x_2574_, v___y_2499_, v___y_2500_);
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
v___x_2597_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
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
lean_dec(v_decl_2494_);
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
v___x_2615_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2538_, v___x_2560_, v___y_2606_, v___f_2498_, v___x_2614_, v___y_2499_, v___y_2500_);
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
v___y_2618_ = v___y_2635_;
v_a_2619_ = v___y_2634_;
goto v___jp_2616_;
}
else
{
lean_dec_ref(v___y_2634_);
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2635_;
v___y_2629_ = v___x_2637_;
goto v___jp_2626_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2617_ = v___y_2633_;
v___y_2618_ = v___y_2635_;
v_a_2619_ = v___y_2634_;
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
v___y_2634_ = v_a_2641_;
v___y_2635_ = v___y_2640_;
v___y_2636_ = v___x_2643_;
goto v___jp_2632_;
}
else
{
v___y_2633_ = v___y_2639_;
v___y_2634_ = v_a_2641_;
v___y_2635_ = v___y_2640_;
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
v___y_2587_ = v___x_2649_;
v___y_2588_ = v_a_2646_;
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
lean_dec(v_decl_2494_);
v___y_2627_ = v___x_2659_;
v___y_2628_ = v_a_2646_;
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
v___x_3000_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2995_, v___y_2994_, v___y_2991_, v___y_2999_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref_known(v___x_3000_, 1);
lean_inc_ref(v___y_2993_);
v___x_3001_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2993_, v___y_2997_);
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
v_options_3005_ = lean_ctor_get(v___y_2990_, 2);
v___x_3006_ = l_Lean_Elab_async;
v___x_3007_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3005_, v___x_3006_);
if (v___x_3007_ == 0)
{
lean_object* v___x_3008_; lean_object* v_r_3009_; 
lean_del_object(v___x_3003_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v___y_2992_);
v___x_3008_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2994_, v___y_2997_);
lean_dec_ref(v___x_3008_);
v_r_3009_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2952_, v___y_2990_, v___y_2997_);
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
v___x_3016_ = lean_apply_2(v___y_2996_, v___x_3015_, lean_box(0));
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
v___y_2977_ = v___y_2993_;
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
v___y_2964_ = v___y_2993_;
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
v___x_3022_ = lean_apply_2(v___y_2996_, v___x_3021_, lean_box(0));
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_dec_ref_known(v___x_3022_, 1);
v___y_2964_ = v___y_2993_;
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
v___y_2964_ = v___y_2993_;
v___y_2965_ = v___y_2997_;
v_a_2966_ = v_a_3023_;
goto v___jp_2963_;
}
}
}
else
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
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
v___x_3030_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2998_, v___x_3026_, v___x_3029_, v___y_2990_, v___y_2997_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_object* v_a_3031_; lean_object* v_checked_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; 
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
lean_inc(v_a_3031_);
lean_dec_ref_known(v___x_3030_, 1);
v_checked_3032_ = lean_ctor_get(v___y_2992_, 2);
lean_inc_ref(v_checked_3032_);
lean_dec_ref(v___y_2992_);
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
lean_dec_ref(v___y_2992_);
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
lean_dec_ref(v___y_2998_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
lean_dec_ref(v___y_2993_);
lean_dec_ref(v___y_2992_);
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
v_ref_3053_ = lean_ctor_get(v___y_2990_, 5);
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
lean_inc_ref(v___y_3073_);
v___x_3081_ = l_Lean_Environment_addConstAsync(v___y_3073_, v_fst_3063_, v___x_3080_, v___y_3079_, v___x_2954_, v_hasTrace_2953_);
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
lean_inc_ref(v___y_3075_);
lean_inc(v___y_3074_);
v___f_3085_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3085_, 0, v___y_3074_);
lean_closure_set(v___f_3085_, 1, v_a_3082_);
lean_closure_set(v___f_3085_, 2, v___y_3075_);
lean_inc(v_decl_2952_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3086_, 0, v_asyncEnv_3084_);
lean_closure_set(v___f_3086_, 1, v_a_3082_);
lean_closure_set(v___f_3086_, 2, v_decl_2952_);
v___x_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3087_, 0, v_fst_3067_);
if (lean_obj_tag(v___y_3078_) == 0)
{
lean_inc_ref(v___x_3087_);
v___y_2990_ = v___y_3076_;
v___y_2991_ = v___x_3087_;
v___y_2992_ = v___y_3073_;
v___y_2993_ = v_mainEnv_3083_;
v___y_2994_ = v_asyncEnv_3084_;
v___y_2995_ = v_a_3082_;
v___y_2996_ = v___f_3085_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___f_3086_;
v___y_2999_ = v___x_3087_;
goto v___jp_2989_;
}
else
{
v___y_2990_ = v___y_3076_;
v___y_2991_ = v___x_3087_;
v___y_2992_ = v___y_3073_;
v___y_2993_ = v_mainEnv_3083_;
v___y_2994_ = v_asyncEnv_3084_;
v___y_2995_ = v_a_3082_;
v___y_2996_ = v___f_3085_;
v___y_2997_ = v___y_3077_;
v___y_2998_ = v___f_3086_;
v___y_2999_ = v___y_3078_;
goto v___jp_2989_;
}
}
else
{
lean_object* v_a_3088_; lean_object* v___x_3090_; uint8_t v_isShared_3091_; uint8_t v_isSharedCheck_3102_; 
lean_dec(v___y_3078_);
lean_dec_ref(v___y_3073_);
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
v_ref_3092_ = lean_ctor_get(v___y_3076_, 5);
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
v___y_3073_ = v_env_3108_;
v___y_3074_ = v___y_3106_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v_exportedInfo_x3f_3104_;
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
v___y_3073_ = v_env_3110_;
v___y_3074_ = v___y_3106_;
v___y_3075_ = v___y_3105_;
v___y_3076_ = v___y_3105_;
v___y_3077_ = v___y_3106_;
v___y_3078_ = v_exportedInfo_x3f_3104_;
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
v___x_3126_ = lean_st_ref_take(v___y_3124_);
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
v___x_3142_ = lean_st_ref_set(v___y_3124_, v___x_3141_);
v_exportedInfo_x3f_3104_ = v_exportedInfo_x3f_2959_;
v___y_3105_ = v___y_3125_;
v___y_3106_ = v___y_3124_;
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
v___y_3124_ = v___y_3148_;
v___y_3125_ = v___y_3147_;
goto v___jp_3123_;
}
}
else
{
lean_dec(v_cls_2956_);
v___y_3124_ = v___y_3148_;
v___y_3125_ = v___y_3147_;
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
uint8_t v_hasTrace_boxed_3202_; uint8_t v___x_62998__boxed_3203_; lean_object* v_res_3204_; 
v_hasTrace_boxed_3202_ = lean_unbox(v_hasTrace_3192_);
v___x_62998__boxed_3203_ = lean_unbox(v___x_3193_);
v_res_3204_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3191_, v_hasTrace_boxed_3202_, v___x_62998__boxed_3203_, v___x_3194_, v_cls_3195_, v___x_3196_, v_____x_3197_, v_exportedInfo_x3f_3198_, v___y_3199_, v___y_3200_);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3211_, uint8_t v_hasTrace_3212_, uint8_t v___x_3213_, lean_object* v_cls_3214_, lean_object* v___x_3215_, uint8_t v_forceExpose_3216_, lean_object* v_defn_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_exportedInfo_x3f_3222_; lean_object* v___y_3223_; lean_object* v___y_3224_; lean_object* v___y_3234_; lean_object* v___y_3235_; lean_object* v___y_3236_; uint8_t v___y_3237_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v_env_3265_; lean_object* v_env_3266_; 
v___x_3248_ = lean_st_ref_get(v___y_3219_);
v___x_3249_ = lean_st_ref_get(v___y_3219_);
v_env_3265_ = lean_ctor_get(v___x_3248_, 0);
lean_inc_ref(v_env_3265_);
lean_dec(v___x_3248_);
v_env_3266_ = lean_ctor_get(v___x_3249_, 0);
lean_inc_ref(v_env_3266_);
lean_dec(v___x_3249_);
if (v_forceExpose_3216_ == 0)
{
goto v___jp_3267_;
}
else
{
if (v___x_3213_ == 0)
{
lean_dec_ref(v_env_3266_);
lean_dec_ref(v_env_3265_);
lean_dec(v_cls_3214_);
v_exportedInfo_x3f_3222_ = v___x_3215_;
v___y_3223_ = v___y_3218_;
v___y_3224_ = v___y_3219_;
goto v___jp_3221_;
}
else
{
goto v___jp_3267_;
}
}
v___jp_3221_:
{
lean_object* v_toConstantVal_3225_; lean_object* v_name_3226_; lean_object* v___x_3227_; uint8_t v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
v_toConstantVal_3225_ = lean_ctor_get(v_defn_3217_, 0);
v_name_3226_ = lean_ctor_get(v_toConstantVal_3225_, 0);
lean_inc(v_name_3226_);
v___x_3227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3227_, 0, v_defn_3217_);
v___x_3228_ = 0;
v___x_3229_ = lean_box(v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3227_);
lean_ctor_set(v___x_3230_, 1, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v_name_3226_);
lean_ctor_set(v___x_3231_, 1, v___x_3230_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
v___x_3232_ = lean_apply_5(v___f_3211_, v___x_3231_, v_exportedInfo_x3f_3222_, v___y_3223_, v___y_3224_, lean_box(0));
return v___x_3232_;
}
v___jp_3233_:
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3238_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3238_, 0, v___y_3236_);
lean_ctor_set_uint8(v___x_3238_, sizeof(void*)*1, v___y_3237_);
v___x_3239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3238_);
v___x_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3239_);
v_exportedInfo_x3f_3222_ = v___x_3240_;
v___y_3223_ = v___y_3235_;
v___y_3224_ = v___y_3234_;
goto v___jp_3221_;
}
v___jp_3241_:
{
lean_object* v_toConstantVal_3244_; uint8_t v_safety_3245_; uint8_t v___x_3246_; uint8_t v___x_3247_; 
v_toConstantVal_3244_ = lean_ctor_get(v_defn_3217_, 0);
v_safety_3245_ = lean_ctor_get_uint8(v_defn_3217_, sizeof(void*)*4);
v___x_3246_ = 1;
v___x_3247_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3245_, v___x_3246_);
if (v___x_3247_ == 0)
{
lean_inc_ref(v_toConstantVal_3244_);
v___y_3234_ = v___y_3243_;
v___y_3235_ = v___y_3242_;
v___y_3236_ = v_toConstantVal_3244_;
v___y_3237_ = v_hasTrace_3212_;
goto v___jp_3233_;
}
else
{
lean_inc_ref(v_toConstantVal_3244_);
v___y_3234_ = v___y_3243_;
v___y_3235_ = v___y_3242_;
v___y_3236_ = v_toConstantVal_3244_;
v___y_3237_ = v___x_3213_;
goto v___jp_3233_;
}
}
v___jp_3250_:
{
lean_object* v_options_3251_; uint8_t v_hasTrace_3252_; 
v_options_3251_ = lean_ctor_get(v___y_3218_, 2);
v_hasTrace_3252_ = lean_ctor_get_uint8(v_options_3251_, sizeof(void*)*1);
if (v_hasTrace_3252_ == 0)
{
lean_dec(v_cls_3214_);
v___y_3242_ = v___y_3218_;
v___y_3243_ = v___y_3219_;
goto v___jp_3241_;
}
else
{
lean_object* v_inheritedTraceOptions_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; uint8_t v___x_3256_; 
v_inheritedTraceOptions_3253_ = lean_ctor_get(v___y_3218_, 13);
v___x_3254_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3214_);
v___x_3255_ = l_Lean_Name_append(v___x_3254_, v_cls_3214_);
v___x_3256_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3253_, v_options_3251_, v___x_3255_);
lean_dec(v___x_3255_);
if (v___x_3256_ == 0)
{
lean_dec(v_cls_3214_);
v___y_3242_ = v___y_3218_;
v___y_3243_ = v___y_3219_;
goto v___jp_3241_;
}
else
{
lean_object* v_toConstantVal_3257_; lean_object* v_name_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
v_toConstantVal_3257_ = lean_ctor_get(v_defn_3217_, 0);
v_name_3258_ = lean_ctor_get(v_toConstantVal_3257_, 0);
v___x_3259_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3258_);
v___x_3260_ = l_Lean_MessageData_ofName(v_name_3258_);
v___x_3261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3261_, 0, v___x_3259_);
lean_ctor_set(v___x_3261_, 1, v___x_3260_);
v___x_3262_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3261_);
lean_ctor_set(v___x_3263_, 1, v___x_3262_);
v___x_3264_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3214_, v___x_3263_, v___y_3218_, v___y_3219_);
if (lean_obj_tag(v___x_3264_) == 0)
{
lean_dec_ref_known(v___x_3264_, 1);
v___y_3242_ = v___y_3218_;
v___y_3243_ = v___y_3219_;
goto v___jp_3241_;
}
else
{
lean_dec_ref(v_defn_3217_);
lean_dec_ref(v___f_3211_);
return v___x_3264_;
}
}
}
}
v___jp_3267_:
{
lean_object* v___x_3268_; uint8_t v_isModule_3269_; 
v___x_3268_ = l_Lean_Environment_header(v_env_3265_);
lean_dec_ref(v_env_3265_);
v_isModule_3269_ = lean_ctor_get_uint8(v___x_3268_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3268_);
if (v_isModule_3269_ == 0)
{
lean_dec_ref(v_env_3266_);
lean_dec(v_cls_3214_);
v_exportedInfo_x3f_3222_ = v___x_3215_;
v___y_3223_ = v___y_3218_;
v___y_3224_ = v___y_3219_;
goto v___jp_3221_;
}
else
{
uint8_t v_isExporting_3270_; 
v_isExporting_3270_ = lean_ctor_get_uint8(v_env_3266_, sizeof(void*)*8);
lean_dec_ref(v_env_3266_);
if (v_isExporting_3270_ == 0)
{
lean_dec(v___x_3215_);
goto v___jp_3250_;
}
else
{
if (v___x_3213_ == 0)
{
lean_dec(v_cls_3214_);
v_exportedInfo_x3f_3222_ = v___x_3215_;
v___y_3223_ = v___y_3218_;
v___y_3224_ = v___y_3219_;
goto v___jp_3221_;
}
else
{
lean_dec(v___x_3215_);
goto v___jp_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3271_, lean_object* v_hasTrace_3272_, lean_object* v___x_3273_, lean_object* v_cls_3274_, lean_object* v___x_3275_, lean_object* v_forceExpose_3276_, lean_object* v_defn_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
uint8_t v_hasTrace_boxed_3281_; uint8_t v___x_63470__boxed_3282_; uint8_t v_forceExpose_boxed_3283_; lean_object* v_res_3284_; 
v_hasTrace_boxed_3281_ = lean_unbox(v_hasTrace_3272_);
v___x_63470__boxed_3282_ = lean_unbox(v___x_3273_);
v_forceExpose_boxed_3283_ = lean_unbox(v_forceExpose_3276_);
v_res_3284_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3271_, v_hasTrace_boxed_3281_, v___x_63470__boxed_3282_, v_cls_3274_, v___x_3275_, v_forceExpose_boxed_3283_, v_defn_3277_, v___y_3278_, v___y_3279_);
lean_dec(v___y_3279_);
lean_dec_ref(v___y_3278_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3285_, lean_object* v___f_3286_, lean_object* v_____r_3287_, lean_object* v_exportedInfo_x3f_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_toConstantVal_3292_; lean_object* v_name_3293_; lean_object* v___x_3294_; uint8_t v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; 
v_toConstantVal_3292_ = lean_ctor_get(v_val_3285_, 0);
v_name_3293_ = lean_ctor_get(v_toConstantVal_3292_, 0);
lean_inc(v_name_3293_);
v___x_3294_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3294_, 0, v_val_3285_);
v___x_3295_ = 1;
v___x_3296_ = lean_box(v___x_3295_);
v___x_3297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3294_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3298_, 0, v_name_3293_);
lean_ctor_set(v___x_3298_, 1, v___x_3297_);
lean_inc(v___y_3290_);
lean_inc_ref(v___y_3289_);
v___x_3299_ = lean_apply_5(v___f_3286_, v___x_3298_, v_exportedInfo_x3f_3288_, v___y_3289_, v___y_3290_, lean_box(0));
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3300_, lean_object* v___f_3301_, lean_object* v_____r_3302_, lean_object* v_exportedInfo_x3f_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3300_, v___f_3301_, v_____r_3302_, v_exportedInfo_x3f_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3308_, uint8_t v___x_3309_, lean_object* v___f_3310_, lean_object* v_____r_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
lean_object* v_toConstantVal_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; 
v_toConstantVal_3315_ = lean_ctor_get(v_val_3308_, 0);
lean_inc_ref(v_toConstantVal_3315_);
v___x_3316_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3316_, 0, v_toConstantVal_3315_);
lean_ctor_set_uint8(v___x_3316_, sizeof(void*)*1, v___x_3309_);
v___x_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3316_);
v___x_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3317_);
v___x_3319_ = lean_box(0);
lean_inc(v___y_3313_);
lean_inc_ref(v___y_3312_);
v___x_3320_ = lean_apply_5(v___f_3310_, v___x_3319_, v___x_3318_, v___y_3312_, v___y_3313_, lean_box(0));
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3321_, lean_object* v___x_3322_, lean_object* v___f_3323_, lean_object* v_____r_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_){
_start:
{
uint8_t v___x_63601__boxed_3328_; lean_object* v_res_3329_; 
v___x_63601__boxed_3328_ = lean_unbox(v___x_3322_);
v_res_3329_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3321_, v___x_63601__boxed_3328_, v___f_3323_, v_____r_3324_, v___y_3325_, v___y_3326_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
lean_dec_ref(v_val_3321_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3330_, lean_object* v___f_3331_, lean_object* v_____r_3332_, lean_object* v_exportedInfo_x3f_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_toConstantVal_3337_; lean_object* v_name_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_toConstantVal_3337_ = lean_ctor_get(v_val_3330_, 0);
v_name_3338_ = lean_ctor_get(v_toConstantVal_3337_, 0);
lean_inc(v_name_3338_);
v___x_3339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_val_3330_);
v___x_3340_ = 3;
v___x_3341_ = lean_box(v___x_3340_);
v___x_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3342_, 0, v___x_3339_);
lean_ctor_set(v___x_3342_, 1, v___x_3341_);
v___x_3343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3343_, 0, v_name_3338_);
lean_ctor_set(v___x_3343_, 1, v___x_3342_);
lean_inc(v___y_3335_);
lean_inc_ref(v___y_3334_);
v___x_3344_ = lean_apply_5(v___f_3331_, v___x_3343_, v_exportedInfo_x3f_3333_, v___y_3334_, v___y_3335_, lean_box(0));
return v___x_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3345_, lean_object* v___f_3346_, lean_object* v_____r_3347_, lean_object* v_exportedInfo_x3f_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3345_, v___f_3346_, v_____r_3347_, v_exportedInfo_x3f_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3353_, lean_object* v___f_3354_, lean_object* v_____r_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_toConstantVal_3359_; uint8_t v_isUnsafe_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_toConstantVal_3359_ = lean_ctor_get(v_val_3353_, 0);
v_isUnsafe_3360_ = lean_ctor_get_uint8(v_val_3353_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3359_);
v___x_3361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3361_, 0, v_toConstantVal_3359_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*1, v_isUnsafe_3360_);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = lean_box(0);
lean_inc(v___y_3357_);
lean_inc_ref(v___y_3356_);
v___x_3365_ = lean_apply_5(v___f_3354_, v___x_3364_, v___x_3363_, v___y_3356_, v___y_3357_, lean_box(0));
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3366_, lean_object* v___f_3367_, lean_object* v_____r_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3366_, v___f_3367_, v_____r_3368_, v___y_3369_, v___y_3370_);
lean_dec(v___y_3370_);
lean_dec_ref(v___y_3369_);
lean_dec_ref(v_val_3366_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3373_, uint8_t v___x_3374_, lean_object* v_cls_3375_, lean_object* v___x_3376_, lean_object* v___x_3377_, lean_object* v_____x_3378_, lean_object* v_exportedInfo_x3f_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v_a_3386_; lean_object* v___y_3397_; lean_object* v___y_3398_; lean_object* v_a_3399_; lean_object* v___y_3410_; lean_object* v___y_3411_; uint8_t v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3415_; lean_object* v___y_3416_; lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v_snd_3483_; lean_object* v_fst_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3613_; 
v_snd_3483_ = lean_ctor_get(v_____x_3378_, 1);
v_fst_3484_ = lean_ctor_get(v_____x_3378_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v_____x_3378_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3486_ = v_____x_3378_;
v_isShared_3487_ = v_isSharedCheck_3613_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_snd_3483_);
lean_inc(v_fst_3484_);
lean_dec(v_____x_3378_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3613_;
goto v_resetjp_3485_;
}
v___jp_3383_:
{
lean_object* v___x_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
v___x_3387_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3385_, v___y_3384_);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3394_ == 0)
{
lean_object* v_unused_3395_; 
v_unused_3395_ = lean_ctor_get(v___x_3387_, 0);
lean_dec(v_unused_3395_);
v___x_3389_ = v___x_3387_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_dec(v___x_3387_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
lean_ctor_set_tag(v___x_3389_, 1);
lean_ctor_set(v___x_3389_, 0, v_a_3386_);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3386_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
v___jp_3396_:
{
lean_object* v___x_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3407_; 
v___x_3400_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3398_, v___y_3397_);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3400_);
if (v_isSharedCheck_3407_ == 0)
{
lean_object* v_unused_3408_; 
v_unused_3408_ = lean_ctor_get(v___x_3400_, 0);
lean_dec(v_unused_3408_);
v___x_3402_ = v___x_3400_;
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
else
{
lean_dec(v___x_3400_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3407_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
lean_object* v___x_3405_; 
if (v_isShared_3403_ == 0)
{
lean_ctor_set(v___x_3402_, 0, v_a_3399_);
v___x_3405_ = v___x_3402_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v_a_3399_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
v___jp_3409_:
{
lean_object* v___x_3421_; 
lean_inc_ref(v___y_3419_);
v___x_3421_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3416_, v___y_3419_, v___y_3418_, v___y_3420_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v___x_3422_; lean_object* v___x_3424_; uint8_t v_isShared_3425_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref_known(v___x_3421_, 1);
lean_inc_ref(v___y_3414_);
v___x_3422_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3414_, v___y_3413_);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3422_);
if (v_isSharedCheck_3468_ == 0)
{
lean_object* v_unused_3469_; 
v_unused_3469_ = lean_ctor_get(v___x_3422_, 0);
lean_dec(v_unused_3469_);
v___x_3424_ = v___x_3422_;
v_isShared_3425_ = v_isSharedCheck_3468_;
goto v_resetjp_3423_;
}
else
{
lean_dec(v___x_3422_);
v___x_3424_ = lean_box(0);
v_isShared_3425_ = v_isSharedCheck_3468_;
goto v_resetjp_3423_;
}
v_resetjp_3423_:
{
lean_object* v_options_3426_; lean_object* v___x_3427_; uint8_t v___x_3428_; 
v_options_3426_ = lean_ctor_get(v___y_3415_, 2);
v___x_3427_ = l_Lean_Elab_async;
v___x_3428_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3426_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; lean_object* v_r_3430_; 
lean_del_object(v___x_3424_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3411_);
v___x_3429_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3419_, v___y_3413_);
lean_dec_ref(v___x_3429_);
v_r_3430_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3373_, v___y_3415_, v___y_3413_);
if (lean_obj_tag(v_r_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3433_; uint8_t v_isShared_3434_; uint8_t v_isSharedCheck_3440_; 
v_a_3431_ = lean_ctor_get(v_r_3430_, 0);
v_isSharedCheck_3440_ = !lean_is_exclusive(v_r_3430_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3433_ = v_r_3430_;
v_isShared_3434_ = v_isSharedCheck_3440_;
goto v_resetjp_3432_;
}
else
{
lean_inc(v_a_3431_);
lean_dec(v_r_3430_);
v___x_3433_ = lean_box(0);
v_isShared_3434_ = v_isSharedCheck_3440_;
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
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3431_);
v___x_3436_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3435_;
}
v_reusejp_3435_:
{
lean_object* v___x_3437_; 
v___x_3437_ = lean_apply_2(v___y_3410_, v___x_3436_, lean_box(0));
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_dec_ref_known(v___x_3437_, 1);
v___y_3397_ = v___y_3413_;
v___y_3398_ = v___y_3414_;
v_a_3399_ = v_a_3431_;
goto v___jp_3396_;
}
else
{
lean_object* v_a_3438_; 
lean_dec(v_a_3431_);
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v___y_3384_ = v___y_3413_;
v___y_3385_ = v___y_3414_;
v_a_3386_ = v_a_3438_;
goto v___jp_3383_;
}
}
}
}
else
{
lean_object* v_a_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; 
v_a_3441_ = lean_ctor_get(v_r_3430_, 0);
lean_inc(v_a_3441_);
lean_dec_ref_known(v_r_3430_, 1);
v___x_3442_ = lean_box(0);
v___x_3443_ = lean_apply_2(v___y_3410_, v___x_3442_, lean_box(0));
if (lean_obj_tag(v___x_3443_) == 0)
{
lean_dec_ref_known(v___x_3443_, 1);
v___y_3384_ = v___y_3413_;
v___y_3385_ = v___y_3414_;
v_a_3386_ = v_a_3441_;
goto v___jp_3383_;
}
else
{
lean_object* v_a_3444_; 
lean_dec(v_a_3441_);
v_a_3444_ = lean_ctor_get(v___x_3443_, 0);
lean_inc(v_a_3444_);
lean_dec_ref_known(v___x_3443_, 1);
v___y_3384_ = v___y_3413_;
v___y_3385_ = v___y_3414_;
v_a_3386_ = v_a_3444_;
goto v___jp_3383_;
}
}
}
else
{
lean_object* v___x_3445_; lean_object* v___x_3447_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3410_);
lean_dec(v_decl_3373_);
v___x_3445_ = l_IO_CancelToken_new();
if (v_isShared_3425_ == 0)
{
lean_ctor_set_tag(v___x_3424_, 1);
lean_ctor_set(v___x_3424_, 0, v___x_3445_);
v___x_3447_ = v___x_3424_;
goto v_reusejp_3446_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3445_);
v___x_3447_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3446_;
}
v_reusejp_3446_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3448_ = lean_unsigned_to_nat(0u);
v___x_3449_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3450_ = l_Lean_Name_toString(v___x_3449_, v___x_3374_);
lean_inc_ref(v___x_3447_);
v___x_3451_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3411_, v___x_3447_, v___x_3450_, v___y_3415_, v___y_3413_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v_checked_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v_checked_3453_ = lean_ctor_get(v___y_3417_, 2);
lean_inc_ref(v_checked_3453_);
lean_dec_ref(v___y_3417_);
v___x_3454_ = lean_io_map_task(v_a_3452_, v_checked_3453_, v___x_3448_, v___y_3412_);
v___x_3455_ = lean_box(0);
v___x_3456_ = lean_box(2);
v___x_3457_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3455_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
lean_ctor_set(v___x_3457_, 2, v___x_3447_);
lean_ctor_set(v___x_3457_, 3, v___x_3454_);
v___x_3458_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3457_, v___y_3413_);
return v___x_3458_;
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec_ref(v___x_3447_);
lean_dec_ref(v___y_3417_);
v_a_3459_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3451_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3451_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3482_; 
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3417_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v___y_3411_);
lean_dec_ref(v___y_3410_);
lean_dec(v_decl_3373_);
v_a_3470_ = lean_ctor_get(v___x_3421_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3421_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3472_ = v___x_3421_;
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_a_3470_);
lean_dec(v___x_3421_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3482_;
goto v_resetjp_3471_;
}
v_resetjp_3471_:
{
lean_object* v_ref_3474_; lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v___x_3480_; 
v_ref_3474_ = lean_ctor_get(v___y_3415_, 5);
v___x_3475_ = lean_io_error_to_string(v_a_3470_);
v___x_3476_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3476_, 0, v___x_3475_);
v___x_3477_ = l_Lean_MessageData_ofFormat(v___x_3476_);
lean_inc(v_ref_3474_);
v___x_3478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3478_, 0, v_ref_3474_);
lean_ctor_set(v___x_3478_, 1, v___x_3477_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set(v___x_3472_, 0, v___x_3478_);
v___x_3480_ = v___x_3472_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v___x_3478_);
v___x_3480_ = v_reuseFailAlloc_3481_;
goto v_reusejp_3479_;
}
v_reusejp_3479_:
{
return v___x_3480_;
}
}
}
}
v_resetjp_3485_:
{
lean_object* v_fst_3488_; lean_object* v_snd_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3612_; 
v_fst_3488_ = lean_ctor_get(v_snd_3483_, 0);
v_snd_3489_ = lean_ctor_get(v_snd_3483_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_snd_3483_);
if (v_isSharedCheck_3612_ == 0)
{
v___x_3491_ = v_snd_3483_;
v_isShared_3492_ = v_isSharedCheck_3612_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_snd_3489_);
lean_inc(v_fst_3488_);
lean_dec(v_snd_3483_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3612_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; lean_object* v___y_3497_; lean_object* v___y_3498_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v_exportedInfo_x3f_3526_; lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3538_; lean_object* v___y_3539_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3546_; lean_object* v___y_3547_; uint8_t v___y_3548_; lean_object* v___y_3578_; lean_object* v___y_3579_; lean_object* v___x_3602_; lean_object* v_env_3603_; uint8_t v___x_3604_; 
v___x_3602_ = lean_st_ref_get(v___y_3381_);
v_env_3603_ = lean_ctor_get(v___x_3602_, 0);
lean_inc_ref(v_env_3603_);
lean_dec(v___x_3602_);
v___x_3604_ = l_Lean_Environment_containsOnBranch(v_env_3603_, v_fst_3484_);
lean_dec_ref(v_env_3603_);
if (v___x_3604_ == 0)
{
lean_del_object(v___x_3486_);
v___y_3578_ = v___y_3380_;
v___y_3579_ = v___y_3381_;
goto v___jp_3577_;
}
else
{
lean_object* v___x_3605_; lean_object* v_env_3606_; lean_object* v___x_3607_; lean_object* v___x_3609_; 
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_fst_3488_);
lean_dec(v_exportedInfo_x3f_3379_);
lean_dec(v___x_3377_);
lean_dec_ref(v___x_3376_);
lean_dec(v_cls_3375_);
lean_dec(v_decl_3373_);
v___x_3605_ = lean_st_ref_get(v___y_3381_);
v_env_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc_ref(v_env_3606_);
lean_dec(v___x_3605_);
v___x_3607_ = lean_elab_environment_to_kernel_env(v_env_3606_);
if (v_isShared_3487_ == 0)
{
lean_ctor_set_tag(v___x_3486_, 1);
lean_ctor_set(v___x_3486_, 1, v_fst_3484_);
lean_ctor_set(v___x_3486_, 0, v___x_3607_);
v___x_3609_ = v___x_3486_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3607_);
lean_ctor_set(v_reuseFailAlloc_3611_, 1, v_fst_3484_);
v___x_3609_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; 
v___x_3610_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3609_, v___y_3380_, v___y_3381_);
return v___x_3610_;
}
}
v___jp_3493_:
{
uint8_t v___x_3501_; uint8_t v___x_3502_; lean_object* v___x_3503_; 
v___x_3501_ = 0;
v___x_3502_ = lean_unbox(v_snd_3489_);
lean_dec(v_snd_3489_);
lean_inc_ref(v___y_3495_);
v___x_3503_ = l_Lean_Environment_addConstAsync(v___y_3495_, v_fst_3484_, v___x_3502_, v___y_3500_, v___x_3501_, v___x_3374_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v_mainEnv_3505_; lean_object* v_asyncEnv_3506_; lean_object* v___f_3507_; lean_object* v___f_3508_; lean_object* v___x_3509_; 
lean_del_object(v___x_3491_);
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc_n(v_a_3504_, 3);
lean_dec_ref_known(v___x_3503_, 1);
v_mainEnv_3505_ = lean_ctor_get(v_a_3504_, 0);
lean_inc_ref(v_mainEnv_3505_);
v_asyncEnv_3506_ = lean_ctor_get(v_a_3504_, 1);
lean_inc_ref_n(v_asyncEnv_3506_, 2);
lean_inc_ref(v___y_3494_);
lean_inc(v___y_3496_);
v___f_3507_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3507_, 0, v___y_3496_);
lean_closure_set(v___f_3507_, 1, v_a_3504_);
lean_closure_set(v___f_3507_, 2, v___y_3494_);
lean_inc(v_decl_3373_);
v___f_3508_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3508_, 0, v_asyncEnv_3506_);
lean_closure_set(v___f_3508_, 1, v_a_3504_);
lean_closure_set(v___f_3508_, 2, v_decl_3373_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v_fst_3488_);
if (lean_obj_tag(v___y_3497_) == 0)
{
lean_inc_ref(v___x_3509_);
v___y_3410_ = v___f_3507_;
v___y_3411_ = v___f_3508_;
v___y_3412_ = v___x_3501_;
v___y_3413_ = v___y_3498_;
v___y_3414_ = v_mainEnv_3505_;
v___y_3415_ = v___y_3499_;
v___y_3416_ = v_a_3504_;
v___y_3417_ = v___y_3495_;
v___y_3418_ = v___x_3509_;
v___y_3419_ = v_asyncEnv_3506_;
v___y_3420_ = v___x_3509_;
goto v___jp_3409_;
}
else
{
v___y_3410_ = v___f_3507_;
v___y_3411_ = v___f_3508_;
v___y_3412_ = v___x_3501_;
v___y_3413_ = v___y_3498_;
v___y_3414_ = v_mainEnv_3505_;
v___y_3415_ = v___y_3499_;
v___y_3416_ = v_a_3504_;
v___y_3417_ = v___y_3495_;
v___y_3418_ = v___x_3509_;
v___y_3419_ = v_asyncEnv_3506_;
v___y_3420_ = v___y_3497_;
goto v___jp_3409_;
}
}
else
{
lean_object* v_a_3510_; lean_object* v___x_3512_; uint8_t v_isShared_3513_; uint8_t v_isSharedCheck_3524_; 
lean_dec(v___y_3497_);
lean_dec_ref(v___y_3495_);
lean_dec(v_fst_3488_);
lean_dec(v_decl_3373_);
v_a_3510_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3512_ = v___x_3503_;
v_isShared_3513_ = v_isSharedCheck_3524_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3503_);
v___x_3512_ = lean_box(0);
v_isShared_3513_ = v_isSharedCheck_3524_;
goto v_resetjp_3511_;
}
v_resetjp_3511_:
{
lean_object* v_ref_3514_; lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v_ref_3514_ = lean_ctor_get(v___y_3499_, 5);
v___x_3515_ = lean_io_error_to_string(v_a_3510_);
v___x_3516_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3516_, 0, v___x_3515_);
v___x_3517_ = l_Lean_MessageData_ofFormat(v___x_3516_);
lean_inc(v_ref_3514_);
if (v_isShared_3492_ == 0)
{
lean_ctor_set(v___x_3491_, 1, v___x_3517_);
lean_ctor_set(v___x_3491_, 0, v_ref_3514_);
v___x_3519_ = v___x_3491_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_ref_3514_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3513_ == 0)
{
lean_ctor_set(v___x_3512_, 0, v___x_3519_);
v___x_3521_ = v___x_3512_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3519_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
}
}
}
v___jp_3525_:
{
lean_object* v___x_3529_; 
v___x_3529_ = lean_st_ref_get(v___y_3528_);
if (lean_obj_tag(v_exportedInfo_x3f_3526_) == 0)
{
lean_object* v_env_3530_; lean_object* v___x_3531_; 
v_env_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc_ref(v_env_3530_);
lean_dec(v___x_3529_);
v___x_3531_ = lean_box(0);
v___y_3494_ = v___y_3527_;
v___y_3495_ = v_env_3530_;
v___y_3496_ = v___y_3528_;
v___y_3497_ = v_exportedInfo_x3f_3526_;
v___y_3498_ = v___y_3528_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___x_3531_;
goto v___jp_3493_;
}
else
{
lean_object* v_env_3532_; lean_object* v_val_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
v_env_3532_ = lean_ctor_get(v___x_3529_, 0);
lean_inc_ref(v_env_3532_);
lean_dec(v___x_3529_);
v_val_3533_ = lean_ctor_get(v_exportedInfo_x3f_3526_, 0);
v___x_3534_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3533_);
v___x_3535_ = lean_box(v___x_3534_);
v___x_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3536_, 0, v___x_3535_);
v___y_3494_ = v___y_3527_;
v___y_3495_ = v_env_3532_;
v___y_3496_ = v___y_3528_;
v___y_3497_ = v_exportedInfo_x3f_3526_;
v___y_3498_ = v___y_3528_;
v___y_3499_ = v___y_3527_;
v___y_3500_ = v___x_3536_;
goto v___jp_3493_;
}
}
v___jp_3537_:
{
lean_object* v___x_3540_; 
lean_inc(v_fst_3488_);
v___x_3540_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3540_, 0, v_fst_3488_);
v_exportedInfo_x3f_3526_ = v___x_3540_;
v___y_3527_ = v___y_3538_;
v___y_3528_ = v___y_3539_;
goto v___jp_3525_;
}
v___jp_3541_:
{
lean_object* v___x_3544_; 
lean_inc(v_fst_3488_);
v___x_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3544_, 0, v_fst_3488_);
v_exportedInfo_x3f_3526_ = v___x_3544_;
v___y_3527_ = v___y_3542_;
v___y_3528_ = v___y_3543_;
goto v___jp_3525_;
}
v___jp_3545_:
{
if (v___y_3548_ == 0)
{
lean_object* v_options_3549_; uint8_t v_hasTrace_3550_; 
lean_dec(v_exportedInfo_x3f_3379_);
lean_dec_ref(v___x_3376_);
v_options_3549_ = lean_ctor_get(v___y_3547_, 2);
v_hasTrace_3550_ = lean_ctor_get_uint8(v_options_3549_, sizeof(void*)*1);
if (v_hasTrace_3550_ == 0)
{
lean_dec(v_cls_3375_);
v___y_3538_ = v___y_3547_;
v___y_3539_ = v___y_3546_;
goto v___jp_3537_;
}
else
{
lean_object* v_inheritedTraceOptions_3551_; lean_object* v___x_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v_inheritedTraceOptions_3551_ = lean_ctor_get(v___y_3547_, 13);
v___x_3552_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3375_);
v___x_3553_ = l_Lean_Name_append(v___x_3552_, v_cls_3375_);
v___x_3554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3551_, v_options_3549_, v___x_3553_);
lean_dec(v___x_3553_);
if (v___x_3554_ == 0)
{
lean_dec(v_cls_3375_);
v___y_3538_ = v___y_3547_;
v___y_3539_ = v___y_3546_;
goto v___jp_3537_;
}
else
{
lean_object* v___x_3555_; lean_object* v___x_3556_; 
v___x_3555_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3556_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3375_, v___x_3555_, v___y_3547_, v___y_3546_);
if (lean_obj_tag(v___x_3556_) == 0)
{
lean_dec_ref_known(v___x_3556_, 1);
v___y_3538_ = v___y_3547_;
v___y_3539_ = v___y_3546_;
goto v___jp_3537_;
}
else
{
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_fst_3488_);
lean_dec(v_fst_3484_);
lean_dec(v_decl_3373_);
return v___x_3556_;
}
}
}
}
else
{
lean_object* v___x_3557_; lean_object* v_env_3558_; lean_object* v_nextMacroScope_3559_; lean_object* v_ngen_3560_; lean_object* v_auxDeclNGen_3561_; lean_object* v_traceState_3562_; lean_object* v_messages_3563_; lean_object* v_infoState_3564_; lean_object* v_snapshotTasks_3565_; lean_object* v___x_3567_; uint8_t v_isShared_3568_; uint8_t v_isSharedCheck_3575_; 
lean_dec(v_cls_3375_);
v___x_3557_ = lean_st_ref_take(v___y_3546_);
v_env_3558_ = lean_ctor_get(v___x_3557_, 0);
v_nextMacroScope_3559_ = lean_ctor_get(v___x_3557_, 1);
v_ngen_3560_ = lean_ctor_get(v___x_3557_, 2);
v_auxDeclNGen_3561_ = lean_ctor_get(v___x_3557_, 3);
v_traceState_3562_ = lean_ctor_get(v___x_3557_, 4);
v_messages_3563_ = lean_ctor_get(v___x_3557_, 6);
v_infoState_3564_ = lean_ctor_get(v___x_3557_, 7);
v_snapshotTasks_3565_ = lean_ctor_get(v___x_3557_, 8);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3575_ == 0)
{
lean_object* v_unused_3576_; 
v_unused_3576_ = lean_ctor_get(v___x_3557_, 5);
lean_dec(v_unused_3576_);
v___x_3567_ = v___x_3557_;
v_isShared_3568_ = v_isSharedCheck_3575_;
goto v_resetjp_3566_;
}
else
{
lean_inc(v_snapshotTasks_3565_);
lean_inc(v_infoState_3564_);
lean_inc(v_messages_3563_);
lean_inc(v_traceState_3562_);
lean_inc(v_auxDeclNGen_3561_);
lean_inc(v_ngen_3560_);
lean_inc(v_nextMacroScope_3559_);
lean_inc(v_env_3558_);
lean_dec(v___x_3557_);
v___x_3567_ = lean_box(0);
v_isShared_3568_ = v_isSharedCheck_3575_;
goto v_resetjp_3566_;
}
v_resetjp_3566_:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3572_; 
v___x_3569_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3489_);
lean_inc(v_fst_3484_);
v___x_3570_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3569_, v_env_3558_, v_fst_3484_, v_snd_3489_);
if (v_isShared_3568_ == 0)
{
lean_ctor_set(v___x_3567_, 5, v___x_3376_);
lean_ctor_set(v___x_3567_, 0, v___x_3570_);
v___x_3572_ = v___x_3567_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v___x_3570_);
lean_ctor_set(v_reuseFailAlloc_3574_, 1, v_nextMacroScope_3559_);
lean_ctor_set(v_reuseFailAlloc_3574_, 2, v_ngen_3560_);
lean_ctor_set(v_reuseFailAlloc_3574_, 3, v_auxDeclNGen_3561_);
lean_ctor_set(v_reuseFailAlloc_3574_, 4, v_traceState_3562_);
lean_ctor_set(v_reuseFailAlloc_3574_, 5, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3574_, 6, v_messages_3563_);
lean_ctor_set(v_reuseFailAlloc_3574_, 7, v_infoState_3564_);
lean_ctor_set(v_reuseFailAlloc_3574_, 8, v_snapshotTasks_3565_);
v___x_3572_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
lean_object* v___x_3573_; 
v___x_3573_ = lean_st_ref_set(v___y_3546_, v___x_3572_);
v_exportedInfo_x3f_3526_ = v_exportedInfo_x3f_3379_;
v___y_3527_ = v___y_3547_;
v___y_3528_ = v___y_3546_;
goto v___jp_3525_;
}
}
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; uint8_t v___x_3581_; 
lean_inc(v_decl_3373_);
v___x_3580_ = l_Lean_Declaration_getTopLevelNames(v_decl_3373_);
v___x_3581_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3580_);
lean_dec(v___x_3580_);
if (v___x_3581_ == 0)
{
lean_dec(v___x_3377_);
if (lean_obj_tag(v_exportedInfo_x3f_3379_) == 0)
{
v___y_3546_ = v___y_3579_;
v___y_3547_ = v___y_3578_;
v___y_3548_ = v___x_3581_;
goto v___jp_3545_;
}
else
{
v___y_3546_ = v___y_3579_;
v___y_3547_ = v___y_3578_;
v___y_3548_ = v___x_3374_;
goto v___jp_3545_;
}
}
else
{
lean_object* v___x_3582_; lean_object* v___x_3583_; lean_object* v_a_3584_; uint8_t v___x_3585_; 
lean_dec(v_exportedInfo_x3f_3379_);
lean_dec_ref(v___x_3376_);
v___x_3582_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3583_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3582_, v___y_3578_);
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref(v___x_3583_);
v___x_3585_ = lean_unbox(v_a_3584_);
lean_dec(v_a_3584_);
if (v___x_3585_ == 0)
{
lean_object* v_options_3586_; uint8_t v_hasTrace_3587_; 
v_options_3586_ = lean_ctor_get(v___y_3578_, 2);
v_hasTrace_3587_ = lean_ctor_get_uint8(v_options_3586_, sizeof(void*)*1);
if (v_hasTrace_3587_ == 0)
{
lean_dec(v_cls_3375_);
v_exportedInfo_x3f_3526_ = v___x_3377_;
v___y_3527_ = v___y_3578_;
v___y_3528_ = v___y_3579_;
goto v___jp_3525_;
}
else
{
lean_object* v_inheritedTraceOptions_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; uint8_t v___x_3591_; 
v_inheritedTraceOptions_3588_ = lean_ctor_get(v___y_3578_, 13);
v___x_3589_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3375_);
v___x_3590_ = l_Lean_Name_append(v___x_3589_, v_cls_3375_);
v___x_3591_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3588_, v_options_3586_, v___x_3590_);
lean_dec(v___x_3590_);
if (v___x_3591_ == 0)
{
lean_dec(v_cls_3375_);
v_exportedInfo_x3f_3526_ = v___x_3377_;
v___y_3527_ = v___y_3578_;
v___y_3528_ = v___y_3579_;
goto v___jp_3525_;
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3593_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3375_, v___x_3592_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_dec_ref_known(v___x_3593_, 1);
v_exportedInfo_x3f_3526_ = v___x_3377_;
v___y_3527_ = v___y_3578_;
v___y_3528_ = v___y_3579_;
goto v___jp_3525_;
}
else
{
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_fst_3488_);
lean_dec(v_fst_3484_);
lean_dec(v___x_3377_);
lean_dec(v_decl_3373_);
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_options_3594_; uint8_t v_hasTrace_3595_; 
lean_dec(v___x_3377_);
v_options_3594_ = lean_ctor_get(v___y_3578_, 2);
v_hasTrace_3595_ = lean_ctor_get_uint8(v_options_3594_, sizeof(void*)*1);
if (v_hasTrace_3595_ == 0)
{
lean_dec(v_cls_3375_);
v___y_3542_ = v___y_3578_;
v___y_3543_ = v___y_3579_;
goto v___jp_3541_;
}
else
{
lean_object* v_inheritedTraceOptions_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; uint8_t v___x_3599_; 
v_inheritedTraceOptions_3596_ = lean_ctor_get(v___y_3578_, 13);
v___x_3597_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3375_);
v___x_3598_ = l_Lean_Name_append(v___x_3597_, v_cls_3375_);
v___x_3599_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3596_, v_options_3594_, v___x_3598_);
lean_dec(v___x_3598_);
if (v___x_3599_ == 0)
{
lean_dec(v_cls_3375_);
v___y_3542_ = v___y_3578_;
v___y_3543_ = v___y_3579_;
goto v___jp_3541_;
}
else
{
lean_object* v___x_3600_; lean_object* v___x_3601_; 
v___x_3600_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3601_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3375_, v___x_3600_, v___y_3578_, v___y_3579_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_dec_ref_known(v___x_3601_, 1);
v___y_3542_ = v___y_3578_;
v___y_3543_ = v___y_3579_;
goto v___jp_3541_;
}
else
{
lean_del_object(v___x_3491_);
lean_dec(v_snd_3489_);
lean_dec(v_fst_3488_);
lean_dec(v_fst_3484_);
lean_dec(v_decl_3373_);
return v___x_3601_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3614_, lean_object* v___x_3615_, lean_object* v_cls_3616_, lean_object* v___x_3617_, lean_object* v___x_3618_, lean_object* v_____x_3619_, lean_object* v_exportedInfo_x3f_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
uint8_t v___x_63732__boxed_3624_; lean_object* v_res_3625_; 
v___x_63732__boxed_3624_ = lean_unbox(v___x_3615_);
v_res_3625_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3614_, v___x_63732__boxed_3624_, v_cls_3616_, v___x_3617_, v___x_3618_, v_____x_3619_, v_exportedInfo_x3f_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
return v_res_3625_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3626_, uint8_t v_forceExpose_3627_, uint8_t v___x_3628_, lean_object* v___x_3629_, lean_object* v_cls_3630_, lean_object* v_defn_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_){
_start:
{
lean_object* v_exportedInfo_x3f_3636_; lean_object* v___y_3637_; lean_object* v___y_3638_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; uint8_t v___y_3651_; lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_st_ref_get(v___y_3633_);
v___x_3656_ = lean_st_ref_get(v___y_3633_);
if (v_forceExpose_3627_ == 0)
{
if (v___x_3628_ == 0)
{
lean_dec(v___x_3656_);
lean_dec(v___x_3655_);
lean_dec(v_cls_3630_);
v_exportedInfo_x3f_3636_ = v___x_3629_;
v___y_3637_ = v___y_3632_;
v___y_3638_ = v___y_3633_;
goto v___jp_3635_;
}
else
{
lean_object* v_env_3657_; lean_object* v_env_3658_; lean_object* v___x_3659_; uint8_t v_isModule_3660_; 
v_env_3657_ = lean_ctor_get(v___x_3655_, 0);
lean_inc_ref(v_env_3657_);
lean_dec(v___x_3655_);
v_env_3658_ = lean_ctor_get(v___x_3656_, 0);
lean_inc_ref(v_env_3658_);
lean_dec(v___x_3656_);
v___x_3659_ = l_Lean_Environment_header(v_env_3657_);
lean_dec_ref(v_env_3657_);
v_isModule_3660_ = lean_ctor_get_uint8(v___x_3659_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3659_);
if (v_isModule_3660_ == 0)
{
lean_dec_ref(v_env_3658_);
lean_dec(v_cls_3630_);
v_exportedInfo_x3f_3636_ = v___x_3629_;
v___y_3637_ = v___y_3632_;
v___y_3638_ = v___y_3633_;
goto v___jp_3635_;
}
else
{
uint8_t v_isExporting_3661_; lean_object* v___y_3663_; lean_object* v___y_3664_; 
v_isExporting_3661_ = lean_ctor_get_uint8(v_env_3658_, sizeof(void*)*8);
lean_dec_ref(v_env_3658_);
if (v_isExporting_3661_ == 0)
{
lean_object* v_options_3669_; uint8_t v_hasTrace_3670_; 
lean_dec(v___x_3629_);
v_options_3669_ = lean_ctor_get(v___y_3632_, 2);
v_hasTrace_3670_ = lean_ctor_get_uint8(v_options_3669_, sizeof(void*)*1);
if (v_hasTrace_3670_ == 0)
{
lean_dec(v_cls_3630_);
v___y_3663_ = v___y_3632_;
v___y_3664_ = v___y_3633_;
goto v___jp_3662_;
}
else
{
lean_object* v_inheritedTraceOptions_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; uint8_t v___x_3674_; 
v_inheritedTraceOptions_3671_ = lean_ctor_get(v___y_3632_, 13);
v___x_3672_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3630_);
v___x_3673_ = l_Lean_Name_append(v___x_3672_, v_cls_3630_);
v___x_3674_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3671_, v_options_3669_, v___x_3673_);
lean_dec(v___x_3673_);
if (v___x_3674_ == 0)
{
lean_dec(v_cls_3630_);
v___y_3663_ = v___y_3632_;
v___y_3664_ = v___y_3633_;
goto v___jp_3662_;
}
else
{
lean_object* v_toConstantVal_3675_; lean_object* v_name_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; 
v_toConstantVal_3675_ = lean_ctor_get(v_defn_3631_, 0);
v_name_3676_ = lean_ctor_get(v_toConstantVal_3675_, 0);
v___x_3677_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3676_);
v___x_3678_ = l_Lean_MessageData_ofName(v_name_3676_);
v___x_3679_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3677_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3681_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3679_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3630_, v___x_3681_, v___y_3632_, v___y_3633_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
v___y_3663_ = v___y_3632_;
v___y_3664_ = v___y_3633_;
goto v___jp_3662_;
}
else
{
lean_dec_ref(v_defn_3631_);
lean_dec_ref(v___f_3626_);
return v___x_3682_;
}
}
}
}
else
{
lean_dec(v_cls_3630_);
v_exportedInfo_x3f_3636_ = v___x_3629_;
v___y_3637_ = v___y_3632_;
v___y_3638_ = v___y_3633_;
goto v___jp_3635_;
}
v___jp_3662_:
{
lean_object* v_toConstantVal_3665_; uint8_t v_safety_3666_; uint8_t v___x_3667_; uint8_t v___x_3668_; 
v_toConstantVal_3665_ = lean_ctor_get(v_defn_3631_, 0);
v_safety_3666_ = lean_ctor_get_uint8(v_defn_3631_, sizeof(void*)*4);
v___x_3667_ = 1;
v___x_3668_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3666_, v___x_3667_);
if (v___x_3668_ == 0)
{
lean_inc_ref(v_toConstantVal_3665_);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_toConstantVal_3665_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v___x_3628_;
goto v___jp_3647_;
}
else
{
lean_inc_ref(v_toConstantVal_3665_);
v___y_3648_ = v___y_3663_;
v___y_3649_ = v_toConstantVal_3665_;
v___y_3650_ = v___y_3664_;
v___y_3651_ = v_isExporting_3661_;
goto v___jp_3647_;
}
}
}
}
}
else
{
lean_dec(v___x_3656_);
lean_dec(v___x_3655_);
lean_dec(v_cls_3630_);
v_exportedInfo_x3f_3636_ = v___x_3629_;
v___y_3637_ = v___y_3632_;
v___y_3638_ = v___y_3633_;
goto v___jp_3635_;
}
v___jp_3635_:
{
lean_object* v_toConstantVal_3639_; lean_object* v_name_3640_; lean_object* v___x_3641_; uint8_t v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; 
v_toConstantVal_3639_ = lean_ctor_get(v_defn_3631_, 0);
v_name_3640_ = lean_ctor_get(v_toConstantVal_3639_, 0);
lean_inc(v_name_3640_);
v___x_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3641_, 0, v_defn_3631_);
v___x_3642_ = 0;
v___x_3643_ = lean_box(v___x_3642_);
v___x_3644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3641_);
lean_ctor_set(v___x_3644_, 1, v___x_3643_);
v___x_3645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3645_, 0, v_name_3640_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
lean_inc(v___y_3638_);
lean_inc_ref(v___y_3637_);
v___x_3646_ = lean_apply_5(v___f_3626_, v___x_3645_, v_exportedInfo_x3f_3636_, v___y_3637_, v___y_3638_, lean_box(0));
return v___x_3646_;
}
v___jp_3647_:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3652_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3652_, 0, v___y_3649_);
lean_ctor_set_uint8(v___x_3652_, sizeof(void*)*1, v___y_3651_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
v_exportedInfo_x3f_3636_ = v___x_3654_;
v___y_3637_ = v___y_3648_;
v___y_3638_ = v___y_3650_;
goto v___jp_3635_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3683_, lean_object* v_forceExpose_3684_, lean_object* v___x_3685_, lean_object* v___x_3686_, lean_object* v_cls_3687_, lean_object* v_defn_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
uint8_t v_forceExpose_boxed_3692_; uint8_t v___x_64207__boxed_3693_; lean_object* v_res_3694_; 
v_forceExpose_boxed_3692_ = lean_unbox(v_forceExpose_3684_);
v___x_64207__boxed_3693_ = lean_unbox(v___x_3685_);
v_res_3694_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3683_, v_forceExpose_boxed_3692_, v___x_64207__boxed_3693_, v___x_3686_, v_cls_3687_, v_defn_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
return v_res_3694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3695_, uint8_t v_forceExpose_3696_, lean_object* v___f_3697_, lean_object* v_____r_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
lean_object* v_toConstantVal_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v_toConstantVal_3702_ = lean_ctor_get(v_val_3695_, 0);
lean_inc_ref(v_toConstantVal_3702_);
v___x_3703_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3703_, 0, v_toConstantVal_3702_);
lean_ctor_set_uint8(v___x_3703_, sizeof(void*)*1, v_forceExpose_3696_);
v___x_3704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v___x_3705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3705_, 0, v___x_3704_);
v___x_3706_ = lean_box(0);
lean_inc(v___y_3700_);
lean_inc_ref(v___y_3699_);
v___x_3707_ = lean_apply_5(v___f_3697_, v___x_3706_, v___x_3705_, v___y_3699_, v___y_3700_, lean_box(0));
return v___x_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3708_, lean_object* v_forceExpose_3709_, lean_object* v___f_3710_, lean_object* v_____r_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
uint8_t v_forceExpose_boxed_3715_; lean_object* v_res_3716_; 
v_forceExpose_boxed_3715_ = lean_unbox(v_forceExpose_3709_);
v_res_3716_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3708_, v_forceExpose_boxed_3715_, v___f_3710_, v_____r_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v_val_3708_);
return v_res_3716_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3717_, lean_object* v_x_3718_){
_start:
{
if (lean_obj_tag(v_x_3718_) == 0)
{
return v_x_3717_;
}
else
{
lean_object* v_head_3719_; lean_object* v_tail_3720_; lean_object* v___x_3721_; 
v_head_3719_ = lean_ctor_get(v_x_3718_, 0);
lean_inc(v_head_3719_);
v_tail_3720_ = lean_ctor_get(v_x_3718_, 1);
lean_inc(v_tail_3720_);
lean_dec_ref_known(v_x_3718_, 2);
v___x_3721_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3717_, v_head_3719_);
v_x_3717_ = v___x_3721_;
v_x_3718_ = v_tail_3720_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3723_; lean_object* v___x_3724_; lean_object* v___x_3725_; 
v_cls_3723_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3724_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3725_ = l_Lean_Name_append(v___x_3724_, v_cls_3723_);
return v___x_3725_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
v___x_3727_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3728_ = l_Lean_stringToMessageData(v___x_3727_);
return v___x_3728_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3730_; lean_object* v___x_3731_; 
v___x_3730_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3731_ = l_Lean_stringToMessageData(v___x_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3732_, uint8_t v_forceExpose_3733_, lean_object* v_a_3734_, lean_object* v_a_3735_){
_start:
{
lean_object* v___y_3738_; lean_object* v___y_3739_; lean_object* v_a_3740_; lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_a_3753_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_a_3766_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_a_3779_; lean_object* v_options_3789_; lean_object* v_inheritedTraceOptions_3790_; uint8_t v_hasTrace_3791_; lean_object* v___y_3793_; lean_object* v___y_3794_; lean_object* v___y_3795_; lean_object* v___y_3796_; lean_object* v___y_3797_; uint8_t v___y_3798_; lean_object* v___y_3799_; lean_object* v___y_3800_; lean_object* v___y_3801_; lean_object* v___y_3802_; lean_object* v___y_3803_; lean_object* v___y_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; uint8_t v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3873_; lean_object* v___y_3874_; lean_object* v___y_3875_; lean_object* v___y_3876_; uint8_t v___y_3899_; lean_object* v___y_3900_; lean_object* v___y_3901_; lean_object* v_exportedInfo_x3f_3902_; lean_object* v___y_3903_; lean_object* v___y_3904_; uint8_t v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; uint8_t v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; lean_object* v___y_3924_; lean_object* v___y_3925_; lean_object* v_cls_3927_; 
v_options_3789_ = lean_ctor_get(v_a_3734_, 2);
v_inheritedTraceOptions_3790_ = lean_ctor_get(v_a_3734_, 13);
v_hasTrace_3791_ = lean_ctor_get_uint8(v_options_3789_, sizeof(void*)*1);
v_cls_3927_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3791_ == 0)
{
lean_object* v___x_3928_; lean_object* v_env_3929_; lean_object* v_nextMacroScope_3930_; lean_object* v_ngen_3931_; lean_object* v_auxDeclNGen_3932_; lean_object* v_traceState_3933_; lean_object* v_messages_3934_; lean_object* v_infoState_3935_; lean_object* v_snapshotTasks_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_4127_; 
v___x_3928_ = lean_st_ref_take(v_a_3735_);
v_env_3929_ = lean_ctor_get(v___x_3928_, 0);
v_nextMacroScope_3930_ = lean_ctor_get(v___x_3928_, 1);
v_ngen_3931_ = lean_ctor_get(v___x_3928_, 2);
v_auxDeclNGen_3932_ = lean_ctor_get(v___x_3928_, 3);
v_traceState_3933_ = lean_ctor_get(v___x_3928_, 4);
v_messages_3934_ = lean_ctor_get(v___x_3928_, 6);
v_infoState_3935_ = lean_ctor_get(v___x_3928_, 7);
v_snapshotTasks_3936_ = lean_ctor_get(v___x_3928_, 8);
v_isSharedCheck_4127_ = !lean_is_exclusive(v___x_3928_);
if (v_isSharedCheck_4127_ == 0)
{
lean_object* v_unused_4128_; 
v_unused_4128_ = lean_ctor_get(v___x_3928_, 5);
lean_dec(v_unused_4128_);
v___x_3938_ = v___x_3928_;
v_isShared_3939_ = v_isSharedCheck_4127_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_snapshotTasks_3936_);
lean_inc(v_infoState_3935_);
lean_inc(v_messages_3934_);
lean_inc(v_traceState_3933_);
lean_inc(v_auxDeclNGen_3932_);
lean_inc(v_ngen_3931_);
lean_inc(v_nextMacroScope_3930_);
lean_inc(v_env_3929_);
lean_dec(v___x_3928_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_4127_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3944_; 
lean_inc(v_decl_3732_);
v___x_3940_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_3941_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3929_, v___x_3940_);
v___x_3942_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 5, v___x_3942_);
lean_ctor_set(v___x_3938_, 0, v___x_3941_);
v___x_3944_ = v___x_3938_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_4126_; 
v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_4126_, 1, v_nextMacroScope_3930_);
lean_ctor_set(v_reuseFailAlloc_4126_, 2, v_ngen_3931_);
lean_ctor_set(v_reuseFailAlloc_4126_, 3, v_auxDeclNGen_3932_);
lean_ctor_set(v_reuseFailAlloc_4126_, 4, v_traceState_3933_);
lean_ctor_set(v_reuseFailAlloc_4126_, 5, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_4126_, 6, v_messages_3934_);
lean_ctor_set(v_reuseFailAlloc_4126_, 7, v_infoState_3935_);
lean_ctor_set(v_reuseFailAlloc_4126_, 8, v_snapshotTasks_3936_);
v___x_3944_ = v_reuseFailAlloc_4126_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v_fst_4003_; lean_object* v_fst_4004_; uint8_t v_snd_4005_; lean_object* v_exportedInfo_x3f_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___y_4018_; lean_object* v_exportedInfo_x3f_4019_; lean_object* v___y_4020_; lean_object* v___y_4021_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; uint8_t v___y_4031_; lean_object* v___y_4036_; lean_object* v_toConstantVal_4037_; uint8_t v_safety_4038_; uint8_t v___y_4039_; lean_object* v___y_4040_; lean_object* v___y_4041_; lean_object* v___y_4045_; uint8_t v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v_defn_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; 
v___x_3945_ = lean_st_ref_set(v_a_3735_, v___x_3944_);
v___x_3946_ = lean_box(0);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4076_; lean_object* v_exportedInfo_x3f_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; lean_object* v___x_4085_; 
v_val_4076_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4085_ = lean_st_ref_get(v_a_3735_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4086_; lean_object* v___x_4087_; uint8_t v_isModule_4088_; 
v_env_4086_ = lean_ctor_get(v___x_4085_, 0);
lean_inc_ref(v_env_4086_);
lean_dec(v___x_4085_);
v___x_4087_ = l_Lean_Environment_header(v_env_4086_);
lean_dec_ref(v_env_4086_);
v_isModule_4088_ = lean_ctor_get_uint8(v___x_4087_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4087_);
if (v_isModule_4088_ == 0)
{
v_exportedInfo_x3f_4078_ = v___x_3946_;
v___y_4079_ = v_a_3734_;
v___y_4080_ = v_a_3735_;
goto v___jp_4077_;
}
else
{
lean_object* v_toConstantVal_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; lean_object* v___x_4092_; 
v_toConstantVal_4089_ = lean_ctor_get(v_val_4076_, 0);
lean_inc_ref(v_toConstantVal_4089_);
v___x_4090_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4090_, 0, v_toConstantVal_4089_);
lean_ctor_set_uint8(v___x_4090_, sizeof(void*)*1, v_hasTrace_3791_);
v___x_4091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
v___x_4092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
v_exportedInfo_x3f_4078_ = v___x_4092_;
v___y_4079_ = v_a_3734_;
v___y_4080_ = v_a_3735_;
goto v___jp_4077_;
}
}
else
{
lean_dec(v___x_4085_);
v_exportedInfo_x3f_4078_ = v___x_3946_;
v___y_4079_ = v_a_3734_;
v___y_4080_ = v_a_3735_;
goto v___jp_4077_;
}
v___jp_4077_:
{
lean_object* v_toConstantVal_4081_; lean_object* v_name_4082_; lean_object* v___x_4083_; uint8_t v___x_4084_; 
v_toConstantVal_4081_ = lean_ctor_get(v_val_4076_, 0);
v_name_4082_ = lean_ctor_get(v_toConstantVal_4081_, 0);
lean_inc_ref(v_val_4076_);
v___x_4083_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4083_, 0, v_val_4076_);
v___x_4084_ = 1;
lean_inc(v_name_4082_);
v_fst_4003_ = v_name_4082_;
v_fst_4004_ = v___x_4083_;
v_snd_4005_ = v___x_4084_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4078_;
v___y_4007_ = v___y_4079_;
v___y_4008_ = v___y_4080_;
goto v___jp_4002_;
}
}
case 1:
{
lean_object* v_val_4093_; 
v_val_4093_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4093_);
v_defn_4052_ = v_val_4093_;
v___y_4053_ = v_a_3734_;
v___y_4054_ = v_a_3735_;
goto v___jp_4051_;
}
case 5:
{
lean_object* v_defns_4094_; 
v_defns_4094_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4094_) == 1)
{
lean_object* v_tail_4095_; 
v_tail_4095_ = lean_ctor_get(v_defns_4094_, 1);
if (lean_obj_tag(v_tail_4095_) == 0)
{
lean_object* v_head_4096_; 
v_head_4096_ = lean_ctor_get(v_defns_4094_, 0);
lean_inc(v_head_4096_);
v_defn_4052_ = v_head_4096_;
v___y_4053_ = v_a_3734_;
v___y_4054_ = v_a_3735_;
goto v___jp_4051_;
}
else
{
lean_object* v___x_4097_; 
v___x_4097_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4097_;
}
}
else
{
lean_object* v___x_4098_; 
v___x_4098_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4098_;
}
}
case 3:
{
lean_object* v_val_4099_; lean_object* v_exportedInfo_x3f_4101_; lean_object* v___y_4102_; lean_object* v___y_4103_; lean_object* v___x_4108_; lean_object* v___x_4109_; 
v_val_4099_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4108_ = lean_st_ref_get(v_a_3735_);
v___x_4109_ = lean_st_ref_get(v_a_3735_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4110_; lean_object* v_env_4111_; lean_object* v___x_4112_; uint8_t v_isModule_4113_; 
v_env_4110_ = lean_ctor_get(v___x_4108_, 0);
lean_inc_ref(v_env_4110_);
lean_dec(v___x_4108_);
v_env_4111_ = lean_ctor_get(v___x_4109_, 0);
lean_inc_ref(v_env_4111_);
lean_dec(v___x_4109_);
v___x_4112_ = l_Lean_Environment_header(v_env_4110_);
lean_dec_ref(v_env_4110_);
v_isModule_4113_ = lean_ctor_get_uint8(v___x_4112_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4112_);
if (v_isModule_4113_ == 0)
{
lean_dec_ref(v_env_4111_);
v_exportedInfo_x3f_4101_ = v___x_3946_;
v___y_4102_ = v_a_3734_;
v___y_4103_ = v_a_3735_;
goto v___jp_4100_;
}
else
{
uint8_t v_isExporting_4114_; 
v_isExporting_4114_ = lean_ctor_get_uint8(v_env_4111_, sizeof(void*)*8);
lean_dec_ref(v_env_4111_);
if (v_isExporting_4114_ == 0)
{
lean_object* v_toConstantVal_4115_; uint8_t v_isUnsafe_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; 
v_toConstantVal_4115_ = lean_ctor_get(v_val_4099_, 0);
v_isUnsafe_4116_ = lean_ctor_get_uint8(v_val_4099_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4115_);
v___x_4117_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4117_, 0, v_toConstantVal_4115_);
lean_ctor_set_uint8(v___x_4117_, sizeof(void*)*1, v_isUnsafe_4116_);
v___x_4118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
v___x_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4119_, 0, v___x_4118_);
v_exportedInfo_x3f_4101_ = v___x_4119_;
v___y_4102_ = v_a_3734_;
v___y_4103_ = v_a_3735_;
goto v___jp_4100_;
}
else
{
v_exportedInfo_x3f_4101_ = v___x_3946_;
v___y_4102_ = v_a_3734_;
v___y_4103_ = v_a_3735_;
goto v___jp_4100_;
}
}
}
else
{
lean_dec(v___x_4109_);
lean_dec(v___x_4108_);
v_exportedInfo_x3f_4101_ = v___x_3946_;
v___y_4102_ = v_a_3734_;
v___y_4103_ = v_a_3735_;
goto v___jp_4100_;
}
v___jp_4100_:
{
lean_object* v_toConstantVal_4104_; lean_object* v_name_4105_; lean_object* v___x_4106_; uint8_t v___x_4107_; 
v_toConstantVal_4104_ = lean_ctor_get(v_val_4099_, 0);
v_name_4105_ = lean_ctor_get(v_toConstantVal_4104_, 0);
lean_inc_ref(v_val_4099_);
v___x_4106_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4106_, 0, v_val_4099_);
v___x_4107_ = 3;
lean_inc(v_name_4105_);
v_fst_4003_ = v_name_4105_;
v_fst_4004_ = v___x_4106_;
v_snd_4005_ = v___x_4107_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4101_;
v___y_4007_ = v___y_4102_;
v___y_4008_ = v___y_4103_;
goto v___jp_4002_;
}
}
case 0:
{
lean_object* v_val_4120_; lean_object* v_toConstantVal_4121_; lean_object* v_name_4122_; lean_object* v___x_4123_; uint8_t v___x_4124_; 
v_val_4120_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4121_ = lean_ctor_get(v_val_4120_, 0);
v_name_4122_ = lean_ctor_get(v_toConstantVal_4121_, 0);
lean_inc_ref(v_val_4120_);
v___x_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4123_, 0, v_val_4120_);
v___x_4124_ = 2;
lean_inc(v_name_4122_);
v_fst_4003_ = v_name_4122_;
v_fst_4004_ = v___x_4123_;
v_snd_4005_ = v___x_4124_;
v_exportedInfo_x3f_4006_ = v___x_3946_;
v___y_4007_ = v_a_3734_;
v___y_4008_ = v_a_3735_;
goto v___jp_4002_;
}
default: 
{
lean_object* v___x_4125_; 
v___x_4125_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v_a_3734_, v_a_3735_);
return v___x_4125_;
}
}
v___jp_3947_:
{
lean_object* v___x_3954_; uint8_t v___x_3955_; 
lean_inc(v_decl_3732_);
v___x_3954_ = l_Lean_Declaration_getTopLevelNames(v_decl_3732_);
v___x_3955_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3954_);
lean_dec(v___x_3954_);
if (v___x_3955_ == 0)
{
if (lean_obj_tag(v___y_3950_) == 0)
{
lean_object* v_options_3956_; uint8_t v_hasTrace_3957_; 
v_options_3956_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3957_ = lean_ctor_get_uint8(v_options_3956_, sizeof(void*)*1);
if (v_hasTrace_3957_ == 0)
{
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3949_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_object* v_inheritedTraceOptions_3958_; lean_object* v___x_3959_; uint8_t v___x_3960_; 
v_inheritedTraceOptions_3958_ = lean_ctor_get(v___y_3952_, 13);
v___x_3959_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3960_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3958_, v_options_3956_, v___x_3959_);
if (v___x_3960_ == 0)
{
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3949_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3961_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3962_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_3961_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_dec_ref_known(v___x_3962_, 1);
v___y_3921_ = v___y_3948_;
v___y_3922_ = v___y_3949_;
v___y_3923_ = v___y_3951_;
v___y_3924_ = v___y_3952_;
v___y_3925_ = v___y_3953_;
goto v___jp_3920_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3732_);
return v___x_3962_;
}
}
}
}
else
{
lean_object* v___x_3963_; lean_object* v_env_3964_; lean_object* v_nextMacroScope_3965_; lean_object* v_ngen_3966_; lean_object* v_auxDeclNGen_3967_; lean_object* v_traceState_3968_; lean_object* v_messages_3969_; lean_object* v_infoState_3970_; lean_object* v_snapshotTasks_3971_; lean_object* v___x_3973_; uint8_t v_isShared_3974_; uint8_t v_isSharedCheck_3982_; 
v___x_3963_ = lean_st_ref_take(v___y_3953_);
v_env_3964_ = lean_ctor_get(v___x_3963_, 0);
v_nextMacroScope_3965_ = lean_ctor_get(v___x_3963_, 1);
v_ngen_3966_ = lean_ctor_get(v___x_3963_, 2);
v_auxDeclNGen_3967_ = lean_ctor_get(v___x_3963_, 3);
v_traceState_3968_ = lean_ctor_get(v___x_3963_, 4);
v_messages_3969_ = lean_ctor_get(v___x_3963_, 6);
v_infoState_3970_ = lean_ctor_get(v___x_3963_, 7);
v_snapshotTasks_3971_ = lean_ctor_get(v___x_3963_, 8);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3982_ == 0)
{
lean_object* v_unused_3983_; 
v_unused_3983_ = lean_ctor_get(v___x_3963_, 5);
lean_dec(v_unused_3983_);
v___x_3973_ = v___x_3963_;
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
else
{
lean_inc(v_snapshotTasks_3971_);
lean_inc(v_infoState_3970_);
lean_inc(v_messages_3969_);
lean_inc(v_traceState_3968_);
lean_inc(v_auxDeclNGen_3967_);
lean_inc(v_ngen_3966_);
lean_inc(v_nextMacroScope_3965_);
lean_inc(v_env_3964_);
lean_dec(v___x_3963_);
v___x_3973_ = lean_box(0);
v_isShared_3974_ = v_isSharedCheck_3982_;
goto v_resetjp_3972_;
}
v_resetjp_3972_:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3979_; 
v___x_3975_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3976_ = lean_box(v___y_3948_);
lean_inc(v___y_3951_);
v___x_3977_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3975_, v_env_3964_, v___y_3951_, v___x_3976_);
if (v_isShared_3974_ == 0)
{
lean_ctor_set(v___x_3973_, 5, v___x_3942_);
lean_ctor_set(v___x_3973_, 0, v___x_3977_);
v___x_3979_ = v___x_3973_;
goto v_reusejp_3978_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3977_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_nextMacroScope_3965_);
lean_ctor_set(v_reuseFailAlloc_3981_, 2, v_ngen_3966_);
lean_ctor_set(v_reuseFailAlloc_3981_, 3, v_auxDeclNGen_3967_);
lean_ctor_set(v_reuseFailAlloc_3981_, 4, v_traceState_3968_);
lean_ctor_set(v_reuseFailAlloc_3981_, 5, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3981_, 6, v_messages_3969_);
lean_ctor_set(v_reuseFailAlloc_3981_, 7, v_infoState_3970_);
lean_ctor_set(v_reuseFailAlloc_3981_, 8, v_snapshotTasks_3971_);
v___x_3979_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3978_;
}
v_reusejp_3978_:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_st_ref_set(v___y_3953_, v___x_3979_);
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3949_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___y_3950_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
}
}
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; lean_object* v_a_3986_; uint8_t v___x_3987_; 
lean_dec(v___y_3950_);
v___x_3984_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3985_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3984_, v___y_3952_);
v_a_3986_ = lean_ctor_get(v___x_3985_, 0);
lean_inc(v_a_3986_);
lean_dec_ref(v___x_3985_);
v___x_3987_ = lean_unbox(v_a_3986_);
lean_dec(v_a_3986_);
if (v___x_3987_ == 0)
{
lean_object* v_options_3988_; uint8_t v_hasTrace_3989_; 
v_options_3988_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3989_ = lean_ctor_get_uint8(v_options_3988_, sizeof(void*)*1);
if (v_hasTrace_3989_ == 0)
{
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3949_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_object* v_inheritedTraceOptions_3990_; lean_object* v___x_3991_; uint8_t v___x_3992_; 
v_inheritedTraceOptions_3990_ = lean_ctor_get(v___y_3952_, 13);
v___x_3991_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3990_, v_options_3988_, v___x_3991_);
if (v___x_3992_ == 0)
{
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3949_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3993_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3994_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_3993_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_dec_ref_known(v___x_3994_, 1);
v___y_3899_ = v___y_3948_;
v___y_3900_ = v___y_3949_;
v___y_3901_ = v___y_3951_;
v_exportedInfo_x3f_3902_ = v___x_3946_;
v___y_3903_ = v___y_3952_;
v___y_3904_ = v___y_3953_;
goto v___jp_3898_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3732_);
return v___x_3994_;
}
}
}
}
else
{
lean_object* v_options_3995_; uint8_t v_hasTrace_3996_; 
v_options_3995_ = lean_ctor_get(v___y_3952_, 2);
v_hasTrace_3996_ = lean_ctor_get_uint8(v_options_3995_, sizeof(void*)*1);
if (v_hasTrace_3996_ == 0)
{
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3949_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_object* v_inheritedTraceOptions_3997_; lean_object* v___x_3998_; uint8_t v___x_3999_; 
v_inheritedTraceOptions_3997_ = lean_ctor_get(v___y_3952_, 13);
v___x_3998_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3999_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3997_, v_options_3995_, v___x_3998_);
if (v___x_3999_ == 0)
{
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3949_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_object* v___x_4000_; lean_object* v___x_4001_; 
v___x_4000_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4001_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4000_, v___y_3952_, v___y_3953_);
if (lean_obj_tag(v___x_4001_) == 0)
{
lean_dec_ref_known(v___x_4001_, 1);
v___y_3914_ = v___y_3948_;
v___y_3915_ = v___y_3949_;
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3953_;
goto v___jp_3913_;
}
else
{
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3949_);
lean_dec(v_decl_3732_);
return v___x_4001_;
}
}
}
}
}
}
v___jp_4002_:
{
lean_object* v___x_4009_; lean_object* v_env_4010_; uint8_t v___x_4011_; 
v___x_4009_ = lean_st_ref_get(v___y_4008_);
v_env_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc_ref(v_env_4010_);
lean_dec(v___x_4009_);
v___x_4011_ = l_Lean_Environment_containsOnBranch(v_env_4010_, v_fst_4003_);
lean_dec_ref(v_env_4010_);
if (v___x_4011_ == 0)
{
v___y_3948_ = v_snd_4005_;
v___y_3949_ = v_fst_4004_;
v___y_3950_ = v_exportedInfo_x3f_4006_;
v___y_3951_ = v_fst_4003_;
v___y_3952_ = v___y_4007_;
v___y_3953_ = v___y_4008_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_4012_; lean_object* v_env_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; lean_object* v___x_4016_; 
lean_dec(v_exportedInfo_x3f_4006_);
lean_dec_ref(v_fst_4004_);
lean_dec(v_decl_3732_);
v___x_4012_ = lean_st_ref_get(v___y_4008_);
v_env_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc_ref(v_env_4013_);
lean_dec(v___x_4012_);
v___x_4014_ = lean_elab_environment_to_kernel_env(v_env_4013_);
v___x_4015_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
lean_ctor_set(v___x_4015_, 1, v_fst_4003_);
v___x_4016_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4015_, v___y_4007_, v___y_4008_);
return v___x_4016_;
}
}
v___jp_4017_:
{
lean_object* v_toConstantVal_4022_; lean_object* v_name_4023_; lean_object* v___x_4024_; uint8_t v___x_4025_; 
v_toConstantVal_4022_ = lean_ctor_get(v___y_4018_, 0);
v_name_4023_ = lean_ctor_get(v_toConstantVal_4022_, 0);
lean_inc(v_name_4023_);
v___x_4024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4024_, 0, v___y_4018_);
v___x_4025_ = 0;
v_fst_4003_ = v_name_4023_;
v_fst_4004_ = v___x_4024_;
v_snd_4005_ = v___x_4025_;
v_exportedInfo_x3f_4006_ = v_exportedInfo_x3f_4019_;
v___y_4007_ = v___y_4020_;
v___y_4008_ = v___y_4021_;
goto v___jp_4002_;
}
v___jp_4026_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4034_; 
v___x_4032_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4032_, 0, v___y_4030_);
lean_ctor_set_uint8(v___x_4032_, sizeof(void*)*1, v___y_4031_);
v___x_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
v___x_4034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4034_, 0, v___x_4033_);
v___y_4018_ = v___y_4028_;
v_exportedInfo_x3f_4019_ = v___x_4034_;
v___y_4020_ = v___y_4029_;
v___y_4021_ = v___y_4027_;
goto v___jp_4017_;
}
v___jp_4035_:
{
uint8_t v___x_4042_; uint8_t v___x_4043_; 
v___x_4042_ = 1;
v___x_4043_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4038_, v___x_4042_);
if (v___x_4043_ == 0)
{
v___y_4027_ = v___y_4041_;
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4040_;
v___y_4030_ = v_toConstantVal_4037_;
v___y_4031_ = v___y_4039_;
goto v___jp_4026_;
}
else
{
v___y_4027_ = v___y_4041_;
v___y_4028_ = v___y_4036_;
v___y_4029_ = v___y_4040_;
v___y_4030_ = v_toConstantVal_4037_;
v___y_4031_ = v_hasTrace_3791_;
goto v___jp_4026_;
}
}
v___jp_4044_:
{
lean_object* v_toConstantVal_4049_; uint8_t v_safety_4050_; 
v_toConstantVal_4049_ = lean_ctor_get(v___y_4045_, 0);
lean_inc_ref(v_toConstantVal_4049_);
v_safety_4050_ = lean_ctor_get_uint8(v___y_4045_, sizeof(void*)*4);
v___y_4036_ = v___y_4045_;
v_toConstantVal_4037_ = v_toConstantVal_4049_;
v_safety_4038_ = v_safety_4050_;
v___y_4039_ = v___y_4046_;
v___y_4040_ = v___y_4047_;
v___y_4041_ = v___y_4048_;
goto v___jp_4035_;
}
v___jp_4051_:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4055_ = lean_st_ref_get(v___y_4054_);
v___x_4056_ = lean_st_ref_get(v___y_4054_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4057_; lean_object* v_env_4058_; lean_object* v___x_4059_; uint8_t v_isModule_4060_; 
v_env_4057_ = lean_ctor_get(v___x_4055_, 0);
lean_inc_ref(v_env_4057_);
lean_dec(v___x_4055_);
v_env_4058_ = lean_ctor_get(v___x_4056_, 0);
lean_inc_ref(v_env_4058_);
lean_dec(v___x_4056_);
v___x_4059_ = l_Lean_Environment_header(v_env_4057_);
lean_dec_ref(v_env_4057_);
v_isModule_4060_ = lean_ctor_get_uint8(v___x_4059_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4059_);
if (v_isModule_4060_ == 0)
{
lean_dec_ref(v_env_4058_);
v___y_4018_ = v_defn_4052_;
v_exportedInfo_x3f_4019_ = v___x_3946_;
v___y_4020_ = v___y_4053_;
v___y_4021_ = v___y_4054_;
goto v___jp_4017_;
}
else
{
uint8_t v_isExporting_4061_; 
v_isExporting_4061_ = lean_ctor_get_uint8(v_env_4058_, sizeof(void*)*8);
lean_dec_ref(v_env_4058_);
if (v_isExporting_4061_ == 0)
{
lean_object* v_options_4062_; uint8_t v_hasTrace_4063_; 
v_options_4062_ = lean_ctor_get(v___y_4053_, 2);
v_hasTrace_4063_ = lean_ctor_get_uint8(v_options_4062_, sizeof(void*)*1);
if (v_hasTrace_4063_ == 0)
{
v___y_4045_ = v_defn_4052_;
v___y_4046_ = v_isModule_4060_;
v___y_4047_ = v___y_4053_;
v___y_4048_ = v___y_4054_;
goto v___jp_4044_;
}
else
{
lean_object* v_inheritedTraceOptions_4064_; lean_object* v___x_4065_; uint8_t v___x_4066_; 
v_inheritedTraceOptions_4064_ = lean_ctor_get(v___y_4053_, 13);
v___x_4065_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4066_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4064_, v_options_4062_, v___x_4065_);
if (v___x_4066_ == 0)
{
v___y_4045_ = v_defn_4052_;
v___y_4046_ = v_isModule_4060_;
v___y_4047_ = v___y_4053_;
v___y_4048_ = v___y_4054_;
goto v___jp_4044_;
}
else
{
lean_object* v_toConstantVal_4067_; uint8_t v_safety_4068_; lean_object* v_name_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; 
v_toConstantVal_4067_ = lean_ctor_get(v_defn_4052_, 0);
lean_inc_ref(v_toConstantVal_4067_);
v_safety_4068_ = lean_ctor_get_uint8(v_defn_4052_, sizeof(void*)*4);
v_name_4069_ = lean_ctor_get(v_toConstantVal_4067_, 0);
v___x_4070_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4069_);
v___x_4071_ = l_Lean_MessageData_ofName(v_name_4069_);
v___x_4072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4072_, 0, v___x_4070_);
lean_ctor_set(v___x_4072_, 1, v___x_4071_);
v___x_4073_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4074_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4074_, 0, v___x_4072_);
lean_ctor_set(v___x_4074_, 1, v___x_4073_);
v___x_4075_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4074_, v___y_4053_, v___y_4054_);
if (lean_obj_tag(v___x_4075_) == 0)
{
lean_dec_ref_known(v___x_4075_, 1);
v___y_4036_ = v_defn_4052_;
v_toConstantVal_4037_ = v_toConstantVal_4067_;
v_safety_4038_ = v_safety_4068_;
v___y_4039_ = v_isModule_4060_;
v___y_4040_ = v___y_4053_;
v___y_4041_ = v___y_4054_;
goto v___jp_4035_;
}
else
{
lean_dec_ref(v_toConstantVal_4067_);
lean_dec_ref(v_defn_4052_);
lean_dec(v_decl_3732_);
return v___x_4075_;
}
}
}
}
else
{
v___y_4018_ = v_defn_4052_;
v_exportedInfo_x3f_4019_ = v___x_3946_;
v___y_4020_ = v___y_4053_;
v___y_4021_ = v___y_4054_;
goto v___jp_4017_;
}
}
}
else
{
lean_dec(v___x_4056_);
lean_dec(v___x_4055_);
v___y_4018_ = v_defn_4052_;
v_exportedInfo_x3f_4019_ = v___x_3946_;
v___y_4020_ = v___y_4053_;
v___y_4021_ = v___y_4054_;
goto v___jp_4017_;
}
}
}
}
}
else
{
lean_object* v___f_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; uint8_t v___x_4132_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v_a_4136_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4166_; lean_object* v___y_4167_; lean_object* v___y_4168_; lean_object* v___y_4169_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4180_; lean_object* v___y_4181_; lean_object* v_a_4182_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4215_; lean_object* v___y_4216_; lean_object* v___y_4217_; lean_object* v___y_4218_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; uint8_t v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4259_; lean_object* v___y_4260_; lean_object* v___y_4261_; lean_object* v___y_4262_; lean_object* v___y_4263_; lean_object* v___y_4264_; lean_object* v___y_4265_; 
lean_inc(v_decl_3732_);
v___f_4129_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4129_, 0, v_decl_3732_);
v___x_4130_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4131_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4132_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3790_, v_options_3789_, v___x_4131_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4432_; uint8_t v___x_4433_; lean_object* v___y_4435_; lean_object* v___y_4436_; lean_object* v___y_4437_; lean_object* v___y_4438_; lean_object* v___y_4439_; lean_object* v___y_4440_; lean_object* v___y_4441_; lean_object* v___y_4442_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; uint8_t v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4539_; lean_object* v___y_4540_; uint8_t v___y_4541_; lean_object* v_exportedInfo_x3f_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4554_; lean_object* v___y_4555_; uint8_t v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4561_; lean_object* v___y_4562_; uint8_t v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; 
v___x_4432_ = l_Lean_trace_profiler;
v___x_4433_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3789_, v___x_4432_);
if (v___x_4433_ == 0)
{
lean_object* v___x_4567_; lean_object* v_env_4568_; lean_object* v_nextMacroScope_4569_; lean_object* v_ngen_4570_; lean_object* v_auxDeclNGen_4571_; lean_object* v_traceState_4572_; lean_object* v_messages_4573_; lean_object* v_infoState_4574_; lean_object* v_snapshotTasks_4575_; lean_object* v___x_4577_; uint8_t v_isShared_4578_; uint8_t v_isSharedCheck_4811_; 
lean_dec_ref(v___f_4129_);
v___x_4567_ = lean_st_ref_take(v_a_3735_);
v_env_4568_ = lean_ctor_get(v___x_4567_, 0);
v_nextMacroScope_4569_ = lean_ctor_get(v___x_4567_, 1);
v_ngen_4570_ = lean_ctor_get(v___x_4567_, 2);
v_auxDeclNGen_4571_ = lean_ctor_get(v___x_4567_, 3);
v_traceState_4572_ = lean_ctor_get(v___x_4567_, 4);
v_messages_4573_ = lean_ctor_get(v___x_4567_, 6);
v_infoState_4574_ = lean_ctor_get(v___x_4567_, 7);
v_snapshotTasks_4575_ = lean_ctor_get(v___x_4567_, 8);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4567_);
if (v_isSharedCheck_4811_ == 0)
{
lean_object* v_unused_4812_; 
v_unused_4812_ = lean_ctor_get(v___x_4567_, 5);
lean_dec(v_unused_4812_);
v___x_4577_ = v___x_4567_;
v_isShared_4578_ = v_isSharedCheck_4811_;
goto v_resetjp_4576_;
}
else
{
lean_inc(v_snapshotTasks_4575_);
lean_inc(v_infoState_4574_);
lean_inc(v_messages_4573_);
lean_inc(v_traceState_4572_);
lean_inc(v_auxDeclNGen_4571_);
lean_inc(v_ngen_4570_);
lean_inc(v_nextMacroScope_4569_);
lean_inc(v_env_4568_);
lean_dec(v___x_4567_);
v___x_4577_ = lean_box(0);
v_isShared_4578_ = v_isSharedCheck_4811_;
goto v_resetjp_4576_;
}
v_resetjp_4576_:
{
lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; uint8_t v___y_4588_; lean_object* v___x_4611_; 
lean_inc(v_decl_3732_);
v___x_4579_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4580_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4568_, v___x_4579_);
v___x_4581_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4578_ == 0)
{
lean_ctor_set(v___x_4577_, 5, v___x_4581_);
lean_ctor_set(v___x_4577_, 0, v___x_4580_);
v___x_4611_ = v___x_4577_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4810_, 1, v_nextMacroScope_4569_);
lean_ctor_set(v_reuseFailAlloc_4810_, 2, v_ngen_4570_);
lean_ctor_set(v_reuseFailAlloc_4810_, 3, v_auxDeclNGen_4571_);
lean_ctor_set(v_reuseFailAlloc_4810_, 4, v_traceState_4572_);
lean_ctor_set(v_reuseFailAlloc_4810_, 5, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4810_, 6, v_messages_4573_);
lean_ctor_set(v_reuseFailAlloc_4810_, 7, v_infoState_4574_);
lean_ctor_set(v_reuseFailAlloc_4810_, 8, v_snapshotTasks_4575_);
v___x_4611_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4610_;
}
v___jp_4582_:
{
lean_object* v___x_4589_; lean_object* v_env_4590_; lean_object* v_nextMacroScope_4591_; lean_object* v_ngen_4592_; lean_object* v_auxDeclNGen_4593_; lean_object* v_traceState_4594_; lean_object* v_messages_4595_; lean_object* v_infoState_4596_; lean_object* v_snapshotTasks_4597_; lean_object* v___x_4599_; uint8_t v_isShared_4600_; uint8_t v_isSharedCheck_4608_; 
v___x_4589_ = lean_st_ref_take(v___y_4586_);
v_env_4590_ = lean_ctor_get(v___x_4589_, 0);
v_nextMacroScope_4591_ = lean_ctor_get(v___x_4589_, 1);
v_ngen_4592_ = lean_ctor_get(v___x_4589_, 2);
v_auxDeclNGen_4593_ = lean_ctor_get(v___x_4589_, 3);
v_traceState_4594_ = lean_ctor_get(v___x_4589_, 4);
v_messages_4595_ = lean_ctor_get(v___x_4589_, 6);
v_infoState_4596_ = lean_ctor_get(v___x_4589_, 7);
v_snapshotTasks_4597_ = lean_ctor_get(v___x_4589_, 8);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4589_);
if (v_isSharedCheck_4608_ == 0)
{
lean_object* v_unused_4609_; 
v_unused_4609_ = lean_ctor_get(v___x_4589_, 5);
lean_dec(v_unused_4609_);
v___x_4599_ = v___x_4589_;
v_isShared_4600_ = v_isSharedCheck_4608_;
goto v_resetjp_4598_;
}
else
{
lean_inc(v_snapshotTasks_4597_);
lean_inc(v_infoState_4596_);
lean_inc(v_messages_4595_);
lean_inc(v_traceState_4594_);
lean_inc(v_auxDeclNGen_4593_);
lean_inc(v_ngen_4592_);
lean_inc(v_nextMacroScope_4591_);
lean_inc(v_env_4590_);
lean_dec(v___x_4589_);
v___x_4599_ = lean_box(0);
v_isShared_4600_ = v_isSharedCheck_4608_;
goto v_resetjp_4598_;
}
v_resetjp_4598_:
{
lean_object* v___x_4601_; lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4605_; 
v___x_4601_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4602_ = lean_box(v___y_4588_);
lean_inc(v___y_4584_);
v___x_4603_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4601_, v_env_4590_, v___y_4584_, v___x_4602_);
if (v_isShared_4600_ == 0)
{
lean_ctor_set(v___x_4599_, 5, v___x_4581_);
lean_ctor_set(v___x_4599_, 0, v___x_4603_);
v___x_4605_ = v___x_4599_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4607_, 1, v_nextMacroScope_4591_);
lean_ctor_set(v_reuseFailAlloc_4607_, 2, v_ngen_4592_);
lean_ctor_set(v_reuseFailAlloc_4607_, 3, v_auxDeclNGen_4593_);
lean_ctor_set(v_reuseFailAlloc_4607_, 4, v_traceState_4594_);
lean_ctor_set(v_reuseFailAlloc_4607_, 5, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4607_, 6, v_messages_4595_);
lean_ctor_set(v_reuseFailAlloc_4607_, 7, v_infoState_4596_);
lean_ctor_set(v_reuseFailAlloc_4607_, 8, v_snapshotTasks_4597_);
v___x_4605_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4606_; 
v___x_4606_ = lean_st_ref_set(v___y_4586_, v___x_4605_);
v___y_4539_ = v___y_4584_;
v___y_4540_ = v___y_4583_;
v___y_4541_ = v___y_4588_;
v_exportedInfo_x3f_4542_ = v___y_4587_;
v___y_4543_ = v___y_4585_;
v___y_4544_ = v___y_4586_;
goto v___jp_4538_;
}
}
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; lean_object* v___y_4614_; lean_object* v_options_4615_; lean_object* v_inheritedTraceOptions_4616_; lean_object* v___y_4617_; lean_object* v___x_4623_; lean_object* v___y_4625_; lean_object* v___y_4626_; uint8_t v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v_fst_4656_; lean_object* v_fst_4657_; uint8_t v_snd_4658_; lean_object* v_exportedInfo_x3f_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4671_; lean_object* v_exportedInfo_x3f_4672_; lean_object* v___y_4673_; lean_object* v___y_4674_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v___y_4682_; lean_object* v___y_4683_; uint8_t v___y_4684_; lean_object* v___y_4689_; lean_object* v_toConstantVal_4690_; uint8_t v_safety_4691_; lean_object* v___y_4692_; lean_object* v___y_4693_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4705_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v_defn_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; 
v___x_4612_ = lean_st_ref_set(v_a_3735_, v___x_4611_);
v___x_4623_ = lean_box(0);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4738_; lean_object* v_exportedInfo_x3f_4740_; lean_object* v___y_4741_; lean_object* v___y_4742_; lean_object* v___y_4748_; lean_object* v___y_4749_; lean_object* v___x_4754_; lean_object* v_env_4755_; 
v_val_4738_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4754_ = lean_st_ref_get(v_a_3735_);
v_env_4755_ = lean_ctor_get(v___x_4754_, 0);
lean_inc_ref(v_env_4755_);
lean_dec(v___x_4754_);
if (v_forceExpose_3733_ == 0)
{
goto v___jp_4756_;
}
else
{
if (v___x_4433_ == 0)
{
lean_dec_ref(v_env_4755_);
v_exportedInfo_x3f_4740_ = v___x_4623_;
v___y_4741_ = v_a_3734_;
v___y_4742_ = v_a_3735_;
goto v___jp_4739_;
}
else
{
goto v___jp_4756_;
}
}
v___jp_4739_:
{
lean_object* v_toConstantVal_4743_; lean_object* v_name_4744_; lean_object* v___x_4745_; uint8_t v___x_4746_; 
v_toConstantVal_4743_ = lean_ctor_get(v_val_4738_, 0);
v_name_4744_ = lean_ctor_get(v_toConstantVal_4743_, 0);
lean_inc_ref(v_val_4738_);
v___x_4745_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4745_, 0, v_val_4738_);
v___x_4746_ = 1;
lean_inc(v_name_4744_);
v_fst_4656_ = v_name_4744_;
v_fst_4657_ = v___x_4745_;
v_snd_4658_ = v___x_4746_;
v_exportedInfo_x3f_4659_ = v_exportedInfo_x3f_4740_;
v___y_4660_ = v___y_4741_;
v___y_4661_ = v___y_4742_;
goto v___jp_4655_;
}
v___jp_4747_:
{
lean_object* v_toConstantVal_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4753_; 
v_toConstantVal_4750_ = lean_ctor_get(v_val_4738_, 0);
lean_inc_ref(v_toConstantVal_4750_);
v___x_4751_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4751_, 0, v_toConstantVal_4750_);
lean_ctor_set_uint8(v___x_4751_, sizeof(void*)*1, v___x_4433_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
v___x_4753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
v_exportedInfo_x3f_4740_ = v___x_4753_;
v___y_4741_ = v___y_4748_;
v___y_4742_ = v___y_4749_;
goto v___jp_4739_;
}
v___jp_4756_:
{
lean_object* v___x_4757_; uint8_t v_isModule_4758_; 
v___x_4757_ = l_Lean_Environment_header(v_env_4755_);
lean_dec_ref(v_env_4755_);
v_isModule_4758_ = lean_ctor_get_uint8(v___x_4757_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4757_);
if (v_isModule_4758_ == 0)
{
v_exportedInfo_x3f_4740_ = v___x_4623_;
v___y_4741_ = v_a_3734_;
v___y_4742_ = v_a_3735_;
goto v___jp_4739_;
}
else
{
if (v___x_4132_ == 0)
{
v___y_4748_ = v_a_3734_;
v___y_4749_ = v_a_3735_;
goto v___jp_4747_;
}
else
{
lean_object* v_toConstantVal_4759_; lean_object* v_name_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v_toConstantVal_4759_ = lean_ctor_get(v_val_4738_, 0);
v_name_4760_ = lean_ctor_get(v_toConstantVal_4759_, 0);
v___x_4761_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4760_);
v___x_4762_ = l_Lean_MessageData_ofName(v_name_4760_);
v___x_4763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4763_, 0, v___x_4761_);
lean_ctor_set(v___x_4763_, 1, v___x_4762_);
v___x_4764_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4763_);
lean_ctor_set(v___x_4765_, 1, v___x_4764_);
v___x_4766_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4765_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4766_) == 0)
{
lean_dec_ref_known(v___x_4766_, 1);
v___y_4748_ = v_a_3734_;
v___y_4749_ = v_a_3735_;
goto v___jp_4747_;
}
else
{
lean_dec_ref_known(v_decl_3732_, 1);
return v___x_4766_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4767_; 
v_val_4767_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4767_);
v_defn_4729_ = v_val_4767_;
v___y_4730_ = v_a_3734_;
v___y_4731_ = v_a_3735_;
goto v___jp_4728_;
}
case 5:
{
lean_object* v_defns_4768_; 
v_defns_4768_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4768_) == 1)
{
lean_object* v_tail_4769_; 
v_tail_4769_ = lean_ctor_get(v_defns_4768_, 1);
if (lean_obj_tag(v_tail_4769_) == 0)
{
lean_object* v_head_4770_; 
v_head_4770_ = lean_ctor_get(v_defns_4768_, 0);
lean_inc(v_head_4770_);
v_defn_4729_ = v_head_4770_;
v___y_4730_ = v_a_3734_;
v___y_4731_ = v_a_3735_;
goto v___jp_4728_;
}
else
{
v___y_4614_ = v_a_3734_;
v_options_4615_ = v_options_3789_;
v_inheritedTraceOptions_4616_ = v_inheritedTraceOptions_3790_;
v___y_4617_ = v_a_3735_;
goto v___jp_4613_;
}
}
else
{
v___y_4614_ = v_a_3734_;
v_options_4615_ = v_options_3789_;
v_inheritedTraceOptions_4616_ = v_inheritedTraceOptions_3790_;
v___y_4617_ = v_a_3735_;
goto v___jp_4613_;
}
}
case 3:
{
lean_object* v_val_4771_; lean_object* v_exportedInfo_x3f_4773_; lean_object* v___y_4774_; lean_object* v___y_4775_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v_env_4799_; lean_object* v_env_4800_; 
v_val_4771_ = lean_ctor_get(v_decl_3732_, 0);
v___x_4788_ = lean_st_ref_get(v_a_3735_);
v___x_4789_ = lean_st_ref_get(v_a_3735_);
v_env_4799_ = lean_ctor_get(v___x_4788_, 0);
lean_inc_ref(v_env_4799_);
lean_dec(v___x_4788_);
v_env_4800_ = lean_ctor_get(v___x_4789_, 0);
lean_inc_ref(v_env_4800_);
lean_dec(v___x_4789_);
if (v_forceExpose_3733_ == 0)
{
goto v___jp_4801_;
}
else
{
if (v___x_4433_ == 0)
{
lean_dec_ref(v_env_4800_);
lean_dec_ref(v_env_4799_);
v_exportedInfo_x3f_4773_ = v___x_4623_;
v___y_4774_ = v_a_3734_;
v___y_4775_ = v_a_3735_;
goto v___jp_4772_;
}
else
{
goto v___jp_4801_;
}
}
v___jp_4772_:
{
lean_object* v_toConstantVal_4776_; lean_object* v_name_4777_; lean_object* v___x_4778_; uint8_t v___x_4779_; 
v_toConstantVal_4776_ = lean_ctor_get(v_val_4771_, 0);
v_name_4777_ = lean_ctor_get(v_toConstantVal_4776_, 0);
lean_inc_ref(v_val_4771_);
v___x_4778_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4778_, 0, v_val_4771_);
v___x_4779_ = 3;
lean_inc(v_name_4777_);
v_fst_4656_ = v_name_4777_;
v_fst_4657_ = v___x_4778_;
v_snd_4658_ = v___x_4779_;
v_exportedInfo_x3f_4659_ = v_exportedInfo_x3f_4773_;
v___y_4660_ = v___y_4774_;
v___y_4661_ = v___y_4775_;
goto v___jp_4655_;
}
v___jp_4780_:
{
lean_object* v_toConstantVal_4783_; uint8_t v_isUnsafe_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v_toConstantVal_4783_ = lean_ctor_get(v_val_4771_, 0);
v_isUnsafe_4784_ = lean_ctor_get_uint8(v_val_4771_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4783_);
v___x_4785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4785_, 0, v_toConstantVal_4783_);
lean_ctor_set_uint8(v___x_4785_, sizeof(void*)*1, v_isUnsafe_4784_);
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
v___x_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
v_exportedInfo_x3f_4773_ = v___x_4787_;
v___y_4774_ = v___y_4781_;
v___y_4775_ = v___y_4782_;
goto v___jp_4772_;
}
v___jp_4790_:
{
if (v___x_4132_ == 0)
{
v___y_4781_ = v_a_3734_;
v___y_4782_ = v_a_3735_;
goto v___jp_4780_;
}
else
{
lean_object* v_toConstantVal_4791_; lean_object* v_name_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; 
v_toConstantVal_4791_ = lean_ctor_get(v_val_4771_, 0);
v_name_4792_ = lean_ctor_get(v_toConstantVal_4791_, 0);
v___x_4793_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4792_);
v___x_4794_ = l_Lean_MessageData_ofName(v_name_4792_);
v___x_4795_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4795_, 0, v___x_4793_);
lean_ctor_set(v___x_4795_, 1, v___x_4794_);
v___x_4796_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4795_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4797_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4798_) == 0)
{
lean_dec_ref_known(v___x_4798_, 1);
v___y_4781_ = v_a_3734_;
v___y_4782_ = v_a_3735_;
goto v___jp_4780_;
}
else
{
lean_dec_ref_known(v_decl_3732_, 1);
return v___x_4798_;
}
}
}
v___jp_4801_:
{
lean_object* v___x_4802_; uint8_t v_isModule_4803_; 
v___x_4802_ = l_Lean_Environment_header(v_env_4799_);
lean_dec_ref(v_env_4799_);
v_isModule_4803_ = lean_ctor_get_uint8(v___x_4802_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4802_);
if (v_isModule_4803_ == 0)
{
lean_dec_ref(v_env_4800_);
v_exportedInfo_x3f_4773_ = v___x_4623_;
v___y_4774_ = v_a_3734_;
v___y_4775_ = v_a_3735_;
goto v___jp_4772_;
}
else
{
uint8_t v_isExporting_4804_; 
v_isExporting_4804_ = lean_ctor_get_uint8(v_env_4800_, sizeof(void*)*8);
lean_dec_ref(v_env_4800_);
if (v_isExporting_4804_ == 0)
{
goto v___jp_4790_;
}
else
{
if (v___x_4433_ == 0)
{
v_exportedInfo_x3f_4773_ = v___x_4623_;
v___y_4774_ = v_a_3734_;
v___y_4775_ = v_a_3735_;
goto v___jp_4772_;
}
else
{
goto v___jp_4790_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4805_; lean_object* v_toConstantVal_4806_; lean_object* v_name_4807_; lean_object* v___x_4808_; uint8_t v___x_4809_; 
v_val_4805_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4806_ = lean_ctor_get(v_val_4805_, 0);
v_name_4807_ = lean_ctor_get(v_toConstantVal_4806_, 0);
lean_inc_ref(v_val_4805_);
v___x_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4808_, 0, v_val_4805_);
v___x_4809_ = 2;
lean_inc(v_name_4807_);
v_fst_4656_ = v_name_4807_;
v_fst_4657_ = v___x_4808_;
v_snd_4658_ = v___x_4809_;
v_exportedInfo_x3f_4659_ = v___x_4623_;
v___y_4660_ = v_a_3734_;
v___y_4661_ = v_a_3735_;
goto v___jp_4655_;
}
default: 
{
v___y_4614_ = v_a_3734_;
v_options_4615_ = v_options_3789_;
v_inheritedTraceOptions_4616_ = v_inheritedTraceOptions_3790_;
v___y_4617_ = v_a_3735_;
goto v___jp_4613_;
}
}
v___jp_4613_:
{
uint8_t v___x_4618_; 
v___x_4618_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4616_, v_options_4615_, v___x_4131_);
if (v___x_4618_ == 0)
{
lean_object* v___x_4619_; 
v___x_4619_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4614_, v___y_4617_);
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4621_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4620_, v___y_4614_, v___y_4617_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v___x_4622_; 
lean_dec_ref_known(v___x_4621_, 1);
v___x_4622_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4614_, v___y_4617_);
return v___x_4622_;
}
else
{
lean_dec(v_decl_3732_);
return v___x_4621_;
}
}
}
v___jp_4624_:
{
lean_object* v___x_4631_; uint8_t v___x_4632_; 
lean_inc(v_decl_3732_);
v___x_4631_ = l_Lean_Declaration_getTopLevelNames(v_decl_3732_);
v___x_4632_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4631_);
lean_dec(v___x_4631_);
if (v___x_4632_ == 0)
{
if (lean_obj_tag(v___y_4628_) == 0)
{
if (v___x_4433_ == 0)
{
lean_object* v_options_4633_; uint8_t v_hasTrace_4634_; 
v_options_4633_ = lean_ctor_get(v___y_4629_, 2);
v_hasTrace_4634_ = lean_ctor_get_uint8(v_options_4633_, sizeof(void*)*1);
if (v_hasTrace_4634_ == 0)
{
v___y_4554_ = v___y_4625_;
v___y_4555_ = v___y_4626_;
v___y_4556_ = v___y_4627_;
v___y_4557_ = v___y_4629_;
v___y_4558_ = v___y_4630_;
goto v___jp_4553_;
}
else
{
lean_object* v_inheritedTraceOptions_4635_; uint8_t v___x_4636_; 
v_inheritedTraceOptions_4635_ = lean_ctor_get(v___y_4629_, 13);
v___x_4636_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4635_, v_options_4633_, v___x_4131_);
if (v___x_4636_ == 0)
{
v___y_4554_ = v___y_4625_;
v___y_4555_ = v___y_4626_;
v___y_4556_ = v___y_4627_;
v___y_4557_ = v___y_4629_;
v___y_4558_ = v___y_4630_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4637_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4638_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4637_, v___y_4629_, v___y_4630_);
if (lean_obj_tag(v___x_4638_) == 0)
{
lean_dec_ref_known(v___x_4638_, 1);
v___y_4554_ = v___y_4625_;
v___y_4555_ = v___y_4626_;
v___y_4556_ = v___y_4627_;
v___y_4557_ = v___y_4629_;
v___y_4558_ = v___y_4630_;
goto v___jp_4553_;
}
else
{
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4638_;
}
}
}
}
else
{
v___y_4583_ = v___y_4626_;
v___y_4584_ = v___y_4625_;
v___y_4585_ = v___y_4629_;
v___y_4586_ = v___y_4630_;
v___y_4587_ = v___y_4628_;
v___y_4588_ = v___y_4627_;
goto v___jp_4582_;
}
}
else
{
v___y_4583_ = v___y_4626_;
v___y_4584_ = v___y_4625_;
v___y_4585_ = v___y_4629_;
v___y_4586_ = v___y_4630_;
v___y_4587_ = v___y_4628_;
v___y_4588_ = v___y_4627_;
goto v___jp_4582_;
}
}
else
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v_a_4641_; uint8_t v___x_4642_; 
lean_dec(v___y_4628_);
v___x_4639_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4640_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4639_, v___y_4629_);
v_a_4641_ = lean_ctor_get(v___x_4640_, 0);
lean_inc(v_a_4641_);
lean_dec_ref(v___x_4640_);
v___x_4642_ = lean_unbox(v_a_4641_);
lean_dec(v_a_4641_);
if (v___x_4642_ == 0)
{
lean_object* v_options_4643_; uint8_t v_hasTrace_4644_; 
v_options_4643_ = lean_ctor_get(v___y_4629_, 2);
v_hasTrace_4644_ = lean_ctor_get_uint8(v_options_4643_, sizeof(void*)*1);
if (v_hasTrace_4644_ == 0)
{
v___y_4539_ = v___y_4625_;
v___y_4540_ = v___y_4626_;
v___y_4541_ = v___y_4627_;
v_exportedInfo_x3f_4542_ = v___x_4623_;
v___y_4543_ = v___y_4629_;
v___y_4544_ = v___y_4630_;
goto v___jp_4538_;
}
else
{
lean_object* v_inheritedTraceOptions_4645_; uint8_t v___x_4646_; 
v_inheritedTraceOptions_4645_ = lean_ctor_get(v___y_4629_, 13);
v___x_4646_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4645_, v_options_4643_, v___x_4131_);
if (v___x_4646_ == 0)
{
v___y_4539_ = v___y_4625_;
v___y_4540_ = v___y_4626_;
v___y_4541_ = v___y_4627_;
v_exportedInfo_x3f_4542_ = v___x_4623_;
v___y_4543_ = v___y_4629_;
v___y_4544_ = v___y_4630_;
goto v___jp_4538_;
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4648_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4647_, v___y_4629_, v___y_4630_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_dec_ref_known(v___x_4648_, 1);
v___y_4539_ = v___y_4625_;
v___y_4540_ = v___y_4626_;
v___y_4541_ = v___y_4627_;
v_exportedInfo_x3f_4542_ = v___x_4623_;
v___y_4543_ = v___y_4629_;
v___y_4544_ = v___y_4630_;
goto v___jp_4538_;
}
else
{
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4648_;
}
}
}
}
else
{
lean_object* v_options_4649_; uint8_t v_hasTrace_4650_; 
v_options_4649_ = lean_ctor_get(v___y_4629_, 2);
v_hasTrace_4650_ = lean_ctor_get_uint8(v_options_4649_, sizeof(void*)*1);
if (v_hasTrace_4650_ == 0)
{
v___y_4561_ = v___y_4625_;
v___y_4562_ = v___y_4626_;
v___y_4563_ = v___y_4627_;
v___y_4564_ = v___y_4629_;
v___y_4565_ = v___y_4630_;
goto v___jp_4560_;
}
else
{
lean_object* v_inheritedTraceOptions_4651_; uint8_t v___x_4652_; 
v_inheritedTraceOptions_4651_ = lean_ctor_get(v___y_4629_, 13);
v___x_4652_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4651_, v_options_4649_, v___x_4131_);
if (v___x_4652_ == 0)
{
v___y_4561_ = v___y_4625_;
v___y_4562_ = v___y_4626_;
v___y_4563_ = v___y_4627_;
v___y_4564_ = v___y_4629_;
v___y_4565_ = v___y_4630_;
goto v___jp_4560_;
}
else
{
lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4653_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4654_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4653_, v___y_4629_, v___y_4630_);
if (lean_obj_tag(v___x_4654_) == 0)
{
lean_dec_ref_known(v___x_4654_, 1);
v___y_4561_ = v___y_4625_;
v___y_4562_ = v___y_4626_;
v___y_4563_ = v___y_4627_;
v___y_4564_ = v___y_4629_;
v___y_4565_ = v___y_4630_;
goto v___jp_4560_;
}
else
{
lean_dec_ref(v___y_4626_);
lean_dec(v___y_4625_);
lean_dec(v_decl_3732_);
return v___x_4654_;
}
}
}
}
}
}
v___jp_4655_:
{
lean_object* v___x_4662_; lean_object* v_env_4663_; uint8_t v___x_4664_; 
v___x_4662_ = lean_st_ref_get(v___y_4661_);
v_env_4663_ = lean_ctor_get(v___x_4662_, 0);
lean_inc_ref(v_env_4663_);
lean_dec(v___x_4662_);
v___x_4664_ = l_Lean_Environment_containsOnBranch(v_env_4663_, v_fst_4656_);
lean_dec_ref(v_env_4663_);
if (v___x_4664_ == 0)
{
v___y_4625_ = v_fst_4656_;
v___y_4626_ = v_fst_4657_;
v___y_4627_ = v_snd_4658_;
v___y_4628_ = v_exportedInfo_x3f_4659_;
v___y_4629_ = v___y_4660_;
v___y_4630_ = v___y_4661_;
goto v___jp_4624_;
}
else
{
lean_object* v___x_4665_; lean_object* v_env_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; 
lean_dec(v_exportedInfo_x3f_4659_);
lean_dec_ref(v_fst_4657_);
lean_dec(v_decl_3732_);
v___x_4665_ = lean_st_ref_get(v___y_4661_);
v_env_4666_ = lean_ctor_get(v___x_4665_, 0);
lean_inc_ref(v_env_4666_);
lean_dec(v___x_4665_);
v___x_4667_ = lean_elab_environment_to_kernel_env(v_env_4666_);
v___x_4668_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
lean_ctor_set(v___x_4668_, 1, v_fst_4656_);
v___x_4669_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4668_, v___y_4660_, v___y_4661_);
return v___x_4669_;
}
}
v___jp_4670_:
{
lean_object* v_toConstantVal_4675_; lean_object* v_name_4676_; lean_object* v___x_4677_; uint8_t v___x_4678_; 
v_toConstantVal_4675_ = lean_ctor_get(v___y_4671_, 0);
v_name_4676_ = lean_ctor_get(v_toConstantVal_4675_, 0);
lean_inc(v_name_4676_);
v___x_4677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4677_, 0, v___y_4671_);
v___x_4678_ = 0;
v_fst_4656_ = v_name_4676_;
v_fst_4657_ = v___x_4677_;
v_snd_4658_ = v___x_4678_;
v_exportedInfo_x3f_4659_ = v_exportedInfo_x3f_4672_;
v___y_4660_ = v___y_4673_;
v___y_4661_ = v___y_4674_;
goto v___jp_4655_;
}
v___jp_4679_:
{
lean_object* v___x_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; 
v___x_4685_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4685_, 0, v___y_4683_);
lean_ctor_set_uint8(v___x_4685_, sizeof(void*)*1, v___y_4684_);
v___x_4686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4686_, 0, v___x_4685_);
v___x_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4687_, 0, v___x_4686_);
v___y_4671_ = v___y_4681_;
v_exportedInfo_x3f_4672_ = v___x_4687_;
v___y_4673_ = v___y_4680_;
v___y_4674_ = v___y_4682_;
goto v___jp_4670_;
}
v___jp_4688_:
{
uint8_t v___x_4694_; uint8_t v___x_4695_; 
v___x_4694_ = 1;
v___x_4695_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4691_, v___x_4694_);
if (v___x_4695_ == 0)
{
v___y_4680_ = v___y_4692_;
v___y_4681_ = v___y_4689_;
v___y_4682_ = v___y_4693_;
v___y_4683_ = v_toConstantVal_4690_;
v___y_4684_ = v_hasTrace_3791_;
goto v___jp_4679_;
}
else
{
v___y_4680_ = v___y_4692_;
v___y_4681_ = v___y_4689_;
v___y_4682_ = v___y_4693_;
v___y_4683_ = v_toConstantVal_4690_;
v___y_4684_ = v___x_4433_;
goto v___jp_4679_;
}
}
v___jp_4696_:
{
lean_object* v_toConstantVal_4700_; uint8_t v_safety_4701_; 
v_toConstantVal_4700_ = lean_ctor_get(v___y_4697_, 0);
lean_inc_ref(v_toConstantVal_4700_);
v_safety_4701_ = lean_ctor_get_uint8(v___y_4697_, sizeof(void*)*4);
v___y_4689_ = v___y_4697_;
v_toConstantVal_4690_ = v_toConstantVal_4700_;
v_safety_4691_ = v_safety_4701_;
v___y_4692_ = v___y_4698_;
v___y_4693_ = v___y_4699_;
goto v___jp_4688_;
}
v___jp_4702_:
{
lean_object* v_options_4706_; uint8_t v_hasTrace_4707_; 
v_options_4706_ = lean_ctor_get(v___y_4705_, 2);
v_hasTrace_4707_ = lean_ctor_get_uint8(v_options_4706_, sizeof(void*)*1);
if (v_hasTrace_4707_ == 0)
{
v___y_4697_ = v___y_4703_;
v___y_4698_ = v___y_4705_;
v___y_4699_ = v___y_4704_;
goto v___jp_4696_;
}
else
{
lean_object* v_inheritedTraceOptions_4708_; uint8_t v___x_4709_; 
v_inheritedTraceOptions_4708_ = lean_ctor_get(v___y_4705_, 13);
v___x_4709_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4708_, v_options_4706_, v___x_4131_);
if (v___x_4709_ == 0)
{
v___y_4697_ = v___y_4703_;
v___y_4698_ = v___y_4705_;
v___y_4699_ = v___y_4704_;
goto v___jp_4696_;
}
else
{
lean_object* v_toConstantVal_4710_; uint8_t v_safety_4711_; lean_object* v_name_4712_; lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v_toConstantVal_4710_ = lean_ctor_get(v___y_4703_, 0);
lean_inc_ref(v_toConstantVal_4710_);
v_safety_4711_ = lean_ctor_get_uint8(v___y_4703_, sizeof(void*)*4);
v_name_4712_ = lean_ctor_get(v_toConstantVal_4710_, 0);
v___x_4713_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4712_);
v___x_4714_ = l_Lean_MessageData_ofName(v_name_4712_);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4717_, v___y_4705_, v___y_4704_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
v___y_4689_ = v___y_4703_;
v_toConstantVal_4690_ = v_toConstantVal_4710_;
v_safety_4691_ = v_safety_4711_;
v___y_4692_ = v___y_4705_;
v___y_4693_ = v___y_4704_;
goto v___jp_4688_;
}
else
{
lean_dec_ref(v_toConstantVal_4710_);
lean_dec_ref(v___y_4703_);
lean_dec(v_decl_3732_);
return v___x_4718_;
}
}
}
}
v___jp_4719_:
{
lean_object* v___x_4725_; uint8_t v_isModule_4726_; 
v___x_4725_ = l_Lean_Environment_header(v___y_4721_);
lean_dec_ref(v___y_4721_);
v_isModule_4726_ = lean_ctor_get_uint8(v___x_4725_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4725_);
if (v_isModule_4726_ == 0)
{
lean_dec_ref(v___y_4723_);
v___y_4671_ = v___y_4720_;
v_exportedInfo_x3f_4672_ = v___x_4623_;
v___y_4673_ = v___y_4724_;
v___y_4674_ = v___y_4722_;
goto v___jp_4670_;
}
else
{
uint8_t v_isExporting_4727_; 
v_isExporting_4727_ = lean_ctor_get_uint8(v___y_4723_, sizeof(void*)*8);
lean_dec_ref(v___y_4723_);
if (v_isExporting_4727_ == 0)
{
v___y_4703_ = v___y_4720_;
v___y_4704_ = v___y_4722_;
v___y_4705_ = v___y_4724_;
goto v___jp_4702_;
}
else
{
if (v___x_4433_ == 0)
{
v___y_4671_ = v___y_4720_;
v_exportedInfo_x3f_4672_ = v___x_4623_;
v___y_4673_ = v___y_4724_;
v___y_4674_ = v___y_4722_;
goto v___jp_4670_;
}
else
{
v___y_4703_ = v___y_4720_;
v___y_4704_ = v___y_4722_;
v___y_4705_ = v___y_4724_;
goto v___jp_4702_;
}
}
}
}
v___jp_4728_:
{
lean_object* v___x_4732_; lean_object* v___x_4733_; 
v___x_4732_ = lean_st_ref_get(v___y_4731_);
v___x_4733_ = lean_st_ref_get(v___y_4731_);
if (v_forceExpose_3733_ == 0)
{
lean_object* v_env_4734_; lean_object* v_env_4735_; 
v_env_4734_ = lean_ctor_get(v___x_4732_, 0);
lean_inc_ref(v_env_4734_);
lean_dec(v___x_4732_);
v_env_4735_ = lean_ctor_get(v___x_4733_, 0);
lean_inc_ref(v_env_4735_);
lean_dec(v___x_4733_);
v___y_4720_ = v_defn_4729_;
v___y_4721_ = v_env_4734_;
v___y_4722_ = v___y_4731_;
v___y_4723_ = v_env_4735_;
v___y_4724_ = v___y_4730_;
goto v___jp_4719_;
}
else
{
if (v___x_4433_ == 0)
{
lean_dec(v___x_4733_);
lean_dec(v___x_4732_);
v___y_4671_ = v_defn_4729_;
v_exportedInfo_x3f_4672_ = v___x_4623_;
v___y_4673_ = v___y_4730_;
v___y_4674_ = v___y_4731_;
goto v___jp_4670_;
}
else
{
lean_object* v_env_4736_; lean_object* v_env_4737_; 
v_env_4736_ = lean_ctor_get(v___x_4732_, 0);
lean_inc_ref(v_env_4736_);
lean_dec(v___x_4732_);
v_env_4737_ = lean_ctor_get(v___x_4733_, 0);
lean_inc_ref(v_env_4737_);
lean_dec(v___x_4733_);
v___y_4720_ = v_defn_4729_;
v___y_4721_ = v_env_4736_;
v___y_4722_ = v___y_4731_;
v___y_4723_ = v_env_4737_;
v___y_4724_ = v___y_4730_;
goto v___jp_4719_;
}
}
}
}
}
}
else
{
goto v___jp_4280_;
}
v___jp_4434_:
{
lean_object* v___x_4445_; 
lean_inc_ref(v___y_4439_);
v___x_4445_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4442_, v___y_4439_, v___y_4441_, v___y_4444_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v___x_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref_known(v___x_4445_, 1);
lean_inc_ref(v___y_4437_);
v___x_4446_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4437_, v___y_4435_);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4492_ == 0)
{
lean_object* v_unused_4493_; 
v_unused_4493_ = lean_ctor_get(v___x_4446_, 0);
lean_dec(v_unused_4493_);
v___x_4448_ = v___x_4446_;
v_isShared_4449_ = v_isSharedCheck_4492_;
goto v_resetjp_4447_;
}
else
{
lean_dec(v___x_4446_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4492_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v_options_4450_; lean_object* v___x_4451_; uint8_t v___x_4452_; 
v_options_4450_ = lean_ctor_get(v___y_4436_, 2);
v___x_4451_ = l_Lean_Elab_async;
v___x_4452_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4450_, v___x_4451_);
if (v___x_4452_ == 0)
{
lean_object* v___x_4453_; lean_object* v_r_4454_; 
lean_del_object(v___x_4448_);
lean_dec_ref(v___y_4443_);
lean_dec_ref(v___y_4440_);
v___x_4453_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4439_, v___y_4435_);
lean_dec_ref(v___x_4453_);
v_r_4454_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_4436_, v___y_4435_);
if (lean_obj_tag(v_r_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4464_; 
v_a_4455_ = lean_ctor_get(v_r_4454_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v_r_4454_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4457_ = v_r_4454_;
v_isShared_4458_ = v_isSharedCheck_4464_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v_r_4454_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4464_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
lean_inc(v_a_4455_);
if (v_isShared_4458_ == 0)
{
lean_ctor_set_tag(v___x_4457_, 1);
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
lean_object* v___x_4461_; 
v___x_4461_ = lean_apply_2(v___y_4438_, v___x_4460_, lean_box(0));
if (lean_obj_tag(v___x_4461_) == 0)
{
lean_dec_ref_known(v___x_4461_, 1);
v___y_3738_ = v___y_4435_;
v___y_3739_ = v___y_4437_;
v_a_3740_ = v_a_4455_;
goto v___jp_3737_;
}
else
{
lean_object* v_a_4462_; 
lean_dec(v_a_4455_);
v_a_4462_ = lean_ctor_get(v___x_4461_, 0);
lean_inc(v_a_4462_);
lean_dec_ref_known(v___x_4461_, 1);
v___y_3751_ = v___y_4435_;
v___y_3752_ = v___y_4437_;
v_a_3753_ = v_a_4462_;
goto v___jp_3750_;
}
}
}
}
else
{
lean_object* v_a_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; 
v_a_4465_ = lean_ctor_get(v_r_4454_, 0);
lean_inc(v_a_4465_);
lean_dec_ref_known(v_r_4454_, 1);
v___x_4466_ = lean_box(0);
v___x_4467_ = lean_apply_2(v___y_4438_, v___x_4466_, lean_box(0));
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_dec_ref_known(v___x_4467_, 1);
v___y_3751_ = v___y_4435_;
v___y_3752_ = v___y_4437_;
v_a_3753_ = v_a_4465_;
goto v___jp_3750_;
}
else
{
lean_object* v_a_4468_; 
lean_dec(v_a_4465_);
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
lean_inc(v_a_4468_);
lean_dec_ref_known(v___x_4467_, 1);
v___y_3751_ = v___y_4435_;
v___y_3752_ = v___y_4437_;
v_a_3753_ = v_a_4468_;
goto v___jp_3750_;
}
}
}
else
{
lean_object* v___x_4469_; lean_object* v___x_4471_; 
lean_dec_ref(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v_decl_3732_);
v___x_4469_ = l_IO_CancelToken_new();
if (v_isShared_4449_ == 0)
{
lean_ctor_set_tag(v___x_4448_, 1);
lean_ctor_set(v___x_4448_, 0, v___x_4469_);
v___x_4471_ = v___x_4448_;
goto v_reusejp_4470_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v___x_4469_);
v___x_4471_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4470_;
}
v_reusejp_4470_:
{
lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; lean_object* v___x_4475_; 
v___x_4472_ = lean_unsigned_to_nat(0u);
v___x_4473_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4474_ = l_Lean_Name_toString(v___x_4473_, v_hasTrace_3791_);
lean_inc_ref(v___x_4471_);
v___x_4475_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4440_, v___x_4471_, v___x_4474_, v___y_4436_, v___y_4435_);
if (lean_obj_tag(v___x_4475_) == 0)
{
lean_object* v_a_4476_; lean_object* v_checked_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; 
v_a_4476_ = lean_ctor_get(v___x_4475_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v___x_4475_, 1);
v_checked_4477_ = lean_ctor_get(v___y_4443_, 2);
lean_inc_ref(v_checked_4477_);
lean_dec_ref(v___y_4443_);
v___x_4478_ = lean_io_map_task(v_a_4476_, v_checked_4477_, v___x_4472_, v___x_4433_);
v___x_4479_ = lean_box(0);
v___x_4480_ = lean_box(2);
v___x_4481_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4481_, 0, v___x_4479_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
lean_ctor_set(v___x_4481_, 2, v___x_4471_);
lean_ctor_set(v___x_4481_, 3, v___x_4478_);
v___x_4482_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4481_, v___y_4435_);
return v___x_4482_;
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec_ref(v___x_4471_);
lean_dec_ref(v___y_4443_);
v_a_4483_ = lean_ctor_get(v___x_4475_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4475_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4475_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4475_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4506_; 
lean_dec_ref(v___y_4443_);
lean_dec_ref(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec(v_decl_3732_);
v_a_4494_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4506_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4506_ == 0)
{
v___x_4496_ = v___x_4445_;
v_isShared_4497_ = v_isSharedCheck_4506_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4445_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4506_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v_ref_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; lean_object* v___x_4504_; 
v_ref_4498_ = lean_ctor_get(v___y_4436_, 5);
v___x_4499_ = lean_io_error_to_string(v_a_4494_);
v___x_4500_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4500_, 0, v___x_4499_);
v___x_4501_ = l_Lean_MessageData_ofFormat(v___x_4500_);
lean_inc(v_ref_4498_);
v___x_4502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4502_, 0, v_ref_4498_);
lean_ctor_set(v___x_4502_, 1, v___x_4501_);
if (v_isShared_4497_ == 0)
{
lean_ctor_set(v___x_4496_, 0, v___x_4502_);
v___x_4504_ = v___x_4496_;
goto v_reusejp_4503_;
}
else
{
lean_object* v_reuseFailAlloc_4505_; 
v_reuseFailAlloc_4505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4505_, 0, v___x_4502_);
v___x_4504_ = v_reuseFailAlloc_4505_;
goto v_reusejp_4503_;
}
v_reusejp_4503_:
{
return v___x_4504_;
}
}
}
}
v___jp_4507_:
{
lean_object* v___x_4518_; 
lean_inc_ref(v___y_4510_);
v___x_4518_ = l_Lean_Environment_addConstAsync(v___y_4510_, v___y_4513_, v___y_4515_, v___y_4517_, v___x_4433_, v_hasTrace_3791_);
if (lean_obj_tag(v___x_4518_) == 0)
{
lean_object* v_a_4519_; lean_object* v_mainEnv_4520_; lean_object* v_asyncEnv_4521_; lean_object* v___f_4522_; lean_object* v___f_4523_; lean_object* v___x_4524_; 
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc_n(v_a_4519_, 3);
lean_dec_ref_known(v___x_4518_, 1);
v_mainEnv_4520_ = lean_ctor_get(v_a_4519_, 0);
lean_inc_ref(v_mainEnv_4520_);
v_asyncEnv_4521_ = lean_ctor_get(v_a_4519_, 1);
lean_inc_ref_n(v_asyncEnv_4521_, 2);
lean_inc_ref(v___y_4509_);
lean_inc(v___y_4508_);
v___f_4522_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4522_, 0, v___y_4508_);
lean_closure_set(v___f_4522_, 1, v_a_4519_);
lean_closure_set(v___f_4522_, 2, v___y_4509_);
lean_inc(v_decl_3732_);
v___f_4523_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4523_, 0, v_asyncEnv_4521_);
lean_closure_set(v___f_4523_, 1, v_a_4519_);
lean_closure_set(v___f_4523_, 2, v_decl_3732_);
v___x_4524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4524_, 0, v___y_4512_);
if (lean_obj_tag(v___y_4516_) == 0)
{
lean_inc_ref(v___x_4524_);
v___y_4435_ = v___y_4511_;
v___y_4436_ = v___y_4514_;
v___y_4437_ = v_mainEnv_4520_;
v___y_4438_ = v___f_4522_;
v___y_4439_ = v_asyncEnv_4521_;
v___y_4440_ = v___f_4523_;
v___y_4441_ = v___x_4524_;
v___y_4442_ = v_a_4519_;
v___y_4443_ = v___y_4510_;
v___y_4444_ = v___x_4524_;
goto v___jp_4434_;
}
else
{
v___y_4435_ = v___y_4511_;
v___y_4436_ = v___y_4514_;
v___y_4437_ = v_mainEnv_4520_;
v___y_4438_ = v___f_4522_;
v___y_4439_ = v_asyncEnv_4521_;
v___y_4440_ = v___f_4523_;
v___y_4441_ = v___x_4524_;
v___y_4442_ = v_a_4519_;
v___y_4443_ = v___y_4510_;
v___y_4444_ = v___y_4516_;
goto v___jp_4434_;
}
}
else
{
lean_object* v_a_4525_; lean_object* v___x_4527_; uint8_t v_isShared_4528_; uint8_t v_isSharedCheck_4537_; 
lean_dec(v___y_4516_);
lean_dec_ref(v___y_4512_);
lean_dec_ref(v___y_4510_);
lean_dec(v_decl_3732_);
v_a_4525_ = lean_ctor_get(v___x_4518_, 0);
v_isSharedCheck_4537_ = !lean_is_exclusive(v___x_4518_);
if (v_isSharedCheck_4537_ == 0)
{
v___x_4527_ = v___x_4518_;
v_isShared_4528_ = v_isSharedCheck_4537_;
goto v_resetjp_4526_;
}
else
{
lean_inc(v_a_4525_);
lean_dec(v___x_4518_);
v___x_4527_ = lean_box(0);
v_isShared_4528_ = v_isSharedCheck_4537_;
goto v_resetjp_4526_;
}
v_resetjp_4526_:
{
lean_object* v_ref_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
v_ref_4529_ = lean_ctor_get(v___y_4514_, 5);
v___x_4530_ = lean_io_error_to_string(v_a_4525_);
v___x_4531_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
v___x_4532_ = l_Lean_MessageData_ofFormat(v___x_4531_);
lean_inc(v_ref_4529_);
v___x_4533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4533_, 0, v_ref_4529_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
if (v_isShared_4528_ == 0)
{
lean_ctor_set(v___x_4527_, 0, v___x_4533_);
v___x_4535_ = v___x_4527_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
}
}
v___jp_4538_:
{
lean_object* v___x_4545_; 
v___x_4545_ = lean_st_ref_get(v___y_4544_);
if (lean_obj_tag(v_exportedInfo_x3f_4542_) == 0)
{
lean_object* v_env_4546_; lean_object* v___x_4547_; 
v_env_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_env_4546_);
lean_dec(v___x_4545_);
v___x_4547_ = lean_box(0);
v___y_4508_ = v___y_4544_;
v___y_4509_ = v___y_4543_;
v___y_4510_ = v_env_4546_;
v___y_4511_ = v___y_4544_;
v___y_4512_ = v___y_4540_;
v___y_4513_ = v___y_4539_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4541_;
v___y_4516_ = v_exportedInfo_x3f_4542_;
v___y_4517_ = v___x_4547_;
goto v___jp_4507_;
}
else
{
lean_object* v_env_4548_; lean_object* v_val_4549_; uint8_t v___x_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; 
v_env_4548_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_ref(v_env_4548_);
lean_dec(v___x_4545_);
v_val_4549_ = lean_ctor_get(v_exportedInfo_x3f_4542_, 0);
v___x_4550_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4549_);
v___x_4551_ = lean_box(v___x_4550_);
v___x_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
v___y_4508_ = v___y_4544_;
v___y_4509_ = v___y_4543_;
v___y_4510_ = v_env_4548_;
v___y_4511_ = v___y_4544_;
v___y_4512_ = v___y_4540_;
v___y_4513_ = v___y_4539_;
v___y_4514_ = v___y_4543_;
v___y_4515_ = v___y_4541_;
v___y_4516_ = v_exportedInfo_x3f_4542_;
v___y_4517_ = v___x_4552_;
goto v___jp_4507_;
}
}
v___jp_4553_:
{
lean_object* v___x_4559_; 
lean_inc_ref(v___y_4555_);
v___x_4559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4559_, 0, v___y_4555_);
v___y_4539_ = v___y_4554_;
v___y_4540_ = v___y_4555_;
v___y_4541_ = v___y_4556_;
v_exportedInfo_x3f_4542_ = v___x_4559_;
v___y_4543_ = v___y_4557_;
v___y_4544_ = v___y_4558_;
goto v___jp_4538_;
}
v___jp_4560_:
{
lean_object* v___x_4566_; 
lean_inc_ref(v___y_4562_);
v___x_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4566_, 0, v___y_4562_);
v___y_4539_ = v___y_4561_;
v___y_4540_ = v___y_4562_;
v___y_4541_ = v___y_4563_;
v_exportedInfo_x3f_4542_ = v___x_4566_;
v___y_4543_ = v___y_4564_;
v___y_4544_ = v___y_4565_;
goto v___jp_4538_;
}
}
else
{
goto v___jp_4280_;
}
v___jp_4133_:
{
lean_object* v___x_4137_; double v___x_4138_; double v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; 
v___x_4137_ = lean_io_get_num_heartbeats();
v___x_4138_ = lean_float_of_nat(v___y_4135_);
v___x_4139_ = lean_float_of_nat(v___x_4137_);
v___x_4140_ = lean_box_float(v___x_4138_);
v___x_4141_ = lean_box_float(v___x_4139_);
v___x_4142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_a_4136_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3927_, v_hasTrace_3791_, v___x_4130_, v_options_3789_, v___x_4132_, v___y_4134_, v___f_4129_, v___x_4143_, v_a_3734_, v_a_3735_);
return v___x_4144_;
}
v___jp_4145_:
{
if (lean_obj_tag(v___y_4148_) == 0)
{
lean_object* v_a_4149_; lean_object* v___x_4151_; uint8_t v_isShared_4152_; uint8_t v_isSharedCheck_4156_; 
v_a_4149_ = lean_ctor_get(v___y_4148_, 0);
v_isSharedCheck_4156_ = !lean_is_exclusive(v___y_4148_);
if (v_isSharedCheck_4156_ == 0)
{
v___x_4151_ = v___y_4148_;
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
else
{
lean_inc(v_a_4149_);
lean_dec(v___y_4148_);
v___x_4151_ = lean_box(0);
v_isShared_4152_ = v_isSharedCheck_4156_;
goto v_resetjp_4150_;
}
v_resetjp_4150_:
{
lean_object* v___x_4154_; 
if (v_isShared_4152_ == 0)
{
lean_ctor_set_tag(v___x_4151_, 1);
v___x_4154_ = v___x_4151_;
goto v_reusejp_4153_;
}
else
{
lean_object* v_reuseFailAlloc_4155_; 
v_reuseFailAlloc_4155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4155_, 0, v_a_4149_);
v___x_4154_ = v_reuseFailAlloc_4155_;
goto v_reusejp_4153_;
}
v_reusejp_4153_:
{
v___y_4134_ = v___y_4146_;
v___y_4135_ = v___y_4147_;
v_a_4136_ = v___x_4154_;
goto v___jp_4133_;
}
}
}
else
{
lean_object* v_a_4157_; lean_object* v___x_4159_; uint8_t v_isShared_4160_; uint8_t v_isSharedCheck_4164_; 
v_a_4157_ = lean_ctor_get(v___y_4148_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___y_4148_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4159_ = v___y_4148_;
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
else
{
lean_inc(v_a_4157_);
lean_dec(v___y_4148_);
v___x_4159_ = lean_box(0);
v_isShared_4160_ = v_isSharedCheck_4164_;
goto v_resetjp_4158_;
}
v_resetjp_4158_:
{
lean_object* v___x_4162_; 
if (v_isShared_4160_ == 0)
{
lean_ctor_set_tag(v___x_4159_, 0);
v___x_4162_ = v___x_4159_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_a_4157_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
v___y_4134_ = v___y_4146_;
v___y_4135_ = v___y_4147_;
v_a_4136_ = v___x_4162_;
goto v___jp_4133_;
}
}
}
}
v___jp_4165_:
{
lean_object* v___x_4170_; lean_object* v___x_4171_; 
v___x_4170_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4171_ = lean_apply_5(v___y_4169_, v___x_4170_, v___y_4167_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4146_ = v___y_4166_;
v___y_4147_ = v___y_4168_;
v___y_4148_ = v___x_4171_;
goto v___jp_4145_;
}
v___jp_4172_:
{
lean_object* v___x_4177_; lean_object* v___x_4178_; 
v___x_4177_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4178_ = lean_apply_5(v___y_4173_, v___x_4177_, v___y_4175_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4146_ = v___y_4174_;
v___y_4147_ = v___y_4176_;
v___y_4148_ = v___x_4178_;
goto v___jp_4145_;
}
v___jp_4179_:
{
lean_object* v___x_4183_; double v___x_4184_; double v___x_4185_; double v___x_4186_; double v___x_4187_; double v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4183_ = lean_io_mono_nanos_now();
v___x_4184_ = lean_float_of_nat(v___y_4181_);
v___x_4185_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4186_ = lean_float_div(v___x_4184_, v___x_4185_);
v___x_4187_ = lean_float_of_nat(v___x_4183_);
v___x_4188_ = lean_float_div(v___x_4187_, v___x_4185_);
v___x_4189_ = lean_box_float(v___x_4186_);
v___x_4190_ = lean_box_float(v___x_4188_);
v___x_4191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
v___x_4192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4192_, 0, v_a_4182_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3927_, v_hasTrace_3791_, v___x_4130_, v_options_3789_, v___x_4132_, v___y_4180_, v___f_4129_, v___x_4192_, v_a_3734_, v_a_3735_);
return v___x_4193_;
}
v___jp_4194_:
{
if (lean_obj_tag(v___y_4197_) == 0)
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
v_a_4198_ = lean_ctor_get(v___y_4197_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___y_4197_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___y_4197_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___y_4197_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
lean_ctor_set_tag(v___x_4200_, 1);
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
v___y_4180_ = v___y_4195_;
v___y_4181_ = v___y_4196_;
v_a_4182_ = v___x_4203_;
goto v___jp_4179_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
v_a_4206_ = lean_ctor_get(v___y_4197_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___y_4197_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___y_4197_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___y_4197_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
lean_ctor_set_tag(v___x_4208_, 0);
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
v___y_4180_ = v___y_4195_;
v___y_4181_ = v___y_4196_;
v_a_4182_ = v___x_4211_;
goto v___jp_4179_;
}
}
}
}
v___jp_4214_:
{
lean_object* v___x_4219_; lean_object* v___x_4220_; 
v___x_4219_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4220_ = lean_apply_5(v___y_4217_, v___x_4219_, v___y_4218_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4215_;
v___y_4196_ = v___y_4216_;
v___y_4197_ = v___x_4220_;
goto v___jp_4194_;
}
v___jp_4221_:
{
if (v___x_4132_ == 0)
{
lean_object* v___x_4226_; lean_object* v___x_4227_; 
lean_dec_ref(v___y_4223_);
v___x_4226_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4227_ = lean_apply_4(v___y_4225_, v___x_4226_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4224_;
v___y_4197_ = v___x_4227_;
goto v___jp_4194_;
}
else
{
lean_object* v_toConstantVal_4228_; lean_object* v_name_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; 
v_toConstantVal_4228_ = lean_ctor_get(v___y_4223_, 0);
lean_inc_ref(v_toConstantVal_4228_);
lean_dec_ref(v___y_4223_);
v_name_4229_ = lean_ctor_get(v_toConstantVal_4228_, 0);
lean_inc(v_name_4229_);
lean_dec_ref(v_toConstantVal_4228_);
v___x_4230_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4231_ = l_Lean_MessageData_ofName(v_name_4229_);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v___x_4230_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4234_, 0, v___x_4232_);
lean_ctor_set(v___x_4234_, 1, v___x_4233_);
v___x_4235_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4234_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4235_) == 0)
{
lean_object* v_a_4236_; lean_object* v___x_4237_; 
v_a_4236_ = lean_ctor_get(v___x_4235_, 0);
lean_inc(v_a_4236_);
lean_dec_ref_known(v___x_4235_, 1);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4237_ = lean_apply_4(v___y_4225_, v_a_4236_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4224_;
v___y_4197_ = v___x_4237_;
goto v___jp_4194_;
}
else
{
lean_dec_ref(v___y_4225_);
v___y_4195_ = v___y_4222_;
v___y_4196_ = v___y_4224_;
v___y_4197_ = v___x_4235_;
goto v___jp_4194_;
}
}
}
v___jp_4238_:
{
lean_object* v___x_4248_; uint8_t v_isModule_4249_; 
v___x_4248_ = l_Lean_Environment_header(v___y_4244_);
lean_dec_ref(v___y_4244_);
v_isModule_4249_ = lean_ctor_get_uint8(v___x_4248_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4248_);
if (v_isModule_4249_ == 0)
{
lean_dec_ref(v___y_4245_);
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___y_4240_);
v___y_4215_ = v___y_4239_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4246_;
v___y_4218_ = v___y_4247_;
goto v___jp_4214_;
}
else
{
uint8_t v_isExporting_4250_; 
v_isExporting_4250_ = lean_ctor_get_uint8(v___y_4240_, sizeof(void*)*8);
lean_dec_ref(v___y_4240_);
if (v_isExporting_4250_ == 0)
{
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
v___y_4222_ = v___y_4239_;
v___y_4223_ = v___y_4241_;
v___y_4224_ = v___y_4243_;
v___y_4225_ = v___y_4245_;
goto v___jp_4221_;
}
else
{
if (v___y_4242_ == 0)
{
lean_dec_ref(v___y_4245_);
lean_dec_ref(v___y_4241_);
v___y_4215_ = v___y_4239_;
v___y_4216_ = v___y_4243_;
v___y_4217_ = v___y_4246_;
v___y_4218_ = v___y_4247_;
goto v___jp_4214_;
}
else
{
lean_dec(v___y_4247_);
lean_dec_ref(v___y_4246_);
v___y_4222_ = v___y_4239_;
v___y_4223_ = v___y_4241_;
v___y_4224_ = v___y_4243_;
v___y_4225_ = v___y_4245_;
goto v___jp_4221_;
}
}
}
}
v___jp_4251_:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4257_ = lean_apply_5(v___y_4253_, v___x_4256_, v___y_4255_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4252_;
v___y_4196_ = v___y_4254_;
v___y_4197_ = v___x_4257_;
goto v___jp_4194_;
}
v___jp_4258_:
{
lean_object* v___x_4266_; uint8_t v_isModule_4267_; 
v___x_4266_ = l_Lean_Environment_header(v___y_4262_);
lean_dec_ref(v___y_4262_);
v_isModule_4267_ = lean_ctor_get_uint8(v___x_4266_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4266_);
if (v_isModule_4267_ == 0)
{
lean_dec_ref(v___y_4263_);
lean_dec_ref(v___y_4260_);
v___y_4252_ = v___y_4259_;
v___y_4253_ = v___y_4261_;
v___y_4254_ = v___y_4264_;
v___y_4255_ = v___y_4265_;
goto v___jp_4251_;
}
else
{
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4261_);
if (v___x_4132_ == 0)
{
lean_object* v___x_4268_; lean_object* v___x_4269_; 
lean_dec_ref(v___y_4263_);
v___x_4268_ = lean_box(0);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4269_ = lean_apply_4(v___y_4260_, v___x_4268_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4259_;
v___y_4196_ = v___y_4264_;
v___y_4197_ = v___x_4269_;
goto v___jp_4194_;
}
else
{
lean_object* v_toConstantVal_4270_; lean_object* v_name_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; 
v_toConstantVal_4270_ = lean_ctor_get(v___y_4263_, 0);
lean_inc_ref(v_toConstantVal_4270_);
lean_dec_ref(v___y_4263_);
v_name_4271_ = lean_ctor_get(v_toConstantVal_4270_, 0);
lean_inc(v_name_4271_);
lean_dec_ref(v_toConstantVal_4270_);
v___x_4272_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4273_ = l_Lean_MessageData_ofName(v_name_4271_);
v___x_4274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4274_, 0, v___x_4272_);
lean_ctor_set(v___x_4274_, 1, v___x_4273_);
v___x_4275_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4274_);
lean_ctor_set(v___x_4276_, 1, v___x_4275_);
v___x_4277_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4276_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v_a_4278_; lean_object* v___x_4279_; 
v_a_4278_ = lean_ctor_get(v___x_4277_, 0);
lean_inc(v_a_4278_);
lean_dec_ref_known(v___x_4277_, 1);
lean_inc(v_a_3735_);
lean_inc_ref(v_a_3734_);
v___x_4279_ = lean_apply_4(v___y_4260_, v_a_4278_, v_a_3734_, v_a_3735_, lean_box(0));
v___y_4195_ = v___y_4259_;
v___y_4196_ = v___y_4264_;
v___y_4197_ = v___x_4279_;
goto v___jp_4194_;
}
else
{
lean_dec_ref(v___y_4260_);
v___y_4195_ = v___y_4259_;
v___y_4196_ = v___y_4264_;
v___y_4197_ = v___x_4277_;
goto v___jp_4194_;
}
}
}
}
v___jp_4280_:
{
lean_object* v___x_4281_; lean_object* v_a_4282_; lean_object* v___x_4284_; uint8_t v_isShared_4285_; uint8_t v_isSharedCheck_4431_; 
v___x_4281_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3735_);
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4281_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4284_ = v___x_4281_;
v_isShared_4285_ = v_isSharedCheck_4431_;
goto v_resetjp_4283_;
}
else
{
lean_inc(v_a_4282_);
lean_dec(v___x_4281_);
v___x_4284_ = lean_box(0);
v_isShared_4285_ = v_isSharedCheck_4431_;
goto v_resetjp_4283_;
}
v_resetjp_4283_:
{
lean_object* v___x_4286_; uint8_t v___x_4287_; 
v___x_4286_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4287_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3789_, v___x_4286_);
if (v___x_4287_ == 0)
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v_env_4290_; lean_object* v_nextMacroScope_4291_; lean_object* v_ngen_4292_; lean_object* v_auxDeclNGen_4293_; lean_object* v_traceState_4294_; lean_object* v_messages_4295_; lean_object* v_infoState_4296_; lean_object* v_snapshotTasks_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4345_; 
v___x_4288_ = lean_io_mono_nanos_now();
v___x_4289_ = lean_st_ref_take(v_a_3735_);
v_env_4290_ = lean_ctor_get(v___x_4289_, 0);
v_nextMacroScope_4291_ = lean_ctor_get(v___x_4289_, 1);
v_ngen_4292_ = lean_ctor_get(v___x_4289_, 2);
v_auxDeclNGen_4293_ = lean_ctor_get(v___x_4289_, 3);
v_traceState_4294_ = lean_ctor_get(v___x_4289_, 4);
v_messages_4295_ = lean_ctor_get(v___x_4289_, 6);
v_infoState_4296_ = lean_ctor_get(v___x_4289_, 7);
v_snapshotTasks_4297_ = lean_ctor_get(v___x_4289_, 8);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4345_ == 0)
{
lean_object* v_unused_4346_; 
v_unused_4346_ = lean_ctor_get(v___x_4289_, 5);
lean_dec(v_unused_4346_);
v___x_4299_ = v___x_4289_;
v_isShared_4300_ = v_isSharedCheck_4345_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_snapshotTasks_4297_);
lean_inc(v_infoState_4296_);
lean_inc(v_messages_4295_);
lean_inc(v_traceState_4294_);
lean_inc(v_auxDeclNGen_4293_);
lean_inc(v_ngen_4292_);
lean_inc(v_nextMacroScope_4291_);
lean_inc(v_env_4290_);
lean_dec(v___x_4289_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4345_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4305_; 
lean_inc(v_decl_3732_);
v___x_4301_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4302_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4290_, v___x_4301_);
v___x_4303_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 5, v___x_4303_);
lean_ctor_set(v___x_4299_, 0, v___x_4302_);
v___x_4305_ = v___x_4299_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4344_, 1, v_nextMacroScope_4291_);
lean_ctor_set(v_reuseFailAlloc_4344_, 2, v_ngen_4292_);
lean_ctor_set(v_reuseFailAlloc_4344_, 3, v_auxDeclNGen_4293_);
lean_ctor_set(v_reuseFailAlloc_4344_, 4, v_traceState_4294_);
lean_ctor_set(v_reuseFailAlloc_4344_, 5, v___x_4303_);
lean_ctor_set(v_reuseFailAlloc_4344_, 6, v_messages_4295_);
lean_ctor_set(v_reuseFailAlloc_4344_, 7, v_infoState_4296_);
lean_ctor_set(v_reuseFailAlloc_4344_, 8, v_snapshotTasks_4297_);
v___x_4305_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___f_4310_; 
v___x_4306_ = lean_st_ref_set(v_a_3735_, v___x_4305_);
v___x_4307_ = lean_box(0);
v___x_4308_ = lean_box(v_hasTrace_3791_);
v___x_4309_ = lean_box(v___x_4287_);
lean_inc(v_decl_3732_);
v___f_4310_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4310_, 0, v_decl_3732_);
lean_closure_set(v___f_4310_, 1, v___x_4308_);
lean_closure_set(v___f_4310_, 2, v___x_4309_);
lean_closure_set(v___f_4310_, 3, v___x_4303_);
lean_closure_set(v___f_4310_, 4, v_cls_3927_);
lean_closure_set(v___f_4310_, 5, v___x_4307_);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4311_; lean_object* v___x_4312_; lean_object* v_env_4313_; lean_object* v___f_4314_; lean_object* v___x_4315_; lean_object* v___f_4316_; 
lean_del_object(v___x_4284_);
v_val_4311_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4311_, 3);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4312_ = lean_st_ref_get(v_a_3735_);
v_env_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc_ref(v_env_4313_);
lean_dec(v___x_4312_);
v___f_4314_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4314_, 0, v_val_4311_);
lean_closure_set(v___f_4314_, 1, v___f_4310_);
v___x_4315_ = lean_box(v___x_4287_);
lean_inc_ref(v___f_4314_);
v___f_4316_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4316_, 0, v_val_4311_);
lean_closure_set(v___f_4316_, 1, v___x_4315_);
lean_closure_set(v___f_4316_, 2, v___f_4314_);
if (v_forceExpose_3733_ == 0)
{
v___y_4259_ = v_a_4282_;
v___y_4260_ = v___f_4316_;
v___y_4261_ = v___f_4314_;
v___y_4262_ = v_env_4313_;
v___y_4263_ = v_val_4311_;
v___y_4264_ = v___x_4288_;
v___y_4265_ = v___x_4307_;
goto v___jp_4258_;
}
else
{
if (v___x_4287_ == 0)
{
lean_dec_ref(v___f_4316_);
lean_dec_ref(v_env_4313_);
lean_dec_ref(v_val_4311_);
v___y_4252_ = v_a_4282_;
v___y_4253_ = v___f_4314_;
v___y_4254_ = v___x_4288_;
v___y_4255_ = v___x_4307_;
goto v___jp_4251_;
}
else
{
v___y_4259_ = v_a_4282_;
v___y_4260_ = v___f_4316_;
v___y_4261_ = v___f_4314_;
v___y_4262_ = v_env_4313_;
v___y_4263_ = v_val_4311_;
v___y_4264_ = v___x_4288_;
v___y_4265_ = v___x_4307_;
goto v___jp_4258_;
}
}
}
case 1:
{
lean_object* v_val_4317_; lean_object* v___x_4318_; 
lean_del_object(v___x_4284_);
v_val_4317_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4317_);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4318_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4310_, v_hasTrace_3791_, v___x_4287_, v_cls_3927_, v___x_4307_, v_forceExpose_3733_, v_val_4317_, v_a_3734_, v_a_3735_);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4318_;
goto v___jp_4194_;
}
case 5:
{
lean_object* v_defns_4319_; 
lean_del_object(v___x_4284_);
v_defns_4319_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4319_) == 1)
{
lean_object* v_tail_4320_; 
v_tail_4320_ = lean_ctor_get(v_defns_4319_, 1);
if (lean_obj_tag(v_tail_4320_) == 0)
{
lean_object* v_head_4321_; lean_object* v___x_4322_; 
lean_inc_ref(v_defns_4319_);
lean_dec_ref_known(v_decl_3732_, 1);
v_head_4321_ = lean_ctor_get(v_defns_4319_, 0);
lean_inc(v_head_4321_);
lean_dec_ref_known(v_defns_4319_, 2);
v___x_4322_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4310_, v_hasTrace_3791_, v___x_4287_, v_cls_3927_, v___x_4307_, v_forceExpose_3733_, v_head_4321_, v_a_3734_, v_a_3735_);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4322_;
goto v___jp_4194_;
}
else
{
lean_object* v___x_4323_; 
lean_dec_ref(v___f_4310_);
lean_inc_ref(v_decl_3732_);
v___x_4323_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4323_;
goto v___jp_4194_;
}
}
else
{
lean_object* v___x_4324_; 
lean_dec_ref(v___f_4310_);
lean_inc_ref(v_decl_3732_);
v___x_4324_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4324_;
goto v___jp_4194_;
}
}
case 3:
{
lean_object* v_val_4325_; lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v_env_4328_; lean_object* v_env_4329_; lean_object* v___f_4330_; lean_object* v___f_4331_; 
lean_del_object(v___x_4284_);
v_val_4325_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4325_, 3);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4326_ = lean_st_ref_get(v_a_3735_);
v___x_4327_ = lean_st_ref_get(v_a_3735_);
v_env_4328_ = lean_ctor_get(v___x_4326_, 0);
lean_inc_ref(v_env_4328_);
lean_dec(v___x_4326_);
v_env_4329_ = lean_ctor_get(v___x_4327_, 0);
lean_inc_ref(v_env_4329_);
lean_dec(v___x_4327_);
v___f_4330_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4330_, 0, v_val_4325_);
lean_closure_set(v___f_4330_, 1, v___f_4310_);
lean_inc_ref(v___f_4330_);
v___f_4331_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4331_, 0, v_val_4325_);
lean_closure_set(v___f_4331_, 1, v___f_4330_);
if (v_forceExpose_3733_ == 0)
{
v___y_4239_ = v_a_4282_;
v___y_4240_ = v_env_4329_;
v___y_4241_ = v_val_4325_;
v___y_4242_ = v___x_4287_;
v___y_4243_ = v___x_4288_;
v___y_4244_ = v_env_4328_;
v___y_4245_ = v___f_4331_;
v___y_4246_ = v___f_4330_;
v___y_4247_ = v___x_4307_;
goto v___jp_4238_;
}
else
{
if (v___x_4287_ == 0)
{
lean_dec_ref(v___f_4331_);
lean_dec_ref(v_env_4329_);
lean_dec_ref(v_env_4328_);
lean_dec_ref(v_val_4325_);
v___y_4215_ = v_a_4282_;
v___y_4216_ = v___x_4288_;
v___y_4217_ = v___f_4330_;
v___y_4218_ = v___x_4307_;
goto v___jp_4214_;
}
else
{
v___y_4239_ = v_a_4282_;
v___y_4240_ = v_env_4329_;
v___y_4241_ = v_val_4325_;
v___y_4242_ = v___x_4287_;
v___y_4243_ = v___x_4288_;
v___y_4244_ = v_env_4328_;
v___y_4245_ = v___f_4331_;
v___y_4246_ = v___f_4330_;
v___y_4247_ = v___x_4307_;
goto v___jp_4238_;
}
}
}
case 0:
{
lean_object* v_val_4332_; lean_object* v_toConstantVal_4333_; lean_object* v_name_4334_; lean_object* v___x_4336_; 
lean_dec_ref(v___f_4310_);
v_val_4332_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4333_ = lean_ctor_get(v_val_4332_, 0);
v_name_4334_ = lean_ctor_get(v_toConstantVal_4333_, 0);
lean_inc_ref(v_val_4332_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v_val_4332_);
v___x_4336_ = v___x_4284_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4342_; 
v_reuseFailAlloc_4342_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4342_, 0, v_val_4332_);
v___x_4336_ = v_reuseFailAlloc_4342_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4337_ = 2;
v___x_4338_ = lean_box(v___x_4337_);
v___x_4339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4336_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
lean_inc(v_name_4334_);
v___x_4340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4340_, 0, v_name_4334_);
lean_ctor_set(v___x_4340_, 1, v___x_4339_);
v___x_4341_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3732_, v_hasTrace_3791_, v___x_4287_, v___x_4303_, v_cls_3927_, v___x_4307_, v___x_4340_, v___x_4307_, v_a_3734_, v_a_3735_);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4341_;
goto v___jp_4194_;
}
}
default: 
{
lean_object* v___x_4343_; 
lean_dec_ref(v___f_4310_);
lean_del_object(v___x_4284_);
lean_inc(v_decl_3732_);
v___x_4343_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec(v_decl_3732_);
v___y_4195_ = v_a_4282_;
v___y_4196_ = v___x_4288_;
v___y_4197_ = v___x_4343_;
goto v___jp_4194_;
}
}
}
}
}
else
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v_env_4349_; lean_object* v_nextMacroScope_4350_; lean_object* v_ngen_4351_; lean_object* v_auxDeclNGen_4352_; lean_object* v_traceState_4353_; lean_object* v_messages_4354_; lean_object* v_infoState_4355_; lean_object* v_snapshotTasks_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4429_; 
v___x_4347_ = lean_io_get_num_heartbeats();
v___x_4348_ = lean_st_ref_take(v_a_3735_);
v_env_4349_ = lean_ctor_get(v___x_4348_, 0);
v_nextMacroScope_4350_ = lean_ctor_get(v___x_4348_, 1);
v_ngen_4351_ = lean_ctor_get(v___x_4348_, 2);
v_auxDeclNGen_4352_ = lean_ctor_get(v___x_4348_, 3);
v_traceState_4353_ = lean_ctor_get(v___x_4348_, 4);
v_messages_4354_ = lean_ctor_get(v___x_4348_, 6);
v_infoState_4355_ = lean_ctor_get(v___x_4348_, 7);
v_snapshotTasks_4356_ = lean_ctor_get(v___x_4348_, 8);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4429_ == 0)
{
lean_object* v_unused_4430_; 
v_unused_4430_ = lean_ctor_get(v___x_4348_, 5);
lean_dec(v_unused_4430_);
v___x_4358_ = v___x_4348_;
v_isShared_4359_ = v_isSharedCheck_4429_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_snapshotTasks_4356_);
lean_inc(v_infoState_4355_);
lean_inc(v_messages_4354_);
lean_inc(v_traceState_4353_);
lean_inc(v_auxDeclNGen_4352_);
lean_inc(v_ngen_4351_);
lean_inc(v_nextMacroScope_4350_);
lean_inc(v_env_4349_);
lean_dec(v___x_4348_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4429_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4364_; 
lean_inc(v_decl_3732_);
v___x_4360_ = l_Lean_Declaration_getNames(v_decl_3732_);
v___x_4361_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4349_, v___x_4360_);
v___x_4362_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 5, v___x_4362_);
lean_ctor_set(v___x_4358_, 0, v___x_4361_);
v___x_4364_ = v___x_4358_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4428_, 1, v_nextMacroScope_4350_);
lean_ctor_set(v_reuseFailAlloc_4428_, 2, v_ngen_4351_);
lean_ctor_set(v_reuseFailAlloc_4428_, 3, v_auxDeclNGen_4352_);
lean_ctor_set(v_reuseFailAlloc_4428_, 4, v_traceState_4353_);
lean_ctor_set(v_reuseFailAlloc_4428_, 5, v___x_4362_);
lean_ctor_set(v_reuseFailAlloc_4428_, 6, v_messages_4354_);
lean_ctor_set(v_reuseFailAlloc_4428_, 7, v_infoState_4355_);
lean_ctor_set(v_reuseFailAlloc_4428_, 8, v_snapshotTasks_4356_);
v___x_4364_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; 
v___x_4365_ = lean_st_ref_set(v_a_3735_, v___x_4364_);
v___x_4366_ = lean_box(0);
v___x_4367_ = lean_box(v___x_4287_);
lean_inc(v_decl_3732_);
v___f_4368_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4368_, 0, v_decl_3732_);
lean_closure_set(v___f_4368_, 1, v___x_4367_);
lean_closure_set(v___f_4368_, 2, v_cls_3927_);
lean_closure_set(v___f_4368_, 3, v___x_4362_);
lean_closure_set(v___f_4368_, 4, v___x_4366_);
switch(lean_obj_tag(v_decl_3732_))
{
case 2:
{
lean_object* v_val_4369_; lean_object* v___x_4370_; lean_object* v_env_4371_; lean_object* v___f_4372_; 
lean_del_object(v___x_4284_);
v_val_4369_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4369_, 2);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4370_ = lean_st_ref_get(v_a_3735_);
v_env_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc_ref(v_env_4371_);
lean_dec(v___x_4370_);
v___f_4372_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4372_, 0, v_val_4369_);
lean_closure_set(v___f_4372_, 1, v___f_4368_);
if (v_forceExpose_3733_ == 0)
{
if (v___x_4287_ == 0)
{
lean_dec_ref(v_env_4371_);
lean_dec_ref(v_val_4369_);
v___y_4173_ = v___f_4372_;
v___y_4174_ = v_a_4282_;
v___y_4175_ = v___x_4366_;
v___y_4176_ = v___x_4347_;
goto v___jp_4172_;
}
else
{
lean_object* v___x_4373_; uint8_t v_isModule_4374_; 
v___x_4373_ = l_Lean_Environment_header(v_env_4371_);
lean_dec_ref(v_env_4371_);
v_isModule_4374_ = lean_ctor_get_uint8(v___x_4373_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4373_);
if (v_isModule_4374_ == 0)
{
lean_dec_ref(v_val_4369_);
v___y_4173_ = v___f_4372_;
v___y_4174_ = v_a_4282_;
v___y_4175_ = v___x_4366_;
v___y_4176_ = v___x_4347_;
goto v___jp_4172_;
}
else
{
if (v___x_4132_ == 0)
{
lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4375_ = lean_box(0);
v___x_4376_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4369_, v_forceExpose_3733_, v___f_4372_, v___x_4375_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4369_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4376_;
goto v___jp_4145_;
}
else
{
lean_object* v_toConstantVal_4377_; lean_object* v_name_4378_; lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; lean_object* v___x_4382_; lean_object* v___x_4383_; lean_object* v___x_4384_; 
v_toConstantVal_4377_ = lean_ctor_get(v_val_4369_, 0);
v_name_4378_ = lean_ctor_get(v_toConstantVal_4377_, 0);
v___x_4379_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4378_);
v___x_4380_ = l_Lean_MessageData_ofName(v_name_4378_);
v___x_4381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4379_);
lean_ctor_set(v___x_4381_, 1, v___x_4380_);
v___x_4382_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4383_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4383_, 0, v___x_4381_);
lean_ctor_set(v___x_4383_, 1, v___x_4382_);
v___x_4384_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4383_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4384_) == 0)
{
lean_object* v_a_4385_; lean_object* v___x_4386_; 
v_a_4385_ = lean_ctor_get(v___x_4384_, 0);
lean_inc(v_a_4385_);
lean_dec_ref_known(v___x_4384_, 1);
v___x_4386_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4369_, v_forceExpose_3733_, v___f_4372_, v_a_4385_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4369_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4386_;
goto v___jp_4145_;
}
else
{
lean_dec_ref(v___f_4372_);
lean_dec_ref(v_val_4369_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4384_;
goto v___jp_4145_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4371_);
lean_dec_ref(v_val_4369_);
v___y_4173_ = v___f_4372_;
v___y_4174_ = v_a_4282_;
v___y_4175_ = v___x_4366_;
v___y_4176_ = v___x_4347_;
goto v___jp_4172_;
}
}
case 1:
{
lean_object* v_val_4387_; lean_object* v___x_4388_; 
lean_del_object(v___x_4284_);
v_val_4387_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref(v_val_4387_);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4388_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4368_, v_forceExpose_3733_, v___x_4287_, v___x_4366_, v_cls_3927_, v_val_4387_, v_a_3734_, v_a_3735_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4388_;
goto v___jp_4145_;
}
case 5:
{
lean_object* v_defns_4389_; 
lean_del_object(v___x_4284_);
v_defns_4389_ = lean_ctor_get(v_decl_3732_, 0);
if (lean_obj_tag(v_defns_4389_) == 1)
{
lean_object* v_tail_4390_; 
v_tail_4390_ = lean_ctor_get(v_defns_4389_, 1);
if (lean_obj_tag(v_tail_4390_) == 0)
{
lean_object* v_head_4391_; lean_object* v___x_4392_; 
lean_inc_ref(v_defns_4389_);
lean_dec_ref_known(v_decl_3732_, 1);
v_head_4391_ = lean_ctor_get(v_defns_4389_, 0);
lean_inc(v_head_4391_);
lean_dec_ref_known(v_defns_4389_, 2);
v___x_4392_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4368_, v_forceExpose_3733_, v___x_4287_, v___x_4366_, v_cls_3927_, v_head_4391_, v_a_3734_, v_a_3735_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4392_;
goto v___jp_4145_;
}
else
{
lean_object* v___x_4393_; 
lean_dec_ref(v___f_4368_);
lean_inc_ref(v_decl_3732_);
v___x_4393_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4393_;
goto v___jp_4145_;
}
}
else
{
lean_object* v___x_4394_; 
lean_dec_ref(v___f_4368_);
lean_inc_ref(v_decl_3732_);
v___x_4394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec_ref_known(v_decl_3732_, 1);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4394_;
goto v___jp_4145_;
}
}
case 3:
{
lean_object* v_val_4395_; lean_object* v___x_4396_; lean_object* v___x_4397_; lean_object* v_env_4398_; lean_object* v_env_4399_; lean_object* v___f_4400_; 
lean_del_object(v___x_4284_);
v_val_4395_ = lean_ctor_get(v_decl_3732_, 0);
lean_inc_ref_n(v_val_4395_, 2);
lean_dec_ref_known(v_decl_3732_, 1);
v___x_4396_ = lean_st_ref_get(v_a_3735_);
v___x_4397_ = lean_st_ref_get(v_a_3735_);
v_env_4398_ = lean_ctor_get(v___x_4396_, 0);
lean_inc_ref(v_env_4398_);
lean_dec(v___x_4396_);
v_env_4399_ = lean_ctor_get(v___x_4397_, 0);
lean_inc_ref(v_env_4399_);
lean_dec(v___x_4397_);
v___f_4400_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4400_, 0, v_val_4395_);
lean_closure_set(v___f_4400_, 1, v___f_4368_);
if (v_forceExpose_3733_ == 0)
{
if (v___x_4287_ == 0)
{
lean_dec_ref(v_env_4399_);
lean_dec_ref(v_env_4398_);
lean_dec_ref(v_val_4395_);
v___y_4166_ = v_a_4282_;
v___y_4167_ = v___x_4366_;
v___y_4168_ = v___x_4347_;
v___y_4169_ = v___f_4400_;
goto v___jp_4165_;
}
else
{
lean_object* v___x_4401_; uint8_t v_isModule_4402_; 
v___x_4401_ = l_Lean_Environment_header(v_env_4398_);
lean_dec_ref(v_env_4398_);
v_isModule_4402_ = lean_ctor_get_uint8(v___x_4401_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4401_);
if (v_isModule_4402_ == 0)
{
lean_dec_ref(v_env_4399_);
lean_dec_ref(v_val_4395_);
v___y_4166_ = v_a_4282_;
v___y_4167_ = v___x_4366_;
v___y_4168_ = v___x_4347_;
v___y_4169_ = v___f_4400_;
goto v___jp_4165_;
}
else
{
uint8_t v_isExporting_4403_; 
v_isExporting_4403_ = lean_ctor_get_uint8(v_env_4399_, sizeof(void*)*8);
lean_dec_ref(v_env_4399_);
if (v_isExporting_4403_ == 0)
{
if (v___x_4132_ == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4405_; 
v___x_4404_ = lean_box(0);
v___x_4405_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4395_, v___f_4400_, v___x_4404_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4395_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4405_;
goto v___jp_4145_;
}
else
{
lean_object* v_toConstantVal_4406_; lean_object* v_name_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v_toConstantVal_4406_ = lean_ctor_get(v_val_4395_, 0);
v_name_4407_ = lean_ctor_get(v_toConstantVal_4406_, 0);
v___x_4408_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4407_);
v___x_4409_ = l_Lean_MessageData_ofName(v_name_4407_);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3927_, v___x_4412_, v_a_3734_, v_a_3735_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_object* v_a_4414_; lean_object* v___x_4415_; 
v_a_4414_ = lean_ctor_get(v___x_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref_known(v___x_4413_, 1);
v___x_4415_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4395_, v___f_4400_, v_a_4414_, v_a_3734_, v_a_3735_);
lean_dec_ref(v_val_4395_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4415_;
goto v___jp_4145_;
}
else
{
lean_dec_ref(v___f_4400_);
lean_dec_ref(v_val_4395_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4413_;
goto v___jp_4145_;
}
}
}
else
{
lean_dec_ref(v_val_4395_);
v___y_4166_ = v_a_4282_;
v___y_4167_ = v___x_4366_;
v___y_4168_ = v___x_4347_;
v___y_4169_ = v___f_4400_;
goto v___jp_4165_;
}
}
}
}
else
{
lean_dec_ref(v_env_4399_);
lean_dec_ref(v_env_4398_);
lean_dec_ref(v_val_4395_);
v___y_4166_ = v_a_4282_;
v___y_4167_ = v___x_4366_;
v___y_4168_ = v___x_4347_;
v___y_4169_ = v___f_4400_;
goto v___jp_4165_;
}
}
case 0:
{
lean_object* v_val_4416_; lean_object* v_toConstantVal_4417_; lean_object* v_name_4418_; lean_object* v___x_4420_; 
lean_dec_ref(v___f_4368_);
v_val_4416_ = lean_ctor_get(v_decl_3732_, 0);
v_toConstantVal_4417_ = lean_ctor_get(v_val_4416_, 0);
v_name_4418_ = lean_ctor_get(v_toConstantVal_4417_, 0);
lean_inc_ref(v_val_4416_);
if (v_isShared_4285_ == 0)
{
lean_ctor_set(v___x_4284_, 0, v_val_4416_);
v___x_4420_ = v___x_4284_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_val_4416_);
v___x_4420_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
uint8_t v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; lean_object* v___x_4425_; 
v___x_4421_ = 2;
v___x_4422_ = lean_box(v___x_4421_);
v___x_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4420_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
lean_inc(v_name_4418_);
v___x_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4424_, 0, v_name_4418_);
lean_ctor_set(v___x_4424_, 1, v___x_4423_);
v___x_4425_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3732_, v___x_4287_, v_cls_3927_, v___x_4362_, v___x_4366_, v___x_4424_, v___x_4366_, v_a_3734_, v_a_3735_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4425_;
goto v___jp_4145_;
}
}
default: 
{
lean_object* v___x_4427_; 
lean_dec_ref(v___f_4368_);
lean_del_object(v___x_4284_);
lean_inc(v_decl_3732_);
v___x_4427_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3732_, v_cls_3927_, v_decl_3732_, v_a_3734_, v_a_3735_);
lean_dec(v_decl_3732_);
v___y_4146_ = v_a_4282_;
v___y_4147_ = v___x_4347_;
v___y_4148_ = v___x_4427_;
goto v___jp_4145_;
}
}
}
}
}
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
lean_ctor_set_tag(v___x_3756_, 1);
lean_ctor_set(v___x_3756_, 0, v_a_3753_);
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
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
lean_ctor_set(v___x_3769_, 0, v_a_3766_);
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
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
v___jp_3776_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v___x_3780_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3778_, v___y_3777_);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3780_);
if (v_isSharedCheck_3787_ == 0)
{
lean_object* v_unused_3788_; 
v_unused_3788_ = lean_ctor_get(v___x_3780_, 0);
lean_dec(v_unused_3788_);
v___x_3782_ = v___x_3780_;
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
else
{
lean_dec(v___x_3780_);
v___x_3782_ = lean_box(0);
v_isShared_3783_ = v_isSharedCheck_3787_;
goto v_resetjp_3781_;
}
v_resetjp_3781_:
{
lean_object* v___x_3785_; 
if (v_isShared_3783_ == 0)
{
lean_ctor_set_tag(v___x_3782_, 1);
lean_ctor_set(v___x_3782_, 0, v_a_3779_);
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v_a_3779_);
v___x_3785_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3784_;
}
v_reusejp_3784_:
{
return v___x_3785_;
}
}
}
v___jp_3792_:
{
lean_object* v___x_3804_; 
lean_inc_ref(v___y_3793_);
v___x_3804_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3802_, v___y_3793_, v___y_3799_, v___y_3803_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3851_; 
lean_dec_ref_known(v___x_3804_, 1);
lean_inc_ref(v___y_3797_);
v___x_3805_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3797_, v___y_3794_);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3851_ == 0)
{
lean_object* v_unused_3852_; 
v_unused_3852_ = lean_ctor_get(v___x_3805_, 0);
lean_dec(v_unused_3852_);
v___x_3807_ = v___x_3805_;
v_isShared_3808_ = v_isSharedCheck_3851_;
goto v_resetjp_3806_;
}
else
{
lean_dec(v___x_3805_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3851_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_options_3809_; lean_object* v___x_3810_; uint8_t v___x_3811_; 
v_options_3809_ = lean_ctor_get(v___y_3801_, 2);
v___x_3810_ = l_Lean_Elab_async;
v___x_3811_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3809_, v___x_3810_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; lean_object* v_r_3813_; 
lean_del_object(v___x_3807_);
lean_dec_ref(v___y_3800_);
lean_dec_ref(v___y_3796_);
v___x_3812_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3793_, v___y_3794_);
lean_dec_ref(v___x_3812_);
v_r_3813_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3732_, v___y_3801_, v___y_3794_);
if (lean_obj_tag(v_r_3813_) == 0)
{
lean_object* v_a_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3823_; 
v_a_3814_ = lean_ctor_get(v_r_3813_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v_r_3813_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3816_ = v_r_3813_;
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
else
{
lean_inc(v_a_3814_);
lean_dec(v_r_3813_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3823_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
lean_inc(v_a_3814_);
if (v_isShared_3817_ == 0)
{
lean_ctor_set_tag(v___x_3816_, 1);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v_a_3814_);
v___x_3819_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
lean_object* v___x_3820_; 
v___x_3820_ = lean_apply_2(v___y_3795_, v___x_3819_, lean_box(0));
if (lean_obj_tag(v___x_3820_) == 0)
{
lean_dec_ref_known(v___x_3820_, 1);
v___y_3764_ = v___y_3794_;
v___y_3765_ = v___y_3797_;
v_a_3766_ = v_a_3814_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_3821_; 
lean_dec(v_a_3814_);
v_a_3821_ = lean_ctor_get(v___x_3820_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3820_, 1);
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___y_3797_;
v_a_3779_ = v_a_3821_;
goto v___jp_3776_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; 
v_a_3824_ = lean_ctor_get(v_r_3813_, 0);
lean_inc(v_a_3824_);
lean_dec_ref_known(v_r_3813_, 1);
v___x_3825_ = lean_box(0);
v___x_3826_ = lean_apply_2(v___y_3795_, v___x_3825_, lean_box(0));
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_dec_ref_known(v___x_3826_, 1);
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___y_3797_;
v_a_3779_ = v_a_3824_;
goto v___jp_3776_;
}
else
{
lean_object* v_a_3827_; 
lean_dec(v_a_3824_);
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref_known(v___x_3826_, 1);
v___y_3777_ = v___y_3794_;
v___y_3778_ = v___y_3797_;
v_a_3779_ = v_a_3827_;
goto v___jp_3776_;
}
}
}
else
{
lean_object* v___x_3828_; lean_object* v___x_3830_; 
lean_dec_ref(v___y_3797_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v___y_3793_);
lean_dec(v_decl_3732_);
v___x_3828_ = l_IO_CancelToken_new();
if (v_isShared_3808_ == 0)
{
lean_ctor_set_tag(v___x_3807_, 1);
lean_ctor_set(v___x_3807_, 0, v___x_3828_);
v___x_3830_ = v___x_3807_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; 
v___x_3831_ = lean_unsigned_to_nat(0u);
v___x_3832_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3833_ = l_Lean_Name_toString(v___x_3832_, v___y_3798_);
lean_inc_ref(v___x_3830_);
v___x_3834_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3796_, v___x_3830_, v___x_3833_, v___y_3801_, v___y_3794_);
if (lean_obj_tag(v___x_3834_) == 0)
{
lean_object* v_a_3835_; lean_object* v_checked_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_a_3835_ = lean_ctor_get(v___x_3834_, 0);
lean_inc(v_a_3835_);
lean_dec_ref_known(v___x_3834_, 1);
v_checked_3836_ = lean_ctor_get(v___y_3800_, 2);
lean_inc_ref(v_checked_3836_);
lean_dec_ref(v___y_3800_);
v___x_3837_ = lean_io_map_task(v_a_3835_, v_checked_3836_, v___x_3831_, v_hasTrace_3791_);
v___x_3838_ = lean_box(0);
v___x_3839_ = lean_box(2);
v___x_3840_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3838_);
lean_ctor_set(v___x_3840_, 1, v___x_3839_);
lean_ctor_set(v___x_3840_, 2, v___x_3830_);
lean_ctor_set(v___x_3840_, 3, v___x_3837_);
v___x_3841_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3840_, v___y_3794_);
return v___x_3841_;
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v___x_3830_);
lean_dec_ref(v___y_3800_);
v_a_3842_ = lean_ctor_get(v___x_3834_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3834_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3834_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3834_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v___y_3800_);
lean_dec_ref(v___y_3797_);
lean_dec_ref(v___y_3796_);
lean_dec_ref(v___y_3795_);
lean_dec_ref(v___y_3793_);
lean_dec(v_decl_3732_);
v_a_3853_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3855_ = v___x_3804_;
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_dec(v___x_3804_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3865_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v_ref_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
v_ref_3857_ = lean_ctor_get(v___y_3801_, 5);
v___x_3858_ = lean_io_error_to_string(v_a_3853_);
v___x_3859_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3859_, 0, v___x_3858_);
v___x_3860_ = l_Lean_MessageData_ofFormat(v___x_3859_);
lean_inc(v_ref_3857_);
v___x_3861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3861_, 0, v_ref_3857_);
lean_ctor_set(v___x_3861_, 1, v___x_3860_);
if (v_isShared_3856_ == 0)
{
lean_ctor_set(v___x_3855_, 0, v___x_3861_);
v___x_3863_ = v___x_3855_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
v___jp_3866_:
{
uint8_t v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = 1;
lean_inc_ref(v___y_3869_);
v___x_3878_ = l_Lean_Environment_addConstAsync(v___y_3869_, v___y_3875_, v___y_3870_, v___y_3876_, v_hasTrace_3791_, v___x_3877_);
if (lean_obj_tag(v___x_3878_) == 0)
{
lean_object* v_a_3879_; lean_object* v_mainEnv_3880_; lean_object* v_asyncEnv_3881_; lean_object* v___f_3882_; lean_object* v___f_3883_; lean_object* v___x_3884_; 
v_a_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc_n(v_a_3879_, 3);
lean_dec_ref_known(v___x_3878_, 1);
v_mainEnv_3880_ = lean_ctor_get(v_a_3879_, 0);
lean_inc_ref(v_mainEnv_3880_);
v_asyncEnv_3881_ = lean_ctor_get(v_a_3879_, 1);
lean_inc_ref_n(v_asyncEnv_3881_, 2);
lean_inc_ref(v___y_3868_);
lean_inc(v___y_3867_);
v___f_3882_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3882_, 0, v___y_3867_);
lean_closure_set(v___f_3882_, 1, v_a_3879_);
lean_closure_set(v___f_3882_, 2, v___y_3868_);
lean_inc(v_decl_3732_);
v___f_3883_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3883_, 0, v_asyncEnv_3881_);
lean_closure_set(v___f_3883_, 1, v_a_3879_);
lean_closure_set(v___f_3883_, 2, v_decl_3732_);
v___x_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3884_, 0, v___y_3871_);
if (lean_obj_tag(v___y_3873_) == 0)
{
lean_inc_ref(v___x_3884_);
v___y_3793_ = v_asyncEnv_3881_;
v___y_3794_ = v___y_3872_;
v___y_3795_ = v___f_3882_;
v___y_3796_ = v___f_3883_;
v___y_3797_ = v_mainEnv_3880_;
v___y_3798_ = v___x_3877_;
v___y_3799_ = v___x_3884_;
v___y_3800_ = v___y_3869_;
v___y_3801_ = v___y_3874_;
v___y_3802_ = v_a_3879_;
v___y_3803_ = v___x_3884_;
goto v___jp_3792_;
}
else
{
v___y_3793_ = v_asyncEnv_3881_;
v___y_3794_ = v___y_3872_;
v___y_3795_ = v___f_3882_;
v___y_3796_ = v___f_3883_;
v___y_3797_ = v_mainEnv_3880_;
v___y_3798_ = v___x_3877_;
v___y_3799_ = v___x_3884_;
v___y_3800_ = v___y_3869_;
v___y_3801_ = v___y_3874_;
v___y_3802_ = v_a_3879_;
v___y_3803_ = v___y_3873_;
goto v___jp_3792_;
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3897_; 
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3871_);
lean_dec_ref(v___y_3869_);
lean_dec(v_decl_3732_);
v_a_3885_ = lean_ctor_get(v___x_3878_, 0);
v_isSharedCheck_3897_ = !lean_is_exclusive(v___x_3878_);
if (v_isSharedCheck_3897_ == 0)
{
v___x_3887_ = v___x_3878_;
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3878_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3897_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_ref_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3895_; 
v_ref_3889_ = lean_ctor_get(v___y_3874_, 5);
v___x_3890_ = lean_io_error_to_string(v_a_3885_);
v___x_3891_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3891_, 0, v___x_3890_);
v___x_3892_ = l_Lean_MessageData_ofFormat(v___x_3891_);
lean_inc(v_ref_3889_);
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v_ref_3889_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3893_);
v___x_3895_ = v___x_3887_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3896_; 
v_reuseFailAlloc_3896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3896_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3896_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
return v___x_3895_;
}
}
}
}
v___jp_3898_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_st_ref_get(v___y_3904_);
if (lean_obj_tag(v_exportedInfo_x3f_3902_) == 0)
{
lean_object* v_env_3906_; lean_object* v___x_3907_; 
v_env_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref(v_env_3906_);
lean_dec(v___x_3905_);
v___x_3907_ = lean_box(0);
v___y_3867_ = v___y_3904_;
v___y_3868_ = v___y_3903_;
v___y_3869_ = v_env_3906_;
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3900_;
v___y_3872_ = v___y_3904_;
v___y_3873_ = v_exportedInfo_x3f_3902_;
v___y_3874_ = v___y_3903_;
v___y_3875_ = v___y_3901_;
v___y_3876_ = v___x_3907_;
goto v___jp_3866_;
}
else
{
lean_object* v_env_3908_; lean_object* v_val_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_env_3908_ = lean_ctor_get(v___x_3905_, 0);
lean_inc_ref(v_env_3908_);
lean_dec(v___x_3905_);
v_val_3909_ = lean_ctor_get(v_exportedInfo_x3f_3902_, 0);
v___x_3910_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3909_);
v___x_3911_ = lean_box(v___x_3910_);
v___x_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3912_, 0, v___x_3911_);
v___y_3867_ = v___y_3904_;
v___y_3868_ = v___y_3903_;
v___y_3869_ = v_env_3908_;
v___y_3870_ = v___y_3899_;
v___y_3871_ = v___y_3900_;
v___y_3872_ = v___y_3904_;
v___y_3873_ = v_exportedInfo_x3f_3902_;
v___y_3874_ = v___y_3903_;
v___y_3875_ = v___y_3901_;
v___y_3876_ = v___x_3912_;
goto v___jp_3866_;
}
}
v___jp_3913_:
{
lean_object* v___x_3919_; 
lean_inc_ref(v___y_3915_);
v___x_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3919_, 0, v___y_3915_);
v___y_3899_ = v___y_3914_;
v___y_3900_ = v___y_3915_;
v___y_3901_ = v___y_3916_;
v_exportedInfo_x3f_3902_ = v___x_3919_;
v___y_3903_ = v___y_3917_;
v___y_3904_ = v___y_3918_;
goto v___jp_3898_;
}
v___jp_3920_:
{
lean_object* v___x_3926_; 
lean_inc_ref(v___y_3922_);
v___x_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3926_, 0, v___y_3922_);
v___y_3899_ = v___y_3921_;
v___y_3900_ = v___y_3922_;
v___y_3901_ = v___y_3923_;
v_exportedInfo_x3f_3902_ = v___x_3926_;
v___y_3903_ = v___y_3924_;
v___y_3904_ = v___y_3925_;
goto v___jp_3898_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4813_, lean_object* v_forceExpose_4814_, lean_object* v_a_4815_, lean_object* v_a_4816_, lean_object* v_a_4817_){
_start:
{
uint8_t v_forceExpose_boxed_4818_; lean_object* v_res_4819_; 
v_forceExpose_boxed_4818_ = lean_unbox(v_forceExpose_4814_);
v_res_4819_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4813_, v_forceExpose_boxed_4818_, v_a_4815_, v_a_4816_);
lean_dec(v_a_4816_);
lean_dec_ref(v_a_4815_);
return v_res_4819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4820_, lean_object* v___y_4821_, lean_object* v___y_4822_){
_start:
{
lean_object* v___x_4824_; 
v___x_4824_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4820_, v___y_4821_);
return v___x_4824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec_ref(v_opt_4825_);
return v_res_4829_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4830_, lean_object* v_x_4831_, lean_object* v___y_4832_, lean_object* v___y_4833_){
_start:
{
if (lean_obj_tag(v_x_4830_) == 0)
{
lean_object* v___x_4835_; lean_object* v___x_4836_; 
v___x_4835_ = l_List_reverse___redArg(v_x_4831_);
v___x_4836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4836_, 0, v___x_4835_);
return v___x_4836_;
}
else
{
lean_object* v_head_4837_; lean_object* v_tail_4838_; lean_object* v___x_4840_; uint8_t v_isShared_4841_; uint8_t v_isSharedCheck_4856_; 
v_head_4837_ = lean_ctor_get(v_x_4830_, 0);
v_tail_4838_ = lean_ctor_get(v_x_4830_, 1);
v_isSharedCheck_4856_ = !lean_is_exclusive(v_x_4830_);
if (v_isSharedCheck_4856_ == 0)
{
v___x_4840_ = v_x_4830_;
v_isShared_4841_ = v_isSharedCheck_4856_;
goto v_resetjp_4839_;
}
else
{
lean_inc(v_tail_4838_);
lean_inc(v_head_4837_);
lean_dec(v_x_4830_);
v___x_4840_ = lean_box(0);
v_isShared_4841_ = v_isSharedCheck_4856_;
goto v_resetjp_4839_;
}
v_resetjp_4839_:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_snapshotEnvLinterOptions(v_head_4837_, v___y_4832_, v___y_4833_);
if (lean_obj_tag(v___x_4842_) == 0)
{
lean_object* v_a_4843_; lean_object* v___x_4845_; 
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref_known(v___x_4842_, 1);
if (v_isShared_4841_ == 0)
{
lean_ctor_set(v___x_4840_, 1, v_x_4831_);
lean_ctor_set(v___x_4840_, 0, v_a_4843_);
v___x_4845_ = v___x_4840_;
goto v_reusejp_4844_;
}
else
{
lean_object* v_reuseFailAlloc_4847_; 
v_reuseFailAlloc_4847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4847_, 0, v_a_4843_);
lean_ctor_set(v_reuseFailAlloc_4847_, 1, v_x_4831_);
v___x_4845_ = v_reuseFailAlloc_4847_;
goto v_reusejp_4844_;
}
v_reusejp_4844_:
{
v_x_4830_ = v_tail_4838_;
v_x_4831_ = v___x_4845_;
goto _start;
}
}
else
{
lean_object* v_a_4848_; lean_object* v___x_4850_; uint8_t v_isShared_4851_; uint8_t v_isSharedCheck_4855_; 
lean_del_object(v___x_4840_);
lean_dec(v_tail_4838_);
lean_dec(v_x_4831_);
v_a_4848_ = lean_ctor_get(v___x_4842_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4842_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4850_ = v___x_4842_;
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
else
{
lean_inc(v_a_4848_);
lean_dec(v___x_4842_);
v___x_4850_ = lean_box(0);
v_isShared_4851_ = v_isSharedCheck_4855_;
goto v_resetjp_4849_;
}
v_resetjp_4849_:
{
lean_object* v___x_4853_; 
if (v_isShared_4851_ == 0)
{
v___x_4853_ = v___x_4850_;
goto v_reusejp_4852_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v_a_4848_);
v___x_4853_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4852_;
}
v_reusejp_4852_:
{
return v___x_4853_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4857_, lean_object* v_x_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4857_, v_x_4858_, v___y_4859_, v___y_4860_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4863_, uint8_t v_forceExpose_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_){
_start:
{
lean_object* v___x_4868_; 
lean_inc(v_decl_4863_);
v___x_4868_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4863_, v_forceExpose_4864_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
lean_dec_ref_known(v___x_4868_, 1);
v___x_4869_ = l_Lean_Declaration_getTopLevelNames(v_decl_4863_);
v___x_4870_ = lean_box(0);
v___x_4871_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4869_, v___x_4870_, v_a_4865_, v_a_4866_);
if (lean_obj_tag(v___x_4871_) == 0)
{
lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4879_; 
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4879_ == 0)
{
lean_object* v_unused_4880_; 
v_unused_4880_ = lean_ctor_get(v___x_4871_, 0);
lean_dec(v_unused_4880_);
v___x_4873_ = v___x_4871_;
v_isShared_4874_ = v_isSharedCheck_4879_;
goto v_resetjp_4872_;
}
else
{
lean_dec(v___x_4871_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4879_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
lean_object* v___x_4875_; lean_object* v___x_4877_; 
v___x_4875_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4875_);
v___x_4877_ = v___x_4873_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4875_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
else
{
lean_object* v_a_4881_; lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4888_; 
v_a_4881_ = lean_ctor_get(v___x_4871_, 0);
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4871_);
if (v_isSharedCheck_4888_ == 0)
{
v___x_4883_ = v___x_4871_;
v_isShared_4884_ = v_isSharedCheck_4888_;
goto v_resetjp_4882_;
}
else
{
lean_inc(v_a_4881_);
lean_dec(v___x_4871_);
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
else
{
lean_dec(v_decl_4863_);
return v___x_4868_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4889_, lean_object* v_forceExpose_4890_, lean_object* v_a_4891_, lean_object* v_a_4892_, lean_object* v_a_4893_){
_start:
{
uint8_t v_forceExpose_boxed_4894_; lean_object* v_res_4895_; 
v_forceExpose_boxed_4894_ = lean_unbox(v_forceExpose_4890_);
v_res_4895_ = l_Lean_addDecl(v_decl_4889_, v_forceExpose_boxed_4894_, v_a_4891_, v_a_4892_);
lean_dec(v_a_4892_);
lean_dec_ref(v_a_4891_);
return v_res_4895_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4896_, lean_object* v_b_4897_, lean_object* v___y_4898_){
_start:
{
if (lean_obj_tag(v_as_x27_4896_) == 0)
{
lean_object* v___x_4900_; 
v___x_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4900_, 0, v_b_4897_);
return v___x_4900_;
}
else
{
lean_object* v_head_4901_; lean_object* v_tail_4902_; lean_object* v___x_4903_; lean_object* v_env_4904_; lean_object* v_nextMacroScope_4905_; lean_object* v_ngen_4906_; lean_object* v_auxDeclNGen_4907_; lean_object* v_traceState_4908_; lean_object* v_messages_4909_; lean_object* v_infoState_4910_; lean_object* v_snapshotTasks_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4923_; 
v_head_4901_ = lean_ctor_get(v_as_x27_4896_, 0);
v_tail_4902_ = lean_ctor_get(v_as_x27_4896_, 1);
v___x_4903_ = lean_st_ref_take(v___y_4898_);
v_env_4904_ = lean_ctor_get(v___x_4903_, 0);
v_nextMacroScope_4905_ = lean_ctor_get(v___x_4903_, 1);
v_ngen_4906_ = lean_ctor_get(v___x_4903_, 2);
v_auxDeclNGen_4907_ = lean_ctor_get(v___x_4903_, 3);
v_traceState_4908_ = lean_ctor_get(v___x_4903_, 4);
v_messages_4909_ = lean_ctor_get(v___x_4903_, 6);
v_infoState_4910_ = lean_ctor_get(v___x_4903_, 7);
v_snapshotTasks_4911_ = lean_ctor_get(v___x_4903_, 8);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4903_);
if (v_isSharedCheck_4923_ == 0)
{
lean_object* v_unused_4924_; 
v_unused_4924_ = lean_ctor_get(v___x_4903_, 5);
lean_dec(v_unused_4924_);
v___x_4913_ = v___x_4903_;
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_snapshotTasks_4911_);
lean_inc(v_infoState_4910_);
lean_inc(v_messages_4909_);
lean_inc(v_traceState_4908_);
lean_inc(v_auxDeclNGen_4907_);
lean_inc(v_ngen_4906_);
lean_inc(v_nextMacroScope_4905_);
lean_inc(v_env_4904_);
lean_dec(v___x_4903_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4923_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; 
lean_inc(v_head_4901_);
v___x_4915_ = l_Lean_markMeta(v_env_4904_, v_head_4901_);
v___x_4916_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4914_ == 0)
{
lean_ctor_set(v___x_4913_, 5, v___x_4916_);
lean_ctor_set(v___x_4913_, 0, v___x_4915_);
v___x_4918_ = v___x_4913_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v___x_4915_);
lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_nextMacroScope_4905_);
lean_ctor_set(v_reuseFailAlloc_4922_, 2, v_ngen_4906_);
lean_ctor_set(v_reuseFailAlloc_4922_, 3, v_auxDeclNGen_4907_);
lean_ctor_set(v_reuseFailAlloc_4922_, 4, v_traceState_4908_);
lean_ctor_set(v_reuseFailAlloc_4922_, 5, v___x_4916_);
lean_ctor_set(v_reuseFailAlloc_4922_, 6, v_messages_4909_);
lean_ctor_set(v_reuseFailAlloc_4922_, 7, v_infoState_4910_);
lean_ctor_set(v_reuseFailAlloc_4922_, 8, v_snapshotTasks_4911_);
v___x_4918_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; 
v___x_4919_ = lean_st_ref_set(v___y_4898_, v___x_4918_);
v___x_4920_ = lean_box(0);
v_as_x27_4896_ = v_tail_4902_;
v_b_4897_ = v___x_4920_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4925_, lean_object* v_b_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_){
_start:
{
lean_object* v_res_4929_; 
v_res_4929_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4925_, v_b_4926_, v___y_4927_);
lean_dec(v___y_4927_);
lean_dec(v_as_x27_4925_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4930_, uint8_t v_logCompileErrors_4931_, uint8_t v_markMeta_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
uint8_t v___x_4936_; lean_object* v___x_4937_; 
v___x_4936_ = 0;
lean_inc(v_decl_4930_);
v___x_4937_ = l_Lean_addDecl(v_decl_4930_, v___x_4936_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4937_) == 0)
{
lean_dec_ref_known(v___x_4937_, 1);
if (v_markMeta_4932_ == 0)
{
lean_object* v___x_4938_; 
v___x_4938_ = l_Lean_compileDecl(v_decl_4930_, v_logCompileErrors_4931_, v_a_4933_, v_a_4934_);
return v___x_4938_;
}
else
{
lean_object* v___x_4939_; lean_object* v___x_4940_; lean_object* v___x_4941_; lean_object* v___x_4942_; 
lean_inc(v_decl_4930_);
v___x_4939_ = l_Lean_Declaration_getNames(v_decl_4930_);
v___x_4940_ = lean_box(0);
v___x_4941_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4939_, v___x_4940_, v_a_4934_);
lean_dec(v___x_4939_);
lean_dec_ref(v___x_4941_);
v___x_4942_ = l_Lean_compileDecl(v_decl_4930_, v_logCompileErrors_4931_, v_a_4933_, v_a_4934_);
return v___x_4942_;
}
}
else
{
lean_dec(v_decl_4930_);
return v___x_4937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4943_, lean_object* v_logCompileErrors_4944_, lean_object* v_markMeta_4945_, lean_object* v_a_4946_, lean_object* v_a_4947_, lean_object* v_a_4948_){
_start:
{
uint8_t v_logCompileErrors_boxed_4949_; uint8_t v_markMeta_boxed_4950_; lean_object* v_res_4951_; 
v_logCompileErrors_boxed_4949_ = lean_unbox(v_logCompileErrors_4944_);
v_markMeta_boxed_4950_ = lean_unbox(v_markMeta_4945_);
v_res_4951_ = l_Lean_addAndCompile(v_decl_4943_, v_logCompileErrors_boxed_4949_, v_markMeta_boxed_4950_, v_a_4946_, v_a_4947_);
lean_dec(v_a_4947_);
lean_dec_ref(v_a_4946_);
return v_res_4951_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4952_, lean_object* v_as_x27_4953_, lean_object* v_b_4954_, lean_object* v_a_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_){
_start:
{
lean_object* v___x_4959_; 
v___x_4959_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4953_, v_b_4954_, v___y_4957_);
return v___x_4959_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4960_, lean_object* v_as_x27_4961_, lean_object* v_b_4962_, lean_object* v_a_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4960_, v_as_x27_4961_, v_b_4962_, v_a_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec(v_as_x27_4961_);
lean_dec(v_as_4960_);
return v_res_4967_;
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
