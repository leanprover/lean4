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
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
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
uint8_t v_suppressElabErrors_boxed_418_; uint8_t v___y_14975__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_suppressElabErrors_boxed_418_ = lean_unbox(v_suppressElabErrors_415_);
v___y_14975__boxed_419_ = lean_unbox(v___y_416_);
v_res_420_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_418_, v___y_14975__boxed_419_, v_x_417_);
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
lean_object* v___y_468_; lean_object* v___y_469_; lean_object* v___y_470_; uint8_t v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; uint8_t v___y_474_; lean_object* v___y_475_; lean_object* v___y_476_; lean_object* v___y_505_; lean_object* v___y_506_; lean_object* v___y_507_; uint8_t v___y_508_; uint8_t v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v___y_512_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; lean_object* v___y_534_; uint8_t v___y_535_; uint8_t v___y_536_; lean_object* v___y_537_; lean_object* v___y_541_; lean_object* v___y_542_; lean_object* v___y_543_; uint8_t v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; uint8_t v___y_547_; uint8_t v___x_552_; lean_object* v___y_554_; lean_object* v___y_555_; lean_object* v___y_556_; lean_object* v___y_557_; uint8_t v___y_558_; uint8_t v___y_559_; uint8_t v___y_560_; uint8_t v___y_562_; uint8_t v___x_578_; 
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
lean_ctor_set(v___x_494_, 1, v___y_470_);
lean_inc_ref(v___y_468_);
lean_inc_ref(v___y_473_);
v___x_495_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_495_, 0, v___y_473_);
lean_ctor_set(v___x_495_, 1, v___y_472_);
lean_ctor_set(v___x_495_, 2, v___y_469_);
lean_ctor_set(v___x_495_, 3, v___y_468_);
lean_ctor_set(v___x_495_, 4, v___x_494_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5, v___y_474_);
lean_ctor_set_uint8(v___x_495_, sizeof(void*)*5 + 1, v___y_471_);
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
lean_inc_ref_n(v___y_506_, 2);
v___x_519_ = l_Lean_FileMap_toPosition(v___y_506_, v___y_507_);
lean_dec(v___y_507_);
v___x_520_ = l_Lean_FileMap_toPosition(v___y_506_, v___y_512_);
lean_dec(v___y_512_);
v___x_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_521_, 0, v___x_520_);
v___x_522_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_509_ == 0)
{
lean_del_object(v___x_517_);
lean_dec_ref(v___y_505_);
v___y_468_ = v___x_522_;
v___y_469_ = v___x_521_;
v___y_470_ = v_a_515_;
v___y_471_ = v___y_508_;
v___y_472_ = v___x_519_;
v___y_473_ = v___y_510_;
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
v___y_469_ = v___x_521_;
v___y_470_ = v_a_515_;
v___y_471_ = v___y_508_;
v___y_472_ = v___x_519_;
v___y_473_ = v___y_510_;
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
v___x_538_ = l_Lean_Syntax_getTailPos_x3f(v___y_532_, v___y_536_);
lean_dec(v___y_532_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_inc(v___y_537_);
v___y_505_ = v___y_530_;
v___y_506_ = v___y_531_;
v___y_507_ = v___y_537_;
v___y_508_ = v___y_533_;
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
v___y_507_ = v___y_537_;
v___y_508_ = v___y_533_;
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
v_ref_548_ = l_Lean_replaceRef(v_ref_460_, v___y_543_);
v___x_549_ = l_Lean_Syntax_getPos_x3f(v_ref_548_, v___y_546_);
if (lean_obj_tag(v___x_549_) == 0)
{
lean_object* v___x_550_; 
v___x_550_ = lean_unsigned_to_nat(0u);
v___y_530_ = v___y_541_;
v___y_531_ = v___y_542_;
v___y_532_ = v_ref_548_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_545_;
v___y_535_ = v___y_544_;
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
v___y_531_ = v___y_542_;
v___y_532_ = v_ref_548_;
v___y_533_ = v___y_547_;
v___y_534_ = v___y_545_;
v___y_535_ = v___y_544_;
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
v___y_542_ = v___y_554_;
v___y_543_ = v___y_557_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_556_;
v___y_546_ = v___y_559_;
v___y_547_ = v_severity_462_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___y_555_;
v___y_542_ = v___y_554_;
v___y_543_ = v___y_557_;
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
v___y_554_ = v_fileMap_567_;
v___y_555_ = v___f_571_;
v___y_556_ = v_fileName_566_;
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
v___y_554_ = v_fileMap_567_;
v___y_555_ = v___f_571_;
v___y_556_ = v_fileName_566_;
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
lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v_nbuckets_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1133_ = lean_array_get_size(v_data_1132_);
v___x_1134_ = lean_unsigned_to_nat(2u);
v_nbuckets_1135_ = lean_nat_mul(v___x_1133_, v___x_1134_);
v___x_1136_ = lean_unsigned_to_nat(0u);
v___x_1137_ = lean_box(0);
v___x_1138_ = lean_mk_array(v_nbuckets_1135_, v___x_1137_);
v___x_1139_ = lean_array_propagate_mark(v_data_1132_, v___x_1138_);
v___x_1140_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1136_, v_data_1132_, v___x_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1141_, lean_object* v_b_1142_, lean_object* v_x_1143_){
_start:
{
if (lean_obj_tag(v_x_1143_) == 0)
{
lean_dec(v_b_1142_);
lean_dec_ref(v_a_1141_);
return v_x_1143_;
}
else
{
lean_object* v_key_1144_; lean_object* v_value_1145_; lean_object* v_tail_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1158_; 
v_key_1144_ = lean_ctor_get(v_x_1143_, 0);
v_value_1145_ = lean_ctor_get(v_x_1143_, 1);
v_tail_1146_ = lean_ctor_get(v_x_1143_, 2);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_x_1143_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1148_ = v_x_1143_;
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_tail_1146_);
lean_inc(v_value_1145_);
lean_inc(v_key_1144_);
lean_dec(v_x_1143_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1158_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; 
v___x_1150_ = lean_expr_eqv(v_key_1144_, v_a_1141_);
if (v___x_1150_ == 0)
{
lean_object* v___x_1151_; lean_object* v___x_1153_; 
v___x_1151_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1141_, v_b_1142_, v_tail_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 2, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_key_1144_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_value_1145_);
lean_ctor_set(v_reuseFailAlloc_1154_, 2, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
return v___x_1153_;
}
}
else
{
lean_object* v___x_1156_; 
lean_dec(v_value_1145_);
lean_dec(v_key_1144_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_b_1142_);
lean_ctor_set(v___x_1148_, 0, v_a_1141_);
v___x_1156_ = v___x_1148_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1141_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_b_1142_);
lean_ctor_set(v_reuseFailAlloc_1157_, 2, v_tail_1146_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1159_, lean_object* v_x_1160_){
_start:
{
if (lean_obj_tag(v_x_1160_) == 0)
{
uint8_t v___x_1161_; 
v___x_1161_ = 0;
return v___x_1161_;
}
else
{
lean_object* v_key_1162_; lean_object* v_tail_1163_; uint8_t v___x_1164_; 
v_key_1162_ = lean_ctor_get(v_x_1160_, 0);
v_tail_1163_ = lean_ctor_get(v_x_1160_, 2);
v___x_1164_ = lean_expr_eqv(v_key_1162_, v_a_1159_);
if (v___x_1164_ == 0)
{
v_x_1160_ = v_tail_1163_;
goto _start;
}
else
{
return v___x_1164_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1166_, lean_object* v_x_1167_){
_start:
{
uint8_t v_res_1168_; lean_object* v_r_1169_; 
v_res_1168_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1166_, v_x_1167_);
lean_dec(v_x_1167_);
lean_dec_ref(v_a_1166_);
v_r_1169_ = lean_box(v_res_1168_);
return v_r_1169_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1170_, lean_object* v_a_1171_, lean_object* v_b_1172_){
_start:
{
lean_object* v_size_1173_; lean_object* v_buckets_1174_; lean_object* v___x_1176_; uint8_t v_isShared_1177_; uint8_t v_isSharedCheck_1217_; 
v_size_1173_ = lean_ctor_get(v_m_1170_, 0);
v_buckets_1174_ = lean_ctor_get(v_m_1170_, 1);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_m_1170_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1176_ = v_m_1170_;
v_isShared_1177_ = v_isSharedCheck_1217_;
goto v_resetjp_1175_;
}
else
{
lean_inc(v_buckets_1174_);
lean_inc(v_size_1173_);
lean_dec(v_m_1170_);
v___x_1176_ = lean_box(0);
v_isShared_1177_ = v_isSharedCheck_1217_;
goto v_resetjp_1175_;
}
v_resetjp_1175_:
{
lean_object* v___x_1178_; uint64_t v___x_1179_; uint64_t v___x_1180_; uint64_t v___x_1181_; uint64_t v_fold_1182_; uint64_t v___x_1183_; uint64_t v___x_1184_; uint64_t v___x_1185_; size_t v___x_1186_; size_t v___x_1187_; size_t v___x_1188_; size_t v___x_1189_; size_t v___x_1190_; lean_object* v_bkt_1191_; uint8_t v___x_1192_; 
v___x_1178_ = lean_array_get_size(v_buckets_1174_);
v___x_1179_ = l_Lean_Expr_hash(v_a_1171_);
v___x_1180_ = 32ULL;
v___x_1181_ = lean_uint64_shift_right(v___x_1179_, v___x_1180_);
v_fold_1182_ = lean_uint64_xor(v___x_1179_, v___x_1181_);
v___x_1183_ = 16ULL;
v___x_1184_ = lean_uint64_shift_right(v_fold_1182_, v___x_1183_);
v___x_1185_ = lean_uint64_xor(v_fold_1182_, v___x_1184_);
v___x_1186_ = lean_uint64_to_usize(v___x_1185_);
v___x_1187_ = lean_usize_of_nat(v___x_1178_);
v___x_1188_ = ((size_t)1ULL);
v___x_1189_ = lean_usize_sub(v___x_1187_, v___x_1188_);
v___x_1190_ = lean_usize_land(v___x_1186_, v___x_1189_);
v_bkt_1191_ = lean_array_uget_borrowed(v_buckets_1174_, v___x_1190_);
v___x_1192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1171_, v_bkt_1191_);
if (v___x_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v_size_x27_1194_; lean_object* v___x_1195_; lean_object* v_buckets_x27_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; 
v___x_1193_ = lean_unsigned_to_nat(1u);
v_size_x27_1194_ = lean_nat_add(v_size_1173_, v___x_1193_);
lean_dec(v_size_1173_);
lean_inc(v_bkt_1191_);
v___x_1195_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1195_, 0, v_a_1171_);
lean_ctor_set(v___x_1195_, 1, v_b_1172_);
lean_ctor_set(v___x_1195_, 2, v_bkt_1191_);
v_buckets_x27_1196_ = lean_array_uset(v_buckets_1174_, v___x_1190_, v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(4u);
v___x_1198_ = lean_nat_mul(v_size_x27_1194_, v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(3u);
v___x_1200_ = lean_nat_div(v___x_1198_, v___x_1199_);
lean_dec(v___x_1198_);
v___x_1201_ = lean_array_get_size(v_buckets_x27_1196_);
v___x_1202_ = lean_nat_dec_le(v___x_1200_, v___x_1201_);
lean_dec(v___x_1200_);
if (v___x_1202_ == 0)
{
lean_object* v_val_1203_; lean_object* v___x_1205_; 
v_val_1203_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1196_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_val_1203_);
lean_ctor_set(v___x_1176_, 0, v_size_x27_1194_);
v___x_1205_ = v___x_1176_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v_val_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
else
{
lean_object* v___x_1208_; 
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v_buckets_x27_1196_);
lean_ctor_set(v___x_1176_, 0, v_size_x27_1194_);
v___x_1208_ = v___x_1176_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1209_; 
v_reuseFailAlloc_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1209_, 0, v_size_x27_1194_);
lean_ctor_set(v_reuseFailAlloc_1209_, 1, v_buckets_x27_1196_);
v___x_1208_ = v_reuseFailAlloc_1209_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
return v___x_1208_;
}
}
}
else
{
lean_object* v___x_1210_; lean_object* v_buckets_x27_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1215_; 
lean_inc(v_bkt_1191_);
v___x_1210_ = lean_box(0);
v_buckets_x27_1211_ = lean_array_uset(v_buckets_1174_, v___x_1190_, v___x_1210_);
v___x_1212_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1171_, v_b_1172_, v_bkt_1191_);
v___x_1213_ = lean_array_uset(v_buckets_x27_1211_, v___x_1190_, v___x_1212_);
if (v_isShared_1177_ == 0)
{
lean_ctor_set(v___x_1176_, 1, v___x_1213_);
v___x_1215_ = v___x_1176_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_size_1173_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1218_, lean_object* v_e_1219_, lean_object* v_a_1220_){
_start:
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; 
v___x_1222_ = lean_st_ref_take(v_a_1218_);
v___x_1223_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1222_, v_e_1219_, v_a_1220_);
v___x_1224_ = lean_st_ref_put(v_a_1218_, v___x_1223_);
v___x_1225_ = lean_box(0);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1226_, lean_object* v_e_1227_, lean_object* v_a_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1226_, v_e_1227_, v_a_1228_);
lean_dec(v_a_1226_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1231_, lean_object* v_e_1232_, lean_object* v_a_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
lean_object* v_res_1240_; 
v_res_1240_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1231_, v_e_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v_a_1233_);
return v_res_1240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1241_, lean_object* v_e_1242_, lean_object* v_a_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_a_1251_; lean_object* v___y_1263_; lean_object* v___x_1265_; lean_object* v___x_1266_; 
lean_inc(v_a_1243_);
v___x_1265_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1265_, 0, lean_box(0));
lean_closure_set(v___x_1265_, 1, lean_box(0));
lean_closure_set(v___x_1265_, 2, v_a_1243_);
v___x_1266_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1265_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1266_) == 0)
{
lean_object* v_a_1267_; lean_object* v___x_1269_; uint8_t v_isShared_1270_; uint8_t v_isSharedCheck_1303_; 
v_a_1267_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1303_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1303_ == 0)
{
v___x_1269_ = v___x_1266_;
v_isShared_1270_ = v_isSharedCheck_1303_;
goto v_resetjp_1268_;
}
else
{
lean_inc(v_a_1267_);
lean_dec(v___x_1266_);
v___x_1269_ = lean_box(0);
v_isShared_1270_ = v_isSharedCheck_1303_;
goto v_resetjp_1268_;
}
v_resetjp_1268_:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1267_, v_e_1242_);
lean_dec(v_a_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1272_; 
lean_del_object(v___x_1269_);
lean_inc_ref(v_fn_1241_);
lean_inc(v___y_1248_);
lean_inc_ref(v___y_1247_);
lean_inc(v___y_1246_);
lean_inc_ref(v___y_1245_);
lean_inc(v___y_1244_);
lean_inc_ref(v_e_1242_);
v___x_1272_ = lean_apply_7(v_fn_1241_, v_e_1242_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_, lean_box(0));
if (lean_obj_tag(v___x_1272_) == 0)
{
lean_object* v_a_1273_; uint8_t v___x_1274_; 
v_a_1273_ = lean_ctor_get(v___x_1272_, 0);
lean_inc(v_a_1273_);
lean_dec_ref_known(v___x_1272_, 1);
v___x_1274_ = lean_unbox(v_a_1273_);
lean_dec(v_a_1273_);
if (v___x_1274_ == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref(v_fn_1241_);
v___x_1275_ = lean_box(0);
v_a_1251_ = v___x_1275_;
goto v___jp_1250_;
}
else
{
switch(lean_obj_tag(v_e_1242_))
{
case 7:
{
lean_object* v___x_1276_; lean_object* v___x_1277_; 
v___x_1276_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1276_, 0, v_fn_1241_);
lean_inc_ref(v_e_1242_);
v___x_1277_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1276_, v_e_1242_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1277_;
goto v___jp_1262_;
}
case 6:
{
lean_object* v___x_1278_; lean_object* v___x_1279_; 
v___x_1278_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1278_, 0, v_fn_1241_);
lean_inc_ref(v_e_1242_);
v___x_1279_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1278_, v_e_1242_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1279_;
goto v___jp_1262_;
}
case 8:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1280_, 0, v_fn_1241_);
lean_inc_ref(v_e_1242_);
v___x_1281_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1280_, v_e_1242_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1281_;
goto v___jp_1262_;
}
case 5:
{
lean_object* v_fn_1282_; lean_object* v_arg_1283_; lean_object* v___x_1284_; 
v_fn_1282_ = lean_ctor_get(v_e_1242_, 0);
v_arg_1283_ = lean_ctor_get(v_e_1242_, 1);
lean_inc_ref(v_fn_1282_);
lean_inc_ref(v_fn_1241_);
v___x_1284_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1241_, v_fn_1282_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1284_) == 0)
{
lean_object* v___x_1285_; 
lean_dec_ref_known(v___x_1284_, 1);
lean_inc_ref(v_arg_1283_);
v___x_1285_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1241_, v_arg_1283_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1285_;
goto v___jp_1262_;
}
else
{
lean_dec_ref(v_fn_1241_);
v___y_1263_ = v___x_1284_;
goto v___jp_1262_;
}
}
case 10:
{
lean_object* v_expr_1286_; lean_object* v___x_1287_; 
v_expr_1286_ = lean_ctor_get(v_e_1242_, 1);
lean_inc_ref(v_expr_1286_);
v___x_1287_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1241_, v_expr_1286_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1287_;
goto v___jp_1262_;
}
case 11:
{
lean_object* v_struct_1288_; lean_object* v___x_1289_; 
v_struct_1288_ = lean_ctor_get(v_e_1242_, 2);
lean_inc_ref(v_struct_1288_);
v___x_1289_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1241_, v_struct_1288_, v_a_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
v___y_1263_ = v___x_1289_;
goto v___jp_1262_;
}
default: 
{
lean_object* v___x_1290_; 
lean_dec_ref(v_fn_1241_);
v___x_1290_ = lean_box(0);
v_a_1251_ = v___x_1290_;
goto v___jp_1250_;
}
}
}
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
lean_dec_ref(v_e_1242_);
lean_dec_ref(v_fn_1241_);
v_a_1291_ = lean_ctor_get(v___x_1272_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1272_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1272_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1272_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
else
{
lean_object* v_val_1299_; lean_object* v___x_1301_; 
lean_dec_ref(v_e_1242_);
lean_dec_ref(v_fn_1241_);
v_val_1299_ = lean_ctor_get(v___x_1271_, 0);
lean_inc(v_val_1299_);
lean_dec_ref_known(v___x_1271_, 1);
if (v_isShared_1270_ == 0)
{
lean_ctor_set(v___x_1269_, 0, v_val_1299_);
v___x_1301_ = v___x_1269_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1302_; 
v_reuseFailAlloc_1302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1302_, 0, v_val_1299_);
v___x_1301_ = v_reuseFailAlloc_1302_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
return v___x_1301_;
}
}
}
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec_ref(v_e_1242_);
lean_dec_ref(v_fn_1241_);
v_a_1304_ = lean_ctor_get(v___x_1266_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1266_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1266_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1266_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
v___jp_1250_:
{
lean_object* v___f_1252_; lean_object* v___x_1253_; 
lean_inc(v_a_1243_);
v___f_1252_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1252_, 0, v_a_1243_);
lean_closure_set(v___f_1252_, 1, v_e_1242_);
lean_closure_set(v___f_1252_, 2, v_a_1251_);
v___x_1253_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1252_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1260_ == 0)
{
lean_object* v_unused_1261_; 
v_unused_1261_ = lean_ctor_get(v___x_1253_, 0);
lean_dec(v_unused_1261_);
v___x_1255_ = v___x_1253_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_dec(v___x_1253_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 0, v_a_1251_);
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1251_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
else
{
return v___x_1253_;
}
}
v___jp_1262_:
{
if (lean_obj_tag(v___y_1263_) == 0)
{
lean_object* v_a_1264_; 
v_a_1264_ = lean_ctor_get(v___y_1263_, 0);
lean_inc(v_a_1264_);
lean_dec_ref_known(v___y_1263_, 1);
v_a_1251_ = v_a_1264_;
goto v___jp_1250_;
}
else
{
lean_dec_ref(v_e_1242_);
return v___y_1263_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1312_; lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1312_ = lean_box(0);
v___x_1313_ = lean_unsigned_to_nat(16u);
v___x_1314_ = lean_mk_array(v___x_1313_, v___x_1312_);
return v___x_1314_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; 
v___x_1315_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1316_ = lean_unsigned_to_nat(0u);
v___x_1317_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1317_, 0, v___x_1316_);
lean_ctor_set(v___x_1317_, 1, v___x_1315_);
return v___x_1317_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1319_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1319_, 0, lean_box(0));
lean_closure_set(v___x_1319_, 1, lean_box(0));
lean_closure_set(v___x_1319_, 2, v___x_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1320_, lean_object* v_fn_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v_a_1330_; lean_object* v___x_1331_; 
v___x_1328_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1329_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1328_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc(v_a_1330_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1321_, v_input_1320_, v_a_1330_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_a_1332_);
lean_dec_ref_known(v___x_1331_, 1);
v___x_1333_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1333_, 0, lean_box(0));
lean_closure_set(v___x_1333_, 1, lean_box(0));
lean_closure_set(v___x_1333_, 2, v_a_1330_);
v___x_1334_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1333_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1342_);
v___x_1336_ = v___x_1334_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_dec(v___x_1334_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
lean_ctor_set(v___x_1336_, 0, v_a_1332_);
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1332_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
else
{
lean_dec(v_a_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1343_, lean_object* v_fn_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v_res_1351_; 
v_res_1351_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1343_, v_fn_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1352_, lean_object* v_fn_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___f_1360_; lean_object* v___x_1361_; 
v___f_1360_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1360_, 0, v_fn_1353_);
v___x_1361_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1352_, v___f_1360_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1362_, lean_object* v_fn_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_){
_start:
{
lean_object* v_res_1370_; 
v_res_1370_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1362_, v_fn_1363_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
lean_dec(v___y_1368_);
lean_dec_ref(v___y_1367_);
lean_dec(v___y_1366_);
lean_dec_ref(v___y_1365_);
lean_dec(v___y_1364_);
return v_res_1370_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1371_, lean_object* v_x_1372_, lean_object* v_x_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
if (lean_obj_tag(v_x_1373_) == 0)
{
lean_object* v___x_1380_; 
lean_dec_ref(v_fn_1371_);
v___x_1380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1380_, 0, v_x_1372_);
return v___x_1380_;
}
else
{
lean_object* v_head_1381_; lean_object* v_tail_1382_; lean_object* v_type_1383_; lean_object* v___x_1384_; 
v_head_1381_ = lean_ctor_get(v_x_1373_, 0);
lean_inc(v_head_1381_);
v_tail_1382_ = lean_ctor_get(v_x_1373_, 1);
lean_inc(v_tail_1382_);
lean_dec_ref_known(v_x_1373_, 2);
v_type_1383_ = lean_ctor_get(v_head_1381_, 1);
lean_inc_ref(v_type_1383_);
lean_dec(v_head_1381_);
lean_inc_ref(v_fn_1371_);
v___x_1384_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1383_, v_fn_1371_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_, v___y_1378_);
if (lean_obj_tag(v___x_1384_) == 0)
{
lean_object* v_a_1385_; 
v_a_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc(v_a_1385_);
lean_dec_ref_known(v___x_1384_, 1);
v_x_1372_ = v_a_1385_;
v_x_1373_ = v_tail_1382_;
goto _start;
}
else
{
lean_dec(v_tail_1382_);
lean_dec_ref(v_fn_1371_);
return v___x_1384_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1387_, v_x_1388_, v_x_1389_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1397_, lean_object* v_x_1398_, lean_object* v_x_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_){
_start:
{
if (lean_obj_tag(v_x_1399_) == 0)
{
lean_object* v___x_1406_; 
lean_dec_ref(v_fn_1397_);
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v_x_1398_);
return v___x_1406_;
}
else
{
lean_object* v_head_1407_; lean_object* v_tail_1408_; lean_object* v___y_1410_; lean_object* v_type_1413_; lean_object* v_ctors_1414_; lean_object* v___x_1415_; 
v_head_1407_ = lean_ctor_get(v_x_1399_, 0);
lean_inc(v_head_1407_);
v_tail_1408_ = lean_ctor_get(v_x_1399_, 1);
lean_inc(v_tail_1408_);
lean_dec_ref_known(v_x_1399_, 2);
v_type_1413_ = lean_ctor_get(v_head_1407_, 1);
lean_inc_ref(v_type_1413_);
v_ctors_1414_ = lean_ctor_get(v_head_1407_, 2);
lean_inc(v_ctors_1414_);
lean_dec(v_head_1407_);
lean_inc_ref(v_fn_1397_);
v___x_1415_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1413_, v_fn_1397_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref_known(v___x_1415_, 1);
lean_inc_ref(v_fn_1397_);
v___x_1417_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1397_, v_a_1416_, v_ctors_1414_, v___y_1400_, v___y_1401_, v___y_1402_, v___y_1403_, v___y_1404_);
v___y_1410_ = v___x_1417_;
goto v___jp_1409_;
}
else
{
lean_dec(v_ctors_1414_);
v___y_1410_ = v___x_1415_;
goto v___jp_1409_;
}
v___jp_1409_:
{
if (lean_obj_tag(v___y_1410_) == 0)
{
lean_object* v_a_1411_; 
v_a_1411_ = lean_ctor_get(v___y_1410_, 0);
lean_inc(v_a_1411_);
lean_dec_ref_known(v___y_1410_, 1);
v_x_1398_ = v_a_1411_;
v_x_1399_ = v_tail_1408_;
goto _start;
}
else
{
lean_dec(v_tail_1408_);
lean_dec_ref(v_fn_1397_);
return v___y_1410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1418_, lean_object* v_x_1419_, lean_object* v_x_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_, lean_object* v___y_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_){
_start:
{
lean_object* v_res_1427_; 
v_res_1427_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1418_, v_x_1419_, v_x_1420_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
lean_dec(v___y_1423_);
lean_dec_ref(v___y_1422_);
lean_dec(v___y_1421_);
return v_res_1427_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1428_, lean_object* v_x_1429_, lean_object* v_x_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 0)
{
lean_object* v___x_1437_; 
lean_dec_ref(v_fn_1428_);
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_x_1429_);
return v___x_1437_;
}
else
{
lean_object* v_head_1438_; lean_object* v_tail_1439_; lean_object* v___y_1441_; lean_object* v_toConstantVal_1444_; lean_object* v_value_1445_; lean_object* v_type_1446_; lean_object* v___x_1447_; 
v_head_1438_ = lean_ctor_get(v_x_1430_, 0);
lean_inc(v_head_1438_);
v_tail_1439_ = lean_ctor_get(v_x_1430_, 1);
lean_inc(v_tail_1439_);
lean_dec_ref_known(v_x_1430_, 2);
v_toConstantVal_1444_ = lean_ctor_get(v_head_1438_, 0);
lean_inc_ref(v_toConstantVal_1444_);
v_value_1445_ = lean_ctor_get(v_head_1438_, 1);
lean_inc_ref(v_value_1445_);
lean_dec(v_head_1438_);
v_type_1446_ = lean_ctor_get(v_toConstantVal_1444_, 2);
lean_inc_ref(v_type_1446_);
lean_dec_ref(v_toConstantVal_1444_);
lean_inc_ref(v_fn_1428_);
v___x_1447_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1446_, v_fn_1428_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
if (lean_obj_tag(v___x_1447_) == 0)
{
lean_object* v___x_1448_; 
lean_dec_ref_known(v___x_1447_, 1);
lean_inc_ref(v_fn_1428_);
v___x_1448_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1445_, v_fn_1428_, v___y_1431_, v___y_1432_, v___y_1433_, v___y_1434_, v___y_1435_);
v___y_1441_ = v___x_1448_;
goto v___jp_1440_;
}
else
{
lean_dec_ref(v_value_1445_);
v___y_1441_ = v___x_1447_;
goto v___jp_1440_;
}
v___jp_1440_:
{
if (lean_obj_tag(v___y_1441_) == 0)
{
lean_object* v_a_1442_; 
v_a_1442_ = lean_ctor_get(v___y_1441_, 0);
lean_inc(v_a_1442_);
lean_dec_ref_known(v___y_1441_, 1);
v_x_1429_ = v_a_1442_;
v_x_1430_ = v_tail_1439_;
goto _start;
}
else
{
lean_dec(v_tail_1439_);
lean_dec_ref(v_fn_1428_);
return v___y_1441_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1449_, lean_object* v_x_1450_, lean_object* v_x_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_){
_start:
{
lean_object* v_res_1458_; 
v_res_1458_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1449_, v_x_1450_, v_x_1451_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
lean_dec(v___y_1456_);
lean_dec_ref(v___y_1455_);
lean_dec(v___y_1454_);
lean_dec_ref(v___y_1453_);
lean_dec(v___y_1452_);
return v_res_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1459_, lean_object* v_d_1460_, lean_object* v_a_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
switch(lean_obj_tag(v_d_1460_))
{
case 0:
{
lean_object* v_val_1468_; lean_object* v_toConstantVal_1469_; lean_object* v_type_1470_; lean_object* v___x_1471_; 
v_val_1468_ = lean_ctor_get(v_d_1460_, 0);
lean_inc_ref(v_val_1468_);
lean_dec_ref_known(v_d_1460_, 1);
v_toConstantVal_1469_ = lean_ctor_get(v_val_1468_, 0);
lean_inc_ref(v_toConstantVal_1469_);
lean_dec_ref(v_val_1468_);
v_type_1470_ = lean_ctor_get(v_toConstantVal_1469_, 2);
lean_inc_ref(v_type_1470_);
lean_dec_ref(v_toConstantVal_1469_);
v___x_1471_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1470_, v_fn_1459_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1471_;
}
case 4:
{
lean_object* v___x_1472_; 
lean_dec_ref(v_fn_1459_);
v___x_1472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1472_, 0, v_a_1461_);
return v___x_1472_;
}
case 5:
{
lean_object* v_defns_1473_; lean_object* v___x_1474_; 
v_defns_1473_ = lean_ctor_get(v_d_1460_, 0);
lean_inc(v_defns_1473_);
lean_dec_ref_known(v_d_1460_, 1);
v___x_1474_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1459_, v_a_1461_, v_defns_1473_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1474_;
}
case 6:
{
lean_object* v_types_1475_; lean_object* v___x_1476_; 
v_types_1475_ = lean_ctor_get(v_d_1460_, 2);
lean_inc(v_types_1475_);
lean_dec_ref_known(v_d_1460_, 3);
v___x_1476_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1459_, v_a_1461_, v_types_1475_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1476_;
}
default: 
{
lean_object* v_val_1477_; lean_object* v_toConstantVal_1478_; lean_object* v_value_1479_; lean_object* v_type_1480_; lean_object* v___x_1481_; 
v_val_1477_ = lean_ctor_get(v_d_1460_, 0);
lean_inc_ref(v_val_1477_);
lean_dec(v_d_1460_);
v_toConstantVal_1478_ = lean_ctor_get(v_val_1477_, 0);
lean_inc_ref(v_toConstantVal_1478_);
v_value_1479_ = lean_ctor_get(v_val_1477_, 1);
lean_inc_ref(v_value_1479_);
lean_dec_ref(v_val_1477_);
v_type_1480_ = lean_ctor_get(v_toConstantVal_1478_, 2);
lean_inc_ref(v_type_1480_);
lean_dec_ref(v_toConstantVal_1478_);
lean_inc_ref(v_fn_1459_);
v___x_1481_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1480_, v_fn_1459_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v___x_1482_; 
lean_dec_ref_known(v___x_1481_, 1);
v___x_1482_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1479_, v_fn_1459_, v___y_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
return v___x_1482_;
}
else
{
lean_dec_ref(v_value_1479_);
lean_dec_ref(v_fn_1459_);
return v___x_1481_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1483_, lean_object* v_d_1484_, lean_object* v_a_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_, lean_object* v___y_1490_, lean_object* v___y_1491_){
_start:
{
lean_object* v_res_1492_; 
v_res_1492_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1483_, v_d_1484_, v_a_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_, v___y_1490_);
lean_dec(v___y_1490_);
lean_dec_ref(v___y_1489_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1493_, lean_object* v_fn_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_box(0);
v___x_1502_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1494_, v_decl_1493_, v___x_1501_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
return v___x_1502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1503_, lean_object* v_fn_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_){
_start:
{
lean_object* v_res_1511_; 
v_res_1511_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1503_, v_fn_1504_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_, v___y_1509_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
return v_res_1511_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1512_; 
v___x_1512_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1512_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1513_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1513_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1515_ = lean_box(1);
v___x_1516_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1517_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1517_);
lean_ctor_set(v___x_1518_, 1, v___x_1516_);
lean_ctor_set(v___x_1518_, 2, v___x_1515_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1522_ = lean_unsigned_to_nat(0u);
v___x_1523_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1522_);
lean_ctor_set(v___x_1523_, 2, v___x_1522_);
lean_ctor_set(v___x_1523_, 3, v___x_1522_);
lean_ctor_set(v___x_1523_, 4, v___x_1521_);
lean_ctor_set(v___x_1523_, 5, v___x_1521_);
lean_ctor_set(v___x_1523_, 6, v___x_1521_);
lean_ctor_set(v___x_1523_, 7, v___x_1521_);
lean_ctor_set(v___x_1523_, 8, v___x_1521_);
lean_ctor_set(v___x_1523_, 9, v___x_1521_);
lean_ctor_set(v___x_1523_, 10, v___x_1521_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; 
v___x_1524_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1525_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1525_, 0, v___x_1524_);
lean_ctor_set(v___x_1525_, 1, v___x_1524_);
lean_ctor_set(v___x_1525_, 2, v___x_1524_);
lean_ctor_set(v___x_1525_, 3, v___x_1524_);
lean_ctor_set(v___x_1525_, 4, v___x_1524_);
lean_ctor_set(v___x_1525_, 5, v___x_1524_);
return v___x_1525_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1526_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1526_);
lean_ctor_set(v___x_1527_, 2, v___x_1526_);
lean_ctor_set(v___x_1527_, 3, v___x_1526_);
lean_ctor_set(v___x_1527_, 4, v___x_1526_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1528_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1529_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1530_ = lean_box(1);
v___x_1531_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1532_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1533_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1533_, 0, v___x_1532_);
lean_ctor_set(v___x_1533_, 1, v___x_1531_);
lean_ctor_set(v___x_1533_, 2, v___x_1530_);
lean_ctor_set(v___x_1533_, 3, v___x_1529_);
lean_ctor_set(v___x_1533_, 4, v___x_1528_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1540_ = l_Lean_stringToMessageData(v___x_1539_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1543_ = l_Lean_stringToMessageData(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1547_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1548_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1549_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1549_, 0, v___x_1548_);
lean_ctor_set(v___x_1549_, 1, v___x_1547_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_){
_start:
{
lean_object* v_toCold_1557_; lean_object* v_options_1558_; lean_object* v___x_1559_; uint8_t v___x_1560_; 
v_toCold_1557_ = lean_ctor_get(v_a_1554_, 0);
v_options_1558_ = lean_ctor_get(v_toCold_1557_, 2);
v___x_1559_ = l_Lean_warn_sorry;
v___x_1560_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1558_, v___x_1559_);
if (v___x_1560_ == 0)
{
lean_object* v___x_1561_; lean_object* v___x_1562_; 
lean_dec(v_decl_1553_);
v___x_1561_ = lean_box(0);
v___x_1562_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1562_, 0, v___x_1561_);
return v___x_1562_;
}
else
{
lean_object* v___x_1563_; lean_object* v_messages_1567_; uint8_t v___x_1568_; 
v___x_1563_ = lean_st_ref_get(v_a_1555_);
v_messages_1567_ = lean_ctor_get(v___x_1563_, 6);
lean_inc_ref(v_messages_1567_);
lean_dec(v___x_1563_);
v___x_1568_ = l_Lean_MessageLog_hasErrors(v_messages_1567_);
lean_dec_ref(v_messages_1567_);
if (v___x_1568_ == 0)
{
if (v___x_1560_ == 0)
{
lean_dec(v_decl_1553_);
goto v___jp_1564_;
}
else
{
uint8_t v___x_1569_; 
v___x_1569_ = l_Lean_Declaration_hasSorry(v_decl_1553_);
if (v___x_1569_ == 0)
{
lean_dec(v_decl_1553_);
goto v___jp_1564_;
}
else
{
lean_object* v___x_1570_; uint8_t v___x_1571_; uint8_t v___x_1572_; uint8_t v___x_1573_; lean_object* v___x_1574_; uint64_t v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___x_1586_; 
v___x_1570_ = lean_box(1);
v___x_1571_ = 1;
v___x_1572_ = 0;
v___x_1573_ = 2;
v___x_1574_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1574_, 0, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 1, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 2, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 3, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 4, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 5, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 6, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 7, v___x_1568_);
lean_ctor_set_uint8(v___x_1574_, 8, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 9, v___x_1571_);
lean_ctor_set_uint8(v___x_1574_, 10, v___x_1572_);
lean_ctor_set_uint8(v___x_1574_, 11, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 12, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 13, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 14, v___x_1573_);
lean_ctor_set_uint8(v___x_1574_, 15, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 16, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 17, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 18, v___x_1569_);
lean_ctor_set_uint8(v___x_1574_, 19, v___x_1568_);
v___x_1575_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1574_);
v___x_1576_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set_uint64(v___x_1576_, sizeof(void*)*1, v___x_1575_);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1579_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1580_ = lean_box(0);
v___x_1581_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1581_, 0, v___x_1576_);
lean_ctor_set(v___x_1581_, 1, v___x_1570_);
lean_ctor_set(v___x_1581_, 2, v___x_1578_);
lean_ctor_set(v___x_1581_, 3, v___x_1579_);
lean_ctor_set(v___x_1581_, 4, v___x_1580_);
lean_ctor_set(v___x_1581_, 5, v___x_1577_);
lean_ctor_set(v___x_1581_, 6, v___x_1580_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*7, v___x_1568_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*7 + 1, v___x_1568_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*7 + 2, v___x_1568_);
lean_ctor_set_uint8(v___x_1581_, sizeof(void*)*7 + 3, v___x_1560_);
v___x_1582_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1583_ = lean_st_mk_ref(v___x_1582_);
v___x_1584_ = lean_st_mk_ref(v___x_1579_);
v___f_1585_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1586_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1553_, v___f_1585_, v___x_1584_, v___x_1581_, v___x_1583_, v_a_1554_, v_a_1555_);
lean_dec_ref_known(v___x_1581_, 7);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_val_1590_; lean_object* v___x_1612_; size_t v_sz_1613_; size_t v___x_1614_; lean_object* v___x_1615_; lean_object* v_fst_1616_; 
lean_dec_ref_known(v___x_1586_, 1);
v___x_1587_ = lean_st_ref_get(v___x_1584_);
lean_dec(v___x_1584_);
v___x_1588_ = lean_st_ref_get(v___x_1583_);
lean_dec(v___x_1583_);
lean_dec(v___x_1588_);
v___x_1612_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1613_ = lean_array_size(v___x_1587_);
v___x_1614_ = ((size_t)0ULL);
v___x_1615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1587_, v_sz_1613_, v___x_1614_, v___x_1612_);
v_fst_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_fst_1616_);
lean_dec_ref(v___x_1615_);
if (lean_obj_tag(v_fst_1616_) == 0)
{
goto v___jp_1606_;
}
else
{
lean_object* v_val_1617_; 
v_val_1617_ = lean_ctor_get(v_fst_1616_, 0);
lean_inc(v_val_1617_);
lean_dec_ref_known(v_fst_1616_, 1);
if (lean_obj_tag(v_val_1617_) == 0)
{
goto v___jp_1606_;
}
else
{
lean_object* v_val_1618_; 
lean_dec(v___x_1587_);
v_val_1618_ = lean_ctor_get(v_val_1617_, 0);
lean_inc(v_val_1618_);
lean_dec_ref_known(v_val_1617_, 1);
v_val_1590_ = v_val_1618_;
goto v___jp_1589_;
}
}
v___jp_1589_:
{
lean_object* v_snd_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1604_; 
v_snd_1591_ = lean_ctor_get(v_val_1590_, 1);
v_isSharedCheck_1604_ = !lean_is_exclusive(v_val_1590_);
if (v_isSharedCheck_1604_ == 0)
{
lean_object* v_unused_1605_; 
v_unused_1605_ = lean_ctor_get(v_val_1590_, 0);
lean_dec(v_unused_1605_);
v___x_1593_ = v_val_1590_;
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
else
{
lean_inc(v_snd_1591_);
lean_dec(v_val_1590_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1604_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1598_; 
v___x_1595_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1596_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1594_ == 0)
{
lean_ctor_set_tag(v___x_1593_, 7);
lean_ctor_set(v___x_1593_, 0, v___x_1596_);
v___x_1598_ = v___x_1593_;
goto v_reusejp_1597_;
}
else
{
lean_object* v_reuseFailAlloc_1603_; 
v_reuseFailAlloc_1603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1603_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1603_, 1, v_snd_1591_);
v___x_1598_ = v_reuseFailAlloc_1603_;
goto v_reusejp_1597_;
}
v_reusejp_1597_:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1599_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1600_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1600_, 0, v___x_1598_);
lean_ctor_set(v___x_1600_, 1, v___x_1599_);
v___x_1601_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1601_, 0, v___x_1595_);
lean_ctor_set(v___x_1601_, 1, v___x_1600_);
v___x_1602_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1601_, v_a_1554_, v_a_1555_);
return v___x_1602_;
}
}
}
v___jp_1606_:
{
lean_object* v___x_1607_; uint8_t v___x_1608_; 
v___x_1607_ = lean_array_get_size(v___x_1587_);
v___x_1608_ = lean_nat_dec_lt(v___x_1577_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_object* v___x_1609_; lean_object* v___x_1610_; 
lean_dec(v___x_1587_);
v___x_1609_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1610_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1609_, v_a_1554_, v_a_1555_);
return v___x_1610_;
}
else
{
lean_object* v___x_1611_; 
v___x_1611_ = lean_array_fget(v___x_1587_, v___x_1577_);
lean_dec(v___x_1587_);
v_val_1590_ = v___x_1611_;
goto v___jp_1589_;
}
}
}
else
{
lean_dec(v___x_1584_);
lean_dec(v___x_1583_);
return v___x_1586_;
}
}
}
}
else
{
lean_dec(v_decl_1553_);
goto v___jp_1564_;
}
v___jp_1564_:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_box(0);
v___x_1566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
return v___x_1566_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1619_, lean_object* v_a_1620_, lean_object* v_a_1621_, lean_object* v_a_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_warnIfUsesSorry(v_decl_1619_, v_a_1620_, v_a_1621_);
lean_dec(v_a_1621_);
lean_dec_ref(v_a_1620_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1624_, lean_object* v_m_1625_, lean_object* v_a_1626_){
_start:
{
lean_object* v___x_1627_; 
v___x_1627_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1625_, v_a_1626_);
return v___x_1627_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1628_, lean_object* v_m_1629_, lean_object* v_a_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1628_, v_m_1629_, v_a_1630_);
lean_dec_ref(v_a_1630_);
lean_dec_ref(v_m_1629_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1632_, lean_object* v_m_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1633_, v_a_1634_, v_b_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1638_, v_x_1639_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1641_, lean_object* v_a_1642_, lean_object* v_x_1643_){
_start:
{
lean_object* v_res_1644_; 
v_res_1644_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1641_, v_a_1642_, v_x_1643_);
lean_dec(v_x_1643_);
lean_dec_ref(v_a_1642_);
return v_res_1644_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_x_1647_){
_start:
{
uint8_t v___x_1648_; 
v___x_1648_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1646_, v_x_1647_);
return v___x_1648_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1649_, lean_object* v_a_1650_, lean_object* v_x_1651_){
_start:
{
uint8_t v_res_1652_; lean_object* v_r_1653_; 
v_res_1652_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1649_, v_a_1650_, v_x_1651_);
lean_dec(v_x_1651_);
lean_dec_ref(v_a_1650_);
v_r_1653_ = lean_box(v_res_1652_);
return v_r_1653_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1654_, lean_object* v_data_1655_){
_start:
{
lean_object* v___x_1656_; 
v___x_1656_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1655_);
return v___x_1656_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1657_, lean_object* v_a_1658_, lean_object* v_b_1659_, lean_object* v_x_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1658_, v_b_1659_, v_x_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1662_, lean_object* v_name_1663_, uint8_t v_bi_1664_, lean_object* v_type_1665_, lean_object* v_k_1666_, uint8_t v_kind_1667_, lean_object* v___y_1668_, lean_object* v___y_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_){
_start:
{
lean_object* v___x_1675_; 
v___x_1675_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1663_, v_bi_1664_, v_type_1665_, v_k_1666_, v_kind_1667_, v___y_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_);
return v___x_1675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1676_, lean_object* v_name_1677_, lean_object* v_bi_1678_, lean_object* v_type_1679_, lean_object* v_k_1680_, lean_object* v_kind_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
uint8_t v_bi_boxed_1689_; uint8_t v_kind_boxed_1690_; lean_object* v_res_1691_; 
v_bi_boxed_1689_ = lean_unbox(v_bi_1678_);
v_kind_boxed_1690_ = lean_unbox(v_kind_1681_);
v_res_1691_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1676_, v_name_1677_, v_bi_boxed_1689_, v_type_1679_, v_k_1680_, v_kind_boxed_1690_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_, v___y_1687_);
lean_dec(v___y_1687_);
lean_dec_ref(v___y_1686_);
lean_dec(v___y_1685_);
lean_dec_ref(v___y_1684_);
lean_dec(v___y_1683_);
lean_dec(v___y_1682_);
return v_res_1691_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1692_, lean_object* v_name_1693_, lean_object* v_type_1694_, lean_object* v_val_1695_, lean_object* v_k_1696_, uint8_t v_nondep_1697_, uint8_t v_kind_1698_, lean_object* v___y_1699_, lean_object* v___y_1700_, lean_object* v___y_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_){
_start:
{
lean_object* v___x_1706_; 
v___x_1706_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1693_, v_type_1694_, v_val_1695_, v_k_1696_, v_nondep_1697_, v_kind_1698_, v___y_1699_, v___y_1700_, v___y_1701_, v___y_1702_, v___y_1703_, v___y_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1707_, lean_object* v_name_1708_, lean_object* v_type_1709_, lean_object* v_val_1710_, lean_object* v_k_1711_, lean_object* v_nondep_1712_, lean_object* v_kind_1713_, lean_object* v___y_1714_, lean_object* v___y_1715_, lean_object* v___y_1716_, lean_object* v___y_1717_, lean_object* v___y_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_){
_start:
{
uint8_t v_nondep_boxed_1721_; uint8_t v_kind_boxed_1722_; lean_object* v_res_1723_; 
v_nondep_boxed_1721_ = lean_unbox(v_nondep_1712_);
v_kind_boxed_1722_ = lean_unbox(v_kind_1713_);
v_res_1723_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1707_, v_name_1708_, v_type_1709_, v_val_1710_, v_k_1711_, v_nondep_boxed_1721_, v_kind_boxed_1722_, v___y_1714_, v___y_1715_, v___y_1716_, v___y_1717_, v___y_1718_, v___y_1719_);
lean_dec(v___y_1719_);
lean_dec_ref(v___y_1718_);
lean_dec(v___y_1717_);
lean_dec_ref(v___y_1716_);
lean_dec(v___y_1715_);
lean_dec(v___y_1714_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1724_, lean_object* v_i_1725_, lean_object* v_source_1726_, lean_object* v_target_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1725_, v_source_1726_, v_target_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1729_, lean_object* v_x_1730_, lean_object* v_x_1731_){
_start:
{
lean_object* v___x_1732_; 
v___x_1732_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1730_, v_x_1731_);
return v___x_1732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1782_; uint8_t v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1782_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1783_ = 0;
v___x_1784_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1785_ = l_Lean_registerTraceClass(v___x_1782_, v___x_1783_, v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1787_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1788_, lean_object* v___y_1789_){
_start:
{
lean_object* v___x_1791_; lean_object* v_nextMacroScope_1792_; lean_object* v_ngen_1793_; lean_object* v_auxDeclNGen_1794_; lean_object* v_traceState_1795_; lean_object* v_messages_1796_; lean_object* v_infoState_1797_; lean_object* v_snapshotTasks_1798_; lean_object* v___x_1800_; uint8_t v_isShared_1801_; uint8_t v_isSharedCheck_1809_; 
v___x_1791_ = lean_st_ref_take(v___y_1789_);
v_nextMacroScope_1792_ = lean_ctor_get(v___x_1791_, 1);
v_ngen_1793_ = lean_ctor_get(v___x_1791_, 2);
v_auxDeclNGen_1794_ = lean_ctor_get(v___x_1791_, 3);
v_traceState_1795_ = lean_ctor_get(v___x_1791_, 4);
v_messages_1796_ = lean_ctor_get(v___x_1791_, 6);
v_infoState_1797_ = lean_ctor_get(v___x_1791_, 7);
v_snapshotTasks_1798_ = lean_ctor_get(v___x_1791_, 8);
v_isSharedCheck_1809_ = !lean_is_exclusive(v___x_1791_);
if (v_isSharedCheck_1809_ == 0)
{
lean_object* v_unused_1810_; lean_object* v_unused_1811_; 
v_unused_1810_ = lean_ctor_get(v___x_1791_, 5);
lean_dec(v_unused_1810_);
v_unused_1811_ = lean_ctor_get(v___x_1791_, 0);
lean_dec(v_unused_1811_);
v___x_1800_ = v___x_1791_;
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
else
{
lean_inc(v_snapshotTasks_1798_);
lean_inc(v_infoState_1797_);
lean_inc(v_messages_1796_);
lean_inc(v_traceState_1795_);
lean_inc(v_auxDeclNGen_1794_);
lean_inc(v_ngen_1793_);
lean_inc(v_nextMacroScope_1792_);
lean_dec(v___x_1791_);
v___x_1800_ = lean_box(0);
v_isShared_1801_ = v_isSharedCheck_1809_;
goto v_resetjp_1799_;
}
v_resetjp_1799_:
{
lean_object* v___x_1802_; lean_object* v___x_1804_; 
v___x_1802_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1801_ == 0)
{
lean_ctor_set(v___x_1800_, 5, v___x_1802_);
lean_ctor_set(v___x_1800_, 0, v_env_1788_);
v___x_1804_ = v___x_1800_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1808_; 
v_reuseFailAlloc_1808_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1808_, 0, v_env_1788_);
lean_ctor_set(v_reuseFailAlloc_1808_, 1, v_nextMacroScope_1792_);
lean_ctor_set(v_reuseFailAlloc_1808_, 2, v_ngen_1793_);
lean_ctor_set(v_reuseFailAlloc_1808_, 3, v_auxDeclNGen_1794_);
lean_ctor_set(v_reuseFailAlloc_1808_, 4, v_traceState_1795_);
lean_ctor_set(v_reuseFailAlloc_1808_, 5, v___x_1802_);
lean_ctor_set(v_reuseFailAlloc_1808_, 6, v_messages_1796_);
lean_ctor_set(v_reuseFailAlloc_1808_, 7, v_infoState_1797_);
lean_ctor_set(v_reuseFailAlloc_1808_, 8, v_snapshotTasks_1798_);
v___x_1804_ = v_reuseFailAlloc_1808_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
lean_object* v___x_1805_; lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_st_ref_put(v___y_1789_, v___x_1804_);
v___x_1806_ = lean_box(0);
v___x_1807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
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
lean_object* v___x_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
v___x_1865_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1866_ = lean_ctor_get(v___x_1865_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1865_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1865_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1865_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
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
lean_object* v_toCold_1861_; lean_object* v_options_1862_; lean_object* v___x_1863_; lean_object* v___x_1864_; 
v_toCold_1861_ = lean_ctor_get(v___y_1859_, 0);
v_options_1862_ = lean_ctor_get(v_toCold_1861_, 2);
lean_inc_ref(v_options_1862_);
v___x_1863_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1854_, v_options_1862_);
v___x_1864_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1863_, v___y_1859_, v___y_1860_);
return v___x_1864_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1874_, lean_object* v___y_1875_, lean_object* v___y_1876_, lean_object* v___y_1877_){
_start:
{
lean_object* v_res_1878_; 
v_res_1878_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1874_, v___y_1875_, v___y_1876_);
lean_dec(v___y_1876_);
lean_dec_ref(v___y_1875_);
return v_res_1878_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1879_, lean_object* v___y_1880_, lean_object* v___y_1881_){
_start:
{
if (lean_obj_tag(v_x_1879_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v_x_1879_, 0);
lean_inc(v_a_1883_);
lean_dec_ref_known(v_x_1879_, 1);
v___x_1884_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1883_, v___y_1880_, v___y_1881_);
return v___x_1884_;
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
v_a_1885_ = lean_ctor_get(v_x_1879_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v_x_1879_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v_x_1879_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v_x_1879_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
lean_ctor_set_tag(v___x_1887_, 0);
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1893_, v___y_1894_, v___y_1895_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1897_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = lean_unsigned_to_nat(1u);
v___x_1899_ = l_Lean_Level_ofNat(v___x_1898_);
return v___x_1899_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1900_ = lean_box(0);
v___x_1901_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1900_);
return v___x_1902_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1910_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1911_ = l_Lean_mkConst(v___x_1910_, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; 
v___x_1912_ = lean_unsigned_to_nat(0u);
v___x_1913_ = l_Lean_Level_ofNat(v___x_1912_);
return v___x_1913_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1914_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1915_ = l_Lean_mkSort(v___x_1914_);
return v___x_1915_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1921_ = lean_box(0);
v___x_1922_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1923_ = l_Lean_mkConst(v___x_1922_, v___x_1921_);
return v___x_1923_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1924_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1925_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1926_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1927_ = l_Lean_mkAppB(v___x_1926_, v___x_1925_, v___x_1924_);
return v___x_1927_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1933_, lean_object* v_b_1934_, lean_object* v___y_1935_, lean_object* v___y_1936_){
_start:
{
if (lean_obj_tag(v_as_x27_1933_) == 0)
{
lean_object* v___x_1938_; 
v___x_1938_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1938_, 0, v_b_1934_);
return v___x_1938_;
}
else
{
lean_object* v_head_1939_; lean_object* v_tail_1940_; lean_object* v___x_1941_; lean_object* v_toCold_1942_; lean_object* v_env_1943_; lean_object* v_options_1944_; lean_object* v_cancelTk_x3f_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___y_1949_; uint8_t v___y_1950_; lean_object* v_a_1954_; lean_object* v___x_1957_; lean_object* v___x_1958_; uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; 
lean_dec_ref(v_b_1934_);
v_head_1939_ = lean_ctor_get(v_as_x27_1933_, 0);
v_tail_1940_ = lean_ctor_get(v_as_x27_1933_, 1);
v___x_1941_ = lean_st_ref_get(v___y_1936_);
v_toCold_1942_ = lean_ctor_get(v___y_1935_, 0);
v_env_1943_ = lean_ctor_get(v___x_1941_, 0);
lean_inc_ref(v_env_1943_);
lean_dec(v___x_1941_);
v_options_1944_ = lean_ctor_get(v_toCold_1942_, 2);
v_cancelTk_x3f_1945_ = lean_ctor_get(v_toCold_1942_, 10);
v___x_1946_ = lean_box(0);
v___x_1947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1957_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1939_);
v___x_1958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1958_, 0, v_head_1939_);
lean_ctor_set(v___x_1958_, 1, v___x_1946_);
lean_ctor_set(v___x_1958_, 2, v___x_1957_);
v___x_1959_ = 0;
v___x_1960_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1960_, 0, v___x_1958_);
lean_ctor_set_uint8(v___x_1960_, sizeof(void*)*1, v___x_1959_);
v___x_1961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1961_, 0, v___x_1960_);
v___x_1962_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1943_, v_options_1944_, v___x_1961_, v_cancelTk_x3f_1945_);
lean_dec_ref_known(v___x_1961_, 1);
v___x_1963_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1962_, v___y_1935_, v___y_1936_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; lean_object* v___x_1967_; uint8_t v_isShared_1968_; uint8_t v_isSharedCheck_1973_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1964_, v___y_1936_);
v_isSharedCheck_1973_ = !lean_is_exclusive(v___x_1965_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v___x_1965_, 0);
lean_dec(v_unused_1974_);
v___x_1967_ = v___x_1965_;
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
else
{
lean_dec(v___x_1965_);
v___x_1967_ = lean_box(0);
v_isShared_1968_ = v_isSharedCheck_1973_;
goto v_resetjp_1966_;
}
v_resetjp_1966_:
{
lean_object* v___x_1969_; lean_object* v___x_1971_; 
v___x_1969_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1968_ == 0)
{
lean_ctor_set(v___x_1967_, 0, v___x_1969_);
v___x_1971_ = v___x_1967_;
goto v_reusejp_1970_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v___x_1969_);
v___x_1971_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1970_;
}
v_reusejp_1970_:
{
return v___x_1971_;
}
}
}
else
{
lean_object* v_a_1975_; 
v_a_1975_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1975_);
lean_dec_ref_known(v___x_1963_, 1);
v_a_1954_ = v_a_1975_;
goto v___jp_1953_;
}
v___jp_1948_:
{
if (v___y_1950_ == 0)
{
lean_dec_ref(v___y_1949_);
v_as_x27_1933_ = v_tail_1940_;
v_b_1934_ = v___x_1947_;
goto _start;
}
else
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1952_, 0, v___y_1949_);
return v___x_1952_;
}
}
v___jp_1953_:
{
uint8_t v___x_1955_; 
v___x_1955_ = l_Lean_Exception_isInterrupt(v_a_1954_);
if (v___x_1955_ == 0)
{
uint8_t v___x_1956_; 
lean_inc_ref(v_a_1954_);
v___x_1956_ = l_Lean_Exception_isRuntime(v_a_1954_);
v___y_1949_ = v_a_1954_;
v___y_1950_ = v___x_1956_;
goto v___jp_1948_;
}
else
{
v___y_1949_ = v_a_1954_;
v___y_1950_ = v___x_1955_;
goto v___jp_1948_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1976_, lean_object* v_b_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_, lean_object* v___y_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1976_, v_b_1977_, v___y_1978_, v___y_1979_);
lean_dec(v___y_1979_);
lean_dec_ref(v___y_1978_);
lean_dec(v_as_x27_1976_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_2015_; uint8_t v___y_2016_; lean_object* v_a_2019_; lean_object* v___y_2023_; uint8_t v___y_2024_; lean_object* v_a_2027_; 
switch(lean_obj_tag(v_decl_1982_))
{
case 1:
{
lean_object* v_val_2030_; lean_object* v___x_2031_; lean_object* v_toCold_2032_; lean_object* v_toConstantVal_2033_; lean_object* v_env_2034_; lean_object* v_options_2035_; lean_object* v_cancelTk_x3f_2036_; uint8_t v___x_2037_; lean_object* v___x_2038_; lean_object* v_fallbackDecl_2039_; lean_object* v___x_2040_; lean_object* v___x_2041_; 
v_val_2030_ = lean_ctor_get(v_decl_1982_, 0);
v___x_2031_ = lean_st_ref_get(v_a_1984_);
v_toCold_2032_ = lean_ctor_get(v_a_1983_, 0);
v_toConstantVal_2033_ = lean_ctor_get(v_val_2030_, 0);
v_env_2034_ = lean_ctor_get(v___x_2031_, 0);
lean_inc_ref(v_env_2034_);
lean_dec(v___x_2031_);
v_options_2035_ = lean_ctor_get(v_toCold_2032_, 2);
v_cancelTk_x3f_2036_ = lean_ctor_get(v_toCold_2032_, 10);
v___x_2037_ = 0;
lean_inc_ref(v_toConstantVal_2033_);
v___x_2038_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2038_, 0, v_toConstantVal_2033_);
lean_ctor_set_uint8(v___x_2038_, sizeof(void*)*1, v___x_2037_);
v_fallbackDecl_2039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2039_, 0, v___x_2038_);
v___x_2040_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2034_, v_options_2035_, v_fallbackDecl_2039_, v_cancelTk_x3f_2036_);
lean_dec_ref_known(v_fallbackDecl_2039_, 1);
v___x_2041_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2040_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2051_; 
lean_dec_ref_known(v_decl_1982_, 1);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2042_, v_a_1984_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; 
v_unused_2052_ = lean_ctor_get(v___x_2043_, 0);
lean_dec(v_unused_2052_);
v___x_2045_ = v___x_2043_;
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
else
{
lean_dec(v___x_2043_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2051_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2047_; lean_object* v___x_2049_; 
v___x_2047_ = lean_box(0);
if (v_isShared_2046_ == 0)
{
lean_ctor_set(v___x_2045_, 0, v___x_2047_);
v___x_2049_ = v___x_2045_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2047_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
else
{
lean_object* v_a_2053_; 
v_a_2053_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2053_);
lean_dec_ref_known(v___x_2041_, 1);
v_a_2019_ = v_a_2053_;
goto v___jp_2018_;
}
}
case 2:
{
lean_object* v_val_2054_; lean_object* v___x_2055_; lean_object* v_toCold_2056_; lean_object* v_toConstantVal_2057_; lean_object* v_env_2058_; lean_object* v_options_2059_; lean_object* v_cancelTk_x3f_2060_; uint8_t v___x_2061_; lean_object* v___x_2062_; lean_object* v_fallbackDecl_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v_val_2054_ = lean_ctor_get(v_decl_1982_, 0);
v___x_2055_ = lean_st_ref_get(v_a_1984_);
v_toCold_2056_ = lean_ctor_get(v_a_1983_, 0);
v_toConstantVal_2057_ = lean_ctor_get(v_val_2054_, 0);
v_env_2058_ = lean_ctor_get(v___x_2055_, 0);
lean_inc_ref(v_env_2058_);
lean_dec(v___x_2055_);
v_options_2059_ = lean_ctor_get(v_toCold_2056_, 2);
v_cancelTk_x3f_2060_ = lean_ctor_get(v_toCold_2056_, 10);
v___x_2061_ = 0;
lean_inc_ref(v_toConstantVal_2057_);
v___x_2062_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2062_, 0, v_toConstantVal_2057_);
lean_ctor_set_uint8(v___x_2062_, sizeof(void*)*1, v___x_2061_);
v_fallbackDecl_2063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2063_, 0, v___x_2062_);
v___x_2064_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2058_, v_options_2059_, v_fallbackDecl_2063_, v_cancelTk_x3f_2060_);
lean_dec_ref_known(v_fallbackDecl_2063_, 1);
v___x_2065_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2064_, v_a_1983_, v_a_1984_);
if (lean_obj_tag(v___x_2065_) == 0)
{
lean_object* v_a_2066_; lean_object* v___x_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2075_; 
lean_dec_ref_known(v_decl_1982_, 1);
v_a_2066_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2066_);
lean_dec_ref_known(v___x_2065_, 1);
v___x_2067_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2066_, v_a_1984_);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2067_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v___x_2067_, 0);
lean_dec(v_unused_2076_);
v___x_2069_ = v___x_2067_;
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
else
{
lean_dec(v___x_2067_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2075_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2071_; lean_object* v___x_2073_; 
v___x_2071_ = lean_box(0);
if (v_isShared_2070_ == 0)
{
lean_ctor_set(v___x_2069_, 0, v___x_2071_);
v___x_2073_ = v___x_2069_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v___x_2071_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
else
{
lean_object* v_a_2077_; 
v_a_2077_ = lean_ctor_get(v___x_2065_, 0);
lean_inc(v_a_2077_);
lean_dec_ref_known(v___x_2065_, 1);
v_a_2027_ = v_a_2077_;
goto v___jp_2026_;
}
}
default: 
{
v___y_1987_ = v_a_1983_;
v___y_1988_ = v_a_1984_;
goto v___jp_1986_;
}
}
v___jp_1986_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = l_Lean_Declaration_getNames(v_decl_1982_);
v___x_1990_ = lean_box(0);
v___x_1991_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1992_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1989_, v___x_1991_, v___y_1987_, v___y_1988_);
lean_dec(v___x_1989_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; lean_object* v___x_1995_; uint8_t v_isShared_1996_; uint8_t v_isSharedCheck_2005_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2005_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2005_ == 0)
{
v___x_1995_ = v___x_1992_;
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
else
{
lean_inc(v_a_1993_);
lean_dec(v___x_1992_);
v___x_1995_ = lean_box(0);
v_isShared_1996_ = v_isSharedCheck_2005_;
goto v_resetjp_1994_;
}
v_resetjp_1994_:
{
lean_object* v_fst_1997_; 
v_fst_1997_ = lean_ctor_get(v_a_1993_, 0);
lean_inc(v_fst_1997_);
lean_dec(v_a_1993_);
if (lean_obj_tag(v_fst_1997_) == 0)
{
lean_object* v___x_1999_; 
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v___x_1990_);
v___x_1999_ = v___x_1995_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v___x_1990_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
else
{
lean_object* v_val_2001_; lean_object* v___x_2003_; 
v_val_2001_ = lean_ctor_get(v_fst_1997_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v_fst_1997_, 1);
if (v_isShared_1996_ == 0)
{
lean_ctor_set(v___x_1995_, 0, v_val_2001_);
v___x_2003_ = v___x_1995_;
goto v_reusejp_2002_;
}
else
{
lean_object* v_reuseFailAlloc_2004_; 
v_reuseFailAlloc_2004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2004_, 0, v_val_2001_);
v___x_2003_ = v_reuseFailAlloc_2004_;
goto v_reusejp_2002_;
}
v_reusejp_2002_:
{
return v___x_2003_;
}
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
v_a_2006_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_1992_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_1992_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
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
v___jp_2014_:
{
if (v___y_2016_ == 0)
{
lean_dec_ref(v___y_2015_);
v___y_1987_ = v_a_1983_;
v___y_1988_ = v_a_1984_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2017_; 
lean_dec(v_decl_1982_);
v___x_2017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2017_, 0, v___y_2015_);
return v___x_2017_;
}
}
v___jp_2018_:
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Lean_Exception_isInterrupt(v_a_2019_);
if (v___x_2020_ == 0)
{
uint8_t v___x_2021_; 
lean_inc_ref(v_a_2019_);
v___x_2021_ = l_Lean_Exception_isRuntime(v_a_2019_);
v___y_2015_ = v_a_2019_;
v___y_2016_ = v___x_2021_;
goto v___jp_2014_;
}
else
{
v___y_2015_ = v_a_2019_;
v___y_2016_ = v___x_2020_;
goto v___jp_2014_;
}
}
v___jp_2022_:
{
if (v___y_2024_ == 0)
{
lean_dec_ref(v___y_2023_);
v___y_1987_ = v_a_1983_;
v___y_1988_ = v_a_1984_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2025_; 
lean_dec(v_decl_1982_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2078_, v_a_2079_, v_a_2080_);
lean_dec(v_a_2080_);
lean_dec_ref(v_a_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2084_, v___y_2085_, v___y_2086_);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_){
_start:
{
lean_object* v_res_2094_; 
v_res_2094_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2089_, v_x_2090_, v___y_2091_, v___y_2092_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
return v_res_2094_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2095_, lean_object* v_as_x27_2096_, lean_object* v_b_2097_, lean_object* v_a_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; 
v___x_2102_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2096_, v_b_2097_, v___y_2099_, v___y_2100_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2103_, lean_object* v_as_x27_2104_, lean_object* v_b_2105_, lean_object* v_a_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2103_, v_as_x27_2104_, v_b_2105_, v_a_2106_, v___y_2107_, v___y_2108_);
lean_dec(v___y_2108_);
lean_dec_ref(v___y_2107_);
lean_dec(v_as_x27_2104_);
lean_dec(v_as_2103_);
return v_res_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_){
_start:
{
lean_object* v___x_2115_; 
v___x_2115_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2121_, lean_object* v_ex_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_ex_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2127_, v_ex_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2133_, lean_object* v_msg_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_){
_start:
{
lean_object* v___x_2138_; 
v___x_2138_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2134_, v___y_2135_, v___y_2136_);
return v___x_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2139_, lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_, lean_object* v___y_2143_){
_start:
{
lean_object* v_res_2144_; 
v_res_2144_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2139_, v_msg_2140_, v___y_2141_, v___y_2142_);
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
return v_res_2144_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = lean_unsigned_to_nat(32u);
v___x_2146_ = lean_mk_empty_array_with_capacity(v___x_2145_);
v___x_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2147_, 0, v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2148_ = ((size_t)5ULL);
v___x_2149_ = lean_unsigned_to_nat(0u);
v___x_2150_ = lean_unsigned_to_nat(32u);
v___x_2151_ = lean_mk_empty_array_with_capacity(v___x_2150_);
v___x_2152_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2153_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
lean_ctor_set(v___x_2153_, 1, v___x_2151_);
lean_ctor_set(v___x_2153_, 2, v___x_2149_);
lean_ctor_set(v___x_2153_, 3, v___x_2149_);
lean_ctor_set_usize(v___x_2153_, 4, v___x_2148_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2154_){
_start:
{
lean_object* v___x_2156_; lean_object* v_traceState_2157_; lean_object* v_traces_2158_; lean_object* v___x_2159_; lean_object* v_traceState_2160_; lean_object* v_env_2161_; lean_object* v_nextMacroScope_2162_; lean_object* v_ngen_2163_; lean_object* v_auxDeclNGen_2164_; lean_object* v_cache_2165_; lean_object* v_messages_2166_; lean_object* v_infoState_2167_; lean_object* v_snapshotTasks_2168_; lean_object* v___x_2170_; uint8_t v_isShared_2171_; uint8_t v_isSharedCheck_2187_; 
v___x_2156_ = lean_st_ref_get(v___y_2154_);
v_traceState_2157_ = lean_ctor_get(v___x_2156_, 4);
lean_inc_ref(v_traceState_2157_);
lean_dec(v___x_2156_);
v_traces_2158_ = lean_ctor_get(v_traceState_2157_, 0);
lean_inc_ref(v_traces_2158_);
lean_dec_ref(v_traceState_2157_);
v___x_2159_ = lean_st_ref_take(v___y_2154_);
v_traceState_2160_ = lean_ctor_get(v___x_2159_, 4);
v_env_2161_ = lean_ctor_get(v___x_2159_, 0);
v_nextMacroScope_2162_ = lean_ctor_get(v___x_2159_, 1);
v_ngen_2163_ = lean_ctor_get(v___x_2159_, 2);
v_auxDeclNGen_2164_ = lean_ctor_get(v___x_2159_, 3);
v_cache_2165_ = lean_ctor_get(v___x_2159_, 5);
v_messages_2166_ = lean_ctor_get(v___x_2159_, 6);
v_infoState_2167_ = lean_ctor_get(v___x_2159_, 7);
v_snapshotTasks_2168_ = lean_ctor_get(v___x_2159_, 8);
v_isSharedCheck_2187_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2187_ == 0)
{
v___x_2170_ = v___x_2159_;
v_isShared_2171_ = v_isSharedCheck_2187_;
goto v_resetjp_2169_;
}
else
{
lean_inc(v_snapshotTasks_2168_);
lean_inc(v_infoState_2167_);
lean_inc(v_messages_2166_);
lean_inc(v_cache_2165_);
lean_inc(v_traceState_2160_);
lean_inc(v_auxDeclNGen_2164_);
lean_inc(v_ngen_2163_);
lean_inc(v_nextMacroScope_2162_);
lean_inc(v_env_2161_);
lean_dec(v___x_2159_);
v___x_2170_ = lean_box(0);
v_isShared_2171_ = v_isSharedCheck_2187_;
goto v_resetjp_2169_;
}
v_resetjp_2169_:
{
uint64_t v_tid_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2185_; 
v_tid_2172_ = lean_ctor_get_uint64(v_traceState_2160_, sizeof(void*)*1);
v_isSharedCheck_2185_ = !lean_is_exclusive(v_traceState_2160_);
if (v_isSharedCheck_2185_ == 0)
{
lean_object* v_unused_2186_; 
v_unused_2186_ = lean_ctor_get(v_traceState_2160_, 0);
lean_dec(v_unused_2186_);
v___x_2174_ = v_traceState_2160_;
v_isShared_2175_ = v_isSharedCheck_2185_;
goto v_resetjp_2173_;
}
else
{
lean_dec(v_traceState_2160_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2185_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2176_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2175_ == 0)
{
lean_ctor_set(v___x_2174_, 0, v___x_2176_);
v___x_2178_ = v___x_2174_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2176_);
lean_ctor_set_uint64(v_reuseFailAlloc_2184_, sizeof(void*)*1, v_tid_2172_);
v___x_2178_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
lean_object* v___x_2180_; 
if (v_isShared_2171_ == 0)
{
lean_ctor_set(v___x_2170_, 4, v___x_2178_);
v___x_2180_ = v___x_2170_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v_env_2161_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_nextMacroScope_2162_);
lean_ctor_set(v_reuseFailAlloc_2183_, 2, v_ngen_2163_);
lean_ctor_set(v_reuseFailAlloc_2183_, 3, v_auxDeclNGen_2164_);
lean_ctor_set(v_reuseFailAlloc_2183_, 4, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2183_, 5, v_cache_2165_);
lean_ctor_set(v_reuseFailAlloc_2183_, 6, v_messages_2166_);
lean_ctor_set(v_reuseFailAlloc_2183_, 7, v_infoState_2167_);
lean_ctor_set(v_reuseFailAlloc_2183_, 8, v_snapshotTasks_2168_);
v___x_2180_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_st_ref_put(v___y_2154_, v___x_2180_);
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v_traces_2158_);
return v___x_2182_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2188_, lean_object* v___y_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2188_);
lean_dec(v___y_2188_);
return v_res_2190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2192_);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_res_2198_; 
v_res_2198_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2195_, v___y_2196_);
lean_dec(v___y_2196_);
lean_dec_ref(v___y_2195_);
return v_res_2198_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2199_, lean_object* v_opts_2200_, lean_object* v_act_2201_, lean_object* v_decl_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; 
lean_inc(v___y_2204_);
lean_inc_ref(v___y_2203_);
v___x_2206_ = lean_apply_2(v_act_2201_, v___y_2203_, v___y_2204_);
v___x_2207_ = l_Lean_profileitIOUnsafe___redArg(v_category_2199_, v_opts_2200_, v___x_2206_, v_decl_2202_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2208_, lean_object* v_opts_2209_, lean_object* v_act_2210_, lean_object* v_decl_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2208_, v_opts_2209_, v_act_2210_, v_decl_2211_, v___y_2212_, v___y_2213_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_opts_2209_);
lean_dec_ref(v_category_2208_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2216_, lean_object* v_category_2217_, lean_object* v_opts_2218_, lean_object* v_act_2219_, lean_object* v_decl_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_){
_start:
{
lean_object* v___x_2224_; 
v___x_2224_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2217_, v_opts_2218_, v_act_2219_, v_decl_2220_, v___y_2221_, v___y_2222_);
return v___x_2224_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2225_, lean_object* v_category_2226_, lean_object* v_opts_2227_, lean_object* v_act_2228_, lean_object* v_decl_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_){
_start:
{
lean_object* v_res_2233_; 
v_res_2233_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2225_, v_category_2226_, v_opts_2227_, v_act_2228_, v_decl_2229_, v___y_2230_, v___y_2231_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
lean_dec_ref(v_opts_2227_);
lean_dec_ref(v_category_2226_);
return v_res_2233_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2234_, lean_object* v_a_2235_){
_start:
{
if (lean_obj_tag(v_a_2234_) == 0)
{
lean_object* v___x_2236_; 
v___x_2236_ = l_List_reverse___redArg(v_a_2235_);
return v___x_2236_;
}
else
{
lean_object* v_head_2237_; lean_object* v_tail_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2247_; 
v_head_2237_ = lean_ctor_get(v_a_2234_, 0);
v_tail_2238_ = lean_ctor_get(v_a_2234_, 1);
v_isSharedCheck_2247_ = !lean_is_exclusive(v_a_2234_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2240_ = v_a_2234_;
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_tail_2238_);
lean_inc(v_head_2237_);
lean_dec(v_a_2234_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2247_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2244_; 
v___x_2242_ = l_Lean_MessageData_ofName(v_head_2237_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 1, v_a_2235_);
lean_ctor_set(v___x_2240_, 0, v___x_2242_);
v___x_2244_ = v___x_2240_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v___x_2242_);
lean_ctor_set(v_reuseFailAlloc_2246_, 1, v_a_2235_);
v___x_2244_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
v_a_2234_ = v_tail_2238_;
v_a_2235_ = v___x_2244_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2250_ = l_Lean_stringToMessageData(v___x_2249_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2251_, lean_object* v_x_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2256_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2257_ = l_Lean_Declaration_getTopLevelNames(v_decl_2251_);
v___x_2258_ = lean_box(0);
v___x_2259_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2257_, v___x_2258_);
v___x_2260_ = l_Lean_MessageData_ofList(v___x_2259_);
v___x_2261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2256_);
lean_ctor_set(v___x_2261_, 1, v___x_2260_);
v___x_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2263_, lean_object* v_x_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2263_, v_x_2264_, v___y_2265_, v___y_2266_);
lean_dec(v___y_2266_);
lean_dec_ref(v___y_2265_);
lean_dec_ref(v_x_2264_);
return v_res_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2269_, size_t v_i_2270_, lean_object* v_bs_2271_){
_start:
{
uint8_t v___x_2272_; 
v___x_2272_ = lean_usize_dec_lt(v_i_2270_, v_sz_2269_);
if (v___x_2272_ == 0)
{
return v_bs_2271_;
}
else
{
lean_object* v_v_2273_; lean_object* v_msg_2274_; lean_object* v___x_2275_; lean_object* v_bs_x27_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v___x_2279_; 
v_v_2273_ = lean_array_uget_borrowed(v_bs_2271_, v_i_2270_);
v_msg_2274_ = lean_ctor_get(v_v_2273_, 1);
lean_inc_ref(v_msg_2274_);
v___x_2275_ = lean_unsigned_to_nat(0u);
v_bs_x27_2276_ = lean_array_uset(v_bs_2271_, v_i_2270_, v___x_2275_);
v___x_2277_ = ((size_t)1ULL);
v___x_2278_ = lean_usize_add(v_i_2270_, v___x_2277_);
v___x_2279_ = lean_array_uset(v_bs_x27_2276_, v_i_2270_, v_msg_2274_);
v_i_2270_ = v___x_2278_;
v_bs_2271_ = v___x_2279_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2281_, lean_object* v_i_2282_, lean_object* v_bs_2283_){
_start:
{
size_t v_sz_boxed_2284_; size_t v_i_boxed_2285_; lean_object* v_res_2286_; 
v_sz_boxed_2284_ = lean_unbox_usize(v_sz_2281_);
lean_dec(v_sz_2281_);
v_i_boxed_2285_ = lean_unbox_usize(v_i_2282_);
lean_dec(v_i_2282_);
v_res_2286_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2284_, v_i_boxed_2285_, v_bs_2283_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2287_, lean_object* v_data_2288_, lean_object* v_ref_2289_, lean_object* v_msg_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_toCold_2294_; lean_object* v_currRecDepth_2295_; lean_object* v_ref_2296_; uint8_t v_diag_2297_; uint8_t v_suppressElabErrors_2298_; lean_object* v___x_2299_; lean_object* v_traceState_2300_; lean_object* v_traces_2301_; lean_object* v_ref_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; size_t v_sz_2305_; size_t v___x_2306_; lean_object* v___x_2307_; lean_object* v_msg_2308_; lean_object* v___x_2309_; lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2347_; 
v_toCold_2294_ = lean_ctor_get(v___y_2291_, 0);
v_currRecDepth_2295_ = lean_ctor_get(v___y_2291_, 1);
v_ref_2296_ = lean_ctor_get(v___y_2291_, 2);
v_diag_2297_ = lean_ctor_get_uint8(v___y_2291_, sizeof(void*)*3);
v_suppressElabErrors_2298_ = lean_ctor_get_uint8(v___y_2291_, sizeof(void*)*3 + 1);
v___x_2299_ = lean_st_ref_get(v___y_2292_);
v_traceState_2300_ = lean_ctor_get(v___x_2299_, 4);
lean_inc_ref(v_traceState_2300_);
lean_dec(v___x_2299_);
v_traces_2301_ = lean_ctor_get(v_traceState_2300_, 0);
lean_inc_ref(v_traces_2301_);
lean_dec_ref(v_traceState_2300_);
v_ref_2302_ = l_Lean_replaceRef(v_ref_2289_, v_ref_2296_);
lean_inc(v_currRecDepth_2295_);
lean_inc_ref(v_toCold_2294_);
v___x_2303_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2303_, 0, v_toCold_2294_);
lean_ctor_set(v___x_2303_, 1, v_currRecDepth_2295_);
lean_ctor_set(v___x_2303_, 2, v_ref_2302_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3, v_diag_2297_);
lean_ctor_set_uint8(v___x_2303_, sizeof(void*)*3 + 1, v_suppressElabErrors_2298_);
v___x_2304_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2301_);
lean_dec_ref(v_traces_2301_);
v_sz_2305_ = lean_array_size(v___x_2304_);
v___x_2306_ = ((size_t)0ULL);
v___x_2307_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2305_, v___x_2306_, v___x_2304_);
v_msg_2308_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2308_, 0, v_data_2288_);
lean_ctor_set(v_msg_2308_, 1, v_msg_2290_);
lean_ctor_set(v_msg_2308_, 2, v___x_2307_);
v___x_2309_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2308_, v___x_2303_, v___y_2292_);
lean_dec_ref_known(v___x_2303_, 3);
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
v___x_2314_ = lean_st_ref_take(v___y_2292_);
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
lean_ctor_set(v___x_2331_, 0, v_ref_2289_);
lean_ctor_set(v___x_2331_, 1, v_a_2310_);
v___x_2332_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2287_, v___x_2331_);
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
v___x_2337_ = lean_st_ref_put(v___y_2292_, v___x_2336_);
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
v_ref_2425_ = lean_ctor_get(v___y_2398_, 2);
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
v___x_2454_ = lean_st_ref_put(v___y_2399_, v___x_2453_);
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
lean_object* v___x_2543_; lean_object* v_env_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; 
lean_dec_ref_known(v___x_2542_, 1);
v___x_2543_ = lean_st_ref_get(v___y_2500_);
v_env_2544_ = lean_ctor_get(v___x_2543_, 0);
lean_inc_ref(v_env_2544_);
lean_dec(v___x_2543_);
v___x_2545_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2544_, v_options_2539_, v_decl_2494_, v_cancelTk_x3f_2541_);
v___x_2546_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2545_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2546_) == 0)
{
lean_object* v_a_2547_; lean_object* v___x_2548_; 
lean_dec(v_decl_2494_);
v_a_2547_ = lean_ctor_get(v___x_2546_, 0);
lean_inc(v_a_2547_);
lean_dec_ref_known(v___x_2546_, 1);
v___x_2548_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2547_, v___y_2500_);
return v___x_2548_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
v_a_2549_ = lean_ctor_get(v___x_2546_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2546_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2546_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2546_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
lean_inc(v_a_2549_);
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
v___y_2534_ = v___x_2554_;
v_a_2535_ = v_a_2549_;
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
lean_object* v_cancelTk_x3f_2557_; lean_object* v_inheritedTraceOptions_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; uint8_t v___x_2561_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v_a_2565_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v_a_2580_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v_a_2585_; lean_object* v___y_2588_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; uint8_t v___y_2597_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v_a_2602_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v_a_2608_; lean_object* v___y_2618_; lean_object* v___y_2619_; lean_object* v_a_2620_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v_a_2625_; lean_object* v___y_2628_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; uint8_t v___y_2637_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v_a_2642_; 
v_cancelTk_x3f_2557_ = lean_ctor_get(v_toCold_2538_, 10);
v_inheritedTraceOptions_2558_ = lean_ctor_get(v_toCold_2538_, 11);
v___x_2559_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2495_);
v___x_2560_ = l_Lean_Name_append(v___x_2559_, v___x_2495_);
v___x_2561_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2558_, v_options_2539_, v___x_2560_);
lean_dec(v___x_2560_);
if (v___x_2561_ == 0)
{
lean_object* v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = l_Lean_trace_profiler;
v___x_2671_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2539_, v___x_2670_);
if (v___x_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec_ref(v___f_2498_);
lean_dec_ref(v___x_2497_);
lean_dec(v___x_2495_);
lean_inc(v_decl_2494_);
v___x_2672_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2673_; lean_object* v_env_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
lean_dec_ref_known(v___x_2672_, 1);
v___x_2673_ = lean_st_ref_get(v___y_2500_);
v_env_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc_ref(v_env_2674_);
lean_dec(v___x_2673_);
v___x_2675_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2674_, v_options_2539_, v_decl_2494_, v_cancelTk_x3f_2557_);
v___x_2676_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2675_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
lean_dec(v_decl_2494_);
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
v___x_2678_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2677_, v___y_2500_);
return v___x_2678_;
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
v_a_2679_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2676_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2676_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
lean_inc(v_a_2679_);
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
v___y_2516_ = v___x_2684_;
v_a_2517_ = v_a_2679_;
goto v___jp_2515_;
}
}
}
}
else
{
lean_dec(v_decl_2494_);
return v___x_2672_;
}
}
else
{
goto v___jp_2645_;
}
}
else
{
goto v___jp_2645_;
}
v___jp_2562_:
{
lean_object* v___x_2566_; double v___x_2567_; double v___x_2568_; double v___x_2569_; double v___x_2570_; double v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2566_ = lean_io_mono_nanos_now();
v___x_2567_ = lean_float_of_nat(v___y_2564_);
v___x_2568_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2569_ = lean_float_div(v___x_2567_, v___x_2568_);
v___x_2570_ = lean_float_of_nat(v___x_2566_);
v___x_2571_ = lean_float_div(v___x_2570_, v___x_2568_);
v___x_2572_ = lean_box_float(v___x_2569_);
v___x_2573_ = lean_box_float(v___x_2571_);
v___x_2574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2574_, 0, v___x_2572_);
lean_ctor_set(v___x_2574_, 1, v___x_2573_);
v___x_2575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2575_, 0, v_a_2565_);
lean_ctor_set(v___x_2575_, 1, v___x_2574_);
v___x_2576_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2539_, v___x_2561_, v___y_2563_, v___f_2498_, v___x_2575_, v___y_2499_, v___y_2500_);
return v___x_2576_;
}
v___jp_2577_:
{
lean_object* v___x_2581_; 
v___x_2581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2580_);
v___y_2563_ = v___y_2578_;
v___y_2564_ = v___y_2579_;
v_a_2565_ = v___x_2581_;
goto v___jp_2562_;
}
v___jp_2582_:
{
lean_object* v___x_2586_; 
v___x_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2586_, 0, v_a_2585_);
v___y_2563_ = v___y_2583_;
v___y_2564_ = v___y_2584_;
v_a_2565_ = v___x_2586_;
goto v___jp_2562_;
}
v___jp_2587_:
{
if (lean_obj_tag(v___y_2590_) == 0)
{
lean_object* v_a_2591_; 
v_a_2591_ = lean_ctor_get(v___y_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___y_2590_, 1);
v___y_2583_ = v___y_2588_;
v___y_2584_ = v___y_2589_;
v_a_2585_ = v_a_2591_;
goto v___jp_2582_;
}
else
{
lean_object* v_a_2592_; 
v_a_2592_ = lean_ctor_get(v___y_2590_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___y_2590_, 1);
v___y_2578_ = v___y_2588_;
v___y_2579_ = v___y_2589_;
v_a_2580_ = v_a_2592_;
goto v___jp_2577_;
}
}
v___jp_2593_:
{
if (v___y_2597_ == 0)
{
lean_object* v___x_2598_; 
v___x_2598_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2598_) == 0)
{
lean_dec_ref_known(v___x_2598_, 1);
v___y_2578_ = v___y_2595_;
v___y_2579_ = v___y_2596_;
v_a_2580_ = v___y_2594_;
goto v___jp_2577_;
}
else
{
lean_dec_ref(v___y_2594_);
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___y_2596_;
v___y_2590_ = v___x_2598_;
goto v___jp_2587_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2578_ = v___y_2595_;
v___y_2579_ = v___y_2596_;
v_a_2580_ = v___y_2594_;
goto v___jp_2577_;
}
}
v___jp_2599_:
{
uint8_t v___x_2603_; 
v___x_2603_ = l_Lean_Exception_isInterrupt(v_a_2602_);
if (v___x_2603_ == 0)
{
uint8_t v___x_2604_; 
lean_inc_ref(v_a_2602_);
v___x_2604_ = l_Lean_Exception_isRuntime(v_a_2602_);
v___y_2594_ = v_a_2602_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2601_;
v___y_2597_ = v___x_2604_;
goto v___jp_2593_;
}
else
{
v___y_2594_ = v_a_2602_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2601_;
v___y_2597_ = v___x_2603_;
goto v___jp_2593_;
}
}
v___jp_2605_:
{
lean_object* v___x_2609_; double v___x_2610_; double v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2609_ = lean_io_get_num_heartbeats();
v___x_2610_ = lean_float_of_nat(v___y_2606_);
v___x_2611_ = lean_float_of_nat(v___x_2609_);
v___x_2612_ = lean_box_float(v___x_2610_);
v___x_2613_ = lean_box_float(v___x_2611_);
v___x_2614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2614_, 0, v___x_2612_);
lean_ctor_set(v___x_2614_, 1, v___x_2613_);
v___x_2615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2615_, 0, v_a_2608_);
lean_ctor_set(v___x_2615_, 1, v___x_2614_);
v___x_2616_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2495_, v___x_2496_, v___x_2497_, v_options_2539_, v___x_2561_, v___y_2607_, v___f_2498_, v___x_2615_, v___y_2499_, v___y_2500_);
return v___x_2616_;
}
v___jp_2617_:
{
lean_object* v___x_2621_; 
v___x_2621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2621_, 0, v_a_2620_);
v___y_2606_ = v___y_2618_;
v___y_2607_ = v___y_2619_;
v_a_2608_ = v___x_2621_;
goto v___jp_2605_;
}
v___jp_2622_:
{
lean_object* v___x_2626_; 
v___x_2626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2626_, 0, v_a_2625_);
v___y_2606_ = v___y_2623_;
v___y_2607_ = v___y_2624_;
v_a_2608_ = v___x_2626_;
goto v___jp_2605_;
}
v___jp_2627_:
{
if (lean_obj_tag(v___y_2630_) == 0)
{
lean_object* v_a_2631_; 
v_a_2631_ = lean_ctor_get(v___y_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___y_2630_, 1);
v___y_2623_ = v___y_2628_;
v___y_2624_ = v___y_2629_;
v_a_2625_ = v_a_2631_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2632_; 
v_a_2632_ = lean_ctor_get(v___y_2630_, 0);
lean_inc(v_a_2632_);
lean_dec_ref_known(v___y_2630_, 1);
v___y_2618_ = v___y_2628_;
v___y_2619_ = v___y_2629_;
v_a_2620_ = v_a_2632_;
goto v___jp_2617_;
}
}
v___jp_2633_:
{
if (v___y_2637_ == 0)
{
lean_object* v___x_2638_; 
v___x_2638_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_dec_ref_known(v___x_2638_, 1);
v___y_2618_ = v___y_2634_;
v___y_2619_ = v___y_2635_;
v_a_2620_ = v___y_2636_;
goto v___jp_2617_;
}
else
{
lean_dec_ref(v___y_2636_);
v___y_2628_ = v___y_2634_;
v___y_2629_ = v___y_2635_;
v___y_2630_ = v___x_2638_;
goto v___jp_2627_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2618_ = v___y_2634_;
v___y_2619_ = v___y_2635_;
v_a_2620_ = v___y_2636_;
goto v___jp_2617_;
}
}
v___jp_2639_:
{
uint8_t v___x_2643_; 
v___x_2643_ = l_Lean_Exception_isInterrupt(v_a_2642_);
if (v___x_2643_ == 0)
{
uint8_t v___x_2644_; 
lean_inc_ref(v_a_2642_);
v___x_2644_ = l_Lean_Exception_isRuntime(v_a_2642_);
v___y_2634_ = v___y_2640_;
v___y_2635_ = v___y_2641_;
v___y_2636_ = v_a_2642_;
v___y_2637_ = v___x_2644_;
goto v___jp_2633_;
}
else
{
v___y_2634_ = v___y_2640_;
v___y_2635_ = v___y_2641_;
v___y_2636_ = v_a_2642_;
v___y_2637_ = v___x_2643_;
goto v___jp_2633_;
}
}
v___jp_2645_:
{
lean_object* v___x_2646_; lean_object* v_a_2647_; lean_object* v___x_2648_; uint8_t v___x_2649_; 
v___x_2646_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2500_);
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref(v___x_2646_);
v___x_2648_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2649_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2539_, v___x_2648_);
if (v___x_2649_ == 0)
{
lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2650_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2494_);
v___x_2651_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2651_) == 0)
{
lean_object* v___x_2652_; lean_object* v_env_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; 
lean_dec_ref_known(v___x_2651_, 1);
v___x_2652_ = lean_st_ref_get(v___y_2500_);
v_env_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc_ref(v_env_2653_);
lean_dec(v___x_2652_);
v___x_2654_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2653_, v_options_2539_, v_decl_2494_, v_cancelTk_x3f_2557_);
v___x_2655_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2654_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v___x_2657_; lean_object* v_a_2658_; 
lean_dec(v_decl_2494_);
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2656_);
lean_dec_ref_known(v___x_2655_, 1);
v___x_2657_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2656_, v___y_2500_);
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2658_);
lean_dec_ref(v___x_2657_);
v___y_2583_ = v_a_2647_;
v___y_2584_ = v___x_2650_;
v_a_2585_ = v_a_2658_;
goto v___jp_2582_;
}
else
{
lean_object* v_a_2659_; 
v_a_2659_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2655_, 1);
v___y_2600_ = v_a_2647_;
v___y_2601_ = v___x_2650_;
v_a_2602_ = v_a_2659_;
goto v___jp_2599_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2588_ = v_a_2647_;
v___y_2589_ = v___x_2650_;
v___y_2590_ = v___x_2651_;
goto v___jp_2587_;
}
}
else
{
lean_object* v___x_2660_; lean_object* v___x_2661_; 
v___x_2660_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2494_);
v___x_2661_ = l_Lean_warnIfUsesSorry(v_decl_2494_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v___x_2662_; lean_object* v_env_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
lean_dec_ref_known(v___x_2661_, 1);
v___x_2662_ = lean_st_ref_get(v___y_2500_);
v_env_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc_ref(v_env_2663_);
lean_dec(v___x_2662_);
v___x_2664_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2663_, v_options_2539_, v_decl_2494_, v_cancelTk_x3f_2557_);
v___x_2665_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2664_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v_a_2666_; lean_object* v___x_2667_; lean_object* v_a_2668_; 
lean_dec(v_decl_2494_);
v_a_2666_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2666_);
lean_dec_ref_known(v___x_2665_, 1);
v___x_2667_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2666_, v___y_2500_);
v_a_2668_ = lean_ctor_get(v___x_2667_, 0);
lean_inc(v_a_2668_);
lean_dec_ref(v___x_2667_);
v___y_2623_ = v___x_2660_;
v___y_2624_ = v_a_2647_;
v_a_2625_ = v_a_2668_;
goto v___jp_2622_;
}
else
{
lean_object* v_a_2669_; 
v_a_2669_ = lean_ctor_get(v___x_2665_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2665_, 1);
v___y_2640_ = v___x_2660_;
v___y_2641_ = v_a_2647_;
v_a_2642_ = v_a_2669_;
goto v___jp_2639_;
}
}
else
{
lean_dec(v_decl_2494_);
v___y_2628_ = v___x_2660_;
v___y_2629_ = v_a_2647_;
v___y_2630_ = v___x_2661_;
goto v___jp_2627_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2687_, lean_object* v___x_2688_, lean_object* v___x_2689_, lean_object* v___x_2690_, lean_object* v___f_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
uint8_t v___x_7930__boxed_2695_; lean_object* v_res_2696_; 
v___x_7930__boxed_2695_ = lean_unbox(v___x_2689_);
v_res_2696_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2687_, v___x_2688_, v___x_7930__boxed_2695_, v___x_2690_, v___f_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
return v_res_2696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v_toCold_2705_; lean_object* v_options_2706_; lean_object* v___f_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; uint8_t v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v_toCold_2705_ = lean_ctor_get(v_a_2702_, 0);
v_options_2706_ = lean_ctor_get(v_toCold_2705_, 2);
lean_inc(v_decl_2701_);
v___f_2707_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2707_, 0, v_decl_2701_);
v___x_2708_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2709_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2710_ = 1;
v___x_2711_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2712_ = lean_box(v___x_2710_);
v___f_2713_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2713_, 0, v_decl_2701_);
lean_closure_set(v___f_2713_, 1, v___x_2709_);
lean_closure_set(v___f_2713_, 2, v___x_2712_);
lean_closure_set(v___f_2713_, 3, v___x_2711_);
lean_closure_set(v___f_2713_, 4, v___f_2707_);
v___x_2714_ = lean_box(0);
v___x_2715_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2708_, v_options_2706_, v___f_2713_, v___x_2714_, v_a_2702_, v_a_2703_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2716_, lean_object* v_a_2717_, lean_object* v_a_2718_, lean_object* v_a_2719_){
_start:
{
lean_object* v_res_2720_; 
v_res_2720_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2716_, v_a_2717_, v_a_2718_);
lean_dec(v_a_2718_);
lean_dec_ref(v_a_2717_);
return v_res_2720_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2721_, lean_object* v_x_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v___x_2726_; 
v___x_2726_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2722_);
return v___x_2726_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2727_, v_x_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2733_, lean_object* v_a_2734_, lean_object* v___y_2735_, lean_object* v_a_x3f_2736_){
_start:
{
lean_object* v___x_2738_; lean_object* v_env_2739_; lean_object* v___x_2740_; 
v___x_2738_ = lean_st_ref_get(v___y_2733_);
v_env_2739_ = lean_ctor_get(v___x_2738_, 0);
lean_inc_ref(v_env_2739_);
lean_dec(v___x_2738_);
v___x_2740_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2734_, v_env_2739_);
if (lean_obj_tag(v___x_2740_) == 0)
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
else
{
lean_object* v_a_2749_; lean_object* v___x_2751_; uint8_t v_isShared_2752_; uint8_t v_isSharedCheck_2761_; 
v_a_2749_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2761_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2761_ == 0)
{
v___x_2751_ = v___x_2740_;
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
else
{
lean_inc(v_a_2749_);
lean_dec(v___x_2740_);
v___x_2751_ = lean_box(0);
v_isShared_2752_ = v_isSharedCheck_2761_;
goto v_resetjp_2750_;
}
v_resetjp_2750_:
{
lean_object* v_ref_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2759_; 
v_ref_2753_ = lean_ctor_get(v___y_2735_, 2);
v___x_2754_ = lean_io_error_to_string(v_a_2749_);
v___x_2755_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2755_, 0, v___x_2754_);
v___x_2756_ = l_Lean_MessageData_ofFormat(v___x_2755_);
lean_inc(v_ref_2753_);
v___x_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2757_, 0, v_ref_2753_);
lean_ctor_set(v___x_2757_, 1, v___x_2756_);
if (v_isShared_2752_ == 0)
{
lean_ctor_set(v___x_2751_, 0, v___x_2757_);
v___x_2759_ = v___x_2751_;
goto v_reusejp_2758_;
}
else
{
lean_object* v_reuseFailAlloc_2760_; 
v_reuseFailAlloc_2760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2760_, 0, v___x_2757_);
v___x_2759_ = v_reuseFailAlloc_2760_;
goto v_reusejp_2758_;
}
v_reusejp_2758_:
{
return v___x_2759_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2762_, lean_object* v_a_2763_, lean_object* v___y_2764_, lean_object* v_a_x3f_2765_, lean_object* v___y_2766_){
_start:
{
lean_object* v_res_2767_; 
v_res_2767_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2762_, v_a_2763_, v___y_2764_, v_a_x3f_2765_);
lean_dec(v_a_x3f_2765_);
lean_dec_ref(v___y_2764_);
lean_dec(v___y_2762_);
return v_res_2767_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2768_, lean_object* v_a_2769_, lean_object* v_decl_2770_, lean_object* v_x_2771_, lean_object* v___y_2772_, lean_object* v___y_2773_){
_start:
{
lean_object* v___x_2775_; lean_object* v_r_2776_; 
v___x_2775_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2768_, v___y_2773_);
lean_dec_ref(v___x_2775_);
v_r_2776_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2770_, v___y_2772_, v___y_2773_);
if (lean_obj_tag(v_r_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2793_; 
v_a_2777_ = lean_ctor_get(v_r_2776_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v_r_2776_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2779_ = v_r_2776_;
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_a_2777_);
lean_dec(v_r_2776_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2793_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2782_; 
lean_inc(v_a_2777_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set_tag(v___x_2779_, 1);
v___x_2782_ = v___x_2779_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2777_);
v___x_2782_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
lean_object* v___x_2783_; 
v___x_2783_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2773_, v_a_2769_, v___y_2772_, v___x_2782_);
lean_dec_ref(v___x_2782_);
if (lean_obj_tag(v___x_2783_) == 0)
{
lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; 
v_unused_2791_ = lean_ctor_get(v___x_2783_, 0);
lean_dec(v_unused_2791_);
v___x_2785_ = v___x_2783_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_dec(v___x_2783_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
lean_ctor_set(v___x_2785_, 0, v_a_2777_);
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2777_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
else
{
lean_dec(v_a_2777_);
return v___x_2783_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v_a_2794_ = lean_ctor_get(v_r_2776_, 0);
lean_inc(v_a_2794_);
lean_dec_ref_known(v_r_2776_, 1);
v___x_2795_ = lean_box(0);
v___x_2796_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2773_, v_a_2769_, v___y_2772_, v___x_2795_);
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
lean_ctor_set_tag(v___x_2798_, 1);
lean_ctor_set(v___x_2798_, 0, v_a_2794_);
v___x_2801_ = v___x_2798_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2802_; 
v_reuseFailAlloc_2802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2802_, 0, v_a_2794_);
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
lean_dec(v_a_2794_);
return v___x_2796_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2805_, lean_object* v_a_2806_, lean_object* v_decl_2807_, lean_object* v_x_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2805_, v_a_2806_, v_decl_2807_, v_x_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec_ref(v_x_2808_);
return v_res_2812_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2816_, lean_object* v_x_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2821_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2822_ = l_Lean_Declaration_getNames(v_decl_2816_);
v___x_2823_ = lean_box(0);
v___x_2824_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2822_, v___x_2823_);
v___x_2825_ = l_Lean_MessageData_ofList(v___x_2824_);
v___x_2826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2826_, 0, v___x_2821_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2827_, 0, v___x_2826_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2828_, lean_object* v_x_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2828_, v_x_2829_, v___y_2830_, v___y_2831_);
lean_dec(v___y_2831_);
lean_dec_ref(v___y_2830_);
lean_dec_ref(v_x_2829_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2836_, lean_object* v_msg_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_ref_2841_; lean_object* v___x_2842_; lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2887_; 
v_ref_2841_ = lean_ctor_get(v___y_2838_, 2);
v___x_2842_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2837_, v___y_2838_, v___y_2839_);
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2845_ = v___x_2842_;
v_isShared_2846_ = v_isSharedCheck_2887_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2842_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2887_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v_traceState_2848_; lean_object* v_env_2849_; lean_object* v_nextMacroScope_2850_; lean_object* v_ngen_2851_; lean_object* v_auxDeclNGen_2852_; lean_object* v_cache_2853_; lean_object* v_messages_2854_; lean_object* v_infoState_2855_; lean_object* v_snapshotTasks_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2886_; 
v___x_2847_ = lean_st_ref_take(v___y_2839_);
v_traceState_2848_ = lean_ctor_get(v___x_2847_, 4);
v_env_2849_ = lean_ctor_get(v___x_2847_, 0);
v_nextMacroScope_2850_ = lean_ctor_get(v___x_2847_, 1);
v_ngen_2851_ = lean_ctor_get(v___x_2847_, 2);
v_auxDeclNGen_2852_ = lean_ctor_get(v___x_2847_, 3);
v_cache_2853_ = lean_ctor_get(v___x_2847_, 5);
v_messages_2854_ = lean_ctor_get(v___x_2847_, 6);
v_infoState_2855_ = lean_ctor_get(v___x_2847_, 7);
v_snapshotTasks_2856_ = lean_ctor_get(v___x_2847_, 8);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2847_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2858_ = v___x_2847_;
v_isShared_2859_ = v_isSharedCheck_2886_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_snapshotTasks_2856_);
lean_inc(v_infoState_2855_);
lean_inc(v_messages_2854_);
lean_inc(v_cache_2853_);
lean_inc(v_traceState_2848_);
lean_inc(v_auxDeclNGen_2852_);
lean_inc(v_ngen_2851_);
lean_inc(v_nextMacroScope_2850_);
lean_inc(v_env_2849_);
lean_dec(v___x_2847_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2886_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
uint64_t v_tid_2860_; lean_object* v_traces_2861_; lean_object* v___x_2863_; uint8_t v_isShared_2864_; uint8_t v_isSharedCheck_2885_; 
v_tid_2860_ = lean_ctor_get_uint64(v_traceState_2848_, sizeof(void*)*1);
v_traces_2861_ = lean_ctor_get(v_traceState_2848_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v_traceState_2848_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2863_ = v_traceState_2848_;
v_isShared_2864_ = v_isSharedCheck_2885_;
goto v_resetjp_2862_;
}
else
{
lean_inc(v_traces_2861_);
lean_dec(v_traceState_2848_);
v___x_2863_ = lean_box(0);
v_isShared_2864_ = v_isSharedCheck_2885_;
goto v_resetjp_2862_;
}
v_resetjp_2862_:
{
lean_object* v___x_2865_; double v___x_2866_; uint8_t v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2875_; 
v___x_2865_ = lean_box(0);
v___x_2866_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2867_ = 0;
v___x_2868_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2869_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2869_, 0, v_cls_2836_);
lean_ctor_set(v___x_2869_, 1, v___x_2865_);
lean_ctor_set(v___x_2869_, 2, v___x_2868_);
lean_ctor_set_float(v___x_2869_, sizeof(void*)*3, v___x_2866_);
lean_ctor_set_float(v___x_2869_, sizeof(void*)*3 + 8, v___x_2866_);
lean_ctor_set_uint8(v___x_2869_, sizeof(void*)*3 + 16, v___x_2867_);
v___x_2870_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2871_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2871_, 0, v___x_2869_);
lean_ctor_set(v___x_2871_, 1, v_a_2843_);
lean_ctor_set(v___x_2871_, 2, v___x_2870_);
lean_inc(v_ref_2841_);
v___x_2872_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2872_, 0, v_ref_2841_);
lean_ctor_set(v___x_2872_, 1, v___x_2871_);
v___x_2873_ = l_Lean_PersistentArray_push___redArg(v_traces_2861_, v___x_2872_);
if (v_isShared_2864_ == 0)
{
lean_ctor_set(v___x_2863_, 0, v___x_2873_);
v___x_2875_ = v___x_2863_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2873_);
lean_ctor_set_uint64(v_reuseFailAlloc_2884_, sizeof(void*)*1, v_tid_2860_);
v___x_2875_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
lean_object* v___x_2877_; 
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 4, v___x_2875_);
v___x_2877_ = v___x_2858_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2883_; 
v_reuseFailAlloc_2883_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2883_, 0, v_env_2849_);
lean_ctor_set(v_reuseFailAlloc_2883_, 1, v_nextMacroScope_2850_);
lean_ctor_set(v_reuseFailAlloc_2883_, 2, v_ngen_2851_);
lean_ctor_set(v_reuseFailAlloc_2883_, 3, v_auxDeclNGen_2852_);
lean_ctor_set(v_reuseFailAlloc_2883_, 4, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2883_, 5, v_cache_2853_);
lean_ctor_set(v_reuseFailAlloc_2883_, 6, v_messages_2854_);
lean_ctor_set(v_reuseFailAlloc_2883_, 7, v_infoState_2855_);
lean_ctor_set(v_reuseFailAlloc_2883_, 8, v_snapshotTasks_2856_);
v___x_2877_ = v_reuseFailAlloc_2883_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2878_ = lean_st_ref_put(v___y_2839_, v___x_2877_);
v___x_2879_ = lean_box(0);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2879_);
v___x_2881_ = v___x_2845_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2888_, lean_object* v_msg_2889_, lean_object* v___y_2890_, lean_object* v___y_2891_, lean_object* v___y_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2888_, v_msg_2889_, v___y_2890_, v___y_2891_);
lean_dec(v___y_2891_);
lean_dec_ref(v___y_2890_);
return v_res_2893_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2895_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2896_ = l_Lean_stringToMessageData(v___x_2895_);
return v___x_2896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2897_, lean_object* v_cls_2898_, lean_object* v_x_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_){
_start:
{
lean_object* v_toCold_2903_; lean_object* v_options_2904_; uint8_t v_hasTrace_2905_; 
v_toCold_2903_ = lean_ctor_get(v___y_2900_, 0);
v_options_2904_ = lean_ctor_get(v_toCold_2903_, 2);
v_hasTrace_2905_ = lean_ctor_get_uint8(v_options_2904_, sizeof(void*)*1);
if (v_hasTrace_2905_ == 0)
{
lean_object* v___x_2906_; 
lean_dec(v_cls_2898_);
v___x_2906_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2897_, v___y_2900_, v___y_2901_);
return v___x_2906_;
}
else
{
lean_object* v_inheritedTraceOptions_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v___x_2910_; 
v_inheritedTraceOptions_2907_ = lean_ctor_get(v_toCold_2903_, 11);
v___x_2908_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2898_);
v___x_2909_ = l_Lean_Name_append(v___x_2908_, v_cls_2898_);
v___x_2910_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2907_, v_options_2904_, v___x_2909_);
lean_dec(v___x_2909_);
if (v___x_2910_ == 0)
{
lean_object* v___x_2911_; 
lean_dec(v_cls_2898_);
v___x_2911_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2897_, v___y_2900_, v___y_2901_);
return v___x_2911_;
}
else
{
lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2912_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2913_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2898_, v___x_2912_, v___y_2900_, v___y_2901_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2914_; 
lean_dec_ref_known(v___x_2913_, 1);
v___x_2914_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2897_, v___y_2900_, v___y_2901_);
return v___x_2914_;
}
else
{
lean_dec(v_decl_2897_);
return v___x_2913_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2915_, lean_object* v_cls_2916_, lean_object* v_x_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2915_, v_cls_2916_, v_x_2917_, v___y_2918_, v___y_2919_);
lean_dec(v___y_2919_);
lean_dec_ref(v___y_2918_);
lean_dec(v_x_2917_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2922_, lean_object* v___y_2923_){
_start:
{
lean_object* v_toCold_2925_; lean_object* v_options_2926_; uint8_t v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v_toCold_2925_ = lean_ctor_get(v___y_2923_, 0);
v_options_2926_ = lean_ctor_get(v_toCold_2925_, 2);
v___x_2927_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2926_, v_opt_2922_);
v___x_2928_ = lean_box(v___x_2927_);
v___x_2929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2930_, v___y_2931_);
lean_dec_ref(v___y_2931_);
lean_dec_ref(v_opt_2930_);
return v_res_2933_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2934_){
_start:
{
if (lean_obj_tag(v_x_2934_) == 0)
{
uint8_t v___x_2935_; 
v___x_2935_ = 1;
return v___x_2935_;
}
else
{
lean_object* v_head_2936_; lean_object* v_tail_2937_; uint8_t v___x_2938_; 
v_head_2936_ = lean_ctor_get(v_x_2934_, 0);
v_tail_2937_ = lean_ctor_get(v_x_2934_, 1);
v___x_2938_ = l_Lean_isPrivateName(v_head_2936_);
if (v___x_2938_ == 0)
{
return v___x_2938_;
}
else
{
v_x_2934_ = v_tail_2937_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2940_){
_start:
{
uint8_t v_res_2941_; lean_object* v_r_2942_; 
v_res_2941_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2940_);
lean_dec(v_x_2940_);
v_r_2942_ = lean_box(v_res_2941_);
return v_r_2942_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2948_; lean_object* v___x_2949_; 
v___x_2948_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2949_ = l_Lean_stringToMessageData(v___x_2948_);
return v___x_2949_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; 
v___x_2951_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2952_ = l_Lean_stringToMessageData(v___x_2951_);
return v___x_2952_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2954_; lean_object* v___x_2955_; 
v___x_2954_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2955_ = l_Lean_stringToMessageData(v___x_2954_);
return v___x_2955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2956_, uint8_t v_hasTrace_2957_, uint8_t v___x_2958_, lean_object* v___x_2959_, lean_object* v_cls_2960_, lean_object* v___x_2961_, lean_object* v_____x_2962_, lean_object* v_exportedInfo_x3f_2963_, lean_object* v___y_2964_, lean_object* v___y_2965_){
_start:
{
lean_object* v___y_2968_; lean_object* v___y_2969_; lean_object* v_a_2970_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v_a_2983_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___y_2999_; lean_object* v___y_3000_; lean_object* v___y_3001_; lean_object* v___y_3002_; lean_object* v___y_3003_; lean_object* v_snd_3067_; lean_object* v_fst_3068_; lean_object* v___x_3070_; uint8_t v_isShared_3071_; uint8_t v_isSharedCheck_3198_; 
v_snd_3067_ = lean_ctor_get(v_____x_2962_, 1);
v_fst_3068_ = lean_ctor_get(v_____x_2962_, 0);
v_isSharedCheck_3198_ = !lean_is_exclusive(v_____x_2962_);
if (v_isSharedCheck_3198_ == 0)
{
v___x_3070_ = v_____x_2962_;
v_isShared_3071_ = v_isSharedCheck_3198_;
goto v_resetjp_3069_;
}
else
{
lean_inc(v_snd_3067_);
lean_inc(v_fst_3068_);
lean_dec(v_____x_2962_);
v___x_3070_ = lean_box(0);
v_isShared_3071_ = v_isSharedCheck_3198_;
goto v_resetjp_3069_;
}
v___jp_2967_:
{
lean_object* v___x_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
v___x_2971_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2969_, v___y_2968_);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v___x_2971_, 0);
lean_dec(v_unused_2979_);
v___x_2973_ = v___x_2971_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_dec(v___x_2971_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
lean_ctor_set_tag(v___x_2973_, 1);
lean_ctor_set(v___x_2973_, 0, v_a_2970_);
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2970_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
v___jp_2980_:
{
lean_object* v___x_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
v___x_2984_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2982_, v___y_2981_);
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
lean_ctor_set(v___x_2986_, 0, v_a_2983_);
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v___x_3004_; 
lean_inc_ref(v___y_3001_);
v___x_3004_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3002_, v___y_3001_, v___y_2999_, v___y_3003_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v___x_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref_known(v___x_3004_, 1);
lean_inc_ref(v___y_3000_);
v___x_3005_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3000_, v___y_2998_);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3005_);
if (v_isSharedCheck_3052_ == 0)
{
lean_object* v_unused_3053_; 
v_unused_3053_ = lean_ctor_get(v___x_3005_, 0);
lean_dec(v_unused_3053_);
v___x_3007_ = v___x_3005_;
v_isShared_3008_ = v_isSharedCheck_3052_;
goto v_resetjp_3006_;
}
else
{
lean_dec(v___x_3005_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3052_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v_toCold_3009_; lean_object* v_options_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_toCold_3009_ = lean_ctor_get(v___y_2997_, 0);
v_options_3010_ = lean_ctor_get(v_toCold_3009_, 2);
v___x_3011_ = l_Lean_Elab_async;
v___x_3012_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
lean_object* v___x_3013_; lean_object* v_r_3014_; 
lean_del_object(v___x_3007_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2994_);
v___x_3013_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3001_, v___y_2998_);
lean_dec_ref(v___x_3013_);
v_r_3014_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2956_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v_r_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3024_; 
v_a_3015_ = lean_ctor_get(v_r_3014_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v_r_3014_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3017_ = v_r_3014_;
v_isShared_3018_ = v_isSharedCheck_3024_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v_r_3014_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3024_;
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
lean_object* v_reuseFailAlloc_3023_; 
v_reuseFailAlloc_3023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3023_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; 
v___x_3021_ = lean_apply_2(v___y_2995_, v___x_3020_, lean_box(0));
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_dec_ref_known(v___x_3021_, 1);
v___y_2981_ = v___y_2998_;
v___y_2982_ = v___y_3000_;
v_a_2983_ = v_a_3015_;
goto v___jp_2980_;
}
else
{
lean_object* v_a_3022_; 
lean_dec(v_a_3015_);
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___y_2968_ = v___y_2998_;
v___y_2969_ = v___y_3000_;
v_a_2970_ = v_a_3022_;
goto v___jp_2967_;
}
}
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v_a_3025_ = lean_ctor_get(v_r_3014_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v_r_3014_, 1);
v___x_3026_ = lean_box(0);
v___x_3027_ = lean_apply_2(v___y_2995_, v___x_3026_, lean_box(0));
if (lean_obj_tag(v___x_3027_) == 0)
{
lean_dec_ref_known(v___x_3027_, 1);
v___y_2968_ = v___y_2998_;
v___y_2969_ = v___y_3000_;
v_a_2970_ = v_a_3025_;
goto v___jp_2967_;
}
else
{
lean_object* v_a_3028_; 
lean_dec(v_a_3025_);
v_a_3028_ = lean_ctor_get(v___x_3027_, 0);
lean_inc(v_a_3028_);
lean_dec_ref_known(v___x_3027_, 1);
v___y_2968_ = v___y_2998_;
v___y_2969_ = v___y_3000_;
v_a_2970_ = v_a_3028_;
goto v___jp_2967_;
}
}
}
else
{
lean_object* v___x_3029_; lean_object* v___x_3031_; 
lean_dec_ref(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v___y_2995_);
lean_dec(v_decl_2956_);
v___x_3029_ = l_IO_CancelToken_new();
if (v_isShared_3008_ == 0)
{
lean_ctor_set_tag(v___x_3007_, 1);
lean_ctor_set(v___x_3007_, 0, v___x_3029_);
v___x_3031_ = v___x_3007_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; 
v___x_3032_ = lean_unsigned_to_nat(0u);
v___x_3033_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3034_ = l_Lean_Name_toString(v___x_3033_, v_hasTrace_2957_);
lean_inc_ref(v___x_3031_);
v___x_3035_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2994_, v___x_3031_, v___x_3034_, v___y_2997_, v___y_2998_);
if (lean_obj_tag(v___x_3035_) == 0)
{
lean_object* v_a_3036_; lean_object* v_checked_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; 
v_a_3036_ = lean_ctor_get(v___x_3035_, 0);
lean_inc(v_a_3036_);
lean_dec_ref_known(v___x_3035_, 1);
v_checked_3037_ = lean_ctor_get(v___y_2996_, 2);
lean_inc_ref(v_checked_3037_);
lean_dec_ref(v___y_2996_);
v___x_3038_ = lean_io_map_task(v_a_3036_, v_checked_3037_, v___x_3032_, v___x_2958_);
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_box(2);
v___x_3041_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
lean_ctor_set(v___x_3041_, 2, v___x_3031_);
lean_ctor_set(v___x_3041_, 3, v___x_3038_);
v___x_3042_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3041_, v___y_2998_);
return v___x_3042_;
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref(v___x_3031_);
lean_dec_ref(v___y_2996_);
v_a_3043_ = lean_ctor_get(v___x_3035_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3035_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3035_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3066_; 
lean_dec_ref(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec_ref(v___y_2996_);
lean_dec_ref(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v_decl_2956_);
v_a_3054_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_3056_ = v___x_3004_;
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3004_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3066_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v_ref_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3064_; 
v_ref_3058_ = lean_ctor_get(v___y_2997_, 2);
v___x_3059_ = lean_io_error_to_string(v_a_3054_);
v___x_3060_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3059_);
v___x_3061_ = l_Lean_MessageData_ofFormat(v___x_3060_);
lean_inc(v_ref_3058_);
v___x_3062_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3062_, 0, v_ref_3058_);
lean_ctor_set(v___x_3062_, 1, v___x_3061_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3062_);
v___x_3064_ = v___x_3056_;
goto v_reusejp_3063_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
v___x_3064_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3063_;
}
v_reusejp_3063_:
{
return v___x_3064_;
}
}
}
}
v_resetjp_3069_:
{
lean_object* v_fst_3072_; lean_object* v_snd_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3197_; 
v_fst_3072_ = lean_ctor_get(v_snd_3067_, 0);
v_snd_3073_ = lean_ctor_get(v_snd_3067_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v_snd_3067_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3075_ = v_snd_3067_;
v_isShared_3076_ = v_isSharedCheck_3197_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_snd_3073_);
lean_inc(v_fst_3072_);
lean_dec(v_snd_3067_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3197_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___y_3078_; lean_object* v___y_3079_; lean_object* v___y_3080_; lean_object* v___y_3081_; lean_object* v___y_3082_; lean_object* v___y_3083_; lean_object* v___y_3084_; lean_object* v_exportedInfo_x3f_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3125_; lean_object* v___y_3126_; lean_object* v___y_3129_; lean_object* v___y_3130_; lean_object* v___y_3152_; lean_object* v___y_3153_; lean_object* v___x_3187_; lean_object* v_env_3188_; uint8_t v___x_3189_; 
v___x_3187_ = lean_st_ref_get(v___y_2965_);
v_env_3188_ = lean_ctor_get(v___x_3187_, 0);
lean_inc_ref(v_env_3188_);
lean_dec(v___x_3187_);
v___x_3189_ = l_Lean_Environment_containsOnBranch(v_env_3188_, v_fst_3068_);
lean_dec_ref(v_env_3188_);
if (v___x_3189_ == 0)
{
lean_del_object(v___x_3070_);
v___y_3152_ = v___y_2964_;
v___y_3153_ = v___y_2965_;
goto v___jp_3151_;
}
else
{
lean_object* v___x_3190_; lean_object* v_env_3191_; lean_object* v___x_3192_; lean_object* v___x_3194_; 
lean_del_object(v___x_3075_);
lean_dec(v_snd_3073_);
lean_dec(v_fst_3072_);
lean_dec(v_exportedInfo_x3f_2963_);
lean_dec(v___x_2961_);
lean_dec(v_cls_2960_);
lean_dec_ref(v___x_2959_);
lean_dec(v_decl_2956_);
v___x_3190_ = lean_st_ref_get(v___y_2965_);
v_env_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc_ref(v_env_3191_);
lean_dec(v___x_3190_);
v___x_3192_ = lean_elab_environment_to_kernel_env(v_env_3191_);
if (v_isShared_3071_ == 0)
{
lean_ctor_set_tag(v___x_3070_, 1);
lean_ctor_set(v___x_3070_, 1, v_fst_3068_);
lean_ctor_set(v___x_3070_, 0, v___x_3192_);
v___x_3194_ = v___x_3070_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_fst_3068_);
v___x_3194_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3194_, v___y_2964_, v___y_2965_);
return v___x_3195_;
}
}
v___jp_3077_:
{
uint8_t v___x_3085_; lean_object* v___x_3086_; 
v___x_3085_ = lean_unbox(v_snd_3073_);
lean_dec(v_snd_3073_);
lean_inc_ref(v___y_3079_);
v___x_3086_ = l_Lean_Environment_addConstAsync(v___y_3079_, v_fst_3068_, v___x_3085_, v___y_3084_, v___x_2958_, v_hasTrace_2957_);
if (lean_obj_tag(v___x_3086_) == 0)
{
lean_object* v_a_3087_; lean_object* v_mainEnv_3088_; lean_object* v_asyncEnv_3089_; lean_object* v___f_3090_; lean_object* v___f_3091_; lean_object* v___x_3092_; 
lean_del_object(v___x_3075_);
v_a_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_n(v_a_3087_, 3);
lean_dec_ref_known(v___x_3086_, 1);
v_mainEnv_3088_ = lean_ctor_get(v_a_3087_, 0);
lean_inc_ref(v_mainEnv_3088_);
v_asyncEnv_3089_ = lean_ctor_get(v_a_3087_, 1);
lean_inc_ref_n(v_asyncEnv_3089_, 2);
lean_inc_ref(v___y_3078_);
lean_inc(v___y_3080_);
v___f_3090_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3090_, 0, v___y_3080_);
lean_closure_set(v___f_3090_, 1, v_a_3087_);
lean_closure_set(v___f_3090_, 2, v___y_3078_);
lean_inc(v_decl_2956_);
v___f_3091_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3091_, 0, v_asyncEnv_3089_);
lean_closure_set(v___f_3091_, 1, v_a_3087_);
lean_closure_set(v___f_3091_, 2, v_decl_2956_);
v___x_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3092_, 0, v_fst_3072_);
if (lean_obj_tag(v___y_3081_) == 0)
{
lean_inc_ref(v___x_3092_);
v___y_2994_ = v___f_3091_;
v___y_2995_ = v___f_3090_;
v___y_2996_ = v___y_3079_;
v___y_2997_ = v___y_3082_;
v___y_2998_ = v___y_3083_;
v___y_2999_ = v___x_3092_;
v___y_3000_ = v_mainEnv_3088_;
v___y_3001_ = v_asyncEnv_3089_;
v___y_3002_ = v_a_3087_;
v___y_3003_ = v___x_3092_;
goto v___jp_2993_;
}
else
{
v___y_2994_ = v___f_3091_;
v___y_2995_ = v___f_3090_;
v___y_2996_ = v___y_3079_;
v___y_2997_ = v___y_3082_;
v___y_2998_ = v___y_3083_;
v___y_2999_ = v___x_3092_;
v___y_3000_ = v_mainEnv_3088_;
v___y_3001_ = v_asyncEnv_3089_;
v___y_3002_ = v_a_3087_;
v___y_3003_ = v___y_3081_;
goto v___jp_2993_;
}
}
else
{
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3107_; 
lean_dec(v___y_3081_);
lean_dec_ref(v___y_3079_);
lean_dec(v_fst_3072_);
lean_dec(v_decl_2956_);
v_a_3093_ = lean_ctor_get(v___x_3086_, 0);
v_isSharedCheck_3107_ = !lean_is_exclusive(v___x_3086_);
if (v_isSharedCheck_3107_ == 0)
{
v___x_3095_ = v___x_3086_;
v_isShared_3096_ = v_isSharedCheck_3107_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3086_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3107_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v_ref_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3102_; 
v_ref_3097_ = lean_ctor_get(v___y_3082_, 2);
v___x_3098_ = lean_io_error_to_string(v_a_3093_);
v___x_3099_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
v___x_3100_ = l_Lean_MessageData_ofFormat(v___x_3099_);
lean_inc(v_ref_3097_);
if (v_isShared_3076_ == 0)
{
lean_ctor_set(v___x_3075_, 1, v___x_3100_);
lean_ctor_set(v___x_3075_, 0, v_ref_3097_);
v___x_3102_ = v___x_3075_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3106_; 
v_reuseFailAlloc_3106_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3106_, 0, v_ref_3097_);
lean_ctor_set(v_reuseFailAlloc_3106_, 1, v___x_3100_);
v___x_3102_ = v_reuseFailAlloc_3106_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
lean_object* v___x_3104_; 
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3102_);
v___x_3104_ = v___x_3095_;
goto v_reusejp_3103_;
}
else
{
lean_object* v_reuseFailAlloc_3105_; 
v_reuseFailAlloc_3105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3105_, 0, v___x_3102_);
v___x_3104_ = v_reuseFailAlloc_3105_;
goto v_reusejp_3103_;
}
v_reusejp_3103_:
{
return v___x_3104_;
}
}
}
}
}
v___jp_3108_:
{
lean_object* v___x_3112_; 
v___x_3112_ = lean_st_ref_get(v___y_3111_);
if (lean_obj_tag(v_exportedInfo_x3f_3109_) == 0)
{
lean_object* v_env_3113_; lean_object* v___x_3114_; 
v_env_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_ref(v_env_3113_);
lean_dec(v___x_3112_);
v___x_3114_ = lean_box(0);
v___y_3078_ = v___y_3110_;
v___y_3079_ = v_env_3113_;
v___y_3080_ = v___y_3111_;
v___y_3081_ = v_exportedInfo_x3f_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___x_3114_;
goto v___jp_3077_;
}
else
{
lean_object* v_env_3115_; lean_object* v_val_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; 
v_env_3115_ = lean_ctor_get(v___x_3112_, 0);
lean_inc_ref(v_env_3115_);
lean_dec(v___x_3112_);
v_val_3116_ = lean_ctor_get(v_exportedInfo_x3f_3109_, 0);
v___x_3117_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3116_);
v___x_3118_ = lean_box(v___x_3117_);
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
v___y_3078_ = v___y_3110_;
v___y_3079_ = v_env_3115_;
v___y_3080_ = v___y_3111_;
v___y_3081_ = v_exportedInfo_x3f_3109_;
v___y_3082_ = v___y_3110_;
v___y_3083_ = v___y_3111_;
v___y_3084_ = v___x_3119_;
goto v___jp_3077_;
}
}
v___jp_3120_:
{
lean_object* v___x_3123_; 
lean_inc(v_fst_3072_);
v___x_3123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3123_, 0, v_fst_3072_);
v_exportedInfo_x3f_3109_ = v___x_3123_;
v___y_3110_ = v___y_3121_;
v___y_3111_ = v___y_3122_;
goto v___jp_3108_;
}
v___jp_3124_:
{
lean_object* v___x_3127_; 
lean_inc(v_fst_3072_);
v___x_3127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3127_, 0, v_fst_3072_);
v_exportedInfo_x3f_3109_ = v___x_3127_;
v___y_3110_ = v___y_3125_;
v___y_3111_ = v___y_3126_;
goto v___jp_3108_;
}
v___jp_3128_:
{
lean_object* v___x_3131_; lean_object* v_env_3132_; lean_object* v_nextMacroScope_3133_; lean_object* v_ngen_3134_; lean_object* v_auxDeclNGen_3135_; lean_object* v_traceState_3136_; lean_object* v_messages_3137_; lean_object* v_infoState_3138_; lean_object* v_snapshotTasks_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3149_; 
v___x_3131_ = lean_st_ref_take(v___y_3129_);
v_env_3132_ = lean_ctor_get(v___x_3131_, 0);
v_nextMacroScope_3133_ = lean_ctor_get(v___x_3131_, 1);
v_ngen_3134_ = lean_ctor_get(v___x_3131_, 2);
v_auxDeclNGen_3135_ = lean_ctor_get(v___x_3131_, 3);
v_traceState_3136_ = lean_ctor_get(v___x_3131_, 4);
v_messages_3137_ = lean_ctor_get(v___x_3131_, 6);
v_infoState_3138_ = lean_ctor_get(v___x_3131_, 7);
v_snapshotTasks_3139_ = lean_ctor_get(v___x_3131_, 8);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3149_ == 0)
{
lean_object* v_unused_3150_; 
v_unused_3150_ = lean_ctor_get(v___x_3131_, 5);
lean_dec(v_unused_3150_);
v___x_3141_ = v___x_3131_;
v_isShared_3142_ = v_isSharedCheck_3149_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_snapshotTasks_3139_);
lean_inc(v_infoState_3138_);
lean_inc(v_messages_3137_);
lean_inc(v_traceState_3136_);
lean_inc(v_auxDeclNGen_3135_);
lean_inc(v_ngen_3134_);
lean_inc(v_nextMacroScope_3133_);
lean_inc(v_env_3132_);
lean_dec(v___x_3131_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3149_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3146_; 
v___x_3143_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3073_);
lean_inc(v_fst_3068_);
v___x_3144_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3143_, v_env_3132_, v_fst_3068_, v_snd_3073_);
if (v_isShared_3142_ == 0)
{
lean_ctor_set(v___x_3141_, 5, v___x_2959_);
lean_ctor_set(v___x_3141_, 0, v___x_3144_);
v___x_3146_ = v___x_3141_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v___x_3144_);
lean_ctor_set(v_reuseFailAlloc_3148_, 1, v_nextMacroScope_3133_);
lean_ctor_set(v_reuseFailAlloc_3148_, 2, v_ngen_3134_);
lean_ctor_set(v_reuseFailAlloc_3148_, 3, v_auxDeclNGen_3135_);
lean_ctor_set(v_reuseFailAlloc_3148_, 4, v_traceState_3136_);
lean_ctor_set(v_reuseFailAlloc_3148_, 5, v___x_2959_);
lean_ctor_set(v_reuseFailAlloc_3148_, 6, v_messages_3137_);
lean_ctor_set(v_reuseFailAlloc_3148_, 7, v_infoState_3138_);
lean_ctor_set(v_reuseFailAlloc_3148_, 8, v_snapshotTasks_3139_);
v___x_3146_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
lean_object* v___x_3147_; 
v___x_3147_ = lean_st_ref_put(v___y_3129_, v___x_3146_);
v_exportedInfo_x3f_3109_ = v_exportedInfo_x3f_2963_;
v___y_3110_ = v___y_3130_;
v___y_3111_ = v___y_3129_;
goto v___jp_3108_;
}
}
}
v___jp_3151_:
{
lean_object* v___x_3154_; uint8_t v___x_3155_; 
lean_inc(v_decl_2956_);
v___x_3154_ = l_Lean_Declaration_getTopLevelNames(v_decl_2956_);
v___x_3155_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3154_);
lean_dec(v___x_3154_);
if (v___x_3155_ == 0)
{
lean_dec(v___x_2961_);
if (lean_obj_tag(v_exportedInfo_x3f_2963_) == 0)
{
if (v___x_3155_ == 0)
{
lean_object* v_toCold_3156_; lean_object* v_options_3157_; uint8_t v_hasTrace_3158_; 
lean_dec_ref(v___x_2959_);
v_toCold_3156_ = lean_ctor_get(v___y_3152_, 0);
v_options_3157_ = lean_ctor_get(v_toCold_3156_, 2);
v_hasTrace_3158_ = lean_ctor_get_uint8(v_options_3157_, sizeof(void*)*1);
if (v_hasTrace_3158_ == 0)
{
lean_dec(v_cls_2960_);
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
goto v___jp_3120_;
}
else
{
lean_object* v_inheritedTraceOptions_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_inheritedTraceOptions_3159_ = lean_ctor_get(v_toCold_3156_, 11);
v___x_3160_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2960_);
v___x_3161_ = l_Lean_Name_append(v___x_3160_, v_cls_2960_);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3159_, v_options_3157_, v___x_3161_);
lean_dec(v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec(v_cls_2960_);
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
goto v___jp_3120_;
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3164_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2960_, v___x_3163_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_dec_ref_known(v___x_3164_, 1);
v___y_3121_ = v___y_3152_;
v___y_3122_ = v___y_3153_;
goto v___jp_3120_;
}
else
{
lean_del_object(v___x_3075_);
lean_dec(v_snd_3073_);
lean_dec(v_fst_3072_);
lean_dec(v_fst_3068_);
lean_dec(v_decl_2956_);
return v___x_3164_;
}
}
}
}
else
{
lean_dec(v_cls_2960_);
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3152_;
goto v___jp_3128_;
}
}
else
{
lean_dec(v_cls_2960_);
v___y_3129_ = v___y_3153_;
v___y_3130_ = v___y_3152_;
goto v___jp_3128_;
}
}
else
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v_a_3167_; uint8_t v___x_3168_; 
lean_dec(v_exportedInfo_x3f_2963_);
lean_dec_ref(v___x_2959_);
v___x_3165_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3166_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3165_, v___y_3152_);
v_a_3167_ = lean_ctor_get(v___x_3166_, 0);
lean_inc(v_a_3167_);
lean_dec_ref(v___x_3166_);
v___x_3168_ = lean_unbox(v_a_3167_);
lean_dec(v_a_3167_);
if (v___x_3168_ == 0)
{
lean_object* v_toCold_3169_; lean_object* v_options_3170_; uint8_t v_hasTrace_3171_; 
v_toCold_3169_ = lean_ctor_get(v___y_3152_, 0);
v_options_3170_ = lean_ctor_get(v_toCold_3169_, 2);
v_hasTrace_3171_ = lean_ctor_get_uint8(v_options_3170_, sizeof(void*)*1);
if (v_hasTrace_3171_ == 0)
{
lean_dec(v_cls_2960_);
v_exportedInfo_x3f_3109_ = v___x_2961_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
goto v___jp_3108_;
}
else
{
lean_object* v_inheritedTraceOptions_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; uint8_t v___x_3175_; 
v_inheritedTraceOptions_3172_ = lean_ctor_get(v_toCold_3169_, 11);
v___x_3173_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2960_);
v___x_3174_ = l_Lean_Name_append(v___x_3173_, v_cls_2960_);
v___x_3175_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3172_, v_options_3170_, v___x_3174_);
lean_dec(v___x_3174_);
if (v___x_3175_ == 0)
{
lean_dec(v_cls_2960_);
v_exportedInfo_x3f_3109_ = v___x_2961_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
goto v___jp_3108_;
}
else
{
lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3176_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3177_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2960_, v___x_3176_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_dec_ref_known(v___x_3177_, 1);
v_exportedInfo_x3f_3109_ = v___x_2961_;
v___y_3110_ = v___y_3152_;
v___y_3111_ = v___y_3153_;
goto v___jp_3108_;
}
else
{
lean_del_object(v___x_3075_);
lean_dec(v_snd_3073_);
lean_dec(v_fst_3072_);
lean_dec(v_fst_3068_);
lean_dec(v___x_2961_);
lean_dec(v_decl_2956_);
return v___x_3177_;
}
}
}
}
else
{
lean_object* v_toCold_3178_; lean_object* v_options_3179_; uint8_t v_hasTrace_3180_; 
lean_dec(v___x_2961_);
v_toCold_3178_ = lean_ctor_get(v___y_3152_, 0);
v_options_3179_ = lean_ctor_get(v_toCold_3178_, 2);
v_hasTrace_3180_ = lean_ctor_get_uint8(v_options_3179_, sizeof(void*)*1);
if (v_hasTrace_3180_ == 0)
{
lean_dec(v_cls_2960_);
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
goto v___jp_3124_;
}
else
{
lean_object* v_inheritedTraceOptions_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___x_3184_; 
v_inheritedTraceOptions_3181_ = lean_ctor_get(v_toCold_3178_, 11);
v___x_3182_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2960_);
v___x_3183_ = l_Lean_Name_append(v___x_3182_, v_cls_2960_);
v___x_3184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3181_, v_options_3179_, v___x_3183_);
lean_dec(v___x_3183_);
if (v___x_3184_ == 0)
{
lean_dec(v_cls_2960_);
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
goto v___jp_3124_;
}
else
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3186_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2960_, v___x_3185_, v___y_3152_, v___y_3153_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_dec_ref_known(v___x_3186_, 1);
v___y_3125_ = v___y_3152_;
v___y_3126_ = v___y_3153_;
goto v___jp_3124_;
}
else
{
lean_del_object(v___x_3075_);
lean_dec(v_snd_3073_);
lean_dec(v_fst_3072_);
lean_dec(v_fst_3068_);
lean_dec(v_decl_2956_);
return v___x_3186_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3199_, lean_object* v_hasTrace_3200_, lean_object* v___x_3201_, lean_object* v___x_3202_, lean_object* v_cls_3203_, lean_object* v___x_3204_, lean_object* v_____x_3205_, lean_object* v_exportedInfo_x3f_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_){
_start:
{
uint8_t v_hasTrace_boxed_3210_; uint8_t v___x_53058__boxed_3211_; lean_object* v_res_3212_; 
v_hasTrace_boxed_3210_ = lean_unbox(v_hasTrace_3200_);
v___x_53058__boxed_3211_ = lean_unbox(v___x_3201_);
v_res_3212_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3199_, v_hasTrace_boxed_3210_, v___x_53058__boxed_3211_, v___x_3202_, v_cls_3203_, v___x_3204_, v_____x_3205_, v_exportedInfo_x3f_3206_, v___y_3207_, v___y_3208_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3212_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3215_ = l_Lean_stringToMessageData(v___x_3214_);
return v___x_3215_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3218_ = l_Lean_stringToMessageData(v___x_3217_);
return v___x_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3219_, uint8_t v___x_3220_, lean_object* v_cls_3221_, lean_object* v___x_3222_, uint8_t v_forceExpose_3223_, lean_object* v_defn_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v_exportedInfo_x3f_3229_; lean_object* v___y_3230_; lean_object* v___y_3231_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; uint8_t v___y_3244_; uint8_t v___y_3249_; lean_object* v___y_3250_; lean_object* v___y_3251_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___y_3259_; lean_object* v_env_3275_; lean_object* v_env_3276_; 
v___x_3256_ = lean_st_ref_get(v___y_3226_);
v___x_3257_ = lean_st_ref_get(v___y_3226_);
v_env_3275_ = lean_ctor_get(v___x_3256_, 0);
lean_inc_ref(v_env_3275_);
lean_dec(v___x_3256_);
v_env_3276_ = lean_ctor_get(v___x_3257_, 0);
lean_inc_ref(v_env_3276_);
lean_dec(v___x_3257_);
if (v_forceExpose_3223_ == 0)
{
goto v___jp_3277_;
}
else
{
if (v___x_3220_ == 0)
{
lean_dec_ref(v_env_3276_);
lean_dec_ref(v_env_3275_);
lean_dec(v_cls_3221_);
v_exportedInfo_x3f_3229_ = v___x_3222_;
v___y_3230_ = v___y_3225_;
v___y_3231_ = v___y_3226_;
goto v___jp_3228_;
}
else
{
goto v___jp_3277_;
}
}
v___jp_3228_:
{
lean_object* v_toConstantVal_3232_; lean_object* v_name_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; 
v_toConstantVal_3232_ = lean_ctor_get(v_defn_3224_, 0);
v_name_3233_ = lean_ctor_get(v_toConstantVal_3232_, 0);
lean_inc(v_name_3233_);
v___x_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3234_, 0, v_defn_3224_);
v___x_3235_ = 0;
v___x_3236_ = lean_box(v___x_3235_);
v___x_3237_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3237_, 0, v___x_3234_);
lean_ctor_set(v___x_3237_, 1, v___x_3236_);
v___x_3238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3238_, 0, v_name_3233_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
lean_inc(v___y_3231_);
lean_inc_ref(v___y_3230_);
v___x_3239_ = lean_apply_5(v___f_3219_, v___x_3238_, v_exportedInfo_x3f_3229_, v___y_3230_, v___y_3231_, lean_box(0));
return v___x_3239_;
}
v___jp_3240_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3245_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3245_, 0, v___y_3243_);
lean_ctor_set_uint8(v___x_3245_, sizeof(void*)*1, v___y_3244_);
v___x_3246_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
v___x_3247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3246_);
v_exportedInfo_x3f_3229_ = v___x_3247_;
v___y_3230_ = v___y_3242_;
v___y_3231_ = v___y_3241_;
goto v___jp_3228_;
}
v___jp_3248_:
{
lean_object* v_toConstantVal_3252_; uint8_t v_safety_3253_; uint8_t v___x_3254_; uint8_t v___x_3255_; 
v_toConstantVal_3252_ = lean_ctor_get(v_defn_3224_, 0);
v_safety_3253_ = lean_ctor_get_uint8(v_defn_3224_, sizeof(void*)*4);
v___x_3254_ = 1;
v___x_3255_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_inc_ref(v_toConstantVal_3252_);
v___y_3241_ = v___y_3251_;
v___y_3242_ = v___y_3250_;
v___y_3243_ = v_toConstantVal_3252_;
v___y_3244_ = v___y_3249_;
goto v___jp_3240_;
}
else
{
lean_inc_ref(v_toConstantVal_3252_);
v___y_3241_ = v___y_3251_;
v___y_3242_ = v___y_3250_;
v___y_3243_ = v_toConstantVal_3252_;
v___y_3244_ = v___x_3220_;
goto v___jp_3240_;
}
}
v___jp_3258_:
{
lean_object* v_toCold_3260_; lean_object* v_options_3261_; uint8_t v_hasTrace_3262_; 
v_toCold_3260_ = lean_ctor_get(v___y_3225_, 0);
v_options_3261_ = lean_ctor_get(v_toCold_3260_, 2);
v_hasTrace_3262_ = lean_ctor_get_uint8(v_options_3261_, sizeof(void*)*1);
if (v_hasTrace_3262_ == 0)
{
lean_dec(v_cls_3221_);
v___y_3249_ = v___y_3259_;
v___y_3250_ = v___y_3225_;
v___y_3251_ = v___y_3226_;
goto v___jp_3248_;
}
else
{
lean_object* v_inheritedTraceOptions_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; 
v_inheritedTraceOptions_3263_ = lean_ctor_get(v_toCold_3260_, 11);
v___x_3264_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3221_);
v___x_3265_ = l_Lean_Name_append(v___x_3264_, v_cls_3221_);
v___x_3266_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3263_, v_options_3261_, v___x_3265_);
lean_dec(v___x_3265_);
if (v___x_3266_ == 0)
{
lean_dec(v_cls_3221_);
v___y_3249_ = v___y_3259_;
v___y_3250_ = v___y_3225_;
v___y_3251_ = v___y_3226_;
goto v___jp_3248_;
}
else
{
lean_object* v_toConstantVal_3267_; lean_object* v_name_3268_; lean_object* v___x_3269_; lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v_toConstantVal_3267_ = lean_ctor_get(v_defn_3224_, 0);
v_name_3268_ = lean_ctor_get(v_toConstantVal_3267_, 0);
v___x_3269_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3268_);
v___x_3270_ = l_Lean_MessageData_ofName(v_name_3268_);
v___x_3271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3269_);
lean_ctor_set(v___x_3271_, 1, v___x_3270_);
v___x_3272_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3271_);
lean_ctor_set(v___x_3273_, 1, v___x_3272_);
v___x_3274_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3221_, v___x_3273_, v___y_3225_, v___y_3226_);
if (lean_obj_tag(v___x_3274_) == 0)
{
lean_dec_ref_known(v___x_3274_, 1);
v___y_3249_ = v___y_3259_;
v___y_3250_ = v___y_3225_;
v___y_3251_ = v___y_3226_;
goto v___jp_3248_;
}
else
{
lean_dec_ref(v_defn_3224_);
lean_dec_ref(v___f_3219_);
return v___x_3274_;
}
}
}
}
v___jp_3277_:
{
lean_object* v___x_3278_; uint8_t v_isModule_3279_; 
v___x_3278_ = l_Lean_Environment_header(v_env_3275_);
lean_dec_ref(v_env_3275_);
v_isModule_3279_ = lean_ctor_get_uint8(v___x_3278_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3278_);
if (v_isModule_3279_ == 0)
{
lean_dec_ref(v_env_3276_);
lean_dec(v_cls_3221_);
v_exportedInfo_x3f_3229_ = v___x_3222_;
v___y_3230_ = v___y_3225_;
v___y_3231_ = v___y_3226_;
goto v___jp_3228_;
}
else
{
uint8_t v_isExporting_3280_; 
v_isExporting_3280_ = lean_ctor_get_uint8(v_env_3276_, sizeof(void*)*8);
lean_dec_ref(v_env_3276_);
if (v_isExporting_3280_ == 0)
{
lean_dec(v___x_3222_);
v___y_3259_ = v_isModule_3279_;
goto v___jp_3258_;
}
else
{
if (v___x_3220_ == 0)
{
lean_dec(v_cls_3221_);
v_exportedInfo_x3f_3229_ = v___x_3222_;
v___y_3230_ = v___y_3225_;
v___y_3231_ = v___y_3226_;
goto v___jp_3228_;
}
else
{
lean_dec(v___x_3222_);
v___y_3259_ = v___x_3220_;
goto v___jp_3258_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3281_, lean_object* v___x_3282_, lean_object* v_cls_3283_, lean_object* v___x_3284_, lean_object* v_forceExpose_3285_, lean_object* v_defn_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
uint8_t v___x_53530__boxed_3290_; uint8_t v_forceExpose_boxed_3291_; lean_object* v_res_3292_; 
v___x_53530__boxed_3290_ = lean_unbox(v___x_3282_);
v_forceExpose_boxed_3291_ = lean_unbox(v_forceExpose_3285_);
v_res_3292_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3281_, v___x_53530__boxed_3290_, v_cls_3283_, v___x_3284_, v_forceExpose_boxed_3291_, v_defn_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3293_, lean_object* v___f_3294_, lean_object* v_____r_3295_, lean_object* v_exportedInfo_x3f_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v_toConstantVal_3300_; lean_object* v_name_3301_; lean_object* v___x_3302_; uint8_t v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_toConstantVal_3300_ = lean_ctor_get(v_val_3293_, 0);
v_name_3301_ = lean_ctor_get(v_toConstantVal_3300_, 0);
lean_inc(v_name_3301_);
v___x_3302_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3302_, 0, v_val_3293_);
v___x_3303_ = 1;
v___x_3304_ = lean_box(v___x_3303_);
v___x_3305_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3305_, 0, v___x_3302_);
lean_ctor_set(v___x_3305_, 1, v___x_3304_);
v___x_3306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3306_, 0, v_name_3301_);
lean_ctor_set(v___x_3306_, 1, v___x_3305_);
lean_inc(v___y_3298_);
lean_inc_ref(v___y_3297_);
v___x_3307_ = lean_apply_5(v___f_3294_, v___x_3306_, v_exportedInfo_x3f_3296_, v___y_3297_, v___y_3298_, lean_box(0));
return v___x_3307_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3308_, lean_object* v___f_3309_, lean_object* v_____r_3310_, lean_object* v_exportedInfo_x3f_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
lean_object* v_res_3315_; 
v_res_3315_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3308_, v___f_3309_, v_____r_3310_, v_exportedInfo_x3f_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3316_, uint8_t v___x_3317_, lean_object* v___f_3318_, lean_object* v_____r_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_toConstantVal_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_toConstantVal_3323_ = lean_ctor_get(v_val_3316_, 0);
lean_inc_ref(v_toConstantVal_3323_);
v___x_3324_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3324_, 0, v_toConstantVal_3323_);
lean_ctor_set_uint8(v___x_3324_, sizeof(void*)*1, v___x_3317_);
v___x_3325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3325_, 0, v___x_3324_);
v___x_3326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3326_, 0, v___x_3325_);
v___x_3327_ = lean_box(0);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3320_);
v___x_3328_ = lean_apply_5(v___f_3318_, v___x_3327_, v___x_3326_, v___y_3320_, v___y_3321_, lean_box(0));
return v___x_3328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3329_, lean_object* v___x_3330_, lean_object* v___f_3331_, lean_object* v_____r_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
uint8_t v___x_53665__boxed_3336_; lean_object* v_res_3337_; 
v___x_53665__boxed_3336_ = lean_unbox(v___x_3330_);
v_res_3337_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3329_, v___x_53665__boxed_3336_, v___f_3331_, v_____r_3332_, v___y_3333_, v___y_3334_);
lean_dec(v___y_3334_);
lean_dec_ref(v___y_3333_);
lean_dec_ref(v_val_3329_);
return v_res_3337_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3338_, lean_object* v___f_3339_, lean_object* v_____r_3340_, lean_object* v_exportedInfo_x3f_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_toConstantVal_3345_; lean_object* v_name_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; 
v_toConstantVal_3345_ = lean_ctor_get(v_val_3338_, 0);
v_name_3346_ = lean_ctor_get(v_toConstantVal_3345_, 0);
lean_inc(v_name_3346_);
v___x_3347_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_val_3338_);
v___x_3348_ = 3;
v___x_3349_ = lean_box(v___x_3348_);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3347_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3351_, 0, v_name_3346_);
lean_ctor_set(v___x_3351_, 1, v___x_3350_);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
v___x_3352_ = lean_apply_5(v___f_3339_, v___x_3351_, v_exportedInfo_x3f_3341_, v___y_3342_, v___y_3343_, lean_box(0));
return v___x_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3353_, lean_object* v___f_3354_, lean_object* v_____r_3355_, lean_object* v_exportedInfo_x3f_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_){
_start:
{
lean_object* v_res_3360_; 
v_res_3360_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3353_, v___f_3354_, v_____r_3355_, v_exportedInfo_x3f_3356_, v___y_3357_, v___y_3358_);
lean_dec(v___y_3358_);
lean_dec_ref(v___y_3357_);
return v_res_3360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3361_, lean_object* v___f_3362_, lean_object* v_____r_3363_, lean_object* v___y_3364_, lean_object* v___y_3365_){
_start:
{
lean_object* v_toConstantVal_3367_; uint8_t v_isUnsafe_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; 
v_toConstantVal_3367_ = lean_ctor_get(v_val_3361_, 0);
v_isUnsafe_3368_ = lean_ctor_get_uint8(v_val_3361_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3367_);
v___x_3369_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3369_, 0, v_toConstantVal_3367_);
lean_ctor_set_uint8(v___x_3369_, sizeof(void*)*1, v_isUnsafe_3368_);
v___x_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3369_);
v___x_3371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3370_);
v___x_3372_ = lean_box(0);
lean_inc(v___y_3365_);
lean_inc_ref(v___y_3364_);
v___x_3373_ = lean_apply_5(v___f_3362_, v___x_3372_, v___x_3371_, v___y_3364_, v___y_3365_, lean_box(0));
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3374_, lean_object* v___f_3375_, lean_object* v_____r_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3374_, v___f_3375_, v_____r_3376_, v___y_3377_, v___y_3378_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec_ref(v_val_3374_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3381_, uint8_t v___x_3382_, lean_object* v_cls_3383_, lean_object* v___x_3384_, lean_object* v___x_3385_, lean_object* v_____x_3386_, lean_object* v_exportedInfo_x3f_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v_a_3394_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v_a_3407_; lean_object* v___y_3418_; lean_object* v___y_3419_; lean_object* v___y_3420_; lean_object* v___y_3421_; lean_object* v___y_3422_; uint8_t v___y_3423_; lean_object* v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; lean_object* v___y_3428_; lean_object* v_snd_3492_; lean_object* v_fst_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3625_; 
v_snd_3492_ = lean_ctor_get(v_____x_3386_, 1);
v_fst_3493_ = lean_ctor_get(v_____x_3386_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_____x_3386_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3495_ = v_____x_3386_;
v_isShared_3496_ = v_isSharedCheck_3625_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_snd_3492_);
lean_inc(v_fst_3493_);
lean_dec(v_____x_3386_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3625_;
goto v_resetjp_3494_;
}
v___jp_3391_:
{
lean_object* v___x_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
v___x_3395_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3392_, v___y_3393_);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3395_);
if (v_isSharedCheck_3402_ == 0)
{
lean_object* v_unused_3403_; 
v_unused_3403_ = lean_ctor_get(v___x_3395_, 0);
lean_dec(v_unused_3403_);
v___x_3397_ = v___x_3395_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_dec(v___x_3395_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
lean_ctor_set_tag(v___x_3397_, 1);
lean_ctor_set(v___x_3397_, 0, v_a_3394_);
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3394_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
v___jp_3404_:
{
lean_object* v___x_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3415_; 
v___x_3408_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3405_, v___y_3406_);
v_isSharedCheck_3415_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3415_ == 0)
{
lean_object* v_unused_3416_; 
v_unused_3416_ = lean_ctor_get(v___x_3408_, 0);
lean_dec(v_unused_3416_);
v___x_3410_ = v___x_3408_;
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
else
{
lean_dec(v___x_3408_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3415_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v___x_3413_; 
if (v_isShared_3411_ == 0)
{
lean_ctor_set(v___x_3410_, 0, v_a_3407_);
v___x_3413_ = v___x_3410_;
goto v_reusejp_3412_;
}
else
{
lean_object* v_reuseFailAlloc_3414_; 
v_reuseFailAlloc_3414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3414_, 0, v_a_3407_);
v___x_3413_ = v_reuseFailAlloc_3414_;
goto v_reusejp_3412_;
}
v_reusejp_3412_:
{
return v___x_3413_;
}
}
}
v___jp_3417_:
{
lean_object* v___x_3429_; 
lean_inc_ref(v___y_3424_);
v___x_3429_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3427_, v___y_3424_, v___y_3425_, v___y_3428_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v___x_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3477_; 
lean_dec_ref_known(v___x_3429_, 1);
lean_inc_ref(v___y_3419_);
v___x_3430_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3419_, v___y_3426_);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3430_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3430_, 0);
lean_dec(v_unused_3478_);
v___x_3432_ = v___x_3430_;
v_isShared_3433_ = v_isSharedCheck_3477_;
goto v_resetjp_3431_;
}
else
{
lean_dec(v___x_3430_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3477_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v_toCold_3434_; lean_object* v_options_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_toCold_3434_ = lean_ctor_get(v___y_3421_, 0);
v_options_3435_ = lean_ctor_get(v_toCold_3434_, 2);
v___x_3436_ = l_Lean_Elab_async;
v___x_3437_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3435_, v___x_3436_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v_r_3439_; 
lean_del_object(v___x_3432_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3418_);
v___x_3438_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3424_, v___y_3426_);
lean_dec_ref(v___x_3438_);
v_r_3439_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3381_, v___y_3421_, v___y_3426_);
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
v___x_3446_ = lean_apply_2(v___y_3420_, v___x_3445_, lean_box(0));
if (lean_obj_tag(v___x_3446_) == 0)
{
lean_dec_ref_known(v___x_3446_, 1);
v___y_3405_ = v___y_3419_;
v___y_3406_ = v___y_3426_;
v_a_3407_ = v_a_3440_;
goto v___jp_3404_;
}
else
{
lean_object* v_a_3447_; 
lean_dec(v_a_3440_);
v_a_3447_ = lean_ctor_get(v___x_3446_, 0);
lean_inc(v_a_3447_);
lean_dec_ref_known(v___x_3446_, 1);
v___y_3392_ = v___y_3419_;
v___y_3393_ = v___y_3426_;
v_a_3394_ = v_a_3447_;
goto v___jp_3391_;
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
v___x_3452_ = lean_apply_2(v___y_3420_, v___x_3451_, lean_box(0));
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_dec_ref_known(v___x_3452_, 1);
v___y_3392_ = v___y_3419_;
v___y_3393_ = v___y_3426_;
v_a_3394_ = v_a_3450_;
goto v___jp_3391_;
}
else
{
lean_object* v_a_3453_; 
lean_dec(v_a_3450_);
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___y_3392_ = v___y_3419_;
v___y_3393_ = v___y_3426_;
v_a_3394_ = v_a_3453_;
goto v___jp_3391_;
}
}
}
else
{
lean_object* v___x_3454_; lean_object* v___x_3456_; 
lean_dec_ref(v___y_3424_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec(v_decl_3381_);
v___x_3454_ = l_IO_CancelToken_new();
if (v_isShared_3433_ == 0)
{
lean_ctor_set_tag(v___x_3432_, 1);
lean_ctor_set(v___x_3432_, 0, v___x_3454_);
v___x_3456_ = v___x_3432_;
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
v___x_3458_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3459_ = l_Lean_Name_toString(v___x_3458_, v___x_3382_);
lean_inc_ref(v___x_3456_);
v___x_3460_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3422_, v___x_3456_, v___x_3459_, v___y_3421_, v___y_3426_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v_checked_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v_checked_3462_ = lean_ctor_get(v___y_3418_, 2);
lean_inc_ref(v_checked_3462_);
lean_dec_ref(v___y_3418_);
v___x_3463_ = lean_io_map_task(v_a_3461_, v_checked_3462_, v___x_3457_, v___y_3423_);
v___x_3464_ = lean_box(0);
v___x_3465_ = lean_box(2);
v___x_3466_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3464_);
lean_ctor_set(v___x_3466_, 1, v___x_3465_);
lean_ctor_set(v___x_3466_, 2, v___x_3456_);
lean_ctor_set(v___x_3466_, 3, v___x_3463_);
v___x_3467_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3466_, v___y_3426_);
return v___x_3467_;
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_dec_ref(v___x_3456_);
lean_dec_ref(v___y_3418_);
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
lean_dec_ref(v___y_3424_);
lean_dec_ref(v___y_3422_);
lean_dec_ref(v___y_3420_);
lean_dec_ref(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v_decl_3381_);
v_a_3479_ = lean_ctor_get(v___x_3429_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3429_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3481_ = v___x_3429_;
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3429_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3491_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v_ref_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; lean_object* v___x_3489_; 
v_ref_3483_ = lean_ctor_get(v___y_3421_, 2);
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
lean_object* v_fst_3497_; lean_object* v_snd_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3624_; 
v_fst_3497_ = lean_ctor_get(v_snd_3492_, 0);
v_snd_3498_ = lean_ctor_get(v_snd_3492_, 1);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_snd_3492_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3500_ = v_snd_3492_;
v_isShared_3501_ = v_isSharedCheck_3624_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_snd_3498_);
lean_inc(v_fst_3497_);
lean_dec(v_snd_3492_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3624_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___y_3503_; lean_object* v___y_3504_; lean_object* v___y_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v_exportedInfo_x3f_3535_; lean_object* v___y_3536_; lean_object* v___y_3537_; lean_object* v___y_3547_; lean_object* v___y_3548_; lean_object* v___y_3551_; lean_object* v___y_3552_; lean_object* v___y_3555_; lean_object* v___y_3556_; uint8_t v___y_3557_; lean_object* v___y_3588_; lean_object* v___y_3589_; lean_object* v___x_3614_; lean_object* v_env_3615_; uint8_t v___x_3616_; 
v___x_3614_ = lean_st_ref_get(v___y_3389_);
v_env_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc_ref(v_env_3615_);
lean_dec(v___x_3614_);
v___x_3616_ = l_Lean_Environment_containsOnBranch(v_env_3615_, v_fst_3493_);
lean_dec_ref(v_env_3615_);
if (v___x_3616_ == 0)
{
lean_del_object(v___x_3495_);
v___y_3588_ = v___y_3388_;
v___y_3589_ = v___y_3389_;
goto v___jp_3587_;
}
else
{
lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_exportedInfo_x3f_3387_);
lean_dec(v___x_3385_);
lean_dec_ref(v___x_3384_);
lean_dec(v_cls_3383_);
lean_dec(v_decl_3381_);
v___x_3617_ = lean_st_ref_get(v___y_3389_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
lean_inc_ref(v_env_3618_);
lean_dec(v___x_3617_);
v___x_3619_ = lean_elab_environment_to_kernel_env(v_env_3618_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set_tag(v___x_3495_, 1);
lean_ctor_set(v___x_3495_, 1, v_fst_3493_);
lean_ctor_set(v___x_3495_, 0, v___x_3619_);
v___x_3621_ = v___x_3495_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3619_);
lean_ctor_set(v_reuseFailAlloc_3623_, 1, v_fst_3493_);
v___x_3621_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; 
v___x_3622_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3621_, v___y_3388_, v___y_3389_);
return v___x_3622_;
}
}
v___jp_3502_:
{
uint8_t v___x_3510_; uint8_t v___x_3511_; lean_object* v___x_3512_; 
v___x_3510_ = 0;
v___x_3511_ = lean_unbox(v_snd_3498_);
lean_dec(v_snd_3498_);
lean_inc_ref(v___y_3505_);
v___x_3512_ = l_Lean_Environment_addConstAsync(v___y_3505_, v_fst_3493_, v___x_3511_, v___y_3509_, v___x_3510_, v___x_3382_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v_mainEnv_3514_; lean_object* v_asyncEnv_3515_; lean_object* v___f_3516_; lean_object* v___f_3517_; lean_object* v___x_3518_; 
lean_del_object(v___x_3500_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc_n(v_a_3513_, 3);
lean_dec_ref_known(v___x_3512_, 1);
v_mainEnv_3514_ = lean_ctor_get(v_a_3513_, 0);
lean_inc_ref(v_mainEnv_3514_);
v_asyncEnv_3515_ = lean_ctor_get(v_a_3513_, 1);
lean_inc_ref_n(v_asyncEnv_3515_, 2);
lean_inc_ref(v___y_3504_);
lean_inc(v___y_3503_);
v___f_3516_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3516_, 0, v___y_3503_);
lean_closure_set(v___f_3516_, 1, v_a_3513_);
lean_closure_set(v___f_3516_, 2, v___y_3504_);
lean_inc(v_decl_3381_);
v___f_3517_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3517_, 0, v_asyncEnv_3515_);
lean_closure_set(v___f_3517_, 1, v_a_3513_);
lean_closure_set(v___f_3517_, 2, v_decl_3381_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v_fst_3497_);
if (lean_obj_tag(v___y_3508_) == 0)
{
lean_inc_ref(v___x_3518_);
v___y_3418_ = v___y_3505_;
v___y_3419_ = v_mainEnv_3514_;
v___y_3420_ = v___f_3516_;
v___y_3421_ = v___y_3506_;
v___y_3422_ = v___f_3517_;
v___y_3423_ = v___x_3510_;
v___y_3424_ = v_asyncEnv_3515_;
v___y_3425_ = v___x_3518_;
v___y_3426_ = v___y_3507_;
v___y_3427_ = v_a_3513_;
v___y_3428_ = v___x_3518_;
goto v___jp_3417_;
}
else
{
v___y_3418_ = v___y_3505_;
v___y_3419_ = v_mainEnv_3514_;
v___y_3420_ = v___f_3516_;
v___y_3421_ = v___y_3506_;
v___y_3422_ = v___f_3517_;
v___y_3423_ = v___x_3510_;
v___y_3424_ = v_asyncEnv_3515_;
v___y_3425_ = v___x_3518_;
v___y_3426_ = v___y_3507_;
v___y_3427_ = v_a_3513_;
v___y_3428_ = v___y_3508_;
goto v___jp_3417_;
}
}
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3533_; 
lean_dec(v___y_3508_);
lean_dec_ref(v___y_3505_);
lean_dec(v_fst_3497_);
lean_dec(v_decl_3381_);
v_a_3519_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3521_ = v___x_3512_;
v_isShared_3522_ = v_isSharedCheck_3533_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3512_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3533_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v_ref_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3528_; 
v_ref_3523_ = lean_ctor_get(v___y_3506_, 2);
v___x_3524_ = lean_io_error_to_string(v_a_3519_);
v___x_3525_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3525_, 0, v___x_3524_);
v___x_3526_ = l_Lean_MessageData_ofFormat(v___x_3525_);
lean_inc(v_ref_3523_);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 1, v___x_3526_);
lean_ctor_set(v___x_3500_, 0, v_ref_3523_);
v___x_3528_ = v___x_3500_;
goto v_reusejp_3527_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_ref_3523_);
lean_ctor_set(v_reuseFailAlloc_3532_, 1, v___x_3526_);
v___x_3528_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3527_;
}
v_reusejp_3527_:
{
lean_object* v___x_3530_; 
if (v_isShared_3522_ == 0)
{
lean_ctor_set(v___x_3521_, 0, v___x_3528_);
v___x_3530_ = v___x_3521_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
v___jp_3534_:
{
lean_object* v___x_3538_; 
v___x_3538_ = lean_st_ref_get(v___y_3537_);
if (lean_obj_tag(v_exportedInfo_x3f_3535_) == 0)
{
lean_object* v_env_3539_; lean_object* v___x_3540_; 
v_env_3539_ = lean_ctor_get(v___x_3538_, 0);
lean_inc_ref(v_env_3539_);
lean_dec(v___x_3538_);
v___x_3540_ = lean_box(0);
v___y_3503_ = v___y_3537_;
v___y_3504_ = v___y_3536_;
v___y_3505_ = v_env_3539_;
v___y_3506_ = v___y_3536_;
v___y_3507_ = v___y_3537_;
v___y_3508_ = v_exportedInfo_x3f_3535_;
v___y_3509_ = v___x_3540_;
goto v___jp_3502_;
}
else
{
lean_object* v_env_3541_; lean_object* v_val_3542_; uint8_t v___x_3543_; lean_object* v___x_3544_; lean_object* v___x_3545_; 
v_env_3541_ = lean_ctor_get(v___x_3538_, 0);
lean_inc_ref(v_env_3541_);
lean_dec(v___x_3538_);
v_val_3542_ = lean_ctor_get(v_exportedInfo_x3f_3535_, 0);
v___x_3543_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3542_);
v___x_3544_ = lean_box(v___x_3543_);
v___x_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3545_, 0, v___x_3544_);
v___y_3503_ = v___y_3537_;
v___y_3504_ = v___y_3536_;
v___y_3505_ = v_env_3541_;
v___y_3506_ = v___y_3536_;
v___y_3507_ = v___y_3537_;
v___y_3508_ = v_exportedInfo_x3f_3535_;
v___y_3509_ = v___x_3545_;
goto v___jp_3502_;
}
}
v___jp_3546_:
{
lean_object* v___x_3549_; 
lean_inc(v_fst_3497_);
v___x_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3549_, 0, v_fst_3497_);
v_exportedInfo_x3f_3535_ = v___x_3549_;
v___y_3536_ = v___y_3547_;
v___y_3537_ = v___y_3548_;
goto v___jp_3534_;
}
v___jp_3550_:
{
lean_object* v___x_3553_; 
lean_inc(v_fst_3497_);
v___x_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3553_, 0, v_fst_3497_);
v_exportedInfo_x3f_3535_ = v___x_3553_;
v___y_3536_ = v___y_3551_;
v___y_3537_ = v___y_3552_;
goto v___jp_3534_;
}
v___jp_3554_:
{
if (v___y_3557_ == 0)
{
lean_object* v_toCold_3558_; lean_object* v_options_3559_; uint8_t v_hasTrace_3560_; 
lean_dec(v_exportedInfo_x3f_3387_);
lean_dec_ref(v___x_3384_);
v_toCold_3558_ = lean_ctor_get(v___y_3556_, 0);
v_options_3559_ = lean_ctor_get(v_toCold_3558_, 2);
v_hasTrace_3560_ = lean_ctor_get_uint8(v_options_3559_, sizeof(void*)*1);
if (v_hasTrace_3560_ == 0)
{
lean_dec(v_cls_3383_);
v___y_3547_ = v___y_3556_;
v___y_3548_ = v___y_3555_;
goto v___jp_3546_;
}
else
{
lean_object* v_inheritedTraceOptions_3561_; lean_object* v___x_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_inheritedTraceOptions_3561_ = lean_ctor_get(v_toCold_3558_, 11);
v___x_3562_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3383_);
v___x_3563_ = l_Lean_Name_append(v___x_3562_, v_cls_3383_);
v___x_3564_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3561_, v_options_3559_, v___x_3563_);
lean_dec(v___x_3563_);
if (v___x_3564_ == 0)
{
lean_dec(v_cls_3383_);
v___y_3547_ = v___y_3556_;
v___y_3548_ = v___y_3555_;
goto v___jp_3546_;
}
else
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3566_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3383_, v___x_3565_, v___y_3556_, v___y_3555_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_dec_ref_known(v___x_3566_, 1);
v___y_3547_ = v___y_3556_;
v___y_3548_ = v___y_3555_;
goto v___jp_3546_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v_decl_3381_);
return v___x_3566_;
}
}
}
}
else
{
lean_object* v___x_3567_; lean_object* v_env_3568_; lean_object* v_nextMacroScope_3569_; lean_object* v_ngen_3570_; lean_object* v_auxDeclNGen_3571_; lean_object* v_traceState_3572_; lean_object* v_messages_3573_; lean_object* v_infoState_3574_; lean_object* v_snapshotTasks_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_cls_3383_);
v___x_3567_ = lean_st_ref_take(v___y_3555_);
v_env_3568_ = lean_ctor_get(v___x_3567_, 0);
v_nextMacroScope_3569_ = lean_ctor_get(v___x_3567_, 1);
v_ngen_3570_ = lean_ctor_get(v___x_3567_, 2);
v_auxDeclNGen_3571_ = lean_ctor_get(v___x_3567_, 3);
v_traceState_3572_ = lean_ctor_get(v___x_3567_, 4);
v_messages_3573_ = lean_ctor_get(v___x_3567_, 6);
v_infoState_3574_ = lean_ctor_get(v___x_3567_, 7);
v_snapshotTasks_3575_ = lean_ctor_get(v___x_3567_, 8);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3585_ == 0)
{
lean_object* v_unused_3586_; 
v_unused_3586_ = lean_ctor_get(v___x_3567_, 5);
lean_dec(v_unused_3586_);
v___x_3577_ = v___x_3567_;
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_snapshotTasks_3575_);
lean_inc(v_infoState_3574_);
lean_inc(v_messages_3573_);
lean_inc(v_traceState_3572_);
lean_inc(v_auxDeclNGen_3571_);
lean_inc(v_ngen_3570_);
lean_inc(v_nextMacroScope_3569_);
lean_inc(v_env_3568_);
lean_dec(v___x_3567_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3585_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
v___x_3579_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3498_);
lean_inc(v_fst_3493_);
v___x_3580_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3579_, v_env_3568_, v_fst_3493_, v_snd_3498_);
if (v_isShared_3578_ == 0)
{
lean_ctor_set(v___x_3577_, 5, v___x_3384_);
lean_ctor_set(v___x_3577_, 0, v___x_3580_);
v___x_3582_ = v___x_3577_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_nextMacroScope_3569_);
lean_ctor_set(v_reuseFailAlloc_3584_, 2, v_ngen_3570_);
lean_ctor_set(v_reuseFailAlloc_3584_, 3, v_auxDeclNGen_3571_);
lean_ctor_set(v_reuseFailAlloc_3584_, 4, v_traceState_3572_);
lean_ctor_set(v_reuseFailAlloc_3584_, 5, v___x_3384_);
lean_ctor_set(v_reuseFailAlloc_3584_, 6, v_messages_3573_);
lean_ctor_set(v_reuseFailAlloc_3584_, 7, v_infoState_3574_);
lean_ctor_set(v_reuseFailAlloc_3584_, 8, v_snapshotTasks_3575_);
v___x_3582_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; 
v___x_3583_ = lean_st_ref_put(v___y_3555_, v___x_3582_);
v_exportedInfo_x3f_3535_ = v_exportedInfo_x3f_3387_;
v___y_3536_ = v___y_3556_;
v___y_3537_ = v___y_3555_;
goto v___jp_3534_;
}
}
}
}
v___jp_3587_:
{
lean_object* v___x_3590_; uint8_t v___x_3591_; 
lean_inc(v_decl_3381_);
v___x_3590_ = l_Lean_Declaration_getTopLevelNames(v_decl_3381_);
v___x_3591_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3590_);
lean_dec(v___x_3590_);
if (v___x_3591_ == 0)
{
lean_dec(v___x_3385_);
if (lean_obj_tag(v_exportedInfo_x3f_3387_) == 0)
{
v___y_3555_ = v___y_3589_;
v___y_3556_ = v___y_3588_;
v___y_3557_ = v___x_3591_;
goto v___jp_3554_;
}
else
{
v___y_3555_ = v___y_3589_;
v___y_3556_ = v___y_3588_;
v___y_3557_ = v___x_3382_;
goto v___jp_3554_;
}
}
else
{
lean_object* v___x_3592_; lean_object* v___x_3593_; lean_object* v_a_3594_; uint8_t v___x_3595_; 
lean_dec(v_exportedInfo_x3f_3387_);
lean_dec_ref(v___x_3384_);
v___x_3592_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3593_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3592_, v___y_3588_);
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_unbox(v_a_3594_);
lean_dec(v_a_3594_);
if (v___x_3595_ == 0)
{
lean_object* v_toCold_3596_; lean_object* v_options_3597_; uint8_t v_hasTrace_3598_; 
v_toCold_3596_ = lean_ctor_get(v___y_3588_, 0);
v_options_3597_ = lean_ctor_get(v_toCold_3596_, 2);
v_hasTrace_3598_ = lean_ctor_get_uint8(v_options_3597_, sizeof(void*)*1);
if (v_hasTrace_3598_ == 0)
{
lean_dec(v_cls_3383_);
v_exportedInfo_x3f_3535_ = v___x_3385_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3589_;
goto v___jp_3534_;
}
else
{
lean_object* v_inheritedTraceOptions_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; uint8_t v___x_3602_; 
v_inheritedTraceOptions_3599_ = lean_ctor_get(v_toCold_3596_, 11);
v___x_3600_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3383_);
v___x_3601_ = l_Lean_Name_append(v___x_3600_, v_cls_3383_);
v___x_3602_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3599_, v_options_3597_, v___x_3601_);
lean_dec(v___x_3601_);
if (v___x_3602_ == 0)
{
lean_dec(v_cls_3383_);
v_exportedInfo_x3f_3535_ = v___x_3385_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3589_;
goto v___jp_3534_;
}
else
{
lean_object* v___x_3603_; lean_object* v___x_3604_; 
v___x_3603_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3604_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3383_, v___x_3603_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_dec_ref_known(v___x_3604_, 1);
v_exportedInfo_x3f_3535_ = v___x_3385_;
v___y_3536_ = v___y_3588_;
v___y_3537_ = v___y_3589_;
goto v___jp_3534_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v___x_3385_);
lean_dec(v_decl_3381_);
return v___x_3604_;
}
}
}
}
else
{
lean_object* v_toCold_3605_; lean_object* v_options_3606_; uint8_t v_hasTrace_3607_; 
lean_dec(v___x_3385_);
v_toCold_3605_ = lean_ctor_get(v___y_3588_, 0);
v_options_3606_ = lean_ctor_get(v_toCold_3605_, 2);
v_hasTrace_3607_ = lean_ctor_get_uint8(v_options_3606_, sizeof(void*)*1);
if (v_hasTrace_3607_ == 0)
{
lean_dec(v_cls_3383_);
v___y_3551_ = v___y_3588_;
v___y_3552_ = v___y_3589_;
goto v___jp_3550_;
}
else
{
lean_object* v_inheritedTraceOptions_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v_inheritedTraceOptions_3608_ = lean_ctor_get(v_toCold_3605_, 11);
v___x_3609_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3383_);
v___x_3610_ = l_Lean_Name_append(v___x_3609_, v_cls_3383_);
v___x_3611_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3608_, v_options_3606_, v___x_3610_);
lean_dec(v___x_3610_);
if (v___x_3611_ == 0)
{
lean_dec(v_cls_3383_);
v___y_3551_ = v___y_3588_;
v___y_3552_ = v___y_3589_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3612_; lean_object* v___x_3613_; 
v___x_3612_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3613_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3383_, v___x_3612_, v___y_3588_, v___y_3589_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_dec_ref_known(v___x_3613_, 1);
v___y_3551_ = v___y_3588_;
v___y_3552_ = v___y_3589_;
goto v___jp_3550_;
}
else
{
lean_del_object(v___x_3500_);
lean_dec(v_snd_3498_);
lean_dec(v_fst_3497_);
lean_dec(v_fst_3493_);
lean_dec(v_decl_3381_);
return v___x_3613_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3626_, lean_object* v___x_3627_, lean_object* v_cls_3628_, lean_object* v___x_3629_, lean_object* v___x_3630_, lean_object* v_____x_3631_, lean_object* v_exportedInfo_x3f_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v___x_53796__boxed_3636_; lean_object* v_res_3637_; 
v___x_53796__boxed_3636_ = lean_unbox(v___x_3627_);
v_res_3637_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3626_, v___x_53796__boxed_3636_, v_cls_3628_, v___x_3629_, v___x_3630_, v_____x_3631_, v_exportedInfo_x3f_3632_, v___y_3633_, v___y_3634_);
lean_dec(v___y_3634_);
lean_dec_ref(v___y_3633_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3638_, uint8_t v_forceExpose_3639_, uint8_t v___x_3640_, lean_object* v___x_3641_, lean_object* v_cls_3642_, lean_object* v_defn_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_){
_start:
{
lean_object* v_exportedInfo_x3f_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3660_; lean_object* v___y_3661_; lean_object* v___y_3662_; uint8_t v___y_3663_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_st_ref_get(v___y_3645_);
v___x_3668_ = lean_st_ref_get(v___y_3645_);
if (v_forceExpose_3639_ == 0)
{
if (v___x_3640_ == 0)
{
lean_dec(v___x_3668_);
lean_dec(v___x_3667_);
lean_dec(v_cls_3642_);
v_exportedInfo_x3f_3648_ = v___x_3641_;
v___y_3649_ = v___y_3644_;
v___y_3650_ = v___y_3645_;
goto v___jp_3647_;
}
else
{
lean_object* v_env_3669_; lean_object* v_env_3670_; lean_object* v___x_3671_; uint8_t v_isModule_3672_; 
v_env_3669_ = lean_ctor_get(v___x_3667_, 0);
lean_inc_ref(v_env_3669_);
lean_dec(v___x_3667_);
v_env_3670_ = lean_ctor_get(v___x_3668_, 0);
lean_inc_ref(v_env_3670_);
lean_dec(v___x_3668_);
v___x_3671_ = l_Lean_Environment_header(v_env_3669_);
lean_dec_ref(v_env_3669_);
v_isModule_3672_ = lean_ctor_get_uint8(v___x_3671_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3671_);
if (v_isModule_3672_ == 0)
{
lean_dec_ref(v_env_3670_);
lean_dec(v_cls_3642_);
v_exportedInfo_x3f_3648_ = v___x_3641_;
v___y_3649_ = v___y_3644_;
v___y_3650_ = v___y_3645_;
goto v___jp_3647_;
}
else
{
uint8_t v_isExporting_3673_; lean_object* v___y_3675_; lean_object* v___y_3676_; 
v_isExporting_3673_ = lean_ctor_get_uint8(v_env_3670_, sizeof(void*)*8);
lean_dec_ref(v_env_3670_);
if (v_isExporting_3673_ == 0)
{
lean_object* v_toCold_3681_; lean_object* v_options_3682_; uint8_t v_hasTrace_3683_; 
lean_dec(v___x_3641_);
v_toCold_3681_ = lean_ctor_get(v___y_3644_, 0);
v_options_3682_ = lean_ctor_get(v_toCold_3681_, 2);
v_hasTrace_3683_ = lean_ctor_get_uint8(v_options_3682_, sizeof(void*)*1);
if (v_hasTrace_3683_ == 0)
{
lean_dec(v_cls_3642_);
v___y_3675_ = v___y_3644_;
v___y_3676_ = v___y_3645_;
goto v___jp_3674_;
}
else
{
lean_object* v_inheritedTraceOptions_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; uint8_t v___x_3687_; 
v_inheritedTraceOptions_3684_ = lean_ctor_get(v_toCold_3681_, 11);
v___x_3685_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3642_);
v___x_3686_ = l_Lean_Name_append(v___x_3685_, v_cls_3642_);
v___x_3687_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3684_, v_options_3682_, v___x_3686_);
lean_dec(v___x_3686_);
if (v___x_3687_ == 0)
{
lean_dec(v_cls_3642_);
v___y_3675_ = v___y_3644_;
v___y_3676_ = v___y_3645_;
goto v___jp_3674_;
}
else
{
lean_object* v_toConstantVal_3688_; lean_object* v_name_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; lean_object* v___x_3695_; 
v_toConstantVal_3688_ = lean_ctor_get(v_defn_3643_, 0);
v_name_3689_ = lean_ctor_get(v_toConstantVal_3688_, 0);
v___x_3690_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3689_);
v___x_3691_ = l_Lean_MessageData_ofName(v_name_3689_);
v___x_3692_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3690_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3694_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3694_, 0, v___x_3692_);
lean_ctor_set(v___x_3694_, 1, v___x_3693_);
v___x_3695_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3642_, v___x_3694_, v___y_3644_, v___y_3645_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_dec_ref_known(v___x_3695_, 1);
v___y_3675_ = v___y_3644_;
v___y_3676_ = v___y_3645_;
goto v___jp_3674_;
}
else
{
lean_dec_ref(v_defn_3643_);
lean_dec_ref(v___f_3638_);
return v___x_3695_;
}
}
}
}
else
{
lean_dec(v_cls_3642_);
v_exportedInfo_x3f_3648_ = v___x_3641_;
v___y_3649_ = v___y_3644_;
v___y_3650_ = v___y_3645_;
goto v___jp_3647_;
}
v___jp_3674_:
{
lean_object* v_toConstantVal_3677_; uint8_t v_safety_3678_; uint8_t v___x_3679_; uint8_t v___x_3680_; 
v_toConstantVal_3677_ = lean_ctor_get(v_defn_3643_, 0);
v_safety_3678_ = lean_ctor_get_uint8(v_defn_3643_, sizeof(void*)*4);
v___x_3679_ = 1;
v___x_3680_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3678_, v___x_3679_);
if (v___x_3680_ == 0)
{
lean_inc_ref(v_toConstantVal_3677_);
v___y_3660_ = v___y_3676_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v_toConstantVal_3677_;
v___y_3663_ = v_isModule_3672_;
goto v___jp_3659_;
}
else
{
lean_inc_ref(v_toConstantVal_3677_);
v___y_3660_ = v___y_3676_;
v___y_3661_ = v___y_3675_;
v___y_3662_ = v_toConstantVal_3677_;
v___y_3663_ = v_isExporting_3673_;
goto v___jp_3659_;
}
}
}
}
}
else
{
lean_dec(v___x_3668_);
lean_dec(v___x_3667_);
lean_dec(v_cls_3642_);
v_exportedInfo_x3f_3648_ = v___x_3641_;
v___y_3649_ = v___y_3644_;
v___y_3650_ = v___y_3645_;
goto v___jp_3647_;
}
v___jp_3647_:
{
lean_object* v_toConstantVal_3651_; lean_object* v_name_3652_; lean_object* v___x_3653_; uint8_t v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; 
v_toConstantVal_3651_ = lean_ctor_get(v_defn_3643_, 0);
v_name_3652_ = lean_ctor_get(v_toConstantVal_3651_, 0);
lean_inc(v_name_3652_);
v___x_3653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_defn_3643_);
v___x_3654_ = 0;
v___x_3655_ = lean_box(v___x_3654_);
v___x_3656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3653_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3657_, 0, v_name_3652_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
lean_inc(v___y_3650_);
lean_inc_ref(v___y_3649_);
v___x_3658_ = lean_apply_5(v___f_3638_, v___x_3657_, v_exportedInfo_x3f_3648_, v___y_3649_, v___y_3650_, lean_box(0));
return v___x_3658_;
}
v___jp_3659_:
{
lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; 
v___x_3664_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3664_, 0, v___y_3662_);
lean_ctor_set_uint8(v___x_3664_, sizeof(void*)*1, v___y_3663_);
v___x_3665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3664_);
v___x_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3665_);
v_exportedInfo_x3f_3648_ = v___x_3666_;
v___y_3649_ = v___y_3661_;
v___y_3650_ = v___y_3660_;
goto v___jp_3647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3696_, lean_object* v_forceExpose_3697_, lean_object* v___x_3698_, lean_object* v___x_3699_, lean_object* v_cls_3700_, lean_object* v_defn_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_){
_start:
{
uint8_t v_forceExpose_boxed_3705_; uint8_t v___x_54271__boxed_3706_; lean_object* v_res_3707_; 
v_forceExpose_boxed_3705_ = lean_unbox(v_forceExpose_3697_);
v___x_54271__boxed_3706_ = lean_unbox(v___x_3698_);
v_res_3707_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3696_, v_forceExpose_boxed_3705_, v___x_54271__boxed_3706_, v___x_3699_, v_cls_3700_, v_defn_3701_, v___y_3702_, v___y_3703_);
lean_dec(v___y_3703_);
lean_dec_ref(v___y_3702_);
return v_res_3707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3708_, uint8_t v_forceExpose_3709_, lean_object* v___f_3710_, lean_object* v_____r_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_){
_start:
{
lean_object* v_toConstantVal_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; 
v_toConstantVal_3715_ = lean_ctor_get(v_val_3708_, 0);
lean_inc_ref(v_toConstantVal_3715_);
v___x_3716_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3716_, 0, v_toConstantVal_3715_);
lean_ctor_set_uint8(v___x_3716_, sizeof(void*)*1, v_forceExpose_3709_);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
v___x_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
v___x_3719_ = lean_box(0);
lean_inc(v___y_3713_);
lean_inc_ref(v___y_3712_);
v___x_3720_ = lean_apply_5(v___f_3710_, v___x_3719_, v___x_3718_, v___y_3712_, v___y_3713_, lean_box(0));
return v___x_3720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3721_, lean_object* v_forceExpose_3722_, lean_object* v___f_3723_, lean_object* v_____r_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v_forceExpose_boxed_3728_; lean_object* v_res_3729_; 
v_forceExpose_boxed_3728_ = lean_unbox(v_forceExpose_3722_);
v_res_3729_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3721_, v_forceExpose_boxed_3728_, v___f_3723_, v_____r_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
lean_dec_ref(v_val_3721_);
return v_res_3729_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3730_, lean_object* v_x_3731_){
_start:
{
if (lean_obj_tag(v_x_3731_) == 0)
{
return v_x_3730_;
}
else
{
lean_object* v_head_3732_; lean_object* v_tail_3733_; lean_object* v___x_3734_; 
v_head_3732_ = lean_ctor_get(v_x_3731_, 0);
lean_inc(v_head_3732_);
v_tail_3733_ = lean_ctor_get(v_x_3731_, 1);
lean_inc(v_tail_3733_);
lean_dec_ref_known(v_x_3731_, 2);
v___x_3734_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3730_, v_head_3732_);
v_x_3730_ = v___x_3734_;
v_x_3731_ = v_tail_3733_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; 
v_cls_3736_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3737_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3738_ = l_Lean_Name_append(v___x_3737_, v_cls_3736_);
return v___x_3738_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3740_; lean_object* v___x_3741_; 
v___x_3740_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3741_ = l_Lean_stringToMessageData(v___x_3740_);
return v___x_3741_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; 
v___x_3743_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3744_ = l_Lean_stringToMessageData(v___x_3743_);
return v___x_3744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3745_, uint8_t v_forceExpose_3746_, lean_object* v_a_3747_, lean_object* v_a_3748_){
_start:
{
lean_object* v___y_3751_; lean_object* v___y_3752_; lean_object* v_a_3753_; lean_object* v___y_3764_; lean_object* v___y_3765_; lean_object* v_a_3766_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v_a_3779_; lean_object* v___y_3790_; lean_object* v___y_3791_; lean_object* v_a_3792_; lean_object* v_toCold_3802_; lean_object* v_options_3803_; lean_object* v_inheritedTraceOptions_3804_; uint8_t v_hasTrace_3805_; lean_object* v___y_3807_; lean_object* v___y_3808_; uint8_t v___y_3809_; lean_object* v___y_3810_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v___y_3813_; lean_object* v___y_3814_; lean_object* v___y_3815_; lean_object* v___y_3816_; lean_object* v___y_3817_; lean_object* v___y_3882_; lean_object* v___y_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; uint8_t v___y_3886_; lean_object* v___y_3887_; lean_object* v___y_3888_; lean_object* v___y_3889_; lean_object* v___y_3890_; lean_object* v___y_3891_; uint8_t v___y_3914_; lean_object* v___y_3915_; lean_object* v___y_3916_; lean_object* v_exportedInfo_x3f_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; uint8_t v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; uint8_t v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v_cls_3942_; 
v_toCold_3802_ = lean_ctor_get(v_a_3747_, 0);
v_options_3803_ = lean_ctor_get(v_toCold_3802_, 2);
v_inheritedTraceOptions_3804_ = lean_ctor_get(v_toCold_3802_, 11);
v_hasTrace_3805_ = lean_ctor_get_uint8(v_options_3803_, sizeof(void*)*1);
v_cls_3942_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3805_ == 0)
{
lean_object* v___x_3943_; lean_object* v_env_3944_; lean_object* v_nextMacroScope_3945_; lean_object* v_ngen_3946_; lean_object* v_auxDeclNGen_3947_; lean_object* v_traceState_3948_; lean_object* v_messages_3949_; lean_object* v_infoState_3950_; lean_object* v_snapshotTasks_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_4153_; 
v___x_3943_ = lean_st_ref_take(v_a_3748_);
v_env_3944_ = lean_ctor_get(v___x_3943_, 0);
v_nextMacroScope_3945_ = lean_ctor_get(v___x_3943_, 1);
v_ngen_3946_ = lean_ctor_get(v___x_3943_, 2);
v_auxDeclNGen_3947_ = lean_ctor_get(v___x_3943_, 3);
v_traceState_3948_ = lean_ctor_get(v___x_3943_, 4);
v_messages_3949_ = lean_ctor_get(v___x_3943_, 6);
v_infoState_3950_ = lean_ctor_get(v___x_3943_, 7);
v_snapshotTasks_3951_ = lean_ctor_get(v___x_3943_, 8);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_3943_);
if (v_isSharedCheck_4153_ == 0)
{
lean_object* v_unused_4154_; 
v_unused_4154_ = lean_ctor_get(v___x_3943_, 5);
lean_dec(v_unused_4154_);
v___x_3953_ = v___x_3943_;
v_isShared_3954_ = v_isSharedCheck_4153_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_snapshotTasks_3951_);
lean_inc(v_infoState_3950_);
lean_inc(v_messages_3949_);
lean_inc(v_traceState_3948_);
lean_inc(v_auxDeclNGen_3947_);
lean_inc(v_ngen_3946_);
lean_inc(v_nextMacroScope_3945_);
lean_inc(v_env_3944_);
lean_dec(v___x_3943_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_4153_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; uint8_t v___y_3959_; lean_object* v___y_3960_; lean_object* v___y_3961_; lean_object* v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___x_3987_; 
lean_inc(v_decl_3745_);
v___x_3955_ = l_Lean_Declaration_getNames(v_decl_3745_);
v___x_3956_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3944_, v___x_3955_);
v___x_3957_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 5, v___x_3957_);
lean_ctor_set(v___x_3953_, 0, v___x_3956_);
v___x_3987_ = v___x_3953_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_4152_, 1, v_nextMacroScope_3945_);
lean_ctor_set(v_reuseFailAlloc_4152_, 2, v_ngen_3946_);
lean_ctor_set(v_reuseFailAlloc_4152_, 3, v_auxDeclNGen_3947_);
lean_ctor_set(v_reuseFailAlloc_4152_, 4, v_traceState_3948_);
lean_ctor_set(v_reuseFailAlloc_4152_, 5, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_4152_, 6, v_messages_3949_);
lean_ctor_set(v_reuseFailAlloc_4152_, 7, v_infoState_3950_);
lean_ctor_set(v_reuseFailAlloc_4152_, 8, v_snapshotTasks_3951_);
v___x_3987_ = v_reuseFailAlloc_4152_;
goto v_reusejp_3986_;
}
v___jp_3958_:
{
lean_object* v___x_3965_; lean_object* v_env_3966_; lean_object* v_nextMacroScope_3967_; lean_object* v_ngen_3968_; lean_object* v_auxDeclNGen_3969_; lean_object* v_traceState_3970_; lean_object* v_messages_3971_; lean_object* v_infoState_3972_; lean_object* v_snapshotTasks_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3984_; 
v___x_3965_ = lean_st_ref_take(v___y_3962_);
v_env_3966_ = lean_ctor_get(v___x_3965_, 0);
v_nextMacroScope_3967_ = lean_ctor_get(v___x_3965_, 1);
v_ngen_3968_ = lean_ctor_get(v___x_3965_, 2);
v_auxDeclNGen_3969_ = lean_ctor_get(v___x_3965_, 3);
v_traceState_3970_ = lean_ctor_get(v___x_3965_, 4);
v_messages_3971_ = lean_ctor_get(v___x_3965_, 6);
v_infoState_3972_ = lean_ctor_get(v___x_3965_, 7);
v_snapshotTasks_3973_ = lean_ctor_get(v___x_3965_, 8);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3965_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v___x_3965_, 5);
lean_dec(v_unused_3985_);
v___x_3975_ = v___x_3965_;
v_isShared_3976_ = v_isSharedCheck_3984_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_snapshotTasks_3973_);
lean_inc(v_infoState_3972_);
lean_inc(v_messages_3971_);
lean_inc(v_traceState_3970_);
lean_inc(v_auxDeclNGen_3969_);
lean_inc(v_ngen_3968_);
lean_inc(v_nextMacroScope_3967_);
lean_inc(v_env_3966_);
lean_dec(v___x_3965_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3984_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3981_; 
v___x_3977_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3978_ = lean_box(v___y_3959_);
lean_inc(v___y_3964_);
v___x_3979_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3977_, v_env_3966_, v___y_3964_, v___x_3978_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 5, v___x_3957_);
lean_ctor_set(v___x_3975_, 0, v___x_3979_);
v___x_3981_ = v___x_3975_;
goto v_reusejp_3980_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_nextMacroScope_3967_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_ngen_3968_);
lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_auxDeclNGen_3969_);
lean_ctor_set(v_reuseFailAlloc_3983_, 4, v_traceState_3970_);
lean_ctor_set(v_reuseFailAlloc_3983_, 5, v___x_3957_);
lean_ctor_set(v_reuseFailAlloc_3983_, 6, v_messages_3971_);
lean_ctor_set(v_reuseFailAlloc_3983_, 7, v_infoState_3972_);
lean_ctor_set(v_reuseFailAlloc_3983_, 8, v_snapshotTasks_3973_);
v___x_3981_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3980_;
}
v_reusejp_3980_:
{
lean_object* v___x_3982_; 
v___x_3982_ = lean_st_ref_put(v___y_3962_, v___x_3981_);
v___y_3914_ = v___y_3959_;
v___y_3915_ = v___y_3961_;
v___y_3916_ = v___y_3964_;
v_exportedInfo_x3f_3917_ = v___y_3963_;
v___y_3918_ = v___y_3960_;
v___y_3919_ = v___y_3962_;
goto v___jp_3913_;
}
}
}
v_reusejp_3986_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; uint8_t v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v_fst_4028_; lean_object* v_fst_4029_; uint8_t v_snd_4030_; lean_object* v_exportedInfo_x3f_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; lean_object* v___y_4043_; lean_object* v_exportedInfo_x3f_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4052_; lean_object* v___y_4053_; lean_object* v___y_4054_; lean_object* v___y_4055_; uint8_t v___y_4056_; uint8_t v___y_4061_; lean_object* v___y_4062_; lean_object* v_toConstantVal_4063_; uint8_t v_safety_4064_; lean_object* v___y_4065_; lean_object* v___y_4066_; uint8_t v___y_4070_; lean_object* v___y_4071_; lean_object* v___y_4072_; lean_object* v___y_4073_; lean_object* v_defn_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; 
v___x_3988_ = lean_st_ref_put(v_a_3748_, v___x_3987_);
v___x_3989_ = lean_box(0);
switch(lean_obj_tag(v_decl_3745_))
{
case 2:
{
lean_object* v_val_4102_; lean_object* v_exportedInfo_x3f_4104_; lean_object* v___y_4105_; lean_object* v___y_4106_; lean_object* v___x_4111_; 
v_val_4102_ = lean_ctor_get(v_decl_3745_, 0);
v___x_4111_ = lean_st_ref_get(v_a_3748_);
if (v_forceExpose_3746_ == 0)
{
lean_object* v_env_4112_; lean_object* v___x_4113_; uint8_t v_isModule_4114_; 
v_env_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_env_4112_);
lean_dec(v___x_4111_);
v___x_4113_ = l_Lean_Environment_header(v_env_4112_);
lean_dec_ref(v_env_4112_);
v_isModule_4114_ = lean_ctor_get_uint8(v___x_4113_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4113_);
if (v_isModule_4114_ == 0)
{
v_exportedInfo_x3f_4104_ = v___x_3989_;
v___y_4105_ = v_a_3747_;
v___y_4106_ = v_a_3748_;
goto v___jp_4103_;
}
else
{
lean_object* v_toConstantVal_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; 
v_toConstantVal_4115_ = lean_ctor_get(v_val_4102_, 0);
lean_inc_ref(v_toConstantVal_4115_);
v___x_4116_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4116_, 0, v_toConstantVal_4115_);
lean_ctor_set_uint8(v___x_4116_, sizeof(void*)*1, v_hasTrace_3805_);
v___x_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4117_, 0, v___x_4116_);
v___x_4118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4117_);
v_exportedInfo_x3f_4104_ = v___x_4118_;
v___y_4105_ = v_a_3747_;
v___y_4106_ = v_a_3748_;
goto v___jp_4103_;
}
}
else
{
lean_dec(v___x_4111_);
v_exportedInfo_x3f_4104_ = v___x_3989_;
v___y_4105_ = v_a_3747_;
v___y_4106_ = v_a_3748_;
goto v___jp_4103_;
}
v___jp_4103_:
{
lean_object* v_toConstantVal_4107_; lean_object* v_name_4108_; lean_object* v___x_4109_; uint8_t v___x_4110_; 
v_toConstantVal_4107_ = lean_ctor_get(v_val_4102_, 0);
v_name_4108_ = lean_ctor_get(v_toConstantVal_4107_, 0);
lean_inc_ref(v_val_4102_);
v___x_4109_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4109_, 0, v_val_4102_);
v___x_4110_ = 1;
lean_inc(v_name_4108_);
v_fst_4028_ = v_name_4108_;
v_fst_4029_ = v___x_4109_;
v_snd_4030_ = v___x_4110_;
v_exportedInfo_x3f_4031_ = v_exportedInfo_x3f_4104_;
v___y_4032_ = v___y_4105_;
v___y_4033_ = v___y_4106_;
goto v___jp_4027_;
}
}
case 1:
{
lean_object* v_val_4119_; 
v_val_4119_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref(v_val_4119_);
v_defn_4077_ = v_val_4119_;
v___y_4078_ = v_a_3747_;
v___y_4079_ = v_a_3748_;
goto v___jp_4076_;
}
case 5:
{
lean_object* v_defns_4120_; 
v_defns_4120_ = lean_ctor_get(v_decl_3745_, 0);
if (lean_obj_tag(v_defns_4120_) == 1)
{
lean_object* v_tail_4121_; 
v_tail_4121_ = lean_ctor_get(v_defns_4120_, 1);
if (lean_obj_tag(v_tail_4121_) == 0)
{
lean_object* v_head_4122_; 
v_head_4122_ = lean_ctor_get(v_defns_4120_, 0);
lean_inc(v_head_4122_);
v_defn_4077_ = v_head_4122_;
v___y_4078_ = v_a_3747_;
v___y_4079_ = v_a_3748_;
goto v___jp_4076_;
}
else
{
lean_object* v___x_4123_; 
v___x_4123_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v_a_3747_, v_a_3748_);
return v___x_4123_;
}
}
else
{
lean_object* v___x_4124_; 
v___x_4124_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v_a_3747_, v_a_3748_);
return v___x_4124_;
}
}
case 3:
{
lean_object* v_val_4125_; lean_object* v_exportedInfo_x3f_4127_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___x_4134_; lean_object* v___x_4135_; 
v_val_4125_ = lean_ctor_get(v_decl_3745_, 0);
v___x_4134_ = lean_st_ref_get(v_a_3748_);
v___x_4135_ = lean_st_ref_get(v_a_3748_);
if (v_forceExpose_3746_ == 0)
{
lean_object* v_env_4136_; lean_object* v_env_4137_; lean_object* v___x_4138_; uint8_t v_isModule_4139_; 
v_env_4136_ = lean_ctor_get(v___x_4134_, 0);
lean_inc_ref(v_env_4136_);
lean_dec(v___x_4134_);
v_env_4137_ = lean_ctor_get(v___x_4135_, 0);
lean_inc_ref(v_env_4137_);
lean_dec(v___x_4135_);
v___x_4138_ = l_Lean_Environment_header(v_env_4136_);
lean_dec_ref(v_env_4136_);
v_isModule_4139_ = lean_ctor_get_uint8(v___x_4138_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4138_);
if (v_isModule_4139_ == 0)
{
lean_dec_ref(v_env_4137_);
v_exportedInfo_x3f_4127_ = v___x_3989_;
v___y_4128_ = v_a_3747_;
v___y_4129_ = v_a_3748_;
goto v___jp_4126_;
}
else
{
uint8_t v_isExporting_4140_; 
v_isExporting_4140_ = lean_ctor_get_uint8(v_env_4137_, sizeof(void*)*8);
lean_dec_ref(v_env_4137_);
if (v_isExporting_4140_ == 0)
{
lean_object* v_toConstantVal_4141_; uint8_t v_isUnsafe_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_toConstantVal_4141_ = lean_ctor_get(v_val_4125_, 0);
v_isUnsafe_4142_ = lean_ctor_get_uint8(v_val_4125_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4141_);
v___x_4143_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4143_, 0, v_toConstantVal_4141_);
lean_ctor_set_uint8(v___x_4143_, sizeof(void*)*1, v_isUnsafe_4142_);
v___x_4144_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4143_);
v___x_4145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4145_, 0, v___x_4144_);
v_exportedInfo_x3f_4127_ = v___x_4145_;
v___y_4128_ = v_a_3747_;
v___y_4129_ = v_a_3748_;
goto v___jp_4126_;
}
else
{
v_exportedInfo_x3f_4127_ = v___x_3989_;
v___y_4128_ = v_a_3747_;
v___y_4129_ = v_a_3748_;
goto v___jp_4126_;
}
}
}
else
{
lean_dec(v___x_4135_);
lean_dec(v___x_4134_);
v_exportedInfo_x3f_4127_ = v___x_3989_;
v___y_4128_ = v_a_3747_;
v___y_4129_ = v_a_3748_;
goto v___jp_4126_;
}
v___jp_4126_:
{
lean_object* v_toConstantVal_4130_; lean_object* v_name_4131_; lean_object* v___x_4132_; uint8_t v___x_4133_; 
v_toConstantVal_4130_ = lean_ctor_get(v_val_4125_, 0);
v_name_4131_ = lean_ctor_get(v_toConstantVal_4130_, 0);
lean_inc_ref(v_val_4125_);
v___x_4132_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4132_, 0, v_val_4125_);
v___x_4133_ = 3;
lean_inc(v_name_4131_);
v_fst_4028_ = v_name_4131_;
v_fst_4029_ = v___x_4132_;
v_snd_4030_ = v___x_4133_;
v_exportedInfo_x3f_4031_ = v_exportedInfo_x3f_4127_;
v___y_4032_ = v___y_4128_;
v___y_4033_ = v___y_4129_;
goto v___jp_4027_;
}
}
case 0:
{
lean_object* v_val_4146_; lean_object* v_toConstantVal_4147_; lean_object* v_name_4148_; lean_object* v___x_4149_; uint8_t v___x_4150_; 
v_val_4146_ = lean_ctor_get(v_decl_3745_, 0);
v_toConstantVal_4147_ = lean_ctor_get(v_val_4146_, 0);
v_name_4148_ = lean_ctor_get(v_toConstantVal_4147_, 0);
lean_inc_ref(v_val_4146_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_val_4146_);
v___x_4150_ = 2;
lean_inc(v_name_4148_);
v_fst_4028_ = v_name_4148_;
v_fst_4029_ = v___x_4149_;
v_snd_4030_ = v___x_4150_;
v_exportedInfo_x3f_4031_ = v___x_3989_;
v___y_4032_ = v_a_3747_;
v___y_4033_ = v_a_3748_;
goto v___jp_4027_;
}
default: 
{
lean_object* v___x_4151_; 
v___x_4151_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v_a_3747_, v_a_3748_);
return v___x_4151_;
}
}
v___jp_3990_:
{
lean_object* v___x_3997_; uint8_t v___x_3998_; 
lean_inc(v_decl_3745_);
v___x_3997_ = l_Lean_Declaration_getTopLevelNames(v_decl_3745_);
v___x_3998_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3997_);
lean_dec(v___x_3997_);
if (v___x_3998_ == 0)
{
if (lean_obj_tag(v___y_3993_) == 0)
{
if (v___x_3998_ == 0)
{
lean_object* v_toCold_3999_; lean_object* v_options_4000_; uint8_t v_hasTrace_4001_; 
v_toCold_3999_ = lean_ctor_get(v___y_3995_, 0);
v_options_4000_ = lean_ctor_get(v_toCold_3999_, 2);
v_hasTrace_4001_ = lean_ctor_get_uint8(v_options_4000_, sizeof(void*)*1);
if (v_hasTrace_4001_ == 0)
{
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3992_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
v___y_3940_ = v___y_3996_;
goto v___jp_3935_;
}
else
{
lean_object* v_inheritedTraceOptions_4002_; lean_object* v___x_4003_; uint8_t v___x_4004_; 
v_inheritedTraceOptions_4002_ = lean_ctor_get(v_toCold_3999_, 11);
v___x_4003_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4004_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4002_, v_options_4000_, v___x_4003_);
if (v___x_4004_ == 0)
{
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3992_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
v___y_3940_ = v___y_3996_;
goto v___jp_3935_;
}
else
{
lean_object* v___x_4005_; lean_object* v___x_4006_; 
v___x_4005_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4006_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4005_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4006_) == 0)
{
lean_dec_ref_known(v___x_4006_, 1);
v___y_3936_ = v___y_3991_;
v___y_3937_ = v___y_3992_;
v___y_3938_ = v___y_3994_;
v___y_3939_ = v___y_3995_;
v___y_3940_ = v___y_3996_;
goto v___jp_3935_;
}
else
{
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3992_);
lean_dec(v_decl_3745_);
return v___x_4006_;
}
}
}
}
else
{
v___y_3959_ = v___y_3991_;
v___y_3960_ = v___y_3995_;
v___y_3961_ = v___y_3992_;
v___y_3962_ = v___y_3996_;
v___y_3963_ = v___y_3993_;
v___y_3964_ = v___y_3994_;
goto v___jp_3958_;
}
}
else
{
v___y_3959_ = v___y_3991_;
v___y_3960_ = v___y_3995_;
v___y_3961_ = v___y_3992_;
v___y_3962_ = v___y_3996_;
v___y_3963_ = v___y_3993_;
v___y_3964_ = v___y_3994_;
goto v___jp_3958_;
}
}
else
{
lean_object* v___x_4007_; lean_object* v___x_4008_; lean_object* v_a_4009_; uint8_t v___x_4010_; 
lean_dec(v___y_3993_);
v___x_4007_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4008_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4007_, v___y_3995_);
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref(v___x_4008_);
v___x_4010_ = lean_unbox(v_a_4009_);
lean_dec(v_a_4009_);
if (v___x_4010_ == 0)
{
lean_object* v_toCold_4011_; lean_object* v_options_4012_; uint8_t v_hasTrace_4013_; 
v_toCold_4011_ = lean_ctor_get(v___y_3995_, 0);
v_options_4012_ = lean_ctor_get(v_toCold_4011_, 2);
v_hasTrace_4013_ = lean_ctor_get_uint8(v_options_4012_, sizeof(void*)*1);
if (v_hasTrace_4013_ == 0)
{
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3992_;
v___y_3916_ = v___y_3994_;
v_exportedInfo_x3f_3917_ = v___x_3989_;
v___y_3918_ = v___y_3995_;
v___y_3919_ = v___y_3996_;
goto v___jp_3913_;
}
else
{
lean_object* v_inheritedTraceOptions_4014_; lean_object* v___x_4015_; uint8_t v___x_4016_; 
v_inheritedTraceOptions_4014_ = lean_ctor_get(v_toCold_4011_, 11);
v___x_4015_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4016_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4014_, v_options_4012_, v___x_4015_);
if (v___x_4016_ == 0)
{
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3992_;
v___y_3916_ = v___y_3994_;
v_exportedInfo_x3f_3917_ = v___x_3989_;
v___y_3918_ = v___y_3995_;
v___y_3919_ = v___y_3996_;
goto v___jp_3913_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4017_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4018_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4017_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_dec_ref_known(v___x_4018_, 1);
v___y_3914_ = v___y_3991_;
v___y_3915_ = v___y_3992_;
v___y_3916_ = v___y_3994_;
v_exportedInfo_x3f_3917_ = v___x_3989_;
v___y_3918_ = v___y_3995_;
v___y_3919_ = v___y_3996_;
goto v___jp_3913_;
}
else
{
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3992_);
lean_dec(v_decl_3745_);
return v___x_4018_;
}
}
}
}
else
{
lean_object* v_toCold_4019_; lean_object* v_options_4020_; uint8_t v_hasTrace_4021_; 
v_toCold_4019_ = lean_ctor_get(v___y_3995_, 0);
v_options_4020_ = lean_ctor_get(v_toCold_4019_, 2);
v_hasTrace_4021_ = lean_ctor_get_uint8(v_options_4020_, sizeof(void*)*1);
if (v_hasTrace_4021_ == 0)
{
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3992_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
v___y_3933_ = v___y_3996_;
goto v___jp_3928_;
}
else
{
lean_object* v_inheritedTraceOptions_4022_; lean_object* v___x_4023_; uint8_t v___x_4024_; 
v_inheritedTraceOptions_4022_ = lean_ctor_get(v_toCold_4019_, 11);
v___x_4023_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4024_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4022_, v_options_4020_, v___x_4023_);
if (v___x_4024_ == 0)
{
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3992_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
v___y_3933_ = v___y_3996_;
goto v___jp_3928_;
}
else
{
lean_object* v___x_4025_; lean_object* v___x_4026_; 
v___x_4025_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4026_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4025_, v___y_3995_, v___y_3996_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_dec_ref_known(v___x_4026_, 1);
v___y_3929_ = v___y_3991_;
v___y_3930_ = v___y_3992_;
v___y_3931_ = v___y_3994_;
v___y_3932_ = v___y_3995_;
v___y_3933_ = v___y_3996_;
goto v___jp_3928_;
}
else
{
lean_dec(v___y_3994_);
lean_dec_ref(v___y_3992_);
lean_dec(v_decl_3745_);
return v___x_4026_;
}
}
}
}
}
}
v___jp_4027_:
{
lean_object* v___x_4034_; lean_object* v_env_4035_; uint8_t v___x_4036_; 
v___x_4034_ = lean_st_ref_get(v___y_4033_);
v_env_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc_ref(v_env_4035_);
lean_dec(v___x_4034_);
v___x_4036_ = l_Lean_Environment_containsOnBranch(v_env_4035_, v_fst_4028_);
lean_dec_ref(v_env_4035_);
if (v___x_4036_ == 0)
{
v___y_3991_ = v_snd_4030_;
v___y_3992_ = v_fst_4029_;
v___y_3993_ = v_exportedInfo_x3f_4031_;
v___y_3994_ = v_fst_4028_;
v___y_3995_ = v___y_4032_;
v___y_3996_ = v___y_4033_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4037_; lean_object* v_env_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; 
lean_dec(v_exportedInfo_x3f_4031_);
lean_dec_ref(v_fst_4029_);
lean_dec(v_decl_3745_);
v___x_4037_ = lean_st_ref_get(v___y_4033_);
v_env_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc_ref(v_env_4038_);
lean_dec(v___x_4037_);
v___x_4039_ = lean_elab_environment_to_kernel_env(v_env_4038_);
v___x_4040_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
lean_ctor_set(v___x_4040_, 1, v_fst_4028_);
v___x_4041_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4040_, v___y_4032_, v___y_4033_);
return v___x_4041_;
}
}
v___jp_4042_:
{
lean_object* v_toConstantVal_4047_; lean_object* v_name_4048_; lean_object* v___x_4049_; uint8_t v___x_4050_; 
v_toConstantVal_4047_ = lean_ctor_get(v___y_4043_, 0);
v_name_4048_ = lean_ctor_get(v_toConstantVal_4047_, 0);
lean_inc(v_name_4048_);
v___x_4049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___y_4043_);
v___x_4050_ = 0;
v_fst_4028_ = v_name_4048_;
v_fst_4029_ = v___x_4049_;
v_snd_4030_ = v___x_4050_;
v_exportedInfo_x3f_4031_ = v_exportedInfo_x3f_4044_;
v___y_4032_ = v___y_4045_;
v___y_4033_ = v___y_4046_;
goto v___jp_4027_;
}
v___jp_4051_:
{
lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4057_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4057_, 0, v___y_4052_);
lean_ctor_set_uint8(v___x_4057_, sizeof(void*)*1, v___y_4056_);
v___x_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
v___x_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
v___y_4043_ = v___y_4055_;
v_exportedInfo_x3f_4044_ = v___x_4059_;
v___y_4045_ = v___y_4053_;
v___y_4046_ = v___y_4054_;
goto v___jp_4042_;
}
v___jp_4060_:
{
uint8_t v___x_4067_; uint8_t v___x_4068_; 
v___x_4067_ = 1;
v___x_4068_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4064_, v___x_4067_);
if (v___x_4068_ == 0)
{
v___y_4052_ = v_toConstantVal_4063_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4062_;
v___y_4056_ = v___y_4061_;
goto v___jp_4051_;
}
else
{
v___y_4052_ = v_toConstantVal_4063_;
v___y_4053_ = v___y_4065_;
v___y_4054_ = v___y_4066_;
v___y_4055_ = v___y_4062_;
v___y_4056_ = v_hasTrace_3805_;
goto v___jp_4051_;
}
}
v___jp_4069_:
{
lean_object* v_toConstantVal_4074_; uint8_t v_safety_4075_; 
v_toConstantVal_4074_ = lean_ctor_get(v___y_4071_, 0);
lean_inc_ref(v_toConstantVal_4074_);
v_safety_4075_ = lean_ctor_get_uint8(v___y_4071_, sizeof(void*)*4);
v___y_4061_ = v___y_4070_;
v___y_4062_ = v___y_4071_;
v_toConstantVal_4063_ = v_toConstantVal_4074_;
v_safety_4064_ = v_safety_4075_;
v___y_4065_ = v___y_4072_;
v___y_4066_ = v___y_4073_;
goto v___jp_4060_;
}
v___jp_4076_:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = lean_st_ref_get(v___y_4079_);
v___x_4081_ = lean_st_ref_get(v___y_4079_);
if (v_forceExpose_3746_ == 0)
{
lean_object* v_env_4082_; lean_object* v_env_4083_; lean_object* v___x_4084_; uint8_t v_isModule_4085_; 
v_env_4082_ = lean_ctor_get(v___x_4080_, 0);
lean_inc_ref(v_env_4082_);
lean_dec(v___x_4080_);
v_env_4083_ = lean_ctor_get(v___x_4081_, 0);
lean_inc_ref(v_env_4083_);
lean_dec(v___x_4081_);
v___x_4084_ = l_Lean_Environment_header(v_env_4082_);
lean_dec_ref(v_env_4082_);
v_isModule_4085_ = lean_ctor_get_uint8(v___x_4084_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4084_);
if (v_isModule_4085_ == 0)
{
lean_dec_ref(v_env_4083_);
v___y_4043_ = v_defn_4077_;
v_exportedInfo_x3f_4044_ = v___x_3989_;
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4079_;
goto v___jp_4042_;
}
else
{
uint8_t v_isExporting_4086_; 
v_isExporting_4086_ = lean_ctor_get_uint8(v_env_4083_, sizeof(void*)*8);
lean_dec_ref(v_env_4083_);
if (v_isExporting_4086_ == 0)
{
lean_object* v_toCold_4087_; lean_object* v_options_4088_; uint8_t v_hasTrace_4089_; 
v_toCold_4087_ = lean_ctor_get(v___y_4078_, 0);
v_options_4088_ = lean_ctor_get(v_toCold_4087_, 2);
v_hasTrace_4089_ = lean_ctor_get_uint8(v_options_4088_, sizeof(void*)*1);
if (v_hasTrace_4089_ == 0)
{
v___y_4070_ = v_isModule_4085_;
v___y_4071_ = v_defn_4077_;
v___y_4072_ = v___y_4078_;
v___y_4073_ = v___y_4079_;
goto v___jp_4069_;
}
else
{
lean_object* v_inheritedTraceOptions_4090_; lean_object* v___x_4091_; uint8_t v___x_4092_; 
v_inheritedTraceOptions_4090_ = lean_ctor_get(v_toCold_4087_, 11);
v___x_4091_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4092_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4090_, v_options_4088_, v___x_4091_);
if (v___x_4092_ == 0)
{
v___y_4070_ = v_isModule_4085_;
v___y_4071_ = v_defn_4077_;
v___y_4072_ = v___y_4078_;
v___y_4073_ = v___y_4079_;
goto v___jp_4069_;
}
else
{
lean_object* v_toConstantVal_4093_; uint8_t v_safety_4094_; lean_object* v_name_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_toConstantVal_4093_ = lean_ctor_get(v_defn_4077_, 0);
lean_inc_ref(v_toConstantVal_4093_);
v_safety_4094_ = lean_ctor_get_uint8(v_defn_4077_, sizeof(void*)*4);
v_name_4095_ = lean_ctor_get(v_toConstantVal_4093_, 0);
v___x_4096_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4095_);
v___x_4097_ = l_Lean_MessageData_ofName(v_name_4095_);
v___x_4098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4096_);
lean_ctor_set(v___x_4098_, 1, v___x_4097_);
v___x_4099_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4100_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4098_);
lean_ctor_set(v___x_4100_, 1, v___x_4099_);
v___x_4101_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4100_, v___y_4078_, v___y_4079_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_dec_ref_known(v___x_4101_, 1);
v___y_4061_ = v_isModule_4085_;
v___y_4062_ = v_defn_4077_;
v_toConstantVal_4063_ = v_toConstantVal_4093_;
v_safety_4064_ = v_safety_4094_;
v___y_4065_ = v___y_4078_;
v___y_4066_ = v___y_4079_;
goto v___jp_4060_;
}
else
{
lean_dec_ref(v_toConstantVal_4093_);
lean_dec_ref(v_defn_4077_);
lean_dec(v_decl_3745_);
return v___x_4101_;
}
}
}
}
else
{
v___y_4043_ = v_defn_4077_;
v_exportedInfo_x3f_4044_ = v___x_3989_;
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4079_;
goto v___jp_4042_;
}
}
}
else
{
lean_dec(v___x_4081_);
lean_dec(v___x_4080_);
v___y_4043_ = v_defn_4077_;
v_exportedInfo_x3f_4044_ = v___x_3989_;
v___y_4045_ = v___y_4078_;
v___y_4046_ = v___y_4079_;
goto v___jp_4042_;
}
}
}
}
}
else
{
lean_object* v___f_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; uint8_t v___x_4158_; lean_object* v___y_4160_; lean_object* v___y_4161_; lean_object* v_a_4162_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4199_; lean_object* v___y_4200_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v_a_4208_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4265_; lean_object* v___y_4266_; lean_object* v___y_4267_; uint8_t v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4278_; lean_object* v___y_4279_; lean_object* v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; 
lean_inc(v_decl_3745_);
v___f_4155_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4155_, 0, v_decl_3745_);
v___x_4156_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4157_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4158_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3804_, v_options_3803_, v___x_4157_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4458_; uint8_t v___x_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4466_; lean_object* v___y_4467_; lean_object* v___y_4468_; lean_object* v___y_4469_; lean_object* v___y_4470_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; uint8_t v___y_4543_; lean_object* v___y_4544_; lean_object* v___y_4566_; lean_object* v___y_4567_; uint8_t v___y_4568_; lean_object* v_exportedInfo_x3f_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4581_; lean_object* v___y_4582_; uint8_t v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4588_; lean_object* v___y_4589_; uint8_t v___y_4590_; lean_object* v___y_4591_; lean_object* v___y_4592_; 
v___x_4458_ = l_Lean_trace_profiler;
v___x_4459_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3803_, v___x_4458_);
if (v___x_4459_ == 0)
{
lean_object* v___x_4594_; lean_object* v_env_4595_; lean_object* v_nextMacroScope_4596_; lean_object* v_ngen_4597_; lean_object* v_auxDeclNGen_4598_; lean_object* v_traceState_4599_; lean_object* v_messages_4600_; lean_object* v_infoState_4601_; lean_object* v_snapshotTasks_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4845_; 
lean_dec_ref(v___f_4155_);
v___x_4594_ = lean_st_ref_take(v_a_3748_);
v_env_4595_ = lean_ctor_get(v___x_4594_, 0);
v_nextMacroScope_4596_ = lean_ctor_get(v___x_4594_, 1);
v_ngen_4597_ = lean_ctor_get(v___x_4594_, 2);
v_auxDeclNGen_4598_ = lean_ctor_get(v___x_4594_, 3);
v_traceState_4599_ = lean_ctor_get(v___x_4594_, 4);
v_messages_4600_ = lean_ctor_get(v___x_4594_, 6);
v_infoState_4601_ = lean_ctor_get(v___x_4594_, 7);
v_snapshotTasks_4602_ = lean_ctor_get(v___x_4594_, 8);
v_isSharedCheck_4845_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4845_ == 0)
{
lean_object* v_unused_4846_; 
v_unused_4846_ = lean_ctor_get(v___x_4594_, 5);
lean_dec(v_unused_4846_);
v___x_4604_ = v___x_4594_;
v_isShared_4605_ = v_isSharedCheck_4845_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_snapshotTasks_4602_);
lean_inc(v_infoState_4601_);
lean_inc(v_messages_4600_);
lean_inc(v_traceState_4599_);
lean_inc(v_auxDeclNGen_4598_);
lean_inc(v_ngen_4597_);
lean_inc(v_nextMacroScope_4596_);
lean_inc(v_env_4595_);
lean_dec(v___x_4594_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4845_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___y_4610_; lean_object* v___y_4611_; lean_object* v___y_4612_; lean_object* v___y_4613_; lean_object* v___y_4614_; uint8_t v___y_4615_; lean_object* v___x_4638_; 
lean_inc(v_decl_3745_);
v___x_4606_ = l_Lean_Declaration_getNames(v_decl_3745_);
v___x_4607_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4595_, v___x_4606_);
v___x_4608_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 5, v___x_4608_);
lean_ctor_set(v___x_4604_, 0, v___x_4607_);
v___x_4638_ = v___x_4604_;
goto v_reusejp_4637_;
}
else
{
lean_object* v_reuseFailAlloc_4844_; 
v_reuseFailAlloc_4844_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4844_, 0, v___x_4607_);
lean_ctor_set(v_reuseFailAlloc_4844_, 1, v_nextMacroScope_4596_);
lean_ctor_set(v_reuseFailAlloc_4844_, 2, v_ngen_4597_);
lean_ctor_set(v_reuseFailAlloc_4844_, 3, v_auxDeclNGen_4598_);
lean_ctor_set(v_reuseFailAlloc_4844_, 4, v_traceState_4599_);
lean_ctor_set(v_reuseFailAlloc_4844_, 5, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4844_, 6, v_messages_4600_);
lean_ctor_set(v_reuseFailAlloc_4844_, 7, v_infoState_4601_);
lean_ctor_set(v_reuseFailAlloc_4844_, 8, v_snapshotTasks_4602_);
v___x_4638_ = v_reuseFailAlloc_4844_;
goto v_reusejp_4637_;
}
v___jp_4609_:
{
lean_object* v___x_4616_; lean_object* v_env_4617_; lean_object* v_nextMacroScope_4618_; lean_object* v_ngen_4619_; lean_object* v_auxDeclNGen_4620_; lean_object* v_traceState_4621_; lean_object* v_messages_4622_; lean_object* v_infoState_4623_; lean_object* v_snapshotTasks_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4635_; 
v___x_4616_ = lean_st_ref_take(v___y_4614_);
v_env_4617_ = lean_ctor_get(v___x_4616_, 0);
v_nextMacroScope_4618_ = lean_ctor_get(v___x_4616_, 1);
v_ngen_4619_ = lean_ctor_get(v___x_4616_, 2);
v_auxDeclNGen_4620_ = lean_ctor_get(v___x_4616_, 3);
v_traceState_4621_ = lean_ctor_get(v___x_4616_, 4);
v_messages_4622_ = lean_ctor_get(v___x_4616_, 6);
v_infoState_4623_ = lean_ctor_get(v___x_4616_, 7);
v_snapshotTasks_4624_ = lean_ctor_get(v___x_4616_, 8);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4616_);
if (v_isSharedCheck_4635_ == 0)
{
lean_object* v_unused_4636_; 
v_unused_4636_ = lean_ctor_get(v___x_4616_, 5);
lean_dec(v_unused_4636_);
v___x_4626_ = v___x_4616_;
v_isShared_4627_ = v_isSharedCheck_4635_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_snapshotTasks_4624_);
lean_inc(v_infoState_4623_);
lean_inc(v_messages_4622_);
lean_inc(v_traceState_4621_);
lean_inc(v_auxDeclNGen_4620_);
lean_inc(v_ngen_4619_);
lean_inc(v_nextMacroScope_4618_);
lean_inc(v_env_4617_);
lean_dec(v___x_4616_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4635_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4628_; lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v___x_4632_; 
v___x_4628_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4629_ = lean_box(v___y_4615_);
lean_inc(v___y_4613_);
v___x_4630_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4628_, v_env_4617_, v___y_4613_, v___x_4629_);
if (v_isShared_4627_ == 0)
{
lean_ctor_set(v___x_4626_, 5, v___x_4608_);
lean_ctor_set(v___x_4626_, 0, v___x_4630_);
v___x_4632_ = v___x_4626_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v___x_4630_);
lean_ctor_set(v_reuseFailAlloc_4634_, 1, v_nextMacroScope_4618_);
lean_ctor_set(v_reuseFailAlloc_4634_, 2, v_ngen_4619_);
lean_ctor_set(v_reuseFailAlloc_4634_, 3, v_auxDeclNGen_4620_);
lean_ctor_set(v_reuseFailAlloc_4634_, 4, v_traceState_4621_);
lean_ctor_set(v_reuseFailAlloc_4634_, 5, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4634_, 6, v_messages_4622_);
lean_ctor_set(v_reuseFailAlloc_4634_, 7, v_infoState_4623_);
lean_ctor_set(v_reuseFailAlloc_4634_, 8, v_snapshotTasks_4624_);
v___x_4632_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
lean_object* v___x_4633_; 
v___x_4633_ = lean_st_ref_put(v___y_4614_, v___x_4632_);
v___y_4566_ = v___y_4612_;
v___y_4567_ = v___y_4613_;
v___y_4568_ = v___y_4615_;
v_exportedInfo_x3f_4569_ = v___y_4611_;
v___y_4570_ = v___y_4610_;
v___y_4571_ = v___y_4614_;
goto v___jp_4565_;
}
}
}
v_reusejp_4637_:
{
lean_object* v___x_4639_; lean_object* v___y_4641_; lean_object* v_options_4642_; lean_object* v_inheritedTraceOptions_4643_; lean_object* v___y_4644_; lean_object* v___x_4650_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; uint8_t v___y_4655_; lean_object* v___y_4656_; lean_object* v___y_4657_; lean_object* v_fst_4686_; lean_object* v_fst_4687_; uint8_t v_snd_4688_; lean_object* v_exportedInfo_x3f_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4701_; lean_object* v_exportedInfo_x3f_4702_; lean_object* v___y_4703_; lean_object* v___y_4704_; lean_object* v___y_4710_; lean_object* v___y_4711_; lean_object* v___y_4712_; lean_object* v___y_4713_; uint8_t v___y_4714_; lean_object* v___y_4719_; lean_object* v_toConstantVal_4720_; uint8_t v_safety_4721_; uint8_t v___y_4722_; lean_object* v___y_4723_; lean_object* v___y_4724_; lean_object* v___y_4728_; uint8_t v___y_4729_; lean_object* v___y_4730_; lean_object* v___y_4731_; lean_object* v___y_4735_; lean_object* v___y_4736_; lean_object* v___y_4737_; uint8_t v___y_4738_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4756_; lean_object* v___y_4757_; lean_object* v___y_4758_; lean_object* v_defn_4763_; lean_object* v___y_4764_; lean_object* v___y_4765_; 
v___x_4639_ = lean_st_ref_put(v_a_3748_, v___x_4638_);
v___x_4650_ = lean_box(0);
switch(lean_obj_tag(v_decl_3745_))
{
case 2:
{
lean_object* v_val_4772_; lean_object* v_exportedInfo_x3f_4774_; lean_object* v___y_4775_; lean_object* v___y_4776_; lean_object* v___y_4782_; lean_object* v___y_4783_; lean_object* v___x_4788_; lean_object* v_env_4789_; 
v_val_4772_ = lean_ctor_get(v_decl_3745_, 0);
v___x_4788_ = lean_st_ref_get(v_a_3748_);
v_env_4789_ = lean_ctor_get(v___x_4788_, 0);
lean_inc_ref(v_env_4789_);
lean_dec(v___x_4788_);
if (v_forceExpose_3746_ == 0)
{
goto v___jp_4790_;
}
else
{
if (v___x_4459_ == 0)
{
lean_dec_ref(v_env_4789_);
v_exportedInfo_x3f_4774_ = v___x_4650_;
v___y_4775_ = v_a_3747_;
v___y_4776_ = v_a_3748_;
goto v___jp_4773_;
}
else
{
goto v___jp_4790_;
}
}
v___jp_4773_:
{
lean_object* v_toConstantVal_4777_; lean_object* v_name_4778_; lean_object* v___x_4779_; uint8_t v___x_4780_; 
v_toConstantVal_4777_ = lean_ctor_get(v_val_4772_, 0);
v_name_4778_ = lean_ctor_get(v_toConstantVal_4777_, 0);
lean_inc_ref(v_val_4772_);
v___x_4779_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4779_, 0, v_val_4772_);
v___x_4780_ = 1;
lean_inc(v_name_4778_);
v_fst_4686_ = v_name_4778_;
v_fst_4687_ = v___x_4779_;
v_snd_4688_ = v___x_4780_;
v_exportedInfo_x3f_4689_ = v_exportedInfo_x3f_4774_;
v___y_4690_ = v___y_4775_;
v___y_4691_ = v___y_4776_;
goto v___jp_4685_;
}
v___jp_4781_:
{
lean_object* v_toConstantVal_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v_toConstantVal_4784_ = lean_ctor_get(v_val_4772_, 0);
lean_inc_ref(v_toConstantVal_4784_);
v___x_4785_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4785_, 0, v_toConstantVal_4784_);
lean_ctor_set_uint8(v___x_4785_, sizeof(void*)*1, v___x_4459_);
v___x_4786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4785_);
v___x_4787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4787_, 0, v___x_4786_);
v_exportedInfo_x3f_4774_ = v___x_4787_;
v___y_4775_ = v___y_4782_;
v___y_4776_ = v___y_4783_;
goto v___jp_4773_;
}
v___jp_4790_:
{
lean_object* v___x_4791_; uint8_t v_isModule_4792_; 
v___x_4791_ = l_Lean_Environment_header(v_env_4789_);
lean_dec_ref(v_env_4789_);
v_isModule_4792_ = lean_ctor_get_uint8(v___x_4791_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4791_);
if (v_isModule_4792_ == 0)
{
v_exportedInfo_x3f_4774_ = v___x_4650_;
v___y_4775_ = v_a_3747_;
v___y_4776_ = v_a_3748_;
goto v___jp_4773_;
}
else
{
if (v___x_4158_ == 0)
{
v___y_4782_ = v_a_3747_;
v___y_4783_ = v_a_3748_;
goto v___jp_4781_;
}
else
{
lean_object* v_toConstantVal_4793_; lean_object* v_name_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
v_toConstantVal_4793_ = lean_ctor_get(v_val_4772_, 0);
v_name_4794_ = lean_ctor_get(v_toConstantVal_4793_, 0);
v___x_4795_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4794_);
v___x_4796_ = l_Lean_MessageData_ofName(v_name_4794_);
v___x_4797_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4797_, 0, v___x_4795_);
lean_ctor_set(v___x_4797_, 1, v___x_4796_);
v___x_4798_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4799_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4799_, 0, v___x_4797_);
lean_ctor_set(v___x_4799_, 1, v___x_4798_);
v___x_4800_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4799_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_dec_ref_known(v___x_4800_, 1);
v___y_4782_ = v_a_3747_;
v___y_4783_ = v_a_3748_;
goto v___jp_4781_;
}
else
{
lean_dec_ref_known(v_decl_3745_, 1);
return v___x_4800_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4801_; 
v_val_4801_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref(v_val_4801_);
v_defn_4763_ = v_val_4801_;
v___y_4764_ = v_a_3747_;
v___y_4765_ = v_a_3748_;
goto v___jp_4762_;
}
case 5:
{
lean_object* v_defns_4802_; 
v_defns_4802_ = lean_ctor_get(v_decl_3745_, 0);
if (lean_obj_tag(v_defns_4802_) == 1)
{
lean_object* v_tail_4803_; 
v_tail_4803_ = lean_ctor_get(v_defns_4802_, 1);
if (lean_obj_tag(v_tail_4803_) == 0)
{
lean_object* v_head_4804_; 
v_head_4804_ = lean_ctor_get(v_defns_4802_, 0);
lean_inc(v_head_4804_);
v_defn_4763_ = v_head_4804_;
v___y_4764_ = v_a_3747_;
v___y_4765_ = v_a_3748_;
goto v___jp_4762_;
}
else
{
v___y_4641_ = v_a_3747_;
v_options_4642_ = v_options_3803_;
v_inheritedTraceOptions_4643_ = v_inheritedTraceOptions_3804_;
v___y_4644_ = v_a_3748_;
goto v___jp_4640_;
}
}
else
{
v___y_4641_ = v_a_3747_;
v_options_4642_ = v_options_3803_;
v_inheritedTraceOptions_4643_ = v_inheritedTraceOptions_3804_;
v___y_4644_ = v_a_3748_;
goto v___jp_4640_;
}
}
case 3:
{
lean_object* v_val_4805_; lean_object* v_exportedInfo_x3f_4807_; lean_object* v___y_4808_; lean_object* v___y_4809_; lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___x_4822_; lean_object* v___x_4823_; lean_object* v_env_4833_; lean_object* v_env_4834_; 
v_val_4805_ = lean_ctor_get(v_decl_3745_, 0);
v___x_4822_ = lean_st_ref_get(v_a_3748_);
v___x_4823_ = lean_st_ref_get(v_a_3748_);
v_env_4833_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_env_4833_);
lean_dec(v___x_4822_);
v_env_4834_ = lean_ctor_get(v___x_4823_, 0);
lean_inc_ref(v_env_4834_);
lean_dec(v___x_4823_);
if (v_forceExpose_3746_ == 0)
{
goto v___jp_4835_;
}
else
{
if (v___x_4459_ == 0)
{
lean_dec_ref(v_env_4834_);
lean_dec_ref(v_env_4833_);
v_exportedInfo_x3f_4807_ = v___x_4650_;
v___y_4808_ = v_a_3747_;
v___y_4809_ = v_a_3748_;
goto v___jp_4806_;
}
else
{
goto v___jp_4835_;
}
}
v___jp_4806_:
{
lean_object* v_toConstantVal_4810_; lean_object* v_name_4811_; lean_object* v___x_4812_; uint8_t v___x_4813_; 
v_toConstantVal_4810_ = lean_ctor_get(v_val_4805_, 0);
v_name_4811_ = lean_ctor_get(v_toConstantVal_4810_, 0);
lean_inc_ref(v_val_4805_);
v___x_4812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4812_, 0, v_val_4805_);
v___x_4813_ = 3;
lean_inc(v_name_4811_);
v_fst_4686_ = v_name_4811_;
v_fst_4687_ = v___x_4812_;
v_snd_4688_ = v___x_4813_;
v_exportedInfo_x3f_4689_ = v_exportedInfo_x3f_4807_;
v___y_4690_ = v___y_4808_;
v___y_4691_ = v___y_4809_;
goto v___jp_4685_;
}
v___jp_4814_:
{
lean_object* v_toConstantVal_4817_; uint8_t v_isUnsafe_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_toConstantVal_4817_ = lean_ctor_get(v_val_4805_, 0);
v_isUnsafe_4818_ = lean_ctor_get_uint8(v_val_4805_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4817_);
v___x_4819_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4819_, 0, v_toConstantVal_4817_);
lean_ctor_set_uint8(v___x_4819_, sizeof(void*)*1, v_isUnsafe_4818_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
v_exportedInfo_x3f_4807_ = v___x_4821_;
v___y_4808_ = v___y_4815_;
v___y_4809_ = v___y_4816_;
goto v___jp_4806_;
}
v___jp_4824_:
{
if (v___x_4158_ == 0)
{
v___y_4815_ = v_a_3747_;
v___y_4816_ = v_a_3748_;
goto v___jp_4814_;
}
else
{
lean_object* v_toConstantVal_4825_; lean_object* v_name_4826_; lean_object* v___x_4827_; lean_object* v___x_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; 
v_toConstantVal_4825_ = lean_ctor_get(v_val_4805_, 0);
v_name_4826_ = lean_ctor_get(v_toConstantVal_4825_, 0);
v___x_4827_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4826_);
v___x_4828_ = l_Lean_MessageData_ofName(v_name_4826_);
v___x_4829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4829_, 0, v___x_4827_);
lean_ctor_set(v___x_4829_, 1, v___x_4828_);
v___x_4830_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4831_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4832_) == 0)
{
lean_dec_ref_known(v___x_4832_, 1);
v___y_4815_ = v_a_3747_;
v___y_4816_ = v_a_3748_;
goto v___jp_4814_;
}
else
{
lean_dec_ref_known(v_decl_3745_, 1);
return v___x_4832_;
}
}
}
v___jp_4835_:
{
lean_object* v___x_4836_; uint8_t v_isModule_4837_; 
v___x_4836_ = l_Lean_Environment_header(v_env_4833_);
lean_dec_ref(v_env_4833_);
v_isModule_4837_ = lean_ctor_get_uint8(v___x_4836_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4836_);
if (v_isModule_4837_ == 0)
{
lean_dec_ref(v_env_4834_);
v_exportedInfo_x3f_4807_ = v___x_4650_;
v___y_4808_ = v_a_3747_;
v___y_4809_ = v_a_3748_;
goto v___jp_4806_;
}
else
{
uint8_t v_isExporting_4838_; 
v_isExporting_4838_ = lean_ctor_get_uint8(v_env_4834_, sizeof(void*)*8);
lean_dec_ref(v_env_4834_);
if (v_isExporting_4838_ == 0)
{
goto v___jp_4824_;
}
else
{
if (v___x_4459_ == 0)
{
v_exportedInfo_x3f_4807_ = v___x_4650_;
v___y_4808_ = v_a_3747_;
v___y_4809_ = v_a_3748_;
goto v___jp_4806_;
}
else
{
goto v___jp_4824_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4839_; lean_object* v_toConstantVal_4840_; lean_object* v_name_4841_; lean_object* v___x_4842_; uint8_t v___x_4843_; 
v_val_4839_ = lean_ctor_get(v_decl_3745_, 0);
v_toConstantVal_4840_ = lean_ctor_get(v_val_4839_, 0);
v_name_4841_ = lean_ctor_get(v_toConstantVal_4840_, 0);
lean_inc_ref(v_val_4839_);
v___x_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4842_, 0, v_val_4839_);
v___x_4843_ = 2;
lean_inc(v_name_4841_);
v_fst_4686_ = v_name_4841_;
v_fst_4687_ = v___x_4842_;
v_snd_4688_ = v___x_4843_;
v_exportedInfo_x3f_4689_ = v___x_4650_;
v___y_4690_ = v_a_3747_;
v___y_4691_ = v_a_3748_;
goto v___jp_4685_;
}
default: 
{
v___y_4641_ = v_a_3747_;
v_options_4642_ = v_options_3803_;
v_inheritedTraceOptions_4643_ = v_inheritedTraceOptions_3804_;
v___y_4644_ = v_a_3748_;
goto v___jp_4640_;
}
}
v___jp_4640_:
{
uint8_t v___x_4645_; 
v___x_4645_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4643_, v_options_4642_, v___x_4157_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; 
v___x_4646_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v___y_4641_, v___y_4644_);
return v___x_4646_;
}
else
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
v___x_4647_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4648_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4647_, v___y_4641_, v___y_4644_);
if (lean_obj_tag(v___x_4648_) == 0)
{
lean_object* v___x_4649_; 
lean_dec_ref_known(v___x_4648_, 1);
v___x_4649_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v___y_4641_, v___y_4644_);
return v___x_4649_;
}
else
{
lean_dec(v_decl_3745_);
return v___x_4648_;
}
}
}
v___jp_4651_:
{
lean_object* v___x_4658_; uint8_t v___x_4659_; 
lean_inc(v_decl_3745_);
v___x_4658_ = l_Lean_Declaration_getTopLevelNames(v_decl_3745_);
v___x_4659_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4658_);
lean_dec(v___x_4658_);
if (v___x_4659_ == 0)
{
if (lean_obj_tag(v___y_4652_) == 0)
{
if (v___x_4659_ == 0)
{
lean_object* v_toCold_4660_; lean_object* v_options_4661_; uint8_t v_hasTrace_4662_; 
v_toCold_4660_ = lean_ctor_get(v___y_4656_, 0);
v_options_4661_ = lean_ctor_get(v_toCold_4660_, 2);
v_hasTrace_4662_ = lean_ctor_get_uint8(v_options_4661_, sizeof(void*)*1);
if (v_hasTrace_4662_ == 0)
{
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
v___y_4585_ = v___y_4657_;
goto v___jp_4580_;
}
else
{
lean_object* v_inheritedTraceOptions_4663_; uint8_t v___x_4664_; 
v_inheritedTraceOptions_4663_ = lean_ctor_get(v_toCold_4660_, 11);
v___x_4664_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4663_, v_options_4661_, v___x_4157_);
if (v___x_4664_ == 0)
{
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
v___y_4585_ = v___y_4657_;
goto v___jp_4580_;
}
else
{
lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4665_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4666_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4665_, v___y_4656_, v___y_4657_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_dec_ref_known(v___x_4666_, 1);
v___y_4581_ = v___y_4653_;
v___y_4582_ = v___y_4654_;
v___y_4583_ = v___y_4655_;
v___y_4584_ = v___y_4656_;
v___y_4585_ = v___y_4657_;
goto v___jp_4580_;
}
else
{
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v_decl_3745_);
return v___x_4666_;
}
}
}
}
else
{
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4652_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4654_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4655_;
goto v___jp_4609_;
}
}
else
{
v___y_4610_ = v___y_4656_;
v___y_4611_ = v___y_4652_;
v___y_4612_ = v___y_4653_;
v___y_4613_ = v___y_4654_;
v___y_4614_ = v___y_4657_;
v___y_4615_ = v___y_4655_;
goto v___jp_4609_;
}
}
else
{
lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v_a_4669_; uint8_t v___x_4670_; 
lean_dec(v___y_4652_);
v___x_4667_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4668_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4667_, v___y_4656_);
v_a_4669_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_a_4669_);
lean_dec_ref(v___x_4668_);
v___x_4670_ = lean_unbox(v_a_4669_);
lean_dec(v_a_4669_);
if (v___x_4670_ == 0)
{
lean_object* v_toCold_4671_; lean_object* v_options_4672_; uint8_t v_hasTrace_4673_; 
v_toCold_4671_ = lean_ctor_get(v___y_4656_, 0);
v_options_4672_ = lean_ctor_get(v_toCold_4671_, 2);
v_hasTrace_4673_ = lean_ctor_get_uint8(v_options_4672_, sizeof(void*)*1);
if (v_hasTrace_4673_ == 0)
{
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v___y_4568_ = v___y_4655_;
v_exportedInfo_x3f_4569_ = v___x_4650_;
v___y_4570_ = v___y_4656_;
v___y_4571_ = v___y_4657_;
goto v___jp_4565_;
}
else
{
lean_object* v_inheritedTraceOptions_4674_; uint8_t v___x_4675_; 
v_inheritedTraceOptions_4674_ = lean_ctor_get(v_toCold_4671_, 11);
v___x_4675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4674_, v_options_4672_, v___x_4157_);
if (v___x_4675_ == 0)
{
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v___y_4568_ = v___y_4655_;
v_exportedInfo_x3f_4569_ = v___x_4650_;
v___y_4570_ = v___y_4656_;
v___y_4571_ = v___y_4657_;
goto v___jp_4565_;
}
else
{
lean_object* v___x_4676_; lean_object* v___x_4677_; 
v___x_4676_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4677_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4676_, v___y_4656_, v___y_4657_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_dec_ref_known(v___x_4677_, 1);
v___y_4566_ = v___y_4653_;
v___y_4567_ = v___y_4654_;
v___y_4568_ = v___y_4655_;
v_exportedInfo_x3f_4569_ = v___x_4650_;
v___y_4570_ = v___y_4656_;
v___y_4571_ = v___y_4657_;
goto v___jp_4565_;
}
else
{
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v_decl_3745_);
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_toCold_4678_; lean_object* v_options_4679_; uint8_t v_hasTrace_4680_; 
v_toCold_4678_ = lean_ctor_get(v___y_4656_, 0);
v_options_4679_ = lean_ctor_get(v_toCold_4678_, 2);
v_hasTrace_4680_ = lean_ctor_get_uint8(v_options_4679_, sizeof(void*)*1);
if (v_hasTrace_4680_ == 0)
{
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
v___y_4592_ = v___y_4657_;
goto v___jp_4587_;
}
else
{
lean_object* v_inheritedTraceOptions_4681_; uint8_t v___x_4682_; 
v_inheritedTraceOptions_4681_ = lean_ctor_get(v_toCold_4678_, 11);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4681_, v_options_4679_, v___x_4157_);
if (v___x_4682_ == 0)
{
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
v___y_4592_ = v___y_4657_;
goto v___jp_4587_;
}
else
{
lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4683_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4684_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4683_, v___y_4656_, v___y_4657_);
if (lean_obj_tag(v___x_4684_) == 0)
{
lean_dec_ref_known(v___x_4684_, 1);
v___y_4588_ = v___y_4653_;
v___y_4589_ = v___y_4654_;
v___y_4590_ = v___y_4655_;
v___y_4591_ = v___y_4656_;
v___y_4592_ = v___y_4657_;
goto v___jp_4587_;
}
else
{
lean_dec(v___y_4654_);
lean_dec_ref(v___y_4653_);
lean_dec(v_decl_3745_);
return v___x_4684_;
}
}
}
}
}
}
v___jp_4685_:
{
lean_object* v___x_4692_; lean_object* v_env_4693_; uint8_t v___x_4694_; 
v___x_4692_ = lean_st_ref_get(v___y_4691_);
v_env_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc_ref(v_env_4693_);
lean_dec(v___x_4692_);
v___x_4694_ = l_Lean_Environment_containsOnBranch(v_env_4693_, v_fst_4686_);
lean_dec_ref(v_env_4693_);
if (v___x_4694_ == 0)
{
v___y_4652_ = v_exportedInfo_x3f_4689_;
v___y_4653_ = v_fst_4687_;
v___y_4654_ = v_fst_4686_;
v___y_4655_ = v_snd_4688_;
v___y_4656_ = v___y_4690_;
v___y_4657_ = v___y_4691_;
goto v___jp_4651_;
}
else
{
lean_object* v___x_4695_; lean_object* v_env_4696_; lean_object* v___x_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
lean_dec(v_exportedInfo_x3f_4689_);
lean_dec_ref(v_fst_4687_);
lean_dec(v_decl_3745_);
v___x_4695_ = lean_st_ref_get(v___y_4691_);
v_env_4696_ = lean_ctor_get(v___x_4695_, 0);
lean_inc_ref(v_env_4696_);
lean_dec(v___x_4695_);
v___x_4697_ = lean_elab_environment_to_kernel_env(v_env_4696_);
v___x_4698_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4698_, 0, v___x_4697_);
lean_ctor_set(v___x_4698_, 1, v_fst_4686_);
v___x_4699_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4698_, v___y_4690_, v___y_4691_);
return v___x_4699_;
}
}
v___jp_4700_:
{
lean_object* v_toConstantVal_4705_; lean_object* v_name_4706_; lean_object* v___x_4707_; uint8_t v___x_4708_; 
v_toConstantVal_4705_ = lean_ctor_get(v___y_4701_, 0);
v_name_4706_ = lean_ctor_get(v_toConstantVal_4705_, 0);
lean_inc(v_name_4706_);
v___x_4707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4707_, 0, v___y_4701_);
v___x_4708_ = 0;
v_fst_4686_ = v_name_4706_;
v_fst_4687_ = v___x_4707_;
v_snd_4688_ = v___x_4708_;
v_exportedInfo_x3f_4689_ = v_exportedInfo_x3f_4702_;
v___y_4690_ = v___y_4703_;
v___y_4691_ = v___y_4704_;
goto v___jp_4685_;
}
v___jp_4709_:
{
lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; 
v___x_4715_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4715_, 0, v___y_4713_);
lean_ctor_set_uint8(v___x_4715_, sizeof(void*)*1, v___y_4714_);
v___x_4716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4716_, 0, v___x_4715_);
v___x_4717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4716_);
v___y_4701_ = v___y_4710_;
v_exportedInfo_x3f_4702_ = v___x_4717_;
v___y_4703_ = v___y_4712_;
v___y_4704_ = v___y_4711_;
goto v___jp_4700_;
}
v___jp_4718_:
{
uint8_t v___x_4725_; uint8_t v___x_4726_; 
v___x_4725_ = 1;
v___x_4726_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4721_, v___x_4725_);
if (v___x_4726_ == 0)
{
v___y_4710_ = v___y_4719_;
v___y_4711_ = v___y_4724_;
v___y_4712_ = v___y_4723_;
v___y_4713_ = v_toConstantVal_4720_;
v___y_4714_ = v___y_4722_;
goto v___jp_4709_;
}
else
{
v___y_4710_ = v___y_4719_;
v___y_4711_ = v___y_4724_;
v___y_4712_ = v___y_4723_;
v___y_4713_ = v_toConstantVal_4720_;
v___y_4714_ = v___x_4459_;
goto v___jp_4709_;
}
}
v___jp_4727_:
{
lean_object* v_toConstantVal_4732_; uint8_t v_safety_4733_; 
v_toConstantVal_4732_ = lean_ctor_get(v___y_4728_, 0);
lean_inc_ref(v_toConstantVal_4732_);
v_safety_4733_ = lean_ctor_get_uint8(v___y_4728_, sizeof(void*)*4);
v___y_4719_ = v___y_4728_;
v_toConstantVal_4720_ = v_toConstantVal_4732_;
v_safety_4721_ = v_safety_4733_;
v___y_4722_ = v___y_4729_;
v___y_4723_ = v___y_4730_;
v___y_4724_ = v___y_4731_;
goto v___jp_4718_;
}
v___jp_4734_:
{
lean_object* v_toCold_4739_; lean_object* v_options_4740_; uint8_t v_hasTrace_4741_; 
v_toCold_4739_ = lean_ctor_get(v___y_4735_, 0);
v_options_4740_ = lean_ctor_get(v_toCold_4739_, 2);
v_hasTrace_4741_ = lean_ctor_get_uint8(v_options_4740_, sizeof(void*)*1);
if (v_hasTrace_4741_ == 0)
{
v___y_4728_ = v___y_4737_;
v___y_4729_ = v___y_4738_;
v___y_4730_ = v___y_4735_;
v___y_4731_ = v___y_4736_;
goto v___jp_4727_;
}
else
{
lean_object* v_inheritedTraceOptions_4742_; uint8_t v___x_4743_; 
v_inheritedTraceOptions_4742_ = lean_ctor_get(v_toCold_4739_, 11);
v___x_4743_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4742_, v_options_4740_, v___x_4157_);
if (v___x_4743_ == 0)
{
v___y_4728_ = v___y_4737_;
v___y_4729_ = v___y_4738_;
v___y_4730_ = v___y_4735_;
v___y_4731_ = v___y_4736_;
goto v___jp_4727_;
}
else
{
lean_object* v_toConstantVal_4744_; uint8_t v_safety_4745_; lean_object* v_name_4746_; lean_object* v___x_4747_; lean_object* v___x_4748_; lean_object* v___x_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v_toConstantVal_4744_ = lean_ctor_get(v___y_4737_, 0);
lean_inc_ref(v_toConstantVal_4744_);
v_safety_4745_ = lean_ctor_get_uint8(v___y_4737_, sizeof(void*)*4);
v_name_4746_ = lean_ctor_get(v_toConstantVal_4744_, 0);
v___x_4747_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4746_);
v___x_4748_ = l_Lean_MessageData_ofName(v_name_4746_);
v___x_4749_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4749_, 0, v___x_4747_);
lean_ctor_set(v___x_4749_, 1, v___x_4748_);
v___x_4750_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4751_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4749_);
lean_ctor_set(v___x_4751_, 1, v___x_4750_);
v___x_4752_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4751_, v___y_4735_, v___y_4736_);
if (lean_obj_tag(v___x_4752_) == 0)
{
lean_dec_ref_known(v___x_4752_, 1);
v___y_4719_ = v___y_4737_;
v_toConstantVal_4720_ = v_toConstantVal_4744_;
v_safety_4721_ = v_safety_4745_;
v___y_4722_ = v___y_4738_;
v___y_4723_ = v___y_4735_;
v___y_4724_ = v___y_4736_;
goto v___jp_4718_;
}
else
{
lean_dec_ref(v_toConstantVal_4744_);
lean_dec_ref(v___y_4737_);
lean_dec(v_decl_3745_);
return v___x_4752_;
}
}
}
}
v___jp_4753_:
{
lean_object* v___x_4759_; uint8_t v_isModule_4760_; 
v___x_4759_ = l_Lean_Environment_header(v___y_4756_);
lean_dec_ref(v___y_4756_);
v_isModule_4760_ = lean_ctor_get_uint8(v___x_4759_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4759_);
if (v_isModule_4760_ == 0)
{
lean_dec_ref(v___y_4758_);
v___y_4701_ = v___y_4757_;
v_exportedInfo_x3f_4702_ = v___x_4650_;
v___y_4703_ = v___y_4754_;
v___y_4704_ = v___y_4755_;
goto v___jp_4700_;
}
else
{
uint8_t v_isExporting_4761_; 
v_isExporting_4761_ = lean_ctor_get_uint8(v___y_4758_, sizeof(void*)*8);
lean_dec_ref(v___y_4758_);
if (v_isExporting_4761_ == 0)
{
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4755_;
v___y_4737_ = v___y_4757_;
v___y_4738_ = v_isModule_4760_;
goto v___jp_4734_;
}
else
{
if (v___x_4459_ == 0)
{
v___y_4701_ = v___y_4757_;
v_exportedInfo_x3f_4702_ = v___x_4650_;
v___y_4703_ = v___y_4754_;
v___y_4704_ = v___y_4755_;
goto v___jp_4700_;
}
else
{
v___y_4735_ = v___y_4754_;
v___y_4736_ = v___y_4755_;
v___y_4737_ = v___y_4757_;
v___y_4738_ = v___x_4459_;
goto v___jp_4734_;
}
}
}
}
v___jp_4762_:
{
lean_object* v___x_4766_; lean_object* v___x_4767_; 
v___x_4766_ = lean_st_ref_get(v___y_4765_);
v___x_4767_ = lean_st_ref_get(v___y_4765_);
if (v_forceExpose_3746_ == 0)
{
lean_object* v_env_4768_; lean_object* v_env_4769_; 
v_env_4768_ = lean_ctor_get(v___x_4766_, 0);
lean_inc_ref(v_env_4768_);
lean_dec(v___x_4766_);
v_env_4769_ = lean_ctor_get(v___x_4767_, 0);
lean_inc_ref(v_env_4769_);
lean_dec(v___x_4767_);
v___y_4754_ = v___y_4764_;
v___y_4755_ = v___y_4765_;
v___y_4756_ = v_env_4768_;
v___y_4757_ = v_defn_4763_;
v___y_4758_ = v_env_4769_;
goto v___jp_4753_;
}
else
{
if (v___x_4459_ == 0)
{
lean_dec(v___x_4767_);
lean_dec(v___x_4766_);
v___y_4701_ = v_defn_4763_;
v_exportedInfo_x3f_4702_ = v___x_4650_;
v___y_4703_ = v___y_4764_;
v___y_4704_ = v___y_4765_;
goto v___jp_4700_;
}
else
{
lean_object* v_env_4770_; lean_object* v_env_4771_; 
v_env_4770_ = lean_ctor_get(v___x_4766_, 0);
lean_inc_ref(v_env_4770_);
lean_dec(v___x_4766_);
v_env_4771_ = lean_ctor_get(v___x_4767_, 0);
lean_inc_ref(v_env_4771_);
lean_dec(v___x_4767_);
v___y_4754_ = v___y_4764_;
v___y_4755_ = v___y_4765_;
v___y_4756_ = v_env_4770_;
v___y_4757_ = v_defn_4763_;
v___y_4758_ = v_env_4771_;
goto v___jp_4753_;
}
}
}
}
}
}
else
{
goto v___jp_4306_;
}
v___jp_4460_:
{
lean_object* v___x_4471_; 
lean_inc_ref(v___y_4467_);
v___x_4471_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4463_, v___y_4467_, v___y_4468_, v___y_4470_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v___x_4472_; lean_object* v___x_4474_; uint8_t v_isShared_4475_; uint8_t v_isSharedCheck_4519_; 
lean_dec_ref_known(v___x_4471_, 1);
lean_inc_ref(v___y_4462_);
v___x_4472_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4462_, v___y_4469_);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4472_);
if (v_isSharedCheck_4519_ == 0)
{
lean_object* v_unused_4520_; 
v_unused_4520_ = lean_ctor_get(v___x_4472_, 0);
lean_dec(v_unused_4520_);
v___x_4474_ = v___x_4472_;
v_isShared_4475_ = v_isSharedCheck_4519_;
goto v_resetjp_4473_;
}
else
{
lean_dec(v___x_4472_);
v___x_4474_ = lean_box(0);
v_isShared_4475_ = v_isSharedCheck_4519_;
goto v_resetjp_4473_;
}
v_resetjp_4473_:
{
lean_object* v_toCold_4476_; lean_object* v_options_4477_; lean_object* v___x_4478_; uint8_t v___x_4479_; 
v_toCold_4476_ = lean_ctor_get(v___y_4466_, 0);
v_options_4477_ = lean_ctor_get(v_toCold_4476_, 2);
v___x_4478_ = l_Lean_Elab_async;
v___x_4479_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4477_, v___x_4478_);
if (v___x_4479_ == 0)
{
lean_object* v___x_4480_; lean_object* v_r_4481_; 
lean_del_object(v___x_4474_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v___y_4464_);
v___x_4480_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4467_, v___y_4469_);
lean_dec_ref(v___x_4480_);
v_r_4481_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v___y_4466_, v___y_4469_);
if (lean_obj_tag(v_r_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4491_; 
v_a_4482_ = lean_ctor_get(v_r_4481_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v_r_4481_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4484_ = v_r_4481_;
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v_r_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4491_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v___x_4487_; 
lean_inc(v_a_4482_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set_tag(v___x_4484_, 1);
v___x_4487_ = v___x_4484_;
goto v_reusejp_4486_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4482_);
v___x_4487_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4486_;
}
v_reusejp_4486_:
{
lean_object* v___x_4488_; 
v___x_4488_ = lean_apply_2(v___y_4461_, v___x_4487_, lean_box(0));
if (lean_obj_tag(v___x_4488_) == 0)
{
lean_dec_ref_known(v___x_4488_, 1);
v___y_3751_ = v___y_4462_;
v___y_3752_ = v___y_4469_;
v_a_3753_ = v_a_4482_;
goto v___jp_3750_;
}
else
{
lean_object* v_a_4489_; 
lean_dec(v_a_4482_);
v_a_4489_ = lean_ctor_get(v___x_4488_, 0);
lean_inc(v_a_4489_);
lean_dec_ref_known(v___x_4488_, 1);
v___y_3764_ = v___y_4462_;
v___y_3765_ = v___y_4469_;
v_a_3766_ = v_a_4489_;
goto v___jp_3763_;
}
}
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4493_; lean_object* v___x_4494_; 
v_a_4492_ = lean_ctor_get(v_r_4481_, 0);
lean_inc(v_a_4492_);
lean_dec_ref_known(v_r_4481_, 1);
v___x_4493_ = lean_box(0);
v___x_4494_ = lean_apply_2(v___y_4461_, v___x_4493_, lean_box(0));
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_dec_ref_known(v___x_4494_, 1);
v___y_3764_ = v___y_4462_;
v___y_3765_ = v___y_4469_;
v_a_3766_ = v_a_4492_;
goto v___jp_3763_;
}
else
{
lean_object* v_a_4495_; 
lean_dec(v_a_4492_);
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
v___y_3764_ = v___y_4462_;
v___y_3765_ = v___y_4469_;
v_a_3766_ = v_a_4495_;
goto v___jp_3763_;
}
}
}
else
{
lean_object* v___x_4496_; lean_object* v___x_4498_; 
lean_dec_ref(v___y_4467_);
lean_dec_ref(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v_decl_3745_);
v___x_4496_ = l_IO_CancelToken_new();
if (v_isShared_4475_ == 0)
{
lean_ctor_set_tag(v___x_4474_, 1);
lean_ctor_set(v___x_4474_, 0, v___x_4496_);
v___x_4498_ = v___x_4474_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v___x_4496_);
v___x_4498_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; lean_object* v___x_4502_; 
v___x_4499_ = lean_unsigned_to_nat(0u);
v___x_4500_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4501_ = l_Lean_Name_toString(v___x_4500_, v_hasTrace_3805_);
lean_inc_ref(v___x_4498_);
v___x_4502_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4464_, v___x_4498_, v___x_4501_, v___y_4466_, v___y_4469_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v_a_4503_; lean_object* v_checked_4504_; lean_object* v___x_4505_; lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v_a_4503_ = lean_ctor_get(v___x_4502_, 0);
lean_inc(v_a_4503_);
lean_dec_ref_known(v___x_4502_, 1);
v_checked_4504_ = lean_ctor_get(v___y_4465_, 2);
lean_inc_ref(v_checked_4504_);
lean_dec_ref(v___y_4465_);
v___x_4505_ = lean_io_map_task(v_a_4503_, v_checked_4504_, v___x_4499_, v___x_4459_);
v___x_4506_ = lean_box(0);
v___x_4507_ = lean_box(2);
v___x_4508_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
lean_ctor_set(v___x_4508_, 2, v___x_4498_);
lean_ctor_set(v___x_4508_, 3, v___x_4505_);
v___x_4509_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4508_, v___y_4469_);
return v___x_4509_;
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec_ref(v___x_4498_);
lean_dec_ref(v___y_4465_);
v_a_4510_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4502_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4502_);
v___x_4512_ = lean_box(0);
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
v_resetjp_4511_:
{
lean_object* v___x_4515_; 
if (v_isShared_4513_ == 0)
{
v___x_4515_ = v___x_4512_;
goto v_reusejp_4514_;
}
else
{
lean_object* v_reuseFailAlloc_4516_; 
v_reuseFailAlloc_4516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4516_, 0, v_a_4510_);
v___x_4515_ = v_reuseFailAlloc_4516_;
goto v_reusejp_4514_;
}
v_reusejp_4514_:
{
return v___x_4515_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4533_; 
lean_dec_ref(v___y_4467_);
lean_dec_ref(v___y_4465_);
lean_dec_ref(v___y_4464_);
lean_dec_ref(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v_decl_3745_);
v_a_4521_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4533_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4533_ == 0)
{
v___x_4523_ = v___x_4471_;
v_isShared_4524_ = v_isSharedCheck_4533_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4471_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4533_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v_ref_4525_; lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; lean_object* v___x_4531_; 
v_ref_4525_ = lean_ctor_get(v___y_4466_, 2);
v___x_4526_ = lean_io_error_to_string(v_a_4521_);
v___x_4527_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4527_, 0, v___x_4526_);
v___x_4528_ = l_Lean_MessageData_ofFormat(v___x_4527_);
lean_inc(v_ref_4525_);
v___x_4529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4529_, 0, v_ref_4525_);
lean_ctor_set(v___x_4529_, 1, v___x_4528_);
if (v_isShared_4524_ == 0)
{
lean_ctor_set(v___x_4523_, 0, v___x_4529_);
v___x_4531_ = v___x_4523_;
goto v_reusejp_4530_;
}
else
{
lean_object* v_reuseFailAlloc_4532_; 
v_reuseFailAlloc_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4532_, 0, v___x_4529_);
v___x_4531_ = v_reuseFailAlloc_4532_;
goto v_reusejp_4530_;
}
v_reusejp_4530_:
{
return v___x_4531_;
}
}
}
}
v___jp_4534_:
{
lean_object* v___x_4545_; 
lean_inc_ref(v___y_4536_);
v___x_4545_ = l_Lean_Environment_addConstAsync(v___y_4536_, v___y_4540_, v___y_4543_, v___y_4544_, v___x_4459_, v_hasTrace_3805_);
if (lean_obj_tag(v___x_4545_) == 0)
{
lean_object* v_a_4546_; lean_object* v_mainEnv_4547_; lean_object* v_asyncEnv_4548_; lean_object* v___f_4549_; lean_object* v___f_4550_; lean_object* v___x_4551_; 
v_a_4546_ = lean_ctor_get(v___x_4545_, 0);
lean_inc_n(v_a_4546_, 3);
lean_dec_ref_known(v___x_4545_, 1);
v_mainEnv_4547_ = lean_ctor_get(v_a_4546_, 0);
lean_inc_ref(v_mainEnv_4547_);
v_asyncEnv_4548_ = lean_ctor_get(v_a_4546_, 1);
lean_inc_ref_n(v_asyncEnv_4548_, 2);
lean_inc_ref(v___y_4535_);
lean_inc(v___y_4537_);
v___f_4549_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4549_, 0, v___y_4537_);
lean_closure_set(v___f_4549_, 1, v_a_4546_);
lean_closure_set(v___f_4549_, 2, v___y_4535_);
lean_inc(v_decl_3745_);
v___f_4550_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4550_, 0, v_asyncEnv_4548_);
lean_closure_set(v___f_4550_, 1, v_a_4546_);
lean_closure_set(v___f_4550_, 2, v_decl_3745_);
v___x_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4551_, 0, v___y_4538_);
if (lean_obj_tag(v___y_4542_) == 0)
{
lean_inc_ref(v___x_4551_);
v___y_4461_ = v___f_4549_;
v___y_4462_ = v_mainEnv_4547_;
v___y_4463_ = v_a_4546_;
v___y_4464_ = v___f_4550_;
v___y_4465_ = v___y_4536_;
v___y_4466_ = v___y_4539_;
v___y_4467_ = v_asyncEnv_4548_;
v___y_4468_ = v___x_4551_;
v___y_4469_ = v___y_4541_;
v___y_4470_ = v___x_4551_;
goto v___jp_4460_;
}
else
{
v___y_4461_ = v___f_4549_;
v___y_4462_ = v_mainEnv_4547_;
v___y_4463_ = v_a_4546_;
v___y_4464_ = v___f_4550_;
v___y_4465_ = v___y_4536_;
v___y_4466_ = v___y_4539_;
v___y_4467_ = v_asyncEnv_4548_;
v___y_4468_ = v___x_4551_;
v___y_4469_ = v___y_4541_;
v___y_4470_ = v___y_4542_;
goto v___jp_4460_;
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4564_; 
lean_dec(v___y_4542_);
lean_dec_ref(v___y_4538_);
lean_dec_ref(v___y_4536_);
lean_dec(v_decl_3745_);
v_a_4552_ = lean_ctor_get(v___x_4545_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4545_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4554_ = v___x_4545_;
v_isShared_4555_ = v_isSharedCheck_4564_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4545_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4564_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v_ref_4556_; lean_object* v___x_4557_; lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4562_; 
v_ref_4556_ = lean_ctor_get(v___y_4539_, 2);
v___x_4557_ = lean_io_error_to_string(v_a_4552_);
v___x_4558_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4558_, 0, v___x_4557_);
v___x_4559_ = l_Lean_MessageData_ofFormat(v___x_4558_);
lean_inc(v_ref_4556_);
v___x_4560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4560_, 0, v_ref_4556_);
lean_ctor_set(v___x_4560_, 1, v___x_4559_);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 0, v___x_4560_);
v___x_4562_ = v___x_4554_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v___x_4560_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
v___jp_4565_:
{
lean_object* v___x_4572_; 
v___x_4572_ = lean_st_ref_get(v___y_4571_);
if (lean_obj_tag(v_exportedInfo_x3f_4569_) == 0)
{
lean_object* v_env_4573_; lean_object* v___x_4574_; 
v_env_4573_ = lean_ctor_get(v___x_4572_, 0);
lean_inc_ref(v_env_4573_);
lean_dec(v___x_4572_);
v___x_4574_ = lean_box(0);
v___y_4535_ = v___y_4570_;
v___y_4536_ = v_env_4573_;
v___y_4537_ = v___y_4571_;
v___y_4538_ = v___y_4566_;
v___y_4539_ = v___y_4570_;
v___y_4540_ = v___y_4567_;
v___y_4541_ = v___y_4571_;
v___y_4542_ = v_exportedInfo_x3f_4569_;
v___y_4543_ = v___y_4568_;
v___y_4544_ = v___x_4574_;
goto v___jp_4534_;
}
else
{
lean_object* v_env_4575_; lean_object* v_val_4576_; uint8_t v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; 
v_env_4575_ = lean_ctor_get(v___x_4572_, 0);
lean_inc_ref(v_env_4575_);
lean_dec(v___x_4572_);
v_val_4576_ = lean_ctor_get(v_exportedInfo_x3f_4569_, 0);
v___x_4577_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4576_);
v___x_4578_ = lean_box(v___x_4577_);
v___x_4579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4579_, 0, v___x_4578_);
v___y_4535_ = v___y_4570_;
v___y_4536_ = v_env_4575_;
v___y_4537_ = v___y_4571_;
v___y_4538_ = v___y_4566_;
v___y_4539_ = v___y_4570_;
v___y_4540_ = v___y_4567_;
v___y_4541_ = v___y_4571_;
v___y_4542_ = v_exportedInfo_x3f_4569_;
v___y_4543_ = v___y_4568_;
v___y_4544_ = v___x_4579_;
goto v___jp_4534_;
}
}
v___jp_4580_:
{
lean_object* v___x_4586_; 
lean_inc_ref(v___y_4581_);
v___x_4586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4586_, 0, v___y_4581_);
v___y_4566_ = v___y_4581_;
v___y_4567_ = v___y_4582_;
v___y_4568_ = v___y_4583_;
v_exportedInfo_x3f_4569_ = v___x_4586_;
v___y_4570_ = v___y_4584_;
v___y_4571_ = v___y_4585_;
goto v___jp_4565_;
}
v___jp_4587_:
{
lean_object* v___x_4593_; 
lean_inc_ref(v___y_4588_);
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v___y_4588_);
v___y_4566_ = v___y_4588_;
v___y_4567_ = v___y_4589_;
v___y_4568_ = v___y_4590_;
v_exportedInfo_x3f_4569_ = v___x_4593_;
v___y_4570_ = v___y_4591_;
v___y_4571_ = v___y_4592_;
goto v___jp_4565_;
}
}
else
{
goto v___jp_4306_;
}
v___jp_4159_:
{
lean_object* v___x_4163_; double v___x_4164_; double v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; 
v___x_4163_ = lean_io_get_num_heartbeats();
v___x_4164_ = lean_float_of_nat(v___y_4161_);
v___x_4165_ = lean_float_of_nat(v___x_4163_);
v___x_4166_ = lean_box_float(v___x_4164_);
v___x_4167_ = lean_box_float(v___x_4165_);
v___x_4168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4166_);
lean_ctor_set(v___x_4168_, 1, v___x_4167_);
v___x_4169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4169_, 0, v_a_4162_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3942_, v_hasTrace_3805_, v___x_4156_, v_options_3803_, v___x_4158_, v___y_4160_, v___f_4155_, v___x_4169_, v_a_3747_, v_a_3748_);
return v___x_4170_;
}
v___jp_4171_:
{
if (lean_obj_tag(v___y_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
v_a_4175_ = lean_ctor_get(v___y_4174_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___y_4174_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___y_4174_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___y_4174_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
lean_ctor_set_tag(v___x_4177_, 1);
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
v___y_4160_ = v___y_4172_;
v___y_4161_ = v___y_4173_;
v_a_4162_ = v___x_4180_;
goto v___jp_4159_;
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
v_a_4183_ = lean_ctor_get(v___y_4174_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___y_4174_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___y_4174_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___y_4174_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
lean_ctor_set_tag(v___x_4185_, 0);
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
v___y_4160_ = v___y_4172_;
v___y_4161_ = v___y_4173_;
v_a_4162_ = v___x_4188_;
goto v___jp_4159_;
}
}
}
}
v___jp_4191_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4197_ = lean_apply_5(v___y_4195_, v___x_4196_, v___y_4192_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4172_ = v___y_4193_;
v___y_4173_ = v___y_4194_;
v___y_4174_ = v___x_4197_;
goto v___jp_4171_;
}
v___jp_4198_:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4204_ = lean_apply_5(v___y_4202_, v___x_4203_, v___y_4199_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4172_ = v___y_4200_;
v___y_4173_ = v___y_4201_;
v___y_4174_ = v___x_4204_;
goto v___jp_4171_;
}
v___jp_4205_:
{
lean_object* v___x_4209_; double v___x_4210_; double v___x_4211_; double v___x_4212_; double v___x_4213_; double v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; lean_object* v___x_4219_; 
v___x_4209_ = lean_io_mono_nanos_now();
v___x_4210_ = lean_float_of_nat(v___y_4207_);
v___x_4211_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4212_ = lean_float_div(v___x_4210_, v___x_4211_);
v___x_4213_ = lean_float_of_nat(v___x_4209_);
v___x_4214_ = lean_float_div(v___x_4213_, v___x_4211_);
v___x_4215_ = lean_box_float(v___x_4212_);
v___x_4216_ = lean_box_float(v___x_4214_);
v___x_4217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4218_, 0, v_a_4208_);
lean_ctor_set(v___x_4218_, 1, v___x_4217_);
v___x_4219_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3942_, v_hasTrace_3805_, v___x_4156_, v_options_3803_, v___x_4158_, v___y_4206_, v___f_4155_, v___x_4218_, v_a_3747_, v_a_3748_);
return v___x_4219_;
}
v___jp_4220_:
{
if (lean_obj_tag(v___y_4223_) == 0)
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
v_a_4224_ = lean_ctor_get(v___y_4223_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___y_4223_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___y_4223_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___y_4223_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
lean_ctor_set_tag(v___x_4226_, 1);
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
v___y_4206_ = v___y_4221_;
v___y_4207_ = v___y_4222_;
v_a_4208_ = v___x_4229_;
goto v___jp_4205_;
}
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
v_a_4232_ = lean_ctor_get(v___y_4223_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___y_4223_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___y_4223_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___y_4223_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
lean_ctor_set_tag(v___x_4234_, 0);
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
v___y_4206_ = v___y_4221_;
v___y_4207_ = v___y_4222_;
v_a_4208_ = v___x_4237_;
goto v___jp_4205_;
}
}
}
}
v___jp_4240_:
{
lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4245_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4246_ = lean_apply_5(v___y_4243_, v___x_4245_, v___y_4241_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4242_;
v___y_4222_ = v___y_4244_;
v___y_4223_ = v___x_4246_;
goto v___jp_4220_;
}
v___jp_4247_:
{
if (v___x_4158_ == 0)
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
lean_dec_ref(v___y_4249_);
v___x_4252_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4253_ = lean_apply_4(v___y_4250_, v___x_4252_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4251_;
v___y_4223_ = v___x_4253_;
goto v___jp_4220_;
}
else
{
lean_object* v_toConstantVal_4254_; lean_object* v_name_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; 
v_toConstantVal_4254_ = lean_ctor_get(v___y_4249_, 0);
lean_inc_ref(v_toConstantVal_4254_);
lean_dec_ref(v___y_4249_);
v_name_4255_ = lean_ctor_get(v_toConstantVal_4254_, 0);
lean_inc(v_name_4255_);
lean_dec_ref(v_toConstantVal_4254_);
v___x_4256_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4257_ = l_Lean_MessageData_ofName(v_name_4255_);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4260_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4261_) == 0)
{
lean_object* v_a_4262_; lean_object* v___x_4263_; 
v_a_4262_ = lean_ctor_get(v___x_4261_, 0);
lean_inc(v_a_4262_);
lean_dec_ref_known(v___x_4261_, 1);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4263_ = lean_apply_4(v___y_4250_, v_a_4262_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4251_;
v___y_4223_ = v___x_4263_;
goto v___jp_4220_;
}
else
{
lean_dec_ref(v___y_4250_);
v___y_4221_ = v___y_4248_;
v___y_4222_ = v___y_4251_;
v___y_4223_ = v___x_4261_;
goto v___jp_4220_;
}
}
}
v___jp_4264_:
{
lean_object* v___x_4274_; uint8_t v_isModule_4275_; 
v___x_4274_ = l_Lean_Environment_header(v___y_4272_);
lean_dec_ref(v___y_4272_);
v_isModule_4275_ = lean_ctor_get_uint8(v___x_4274_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4274_);
if (v_isModule_4275_ == 0)
{
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
lean_dec_ref(v___y_4266_);
v___y_4241_ = v___y_4265_;
v___y_4242_ = v___y_4267_;
v___y_4243_ = v___y_4271_;
v___y_4244_ = v___y_4273_;
goto v___jp_4240_;
}
else
{
uint8_t v_isExporting_4276_; 
v_isExporting_4276_ = lean_ctor_get_uint8(v___y_4266_, sizeof(void*)*8);
lean_dec_ref(v___y_4266_);
if (v_isExporting_4276_ == 0)
{
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4265_);
v___y_4248_ = v___y_4267_;
v___y_4249_ = v___y_4270_;
v___y_4250_ = v___y_4269_;
v___y_4251_ = v___y_4273_;
goto v___jp_4247_;
}
else
{
if (v___y_4268_ == 0)
{
lean_dec_ref(v___y_4270_);
lean_dec_ref(v___y_4269_);
v___y_4241_ = v___y_4265_;
v___y_4242_ = v___y_4267_;
v___y_4243_ = v___y_4271_;
v___y_4244_ = v___y_4273_;
goto v___jp_4240_;
}
else
{
lean_dec_ref(v___y_4271_);
lean_dec(v___y_4265_);
v___y_4248_ = v___y_4267_;
v___y_4249_ = v___y_4270_;
v___y_4250_ = v___y_4269_;
v___y_4251_ = v___y_4273_;
goto v___jp_4247_;
}
}
}
}
v___jp_4277_:
{
lean_object* v___x_4282_; lean_object* v___x_4283_; 
v___x_4282_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4283_ = lean_apply_5(v___y_4279_, v___x_4282_, v___y_4278_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4280_;
v___y_4222_ = v___y_4281_;
v___y_4223_ = v___x_4283_;
goto v___jp_4220_;
}
v___jp_4284_:
{
lean_object* v___x_4292_; uint8_t v_isModule_4293_; 
v___x_4292_ = l_Lean_Environment_header(v___y_4286_);
lean_dec_ref(v___y_4286_);
v_isModule_4293_ = lean_ctor_get_uint8(v___x_4292_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4292_);
if (v_isModule_4293_ == 0)
{
lean_dec_ref(v___y_4290_);
lean_dec_ref(v___y_4289_);
v___y_4278_ = v___y_4285_;
v___y_4279_ = v___y_4287_;
v___y_4280_ = v___y_4288_;
v___y_4281_ = v___y_4291_;
goto v___jp_4277_;
}
else
{
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4285_);
if (v___x_4158_ == 0)
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
lean_dec_ref(v___y_4290_);
v___x_4294_ = lean_box(0);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4295_ = lean_apply_4(v___y_4289_, v___x_4294_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4288_;
v___y_4222_ = v___y_4291_;
v___y_4223_ = v___x_4295_;
goto v___jp_4220_;
}
else
{
lean_object* v_toConstantVal_4296_; lean_object* v_name_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; 
v_toConstantVal_4296_ = lean_ctor_get(v___y_4290_, 0);
lean_inc_ref(v_toConstantVal_4296_);
lean_dec_ref(v___y_4290_);
v_name_4297_ = lean_ctor_get(v_toConstantVal_4296_, 0);
lean_inc(v_name_4297_);
lean_dec_ref(v_toConstantVal_4296_);
v___x_4298_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4299_ = l_Lean_MessageData_ofName(v_name_4297_);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4302_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v_a_4304_; lean_object* v___x_4305_; 
v_a_4304_ = lean_ctor_get(v___x_4303_, 0);
lean_inc(v_a_4304_);
lean_dec_ref_known(v___x_4303_, 1);
lean_inc(v_a_3748_);
lean_inc_ref(v_a_3747_);
v___x_4305_ = lean_apply_4(v___y_4289_, v_a_4304_, v_a_3747_, v_a_3748_, lean_box(0));
v___y_4221_ = v___y_4288_;
v___y_4222_ = v___y_4291_;
v___y_4223_ = v___x_4305_;
goto v___jp_4220_;
}
else
{
lean_dec_ref(v___y_4289_);
v___y_4221_ = v___y_4288_;
v___y_4222_ = v___y_4291_;
v___y_4223_ = v___x_4303_;
goto v___jp_4220_;
}
}
}
}
v___jp_4306_:
{
lean_object* v___x_4307_; lean_object* v_a_4308_; lean_object* v___x_4310_; uint8_t v_isShared_4311_; uint8_t v_isSharedCheck_4457_; 
v___x_4307_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3748_);
v_a_4308_ = lean_ctor_get(v___x_4307_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4307_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4310_ = v___x_4307_;
v_isShared_4311_ = v_isSharedCheck_4457_;
goto v_resetjp_4309_;
}
else
{
lean_inc(v_a_4308_);
lean_dec(v___x_4307_);
v___x_4310_ = lean_box(0);
v_isShared_4311_ = v_isSharedCheck_4457_;
goto v_resetjp_4309_;
}
v_resetjp_4309_:
{
lean_object* v___x_4312_; uint8_t v___x_4313_; 
v___x_4312_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4313_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3803_, v___x_4312_);
if (v___x_4313_ == 0)
{
lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v_env_4316_; lean_object* v_nextMacroScope_4317_; lean_object* v_ngen_4318_; lean_object* v_auxDeclNGen_4319_; lean_object* v_traceState_4320_; lean_object* v_messages_4321_; lean_object* v_infoState_4322_; lean_object* v_snapshotTasks_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4371_; 
v___x_4314_ = lean_io_mono_nanos_now();
v___x_4315_ = lean_st_ref_take(v_a_3748_);
v_env_4316_ = lean_ctor_get(v___x_4315_, 0);
v_nextMacroScope_4317_ = lean_ctor_get(v___x_4315_, 1);
v_ngen_4318_ = lean_ctor_get(v___x_4315_, 2);
v_auxDeclNGen_4319_ = lean_ctor_get(v___x_4315_, 3);
v_traceState_4320_ = lean_ctor_get(v___x_4315_, 4);
v_messages_4321_ = lean_ctor_get(v___x_4315_, 6);
v_infoState_4322_ = lean_ctor_get(v___x_4315_, 7);
v_snapshotTasks_4323_ = lean_ctor_get(v___x_4315_, 8);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4371_ == 0)
{
lean_object* v_unused_4372_; 
v_unused_4372_ = lean_ctor_get(v___x_4315_, 5);
lean_dec(v_unused_4372_);
v___x_4325_ = v___x_4315_;
v_isShared_4326_ = v_isSharedCheck_4371_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_snapshotTasks_4323_);
lean_inc(v_infoState_4322_);
lean_inc(v_messages_4321_);
lean_inc(v_traceState_4320_);
lean_inc(v_auxDeclNGen_4319_);
lean_inc(v_ngen_4318_);
lean_inc(v_nextMacroScope_4317_);
lean_inc(v_env_4316_);
lean_dec(v___x_4315_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4371_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; lean_object* v___x_4329_; lean_object* v___x_4331_; 
lean_inc(v_decl_3745_);
v___x_4327_ = l_Lean_Declaration_getNames(v_decl_3745_);
v___x_4328_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4316_, v___x_4327_);
v___x_4329_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4326_ == 0)
{
lean_ctor_set(v___x_4325_, 5, v___x_4329_);
lean_ctor_set(v___x_4325_, 0, v___x_4328_);
v___x_4331_ = v___x_4325_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v___x_4328_);
lean_ctor_set(v_reuseFailAlloc_4370_, 1, v_nextMacroScope_4317_);
lean_ctor_set(v_reuseFailAlloc_4370_, 2, v_ngen_4318_);
lean_ctor_set(v_reuseFailAlloc_4370_, 3, v_auxDeclNGen_4319_);
lean_ctor_set(v_reuseFailAlloc_4370_, 4, v_traceState_4320_);
lean_ctor_set(v_reuseFailAlloc_4370_, 5, v___x_4329_);
lean_ctor_set(v_reuseFailAlloc_4370_, 6, v_messages_4321_);
lean_ctor_set(v_reuseFailAlloc_4370_, 7, v_infoState_4322_);
lean_ctor_set(v_reuseFailAlloc_4370_, 8, v_snapshotTasks_4323_);
v___x_4331_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
lean_object* v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___f_4336_; 
v___x_4332_ = lean_st_ref_put(v_a_3748_, v___x_4331_);
v___x_4333_ = lean_box(0);
v___x_4334_ = lean_box(v_hasTrace_3805_);
v___x_4335_ = lean_box(v___x_4313_);
lean_inc(v_decl_3745_);
v___f_4336_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4336_, 0, v_decl_3745_);
lean_closure_set(v___f_4336_, 1, v___x_4334_);
lean_closure_set(v___f_4336_, 2, v___x_4335_);
lean_closure_set(v___f_4336_, 3, v___x_4329_);
lean_closure_set(v___f_4336_, 4, v_cls_3942_);
lean_closure_set(v___f_4336_, 5, v___x_4333_);
switch(lean_obj_tag(v_decl_3745_))
{
case 2:
{
lean_object* v_val_4337_; lean_object* v___x_4338_; lean_object* v_env_4339_; lean_object* v___f_4340_; lean_object* v___x_4341_; lean_object* v___f_4342_; 
lean_del_object(v___x_4310_);
v_val_4337_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref_n(v_val_4337_, 3);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4338_ = lean_st_ref_get(v_a_3748_);
v_env_4339_ = lean_ctor_get(v___x_4338_, 0);
lean_inc_ref(v_env_4339_);
lean_dec(v___x_4338_);
v___f_4340_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4340_, 0, v_val_4337_);
lean_closure_set(v___f_4340_, 1, v___f_4336_);
v___x_4341_ = lean_box(v___x_4313_);
lean_inc_ref(v___f_4340_);
v___f_4342_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4342_, 0, v_val_4337_);
lean_closure_set(v___f_4342_, 1, v___x_4341_);
lean_closure_set(v___f_4342_, 2, v___f_4340_);
if (v_forceExpose_3746_ == 0)
{
v___y_4285_ = v___x_4333_;
v___y_4286_ = v_env_4339_;
v___y_4287_ = v___f_4340_;
v___y_4288_ = v_a_4308_;
v___y_4289_ = v___f_4342_;
v___y_4290_ = v_val_4337_;
v___y_4291_ = v___x_4314_;
goto v___jp_4284_;
}
else
{
if (v___x_4313_ == 0)
{
lean_dec_ref(v___f_4342_);
lean_dec_ref(v_env_4339_);
lean_dec_ref(v_val_4337_);
v___y_4278_ = v___x_4333_;
v___y_4279_ = v___f_4340_;
v___y_4280_ = v_a_4308_;
v___y_4281_ = v___x_4314_;
goto v___jp_4277_;
}
else
{
v___y_4285_ = v___x_4333_;
v___y_4286_ = v_env_4339_;
v___y_4287_ = v___f_4340_;
v___y_4288_ = v_a_4308_;
v___y_4289_ = v___f_4342_;
v___y_4290_ = v_val_4337_;
v___y_4291_ = v___x_4314_;
goto v___jp_4284_;
}
}
}
case 1:
{
lean_object* v_val_4343_; lean_object* v___x_4344_; 
lean_del_object(v___x_4310_);
v_val_4343_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref(v_val_4343_);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4344_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4336_, v___x_4313_, v_cls_3942_, v___x_4333_, v_forceExpose_3746_, v_val_4343_, v_a_3747_, v_a_3748_);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4344_;
goto v___jp_4220_;
}
case 5:
{
lean_object* v_defns_4345_; 
lean_del_object(v___x_4310_);
v_defns_4345_ = lean_ctor_get(v_decl_3745_, 0);
if (lean_obj_tag(v_defns_4345_) == 1)
{
lean_object* v_tail_4346_; 
v_tail_4346_ = lean_ctor_get(v_defns_4345_, 1);
if (lean_obj_tag(v_tail_4346_) == 0)
{
lean_object* v_head_4347_; lean_object* v___x_4348_; 
lean_inc_ref(v_defns_4345_);
lean_dec_ref_known(v_decl_3745_, 1);
v_head_4347_ = lean_ctor_get(v_defns_4345_, 0);
lean_inc(v_head_4347_);
lean_dec_ref_known(v_defns_4345_, 2);
v___x_4348_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4336_, v___x_4313_, v_cls_3942_, v___x_4333_, v_forceExpose_3746_, v_head_4347_, v_a_3747_, v_a_3748_);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4348_;
goto v___jp_4220_;
}
else
{
lean_object* v___x_4349_; 
lean_dec_ref(v___f_4336_);
lean_inc_ref(v_decl_3745_);
v___x_4349_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec_ref_known(v_decl_3745_, 1);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4349_;
goto v___jp_4220_;
}
}
else
{
lean_object* v___x_4350_; 
lean_dec_ref(v___f_4336_);
lean_inc_ref(v_decl_3745_);
v___x_4350_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec_ref_known(v_decl_3745_, 1);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4350_;
goto v___jp_4220_;
}
}
case 3:
{
lean_object* v_val_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; lean_object* v_env_4354_; lean_object* v_env_4355_; lean_object* v___f_4356_; lean_object* v___f_4357_; 
lean_del_object(v___x_4310_);
v_val_4351_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref_n(v_val_4351_, 3);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4352_ = lean_st_ref_get(v_a_3748_);
v___x_4353_ = lean_st_ref_get(v_a_3748_);
v_env_4354_ = lean_ctor_get(v___x_4352_, 0);
lean_inc_ref(v_env_4354_);
lean_dec(v___x_4352_);
v_env_4355_ = lean_ctor_get(v___x_4353_, 0);
lean_inc_ref(v_env_4355_);
lean_dec(v___x_4353_);
v___f_4356_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4356_, 0, v_val_4351_);
lean_closure_set(v___f_4356_, 1, v___f_4336_);
lean_inc_ref(v___f_4356_);
v___f_4357_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4357_, 0, v_val_4351_);
lean_closure_set(v___f_4357_, 1, v___f_4356_);
if (v_forceExpose_3746_ == 0)
{
v___y_4265_ = v___x_4333_;
v___y_4266_ = v_env_4355_;
v___y_4267_ = v_a_4308_;
v___y_4268_ = v___x_4313_;
v___y_4269_ = v___f_4357_;
v___y_4270_ = v_val_4351_;
v___y_4271_ = v___f_4356_;
v___y_4272_ = v_env_4354_;
v___y_4273_ = v___x_4314_;
goto v___jp_4264_;
}
else
{
if (v___x_4313_ == 0)
{
lean_dec_ref(v___f_4357_);
lean_dec_ref(v_env_4355_);
lean_dec_ref(v_env_4354_);
lean_dec_ref(v_val_4351_);
v___y_4241_ = v___x_4333_;
v___y_4242_ = v_a_4308_;
v___y_4243_ = v___f_4356_;
v___y_4244_ = v___x_4314_;
goto v___jp_4240_;
}
else
{
v___y_4265_ = v___x_4333_;
v___y_4266_ = v_env_4355_;
v___y_4267_ = v_a_4308_;
v___y_4268_ = v___x_4313_;
v___y_4269_ = v___f_4357_;
v___y_4270_ = v_val_4351_;
v___y_4271_ = v___f_4356_;
v___y_4272_ = v_env_4354_;
v___y_4273_ = v___x_4314_;
goto v___jp_4264_;
}
}
}
case 0:
{
lean_object* v_val_4358_; lean_object* v_toConstantVal_4359_; lean_object* v_name_4360_; lean_object* v___x_4362_; 
lean_dec_ref(v___f_4336_);
v_val_4358_ = lean_ctor_get(v_decl_3745_, 0);
v_toConstantVal_4359_ = lean_ctor_get(v_val_4358_, 0);
v_name_4360_ = lean_ctor_get(v_toConstantVal_4359_, 0);
lean_inc_ref(v_val_4358_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v_val_4358_);
v___x_4362_ = v___x_4310_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_val_4358_);
v___x_4362_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
uint8_t v___x_4363_; lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4363_ = 2;
v___x_4364_ = lean_box(v___x_4363_);
v___x_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4365_, 0, v___x_4362_);
lean_ctor_set(v___x_4365_, 1, v___x_4364_);
lean_inc(v_name_4360_);
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v_name_4360_);
lean_ctor_set(v___x_4366_, 1, v___x_4365_);
v___x_4367_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3745_, v_hasTrace_3805_, v___x_4313_, v___x_4329_, v_cls_3942_, v___x_4333_, v___x_4366_, v___x_4333_, v_a_3747_, v_a_3748_);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4367_;
goto v___jp_4220_;
}
}
default: 
{
lean_object* v___x_4369_; 
lean_dec_ref(v___f_4336_);
lean_del_object(v___x_4310_);
lean_inc(v_decl_3745_);
v___x_4369_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec(v_decl_3745_);
v___y_4221_ = v_a_4308_;
v___y_4222_ = v___x_4314_;
v___y_4223_ = v___x_4369_;
goto v___jp_4220_;
}
}
}
}
}
else
{
lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v_env_4375_; lean_object* v_nextMacroScope_4376_; lean_object* v_ngen_4377_; lean_object* v_auxDeclNGen_4378_; lean_object* v_traceState_4379_; lean_object* v_messages_4380_; lean_object* v_infoState_4381_; lean_object* v_snapshotTasks_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4455_; 
v___x_4373_ = lean_io_get_num_heartbeats();
v___x_4374_ = lean_st_ref_take(v_a_3748_);
v_env_4375_ = lean_ctor_get(v___x_4374_, 0);
v_nextMacroScope_4376_ = lean_ctor_get(v___x_4374_, 1);
v_ngen_4377_ = lean_ctor_get(v___x_4374_, 2);
v_auxDeclNGen_4378_ = lean_ctor_get(v___x_4374_, 3);
v_traceState_4379_ = lean_ctor_get(v___x_4374_, 4);
v_messages_4380_ = lean_ctor_get(v___x_4374_, 6);
v_infoState_4381_ = lean_ctor_get(v___x_4374_, 7);
v_snapshotTasks_4382_ = lean_ctor_get(v___x_4374_, 8);
v_isSharedCheck_4455_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4455_ == 0)
{
lean_object* v_unused_4456_; 
v_unused_4456_ = lean_ctor_get(v___x_4374_, 5);
lean_dec(v_unused_4456_);
v___x_4384_ = v___x_4374_;
v_isShared_4385_ = v_isSharedCheck_4455_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_snapshotTasks_4382_);
lean_inc(v_infoState_4381_);
lean_inc(v_messages_4380_);
lean_inc(v_traceState_4379_);
lean_inc(v_auxDeclNGen_4378_);
lean_inc(v_ngen_4377_);
lean_inc(v_nextMacroScope_4376_);
lean_inc(v_env_4375_);
lean_dec(v___x_4374_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4455_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4390_; 
lean_inc(v_decl_3745_);
v___x_4386_ = l_Lean_Declaration_getNames(v_decl_3745_);
v___x_4387_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4375_, v___x_4386_);
v___x_4388_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4385_ == 0)
{
lean_ctor_set(v___x_4384_, 5, v___x_4388_);
lean_ctor_set(v___x_4384_, 0, v___x_4387_);
v___x_4390_ = v___x_4384_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4454_; 
v_reuseFailAlloc_4454_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4454_, 0, v___x_4387_);
lean_ctor_set(v_reuseFailAlloc_4454_, 1, v_nextMacroScope_4376_);
lean_ctor_set(v_reuseFailAlloc_4454_, 2, v_ngen_4377_);
lean_ctor_set(v_reuseFailAlloc_4454_, 3, v_auxDeclNGen_4378_);
lean_ctor_set(v_reuseFailAlloc_4454_, 4, v_traceState_4379_);
lean_ctor_set(v_reuseFailAlloc_4454_, 5, v___x_4388_);
lean_ctor_set(v_reuseFailAlloc_4454_, 6, v_messages_4380_);
lean_ctor_set(v_reuseFailAlloc_4454_, 7, v_infoState_4381_);
lean_ctor_set(v_reuseFailAlloc_4454_, 8, v_snapshotTasks_4382_);
v___x_4390_ = v_reuseFailAlloc_4454_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
lean_object* v___x_4391_; lean_object* v___x_4392_; lean_object* v___x_4393_; lean_object* v___f_4394_; 
v___x_4391_ = lean_st_ref_put(v_a_3748_, v___x_4390_);
v___x_4392_ = lean_box(0);
v___x_4393_ = lean_box(v___x_4313_);
lean_inc(v_decl_3745_);
v___f_4394_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4394_, 0, v_decl_3745_);
lean_closure_set(v___f_4394_, 1, v___x_4393_);
lean_closure_set(v___f_4394_, 2, v_cls_3942_);
lean_closure_set(v___f_4394_, 3, v___x_4388_);
lean_closure_set(v___f_4394_, 4, v___x_4392_);
switch(lean_obj_tag(v_decl_3745_))
{
case 2:
{
lean_object* v_val_4395_; lean_object* v___x_4396_; lean_object* v_env_4397_; lean_object* v___f_4398_; 
lean_del_object(v___x_4310_);
v_val_4395_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref_n(v_val_4395_, 2);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4396_ = lean_st_ref_get(v_a_3748_);
v_env_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc_ref(v_env_4397_);
lean_dec(v___x_4396_);
v___f_4398_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4398_, 0, v_val_4395_);
lean_closure_set(v___f_4398_, 1, v___f_4394_);
if (v_forceExpose_3746_ == 0)
{
if (v___x_4313_ == 0)
{
lean_dec_ref(v_env_4397_);
lean_dec_ref(v_val_4395_);
v___y_4199_ = v___x_4392_;
v___y_4200_ = v_a_4308_;
v___y_4201_ = v___x_4373_;
v___y_4202_ = v___f_4398_;
goto v___jp_4198_;
}
else
{
lean_object* v___x_4399_; uint8_t v_isModule_4400_; 
v___x_4399_ = l_Lean_Environment_header(v_env_4397_);
lean_dec_ref(v_env_4397_);
v_isModule_4400_ = lean_ctor_get_uint8(v___x_4399_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4399_);
if (v_isModule_4400_ == 0)
{
lean_dec_ref(v_val_4395_);
v___y_4199_ = v___x_4392_;
v___y_4200_ = v_a_4308_;
v___y_4201_ = v___x_4373_;
v___y_4202_ = v___f_4398_;
goto v___jp_4198_;
}
else
{
if (v___x_4158_ == 0)
{
lean_object* v___x_4401_; lean_object* v___x_4402_; 
v___x_4401_ = lean_box(0);
v___x_4402_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4395_, v_forceExpose_3746_, v___f_4398_, v___x_4401_, v_a_3747_, v_a_3748_);
lean_dec_ref(v_val_4395_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4402_;
goto v___jp_4171_;
}
else
{
lean_object* v_toConstantVal_4403_; lean_object* v_name_4404_; lean_object* v___x_4405_; lean_object* v___x_4406_; lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; 
v_toConstantVal_4403_ = lean_ctor_get(v_val_4395_, 0);
v_name_4404_ = lean_ctor_get(v_toConstantVal_4403_, 0);
v___x_4405_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4404_);
v___x_4406_ = l_Lean_MessageData_ofName(v_name_4404_);
v___x_4407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4407_, 0, v___x_4405_);
lean_ctor_set(v___x_4407_, 1, v___x_4406_);
v___x_4408_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4409_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4395_, v_forceExpose_3746_, v___f_4398_, v_a_4411_, v_a_3747_, v_a_3748_);
lean_dec_ref(v_val_4395_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4412_;
goto v___jp_4171_;
}
else
{
lean_dec_ref(v___f_4398_);
lean_dec_ref(v_val_4395_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4410_;
goto v___jp_4171_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4397_);
lean_dec_ref(v_val_4395_);
v___y_4199_ = v___x_4392_;
v___y_4200_ = v_a_4308_;
v___y_4201_ = v___x_4373_;
v___y_4202_ = v___f_4398_;
goto v___jp_4198_;
}
}
case 1:
{
lean_object* v_val_4413_; lean_object* v___x_4414_; 
lean_del_object(v___x_4310_);
v_val_4413_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref(v_val_4413_);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4414_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4394_, v_forceExpose_3746_, v___x_4313_, v___x_4392_, v_cls_3942_, v_val_4413_, v_a_3747_, v_a_3748_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4414_;
goto v___jp_4171_;
}
case 5:
{
lean_object* v_defns_4415_; 
lean_del_object(v___x_4310_);
v_defns_4415_ = lean_ctor_get(v_decl_3745_, 0);
if (lean_obj_tag(v_defns_4415_) == 1)
{
lean_object* v_tail_4416_; 
v_tail_4416_ = lean_ctor_get(v_defns_4415_, 1);
if (lean_obj_tag(v_tail_4416_) == 0)
{
lean_object* v_head_4417_; lean_object* v___x_4418_; 
lean_inc_ref(v_defns_4415_);
lean_dec_ref_known(v_decl_3745_, 1);
v_head_4417_ = lean_ctor_get(v_defns_4415_, 0);
lean_inc(v_head_4417_);
lean_dec_ref_known(v_defns_4415_, 2);
v___x_4418_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4394_, v_forceExpose_3746_, v___x_4313_, v___x_4392_, v_cls_3942_, v_head_4417_, v_a_3747_, v_a_3748_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4418_;
goto v___jp_4171_;
}
else
{
lean_object* v___x_4419_; 
lean_dec_ref(v___f_4394_);
lean_inc_ref(v_decl_3745_);
v___x_4419_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec_ref_known(v_decl_3745_, 1);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4419_;
goto v___jp_4171_;
}
}
else
{
lean_object* v___x_4420_; 
lean_dec_ref(v___f_4394_);
lean_inc_ref(v_decl_3745_);
v___x_4420_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec_ref_known(v_decl_3745_, 1);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4420_;
goto v___jp_4171_;
}
}
case 3:
{
lean_object* v_val_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v_env_4424_; lean_object* v_env_4425_; lean_object* v___f_4426_; 
lean_del_object(v___x_4310_);
v_val_4421_ = lean_ctor_get(v_decl_3745_, 0);
lean_inc_ref_n(v_val_4421_, 2);
lean_dec_ref_known(v_decl_3745_, 1);
v___x_4422_ = lean_st_ref_get(v_a_3748_);
v___x_4423_ = lean_st_ref_get(v_a_3748_);
v_env_4424_ = lean_ctor_get(v___x_4422_, 0);
lean_inc_ref(v_env_4424_);
lean_dec(v___x_4422_);
v_env_4425_ = lean_ctor_get(v___x_4423_, 0);
lean_inc_ref(v_env_4425_);
lean_dec(v___x_4423_);
v___f_4426_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4426_, 0, v_val_4421_);
lean_closure_set(v___f_4426_, 1, v___f_4394_);
if (v_forceExpose_3746_ == 0)
{
if (v___x_4313_ == 0)
{
lean_dec_ref(v_env_4425_);
lean_dec_ref(v_env_4424_);
lean_dec_ref(v_val_4421_);
v___y_4192_ = v___x_4392_;
v___y_4193_ = v_a_4308_;
v___y_4194_ = v___x_4373_;
v___y_4195_ = v___f_4426_;
goto v___jp_4191_;
}
else
{
lean_object* v___x_4427_; uint8_t v_isModule_4428_; 
v___x_4427_ = l_Lean_Environment_header(v_env_4424_);
lean_dec_ref(v_env_4424_);
v_isModule_4428_ = lean_ctor_get_uint8(v___x_4427_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4427_);
if (v_isModule_4428_ == 0)
{
lean_dec_ref(v_env_4425_);
lean_dec_ref(v_val_4421_);
v___y_4192_ = v___x_4392_;
v___y_4193_ = v_a_4308_;
v___y_4194_ = v___x_4373_;
v___y_4195_ = v___f_4426_;
goto v___jp_4191_;
}
else
{
uint8_t v_isExporting_4429_; 
v_isExporting_4429_ = lean_ctor_get_uint8(v_env_4425_, sizeof(void*)*8);
lean_dec_ref(v_env_4425_);
if (v_isExporting_4429_ == 0)
{
if (v___x_4158_ == 0)
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = lean_box(0);
v___x_4431_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4421_, v___f_4426_, v___x_4430_, v_a_3747_, v_a_3748_);
lean_dec_ref(v_val_4421_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4431_;
goto v___jp_4171_;
}
else
{
lean_object* v_toConstantVal_4432_; lean_object* v_name_4433_; lean_object* v___x_4434_; lean_object* v___x_4435_; lean_object* v___x_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; 
v_toConstantVal_4432_ = lean_ctor_get(v_val_4421_, 0);
v_name_4433_ = lean_ctor_get(v_toConstantVal_4432_, 0);
v___x_4434_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4433_);
v___x_4435_ = l_Lean_MessageData_ofName(v_name_4433_);
v___x_4436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4436_, 0, v___x_4434_);
lean_ctor_set(v___x_4436_, 1, v___x_4435_);
v___x_4437_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4438_, 0, v___x_4436_);
lean_ctor_set(v___x_4438_, 1, v___x_4437_);
v___x_4439_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3942_, v___x_4438_, v_a_3747_, v_a_3748_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v___x_4441_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v___x_4441_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4421_, v___f_4426_, v_a_4440_, v_a_3747_, v_a_3748_);
lean_dec_ref(v_val_4421_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4441_;
goto v___jp_4171_;
}
else
{
lean_dec_ref(v___f_4426_);
lean_dec_ref(v_val_4421_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4439_;
goto v___jp_4171_;
}
}
}
else
{
lean_dec_ref(v_val_4421_);
v___y_4192_ = v___x_4392_;
v___y_4193_ = v_a_4308_;
v___y_4194_ = v___x_4373_;
v___y_4195_ = v___f_4426_;
goto v___jp_4191_;
}
}
}
}
else
{
lean_dec_ref(v_env_4425_);
lean_dec_ref(v_env_4424_);
lean_dec_ref(v_val_4421_);
v___y_4192_ = v___x_4392_;
v___y_4193_ = v_a_4308_;
v___y_4194_ = v___x_4373_;
v___y_4195_ = v___f_4426_;
goto v___jp_4191_;
}
}
case 0:
{
lean_object* v_val_4442_; lean_object* v_toConstantVal_4443_; lean_object* v_name_4444_; lean_object* v___x_4446_; 
lean_dec_ref(v___f_4394_);
v_val_4442_ = lean_ctor_get(v_decl_3745_, 0);
v_toConstantVal_4443_ = lean_ctor_get(v_val_4442_, 0);
v_name_4444_ = lean_ctor_get(v_toConstantVal_4443_, 0);
lean_inc_ref(v_val_4442_);
if (v_isShared_4311_ == 0)
{
lean_ctor_set(v___x_4310_, 0, v_val_4442_);
v___x_4446_ = v___x_4310_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_val_4442_);
v___x_4446_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
uint8_t v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4447_ = 2;
v___x_4448_ = lean_box(v___x_4447_);
v___x_4449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4446_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
lean_inc(v_name_4444_);
v___x_4450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4450_, 0, v_name_4444_);
lean_ctor_set(v___x_4450_, 1, v___x_4449_);
v___x_4451_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3745_, v___x_4313_, v_cls_3942_, v___x_4388_, v___x_4392_, v___x_4450_, v___x_4392_, v_a_3747_, v_a_3748_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4451_;
goto v___jp_4171_;
}
}
default: 
{
lean_object* v___x_4453_; 
lean_dec_ref(v___f_4394_);
lean_del_object(v___x_4310_);
lean_inc(v_decl_3745_);
v___x_4453_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3745_, v_cls_3942_, v_decl_3745_, v_a_3747_, v_a_3748_);
lean_dec(v_decl_3745_);
v___y_4172_ = v_a_4308_;
v___y_4173_ = v___x_4373_;
v___y_4174_ = v___x_4453_;
goto v___jp_4171_;
}
}
}
}
}
}
}
}
v___jp_3750_:
{
lean_object* v___x_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v___x_3754_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3751_, v___y_3752_);
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
v___x_3767_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3764_, v___y_3765_);
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
v___jp_3776_:
{
lean_object* v___x_3780_; lean_object* v___x_3782_; uint8_t v_isShared_3783_; uint8_t v_isSharedCheck_3787_; 
v___x_3780_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3777_, v___y_3778_);
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
lean_ctor_set(v___x_3782_, 0, v_a_3779_);
v___x_3785_ = v___x_3782_;
goto v_reusejp_3784_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(0, 1, 0);
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
v___jp_3789_:
{
lean_object* v___x_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
v___x_3793_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3790_, v___y_3791_);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3800_ == 0)
{
lean_object* v_unused_3801_; 
v_unused_3801_ = lean_ctor_get(v___x_3793_, 0);
lean_dec(v_unused_3801_);
v___x_3795_ = v___x_3793_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_dec(v___x_3793_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
lean_ctor_set_tag(v___x_3795_, 1);
lean_ctor_set(v___x_3795_, 0, v_a_3792_);
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3792_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
v___jp_3806_:
{
lean_object* v___x_3818_; 
lean_inc_ref(v___y_3816_);
v___x_3818_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3808_, v___y_3816_, v___y_3811_, v___y_3817_);
if (lean_obj_tag(v___x_3818_) == 0)
{
lean_object* v___x_3819_; lean_object* v___x_3821_; uint8_t v_isShared_3822_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref_known(v___x_3818_, 1);
lean_inc_ref(v___y_3810_);
v___x_3819_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3810_, v___y_3812_);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3819_);
if (v_isSharedCheck_3866_ == 0)
{
lean_object* v_unused_3867_; 
v_unused_3867_ = lean_ctor_get(v___x_3819_, 0);
lean_dec(v_unused_3867_);
v___x_3821_ = v___x_3819_;
v_isShared_3822_ = v_isSharedCheck_3866_;
goto v_resetjp_3820_;
}
else
{
lean_dec(v___x_3819_);
v___x_3821_ = lean_box(0);
v_isShared_3822_ = v_isSharedCheck_3866_;
goto v_resetjp_3820_;
}
v_resetjp_3820_:
{
lean_object* v_toCold_3823_; lean_object* v_options_3824_; lean_object* v___x_3825_; uint8_t v___x_3826_; 
v_toCold_3823_ = lean_ctor_get(v___y_3807_, 0);
v_options_3824_ = lean_ctor_get(v_toCold_3823_, 2);
v___x_3825_ = l_Lean_Elab_async;
v___x_3826_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3824_, v___x_3825_);
if (v___x_3826_ == 0)
{
lean_object* v___x_3827_; lean_object* v_r_3828_; 
lean_del_object(v___x_3821_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v___y_3813_);
v___x_3827_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3816_, v___y_3812_);
lean_dec_ref(v___x_3827_);
v_r_3828_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3745_, v___y_3807_, v___y_3812_);
if (lean_obj_tag(v_r_3828_) == 0)
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3838_; 
v_a_3829_ = lean_ctor_get(v_r_3828_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_r_3828_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3831_ = v_r_3828_;
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v_r_3828_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3838_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
lean_inc(v_a_3829_);
if (v_isShared_3832_ == 0)
{
lean_ctor_set_tag(v___x_3831_, 1);
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
lean_object* v___x_3835_; 
v___x_3835_ = lean_apply_2(v___y_3815_, v___x_3834_, lean_box(0));
if (lean_obj_tag(v___x_3835_) == 0)
{
lean_dec_ref_known(v___x_3835_, 1);
v___y_3777_ = v___y_3810_;
v___y_3778_ = v___y_3812_;
v_a_3779_ = v_a_3829_;
goto v___jp_3776_;
}
else
{
lean_object* v_a_3836_; 
lean_dec(v_a_3829_);
v_a_3836_ = lean_ctor_get(v___x_3835_, 0);
lean_inc(v_a_3836_);
lean_dec_ref_known(v___x_3835_, 1);
v___y_3790_ = v___y_3810_;
v___y_3791_ = v___y_3812_;
v_a_3792_ = v_a_3836_;
goto v___jp_3789_;
}
}
}
}
else
{
lean_object* v_a_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; 
v_a_3839_ = lean_ctor_get(v_r_3828_, 0);
lean_inc(v_a_3839_);
lean_dec_ref_known(v_r_3828_, 1);
v___x_3840_ = lean_box(0);
v___x_3841_ = lean_apply_2(v___y_3815_, v___x_3840_, lean_box(0));
if (lean_obj_tag(v___x_3841_) == 0)
{
lean_dec_ref_known(v___x_3841_, 1);
v___y_3790_ = v___y_3810_;
v___y_3791_ = v___y_3812_;
v_a_3792_ = v_a_3839_;
goto v___jp_3789_;
}
else
{
lean_object* v_a_3842_; 
lean_dec(v_a_3839_);
v_a_3842_ = lean_ctor_get(v___x_3841_, 0);
lean_inc(v_a_3842_);
lean_dec_ref_known(v___x_3841_, 1);
v___y_3790_ = v___y_3810_;
v___y_3791_ = v___y_3812_;
v_a_3792_ = v_a_3842_;
goto v___jp_3789_;
}
}
}
else
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
lean_dec_ref(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v___y_3810_);
lean_dec(v_decl_3745_);
v___x_3843_ = l_IO_CancelToken_new();
if (v_isShared_3822_ == 0)
{
lean_ctor_set_tag(v___x_3821_, 1);
lean_ctor_set(v___x_3821_, 0, v___x_3843_);
v___x_3845_ = v___x_3821_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3843_);
v___x_3845_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3846_ = lean_unsigned_to_nat(0u);
v___x_3847_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3848_ = l_Lean_Name_toString(v___x_3847_, v___y_3809_);
lean_inc_ref(v___x_3845_);
v___x_3849_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3814_, v___x_3845_, v___x_3848_, v___y_3807_, v___y_3812_);
if (lean_obj_tag(v___x_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v_checked_3851_; lean_object* v___x_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_a_3850_ = lean_ctor_get(v___x_3849_, 0);
lean_inc(v_a_3850_);
lean_dec_ref_known(v___x_3849_, 1);
v_checked_3851_ = lean_ctor_get(v___y_3813_, 2);
lean_inc_ref(v_checked_3851_);
lean_dec_ref(v___y_3813_);
v___x_3852_ = lean_io_map_task(v_a_3850_, v_checked_3851_, v___x_3846_, v_hasTrace_3805_);
v___x_3853_ = lean_box(0);
v___x_3854_ = lean_box(2);
v___x_3855_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3855_, 0, v___x_3853_);
lean_ctor_set(v___x_3855_, 1, v___x_3854_);
lean_ctor_set(v___x_3855_, 2, v___x_3845_);
lean_ctor_set(v___x_3855_, 3, v___x_3852_);
v___x_3856_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3855_, v___y_3812_);
return v___x_3856_;
}
else
{
lean_object* v_a_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_3864_; 
lean_dec_ref(v___x_3845_);
lean_dec_ref(v___y_3813_);
v_a_3857_ = lean_ctor_get(v___x_3849_, 0);
v_isSharedCheck_3864_ = !lean_is_exclusive(v___x_3849_);
if (v_isSharedCheck_3864_ == 0)
{
v___x_3859_ = v___x_3849_;
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_a_3857_);
lean_dec(v___x_3849_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_3864_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3862_; 
if (v_isShared_3860_ == 0)
{
v___x_3862_ = v___x_3859_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3863_; 
v_reuseFailAlloc_3863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3863_, 0, v_a_3857_);
v___x_3862_ = v_reuseFailAlloc_3863_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
return v___x_3862_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3868_; lean_object* v___x_3870_; uint8_t v_isShared_3871_; uint8_t v_isSharedCheck_3880_; 
lean_dec_ref(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec_ref(v___y_3810_);
lean_dec(v_decl_3745_);
v_a_3868_ = lean_ctor_get(v___x_3818_, 0);
v_isSharedCheck_3880_ = !lean_is_exclusive(v___x_3818_);
if (v_isSharedCheck_3880_ == 0)
{
v___x_3870_ = v___x_3818_;
v_isShared_3871_ = v_isSharedCheck_3880_;
goto v_resetjp_3869_;
}
else
{
lean_inc(v_a_3868_);
lean_dec(v___x_3818_);
v___x_3870_ = lean_box(0);
v_isShared_3871_ = v_isSharedCheck_3880_;
goto v_resetjp_3869_;
}
v_resetjp_3869_:
{
lean_object* v_ref_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3878_; 
v_ref_3872_ = lean_ctor_get(v___y_3807_, 2);
v___x_3873_ = lean_io_error_to_string(v_a_3868_);
v___x_3874_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3874_, 0, v___x_3873_);
v___x_3875_ = l_Lean_MessageData_ofFormat(v___x_3874_);
lean_inc(v_ref_3872_);
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v_ref_3872_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
if (v_isShared_3871_ == 0)
{
lean_ctor_set(v___x_3870_, 0, v___x_3876_);
v___x_3878_ = v___x_3870_;
goto v_reusejp_3877_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3876_);
v___x_3878_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3877_;
}
v_reusejp_3877_:
{
return v___x_3878_;
}
}
}
}
v___jp_3881_:
{
uint8_t v___x_3892_; lean_object* v___x_3893_; 
v___x_3892_ = 1;
lean_inc_ref(v___y_3884_);
v___x_3893_ = l_Lean_Environment_addConstAsync(v___y_3884_, v___y_3890_, v___y_3886_, v___y_3891_, v_hasTrace_3805_, v___x_3892_);
if (lean_obj_tag(v___x_3893_) == 0)
{
lean_object* v_a_3894_; lean_object* v_mainEnv_3895_; lean_object* v_asyncEnv_3896_; lean_object* v___f_3897_; lean_object* v___f_3898_; lean_object* v___x_3899_; 
v_a_3894_ = lean_ctor_get(v___x_3893_, 0);
lean_inc_n(v_a_3894_, 3);
lean_dec_ref_known(v___x_3893_, 1);
v_mainEnv_3895_ = lean_ctor_get(v_a_3894_, 0);
lean_inc_ref(v_mainEnv_3895_);
v_asyncEnv_3896_ = lean_ctor_get(v_a_3894_, 1);
lean_inc_ref_n(v_asyncEnv_3896_, 2);
lean_inc_ref(v___y_3882_);
lean_inc(v___y_3883_);
v___f_3897_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3897_, 0, v___y_3883_);
lean_closure_set(v___f_3897_, 1, v_a_3894_);
lean_closure_set(v___f_3897_, 2, v___y_3882_);
lean_inc(v_decl_3745_);
v___f_3898_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3898_, 0, v_asyncEnv_3896_);
lean_closure_set(v___f_3898_, 1, v_a_3894_);
lean_closure_set(v___f_3898_, 2, v_decl_3745_);
v___x_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3899_, 0, v___y_3887_);
if (lean_obj_tag(v___y_3889_) == 0)
{
lean_inc_ref(v___x_3899_);
v___y_3807_ = v___y_3885_;
v___y_3808_ = v_a_3894_;
v___y_3809_ = v___x_3892_;
v___y_3810_ = v_mainEnv_3895_;
v___y_3811_ = v___x_3899_;
v___y_3812_ = v___y_3888_;
v___y_3813_ = v___y_3884_;
v___y_3814_ = v___f_3898_;
v___y_3815_ = v___f_3897_;
v___y_3816_ = v_asyncEnv_3896_;
v___y_3817_ = v___x_3899_;
goto v___jp_3806_;
}
else
{
v___y_3807_ = v___y_3885_;
v___y_3808_ = v_a_3894_;
v___y_3809_ = v___x_3892_;
v___y_3810_ = v_mainEnv_3895_;
v___y_3811_ = v___x_3899_;
v___y_3812_ = v___y_3888_;
v___y_3813_ = v___y_3884_;
v___y_3814_ = v___f_3898_;
v___y_3815_ = v___f_3897_;
v___y_3816_ = v_asyncEnv_3896_;
v___y_3817_ = v___y_3889_;
goto v___jp_3806_;
}
}
else
{
lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3912_; 
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3887_);
lean_dec_ref(v___y_3884_);
lean_dec(v_decl_3745_);
v_a_3900_ = lean_ctor_get(v___x_3893_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3893_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3902_ = v___x_3893_;
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_dec(v___x_3893_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3912_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v_ref_3904_; lean_object* v___x_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3910_; 
v_ref_3904_ = lean_ctor_get(v___y_3885_, 2);
v___x_3905_ = lean_io_error_to_string(v_a_3900_);
v___x_3906_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
v___x_3907_ = l_Lean_MessageData_ofFormat(v___x_3906_);
lean_inc(v_ref_3904_);
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v_ref_3904_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
if (v_isShared_3903_ == 0)
{
lean_ctor_set(v___x_3902_, 0, v___x_3908_);
v___x_3910_ = v___x_3902_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
v___jp_3913_:
{
lean_object* v___x_3920_; 
v___x_3920_ = lean_st_ref_get(v___y_3919_);
if (lean_obj_tag(v_exportedInfo_x3f_3917_) == 0)
{
lean_object* v_env_3921_; lean_object* v___x_3922_; 
v_env_3921_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_env_3921_);
lean_dec(v___x_3920_);
v___x_3922_ = lean_box(0);
v___y_3882_ = v___y_3918_;
v___y_3883_ = v___y_3919_;
v___y_3884_ = v_env_3921_;
v___y_3885_ = v___y_3918_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3915_;
v___y_3888_ = v___y_3919_;
v___y_3889_ = v_exportedInfo_x3f_3917_;
v___y_3890_ = v___y_3916_;
v___y_3891_ = v___x_3922_;
goto v___jp_3881_;
}
else
{
lean_object* v_env_3923_; lean_object* v_val_3924_; uint8_t v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; 
v_env_3923_ = lean_ctor_get(v___x_3920_, 0);
lean_inc_ref(v_env_3923_);
lean_dec(v___x_3920_);
v_val_3924_ = lean_ctor_get(v_exportedInfo_x3f_3917_, 0);
v___x_3925_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3924_);
v___x_3926_ = lean_box(v___x_3925_);
v___x_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3927_, 0, v___x_3926_);
v___y_3882_ = v___y_3918_;
v___y_3883_ = v___y_3919_;
v___y_3884_ = v_env_3923_;
v___y_3885_ = v___y_3918_;
v___y_3886_ = v___y_3914_;
v___y_3887_ = v___y_3915_;
v___y_3888_ = v___y_3919_;
v___y_3889_ = v_exportedInfo_x3f_3917_;
v___y_3890_ = v___y_3916_;
v___y_3891_ = v___x_3927_;
goto v___jp_3881_;
}
}
v___jp_3928_:
{
lean_object* v___x_3934_; 
lean_inc_ref(v___y_3930_);
v___x_3934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3934_, 0, v___y_3930_);
v___y_3914_ = v___y_3929_;
v___y_3915_ = v___y_3930_;
v___y_3916_ = v___y_3931_;
v_exportedInfo_x3f_3917_ = v___x_3934_;
v___y_3918_ = v___y_3932_;
v___y_3919_ = v___y_3933_;
goto v___jp_3913_;
}
v___jp_3935_:
{
lean_object* v___x_3941_; 
lean_inc_ref(v___y_3937_);
v___x_3941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3941_, 0, v___y_3937_);
v___y_3914_ = v___y_3936_;
v___y_3915_ = v___y_3937_;
v___y_3916_ = v___y_3938_;
v_exportedInfo_x3f_3917_ = v___x_3941_;
v___y_3918_ = v___y_3939_;
v___y_3919_ = v___y_3940_;
goto v___jp_3913_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4847_, lean_object* v_forceExpose_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_){
_start:
{
uint8_t v_forceExpose_boxed_4852_; lean_object* v_res_4853_; 
v_forceExpose_boxed_4852_ = lean_unbox(v_forceExpose_4848_);
v_res_4853_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4847_, v_forceExpose_boxed_4852_, v_a_4849_, v_a_4850_);
lean_dec(v_a_4850_);
lean_dec_ref(v_a_4849_);
return v_res_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v___x_4858_; 
v___x_4858_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4854_, v___y_4855_);
return v___x_4858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_){
_start:
{
lean_object* v_res_4863_; 
v_res_4863_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4859_, v___y_4860_, v___y_4861_);
lean_dec(v___y_4861_);
lean_dec_ref(v___y_4860_);
lean_dec_ref(v_opt_4859_);
return v_res_4863_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4864_, lean_object* v_x_4865_, lean_object* v___y_4866_, lean_object* v___y_4867_){
_start:
{
if (lean_obj_tag(v_x_4864_) == 0)
{
lean_object* v___x_4869_; lean_object* v___x_4870_; 
v___x_4869_ = l_List_reverse___redArg(v_x_4865_);
v___x_4870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4869_);
return v___x_4870_;
}
else
{
lean_object* v_head_4871_; lean_object* v_tail_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4890_; 
v_head_4871_ = lean_ctor_get(v_x_4864_, 0);
v_tail_4872_ = lean_ctor_get(v_x_4864_, 1);
v_isSharedCheck_4890_ = !lean_is_exclusive(v_x_4864_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4874_ = v_x_4864_;
v_isShared_4875_ = v_isSharedCheck_4890_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_tail_4872_);
lean_inc(v_head_4871_);
lean_dec(v_x_4864_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4890_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4876_; 
v___x_4876_ = l_Lean_snapshotEnvLinterOptions(v_head_4871_, v___y_4866_, v___y_4867_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; lean_object* v___x_4879_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref_known(v___x_4876_, 1);
if (v_isShared_4875_ == 0)
{
lean_ctor_set(v___x_4874_, 1, v_x_4865_);
lean_ctor_set(v___x_4874_, 0, v_a_4877_);
v___x_4879_ = v___x_4874_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v_a_4877_);
lean_ctor_set(v_reuseFailAlloc_4881_, 1, v_x_4865_);
v___x_4879_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
v_x_4864_ = v_tail_4872_;
v_x_4865_ = v___x_4879_;
goto _start;
}
}
else
{
lean_object* v_a_4882_; lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4889_; 
lean_del_object(v___x_4874_);
lean_dec(v_tail_4872_);
lean_dec(v_x_4865_);
v_a_4882_ = lean_ctor_get(v___x_4876_, 0);
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4876_);
if (v_isSharedCheck_4889_ == 0)
{
v___x_4884_ = v___x_4876_;
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
else
{
lean_inc(v_a_4882_);
lean_dec(v___x_4876_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4889_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4887_; 
if (v_isShared_4885_ == 0)
{
v___x_4887_ = v___x_4884_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v_a_4882_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4891_, lean_object* v_x_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v_res_4896_; 
v_res_4896_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4891_, v_x_4892_, v___y_4893_, v___y_4894_);
lean_dec(v___y_4894_);
lean_dec_ref(v___y_4893_);
return v_res_4896_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4897_, uint8_t v_forceExpose_4898_, lean_object* v_a_4899_, lean_object* v_a_4900_){
_start:
{
lean_object* v___x_4902_; 
lean_inc(v_decl_4897_);
v___x_4902_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4897_, v_forceExpose_4898_, v_a_4899_, v_a_4900_);
if (lean_obj_tag(v___x_4902_) == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
lean_dec_ref_known(v___x_4902_, 1);
v___x_4903_ = l_Lean_Declaration_getTopLevelNames(v_decl_4897_);
v___x_4904_ = lean_box(0);
v___x_4905_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4903_, v___x_4904_, v_a_4899_, v_a_4900_);
if (lean_obj_tag(v___x_4905_) == 0)
{
lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4913_; 
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4913_ == 0)
{
lean_object* v_unused_4914_; 
v_unused_4914_ = lean_ctor_get(v___x_4905_, 0);
lean_dec(v_unused_4914_);
v___x_4907_ = v___x_4905_;
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
else
{
lean_dec(v___x_4905_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4913_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4909_; lean_object* v___x_4911_; 
v___x_4909_ = lean_box(0);
if (v_isShared_4908_ == 0)
{
lean_ctor_set(v___x_4907_, 0, v___x_4909_);
v___x_4911_ = v___x_4907_;
goto v_reusejp_4910_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4909_);
v___x_4911_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4910_;
}
v_reusejp_4910_:
{
return v___x_4911_;
}
}
}
else
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4922_; 
v_a_4915_ = lean_ctor_get(v___x_4905_, 0);
v_isSharedCheck_4922_ = !lean_is_exclusive(v___x_4905_);
if (v_isSharedCheck_4922_ == 0)
{
v___x_4917_ = v___x_4905_;
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4905_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4922_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___x_4920_; 
if (v_isShared_4918_ == 0)
{
v___x_4920_ = v___x_4917_;
goto v_reusejp_4919_;
}
else
{
lean_object* v_reuseFailAlloc_4921_; 
v_reuseFailAlloc_4921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4921_, 0, v_a_4915_);
v___x_4920_ = v_reuseFailAlloc_4921_;
goto v_reusejp_4919_;
}
v_reusejp_4919_:
{
return v___x_4920_;
}
}
}
}
else
{
lean_dec(v_decl_4897_);
return v___x_4902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4923_, lean_object* v_forceExpose_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
uint8_t v_forceExpose_boxed_4928_; lean_object* v_res_4929_; 
v_forceExpose_boxed_4928_ = lean_unbox(v_forceExpose_4924_);
v_res_4929_ = l_Lean_addDecl(v_decl_4923_, v_forceExpose_boxed_4928_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
return v_res_4929_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4930_, lean_object* v_b_4931_, lean_object* v___y_4932_){
_start:
{
if (lean_obj_tag(v_as_x27_4930_) == 0)
{
lean_object* v___x_4934_; 
v___x_4934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4934_, 0, v_b_4931_);
return v___x_4934_;
}
else
{
lean_object* v_head_4935_; lean_object* v_tail_4936_; lean_object* v___x_4937_; lean_object* v_env_4938_; lean_object* v_nextMacroScope_4939_; lean_object* v_ngen_4940_; lean_object* v_auxDeclNGen_4941_; lean_object* v_traceState_4942_; lean_object* v_messages_4943_; lean_object* v_infoState_4944_; lean_object* v_snapshotTasks_4945_; lean_object* v___x_4947_; uint8_t v_isShared_4948_; uint8_t v_isSharedCheck_4957_; 
v_head_4935_ = lean_ctor_get(v_as_x27_4930_, 0);
v_tail_4936_ = lean_ctor_get(v_as_x27_4930_, 1);
v___x_4937_ = lean_st_ref_take(v___y_4932_);
v_env_4938_ = lean_ctor_get(v___x_4937_, 0);
v_nextMacroScope_4939_ = lean_ctor_get(v___x_4937_, 1);
v_ngen_4940_ = lean_ctor_get(v___x_4937_, 2);
v_auxDeclNGen_4941_ = lean_ctor_get(v___x_4937_, 3);
v_traceState_4942_ = lean_ctor_get(v___x_4937_, 4);
v_messages_4943_ = lean_ctor_get(v___x_4937_, 6);
v_infoState_4944_ = lean_ctor_get(v___x_4937_, 7);
v_snapshotTasks_4945_ = lean_ctor_get(v___x_4937_, 8);
v_isSharedCheck_4957_ = !lean_is_exclusive(v___x_4937_);
if (v_isSharedCheck_4957_ == 0)
{
lean_object* v_unused_4958_; 
v_unused_4958_ = lean_ctor_get(v___x_4937_, 5);
lean_dec(v_unused_4958_);
v___x_4947_ = v___x_4937_;
v_isShared_4948_ = v_isSharedCheck_4957_;
goto v_resetjp_4946_;
}
else
{
lean_inc(v_snapshotTasks_4945_);
lean_inc(v_infoState_4944_);
lean_inc(v_messages_4943_);
lean_inc(v_traceState_4942_);
lean_inc(v_auxDeclNGen_4941_);
lean_inc(v_ngen_4940_);
lean_inc(v_nextMacroScope_4939_);
lean_inc(v_env_4938_);
lean_dec(v___x_4937_);
v___x_4947_ = lean_box(0);
v_isShared_4948_ = v_isSharedCheck_4957_;
goto v_resetjp_4946_;
}
v_resetjp_4946_:
{
lean_object* v___x_4949_; lean_object* v___x_4950_; lean_object* v___x_4952_; 
lean_inc(v_head_4935_);
v___x_4949_ = l_Lean_markMeta(v_env_4938_, v_head_4935_);
v___x_4950_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4948_ == 0)
{
lean_ctor_set(v___x_4947_, 5, v___x_4950_);
lean_ctor_set(v___x_4947_, 0, v___x_4949_);
v___x_4952_ = v___x_4947_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4956_; 
v_reuseFailAlloc_4956_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4956_, 0, v___x_4949_);
lean_ctor_set(v_reuseFailAlloc_4956_, 1, v_nextMacroScope_4939_);
lean_ctor_set(v_reuseFailAlloc_4956_, 2, v_ngen_4940_);
lean_ctor_set(v_reuseFailAlloc_4956_, 3, v_auxDeclNGen_4941_);
lean_ctor_set(v_reuseFailAlloc_4956_, 4, v_traceState_4942_);
lean_ctor_set(v_reuseFailAlloc_4956_, 5, v___x_4950_);
lean_ctor_set(v_reuseFailAlloc_4956_, 6, v_messages_4943_);
lean_ctor_set(v_reuseFailAlloc_4956_, 7, v_infoState_4944_);
lean_ctor_set(v_reuseFailAlloc_4956_, 8, v_snapshotTasks_4945_);
v___x_4952_ = v_reuseFailAlloc_4956_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
lean_object* v___x_4953_; lean_object* v___x_4954_; 
v___x_4953_ = lean_st_ref_put(v___y_4932_, v___x_4952_);
v___x_4954_ = lean_box(0);
v_as_x27_4930_ = v_tail_4936_;
v_b_4931_ = v___x_4954_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4959_, lean_object* v_b_4960_, lean_object* v___y_4961_, lean_object* v___y_4962_){
_start:
{
lean_object* v_res_4963_; 
v_res_4963_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4959_, v_b_4960_, v___y_4961_);
lean_dec(v___y_4961_);
lean_dec(v_as_x27_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4964_, uint8_t v_logCompileErrors_4965_, uint8_t v_markMeta_4966_, lean_object* v_a_4967_, lean_object* v_a_4968_){
_start:
{
uint8_t v___x_4970_; lean_object* v___x_4971_; 
v___x_4970_ = 0;
lean_inc(v_decl_4964_);
v___x_4971_ = l_Lean_addDecl(v_decl_4964_, v___x_4970_, v_a_4967_, v_a_4968_);
if (lean_obj_tag(v___x_4971_) == 0)
{
lean_dec_ref_known(v___x_4971_, 1);
if (v_markMeta_4966_ == 0)
{
lean_object* v___x_4972_; 
v___x_4972_ = l_Lean_compileDecl(v_decl_4964_, v_logCompileErrors_4965_, v_a_4967_, v_a_4968_);
return v___x_4972_;
}
else
{
lean_object* v___x_4973_; lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4976_; 
lean_inc(v_decl_4964_);
v___x_4973_ = l_Lean_Declaration_getNames(v_decl_4964_);
v___x_4974_ = lean_box(0);
v___x_4975_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4973_, v___x_4974_, v_a_4968_);
lean_dec(v___x_4973_);
lean_dec_ref(v___x_4975_);
v___x_4976_ = l_Lean_compileDecl(v_decl_4964_, v_logCompileErrors_4965_, v_a_4967_, v_a_4968_);
return v___x_4976_;
}
}
else
{
lean_dec(v_decl_4964_);
return v___x_4971_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4977_, lean_object* v_logCompileErrors_4978_, lean_object* v_markMeta_4979_, lean_object* v_a_4980_, lean_object* v_a_4981_, lean_object* v_a_4982_){
_start:
{
uint8_t v_logCompileErrors_boxed_4983_; uint8_t v_markMeta_boxed_4984_; lean_object* v_res_4985_; 
v_logCompileErrors_boxed_4983_ = lean_unbox(v_logCompileErrors_4978_);
v_markMeta_boxed_4984_ = lean_unbox(v_markMeta_4979_);
v_res_4985_ = l_Lean_addAndCompile(v_decl_4977_, v_logCompileErrors_boxed_4983_, v_markMeta_boxed_4984_, v_a_4980_, v_a_4981_);
lean_dec(v_a_4981_);
lean_dec_ref(v_a_4980_);
return v_res_4985_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4986_, lean_object* v_as_x27_4987_, lean_object* v_b_4988_, lean_object* v_a_4989_, lean_object* v___y_4990_, lean_object* v___y_4991_){
_start:
{
lean_object* v___x_4993_; 
v___x_4993_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4987_, v_b_4988_, v___y_4991_);
return v___x_4993_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4994_, lean_object* v_as_x27_4995_, lean_object* v_b_4996_, lean_object* v_a_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v_res_5001_; 
v_res_5001_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4994_, v_as_x27_4995_, v_b_4996_, v_a_4997_, v___y_4998_, v___y_4999_);
lean_dec(v___y_4999_);
lean_dec_ref(v___y_4998_);
lean_dec(v_as_x27_4995_);
lean_dec(v_as_4994_);
return v_res_5001_;
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
