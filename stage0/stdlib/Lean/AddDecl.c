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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Environment_registerNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
uint8_t l_Lean_instBEqDefinitionSafety_beq(uint8_t, uint8_t);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
extern lean_object* l_Lean_Linter_instInhabitedLinterSetsState_default;
extern lean_object* l_Lean_Linter_linterSetsExt;
lean_object* l_Lean_PersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
extern lean_object* l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v_env_94_; lean_object* v___x_95_; lean_object* v_toEnvExtension_96_; lean_object* v_asyncMode_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v_merged_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_108_; 
v___x_92_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_93_ = lean_st_ref_get(v___y_90_);
v_env_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc_ref(v_env_94_);
lean_dec(v___x_93_);
v___x_95_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_96_ = lean_ctor_get(v___x_95_, 0);
v_asyncMode_97_ = lean_ctor_get(v_toEnvExtension_96_, 2);
v___x_98_ = lean_box(0);
v___x_99_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_92_, v___x_95_, v_env_94_, v_asyncMode_97_, v___x_98_);
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
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_168_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_167_, v_env_155_, v_declName_129_, v_a_150_);
v___x_169_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_165_ == 0)
{
lean_ctor_set(v___x_164_, 5, v___x_169_);
lean_ctor_set(v___x_164_, 0, v___x_168_);
v___x_171_ = v___x_164_;
goto v_reusejp_170_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_nextMacroScope_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_ngen_157_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_auxDeclNGen_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_traceState_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_messages_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_infoState_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_snapshotTasks_162_);
v___x_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_st_ref_put(v_a_131_, v___x_171_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 0, v___x_166_);
v___x_174_ = v___x_152_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_166_);
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
lean_object* v___x_360_; lean_object* v___x_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_368_; 
v___x_360_ = lean_st_ref_take(v___y_348_);
v___x_361_ = lean_box(0);
v___x_362_ = l_Lean_Expr_isSyntheticSorry(v_s_347_);
lean_dec_ref(v_s_347_);
v___x_363_ = lean_box(v___x_362_);
v___x_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_364_, 0, v___x_363_);
lean_ctor_set(v___x_364_, 1, v_a_356_);
v___x_365_ = lean_array_push(v___x_360_, v___x_364_);
v___x_366_ = lean_st_ref_put(v___y_348_, v___x_365_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_361_);
v___x_368_ = v___x_358_;
goto v_reusejp_367_;
}
else
{
lean_object* v_reuseFailAlloc_369_; 
v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_369_, 0, v___x_361_);
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
uint8_t v_suppressElabErrors_boxed_418_; uint8_t v___y_15043__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_suppressElabErrors_boxed_418_ = lean_unbox(v_suppressElabErrors_415_);
v___y_15043__boxed_419_ = lean_unbox(v___y_416_);
v_res_420_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_418_, v___y_15043__boxed_419_, v_x_417_);
lean_dec(v_x_417_);
v_r_421_ = lean_box(v_res_420_);
return v_r_421_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_423_, 0, v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_424_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_425_ = lean_unsigned_to_nat(0u);
v___x_426_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v___x_425_);
lean_ctor_set(v___x_426_, 2, v___x_425_);
lean_ctor_set(v___x_426_, 3, v___x_425_);
lean_ctor_set(v___x_426_, 4, v___x_424_);
lean_ctor_set(v___x_426_, 5, v___x_424_);
lean_ctor_set(v___x_426_, 6, v___x_424_);
lean_ctor_set(v___x_426_, 7, v___x_424_);
lean_ctor_set(v___x_426_, 8, v___x_424_);
lean_ctor_set(v___x_426_, 9, v___x_424_);
lean_ctor_set(v___x_426_, 10, v___x_424_);
return v___x_426_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_427_ = lean_unsigned_to_nat(32u);
v___x_428_ = lean_mk_empty_array_with_capacity(v___x_427_);
v___x_429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
return v___x_429_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
size_t v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; 
v___x_430_ = ((size_t)5ULL);
v___x_431_ = lean_unsigned_to_nat(0u);
v___x_432_ = lean_unsigned_to_nat(32u);
v___x_433_ = lean_mk_empty_array_with_capacity(v___x_432_);
v___x_434_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_435_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_435_, 0, v___x_434_);
lean_ctor_set(v___x_435_, 1, v___x_433_);
lean_ctor_set(v___x_435_, 2, v___x_431_);
lean_ctor_set(v___x_435_, 3, v___x_431_);
lean_ctor_set_usize(v___x_435_, 4, v___x_430_);
return v___x_435_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_436_ = lean_box(1);
v___x_437_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_438_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
lean_ctor_set(v___x_439_, 1, v___x_437_);
lean_ctor_set(v___x_439_, 2, v___x_436_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
lean_object* v___x_444_; lean_object* v_toCold_445_; lean_object* v_env_446_; lean_object* v_options_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v___x_444_ = lean_st_ref_get(v___y_442_);
v_toCold_445_ = lean_ctor_get(v___y_441_, 0);
v_env_446_ = lean_ctor_get(v___x_444_, 0);
lean_inc_ref(v_env_446_);
lean_dec(v___x_444_);
v_options_447_ = lean_ctor_get(v_toCold_445_, 2);
v___x_448_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_449_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
lean_inc_ref(v_options_447_);
v___x_450_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_450_, 0, v_env_446_);
lean_ctor_set(v___x_450_, 1, v___x_448_);
lean_ctor_set(v___x_450_, 2, v___x_449_);
lean_ctor_set(v___x_450_, 3, v_options_447_);
v___x_451_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_451_, 0, v___x_450_);
lean_ctor_set(v___x_451_, 1, v_msgData_440_);
v___x_452_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_452_, 0, v___x_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_453_, v___y_454_, v___y_455_);
lean_dec(v___y_455_);
lean_dec_ref(v___y_454_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_459_, lean_object* v_msgData_460_, uint8_t v_severity_461_, uint8_t v_isSilent_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
lean_object* v___y_467_; lean_object* v___y_468_; lean_object* v___y_469_; uint8_t v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; uint8_t v___y_473_; lean_object* v_currNamespace_474_; lean_object* v_openDecls_475_; lean_object* v___y_476_; lean_object* v___y_502_; lean_object* v___y_503_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; uint8_t v___y_507_; lean_object* v___y_508_; uint8_t v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_529_; lean_object* v___y_530_; lean_object* v___y_531_; lean_object* v___y_532_; uint8_t v___y_533_; uint8_t v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; lean_object* v___y_538_; lean_object* v___y_542_; lean_object* v___y_543_; lean_object* v___y_544_; lean_object* v___y_545_; uint8_t v___y_546_; lean_object* v___y_547_; uint8_t v___y_548_; lean_object* v___y_549_; uint8_t v___y_550_; uint8_t v___x_555_; lean_object* v___y_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v___y_560_; lean_object* v___y_561_; lean_object* v___y_562_; uint8_t v___y_563_; uint8_t v___y_564_; uint8_t v___y_565_; uint8_t v___y_567_; uint8_t v___x_585_; 
v___x_555_ = 2;
v___x_585_ = l_Lean_instBEqMessageSeverity_beq(v_severity_461_, v___x_555_);
if (v___x_585_ == 0)
{
v___y_567_ = v___x_585_;
goto v___jp_566_;
}
else
{
uint8_t v___x_586_; 
lean_inc_ref(v_msgData_460_);
v___x_586_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_460_);
v___y_567_ = v___x_586_;
goto v___jp_566_;
}
v___jp_466_:
{
lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v_env_481_; lean_object* v_nextMacroScope_482_; lean_object* v_ngen_483_; lean_object* v_auxDeclNGen_484_; lean_object* v_traceState_485_; lean_object* v_cache_486_; lean_object* v_messages_487_; lean_object* v_infoState_488_; lean_object* v_snapshotTasks_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_500_; 
lean_inc(v_openDecls_475_);
lean_inc(v_currNamespace_474_);
v___x_477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_477_, 0, v_currNamespace_474_);
lean_ctor_set(v___x_477_, 1, v_openDecls_475_);
v___x_478_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_478_, 0, v___x_477_);
lean_ctor_set(v___x_478_, 1, v___y_469_);
lean_inc_ref(v___y_467_);
lean_inc_ref(v___y_472_);
v___x_479_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_479_, 0, v___y_472_);
lean_ctor_set(v___x_479_, 1, v___y_471_);
lean_ctor_set(v___x_479_, 2, v___y_468_);
lean_ctor_set(v___x_479_, 3, v___y_467_);
lean_ctor_set(v___x_479_, 4, v___x_478_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*5, v___y_473_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*5 + 1, v___y_470_);
lean_ctor_set_uint8(v___x_479_, sizeof(void*)*5 + 2, v_isSilent_462_);
v___x_480_ = lean_st_ref_take(v___y_476_);
v_env_481_ = lean_ctor_get(v___x_480_, 0);
v_nextMacroScope_482_ = lean_ctor_get(v___x_480_, 1);
v_ngen_483_ = lean_ctor_get(v___x_480_, 2);
v_auxDeclNGen_484_ = lean_ctor_get(v___x_480_, 3);
v_traceState_485_ = lean_ctor_get(v___x_480_, 4);
v_cache_486_ = lean_ctor_get(v___x_480_, 5);
v_messages_487_ = lean_ctor_get(v___x_480_, 6);
v_infoState_488_ = lean_ctor_get(v___x_480_, 7);
v_snapshotTasks_489_ = lean_ctor_get(v___x_480_, 8);
v_isSharedCheck_500_ = !lean_is_exclusive(v___x_480_);
if (v_isSharedCheck_500_ == 0)
{
v___x_491_ = v___x_480_;
v_isShared_492_ = v_isSharedCheck_500_;
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
lean_dec(v___x_480_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_500_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_496_; 
v___x_493_ = lean_box(0);
v___x_494_ = l_Lean_MessageLog_add(v___x_479_, v_messages_487_);
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 6, v___x_494_);
v___x_496_ = v___x_491_;
goto v_reusejp_495_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_env_481_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_nextMacroScope_482_);
lean_ctor_set(v_reuseFailAlloc_499_, 2, v_ngen_483_);
lean_ctor_set(v_reuseFailAlloc_499_, 3, v_auxDeclNGen_484_);
lean_ctor_set(v_reuseFailAlloc_499_, 4, v_traceState_485_);
lean_ctor_set(v_reuseFailAlloc_499_, 5, v_cache_486_);
lean_ctor_set(v_reuseFailAlloc_499_, 6, v___x_494_);
lean_ctor_set(v_reuseFailAlloc_499_, 7, v_infoState_488_);
lean_ctor_set(v_reuseFailAlloc_499_, 8, v_snapshotTasks_489_);
v___x_496_ = v_reuseFailAlloc_499_;
goto v_reusejp_495_;
}
v_reusejp_495_:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_st_ref_put(v___y_476_, v___x_496_);
v___x_498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_498_, 0, v___x_493_);
return v___x_498_;
}
}
}
v___jp_501_:
{
lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_527_; 
v___x_512_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_460_);
v___x_513_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_512_, v___y_463_, v___y_464_);
v_a_514_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_527_ == 0)
{
v___x_516_ = v___x_513_;
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_513_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_527_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
lean_inc_ref_n(v___y_510_, 2);
v___x_518_ = l_Lean_FileMap_toPosition(v___y_510_, v___y_505_);
lean_dec(v___y_505_);
v___x_519_ = l_Lean_FileMap_toPosition(v___y_510_, v___y_511_);
lean_dec(v___y_511_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___x_521_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_506_ == 0)
{
lean_del_object(v___x_516_);
lean_dec_ref(v___y_503_);
v___y_467_ = v___x_521_;
v___y_468_ = v___x_520_;
v___y_469_ = v_a_514_;
v___y_470_ = v___y_507_;
v___y_471_ = v___x_518_;
v___y_472_ = v___y_508_;
v___y_473_ = v___y_509_;
v_currNamespace_474_ = v___y_504_;
v_openDecls_475_ = v___y_502_;
v___y_476_ = v___y_464_;
goto v___jp_466_;
}
else
{
uint8_t v___x_522_; 
lean_inc(v_a_514_);
v___x_522_ = l_Lean_MessageData_hasTag(v___y_503_, v_a_514_);
if (v___x_522_ == 0)
{
lean_object* v___x_523_; lean_object* v___x_525_; 
lean_dec_ref_known(v___x_520_, 1);
lean_dec_ref(v___x_518_);
lean_dec(v_a_514_);
v___x_523_ = lean_box(0);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_523_);
v___x_525_ = v___x_516_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v___x_523_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
else
{
lean_del_object(v___x_516_);
v___y_467_ = v___x_521_;
v___y_468_ = v___x_520_;
v___y_469_ = v_a_514_;
v___y_470_ = v___y_507_;
v___y_471_ = v___x_518_;
v___y_472_ = v___y_508_;
v___y_473_ = v___y_509_;
v_currNamespace_474_ = v___y_504_;
v_openDecls_475_ = v___y_502_;
v___y_476_ = v___y_464_;
goto v___jp_466_;
}
}
}
}
v___jp_528_:
{
lean_object* v___x_539_; 
v___x_539_ = l_Lean_Syntax_getTailPos_x3f(v___y_532_, v___y_537_);
lean_dec(v___y_532_);
if (lean_obj_tag(v___x_539_) == 0)
{
lean_inc(v___y_538_);
v___y_502_ = v___y_529_;
v___y_503_ = v___y_531_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_538_;
v___y_506_ = v___y_533_;
v___y_507_ = v___y_534_;
v___y_508_ = v___y_535_;
v___y_509_ = v___y_537_;
v___y_510_ = v___y_536_;
v___y_511_ = v___y_538_;
goto v___jp_501_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_539_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_539_, 1);
v___y_502_ = v___y_529_;
v___y_503_ = v___y_531_;
v___y_504_ = v___y_530_;
v___y_505_ = v___y_538_;
v___y_506_ = v___y_533_;
v___y_507_ = v___y_534_;
v___y_508_ = v___y_535_;
v___y_509_ = v___y_537_;
v___y_510_ = v___y_536_;
v___y_511_ = v_val_540_;
goto v___jp_501_;
}
}
v___jp_541_:
{
lean_object* v_ref_551_; lean_object* v___x_552_; 
v_ref_551_ = l_Lean_replaceRef(v_ref_459_, v___y_545_);
v___x_552_ = l_Lean_Syntax_getPos_x3f(v_ref_551_, v___y_548_);
if (lean_obj_tag(v___x_552_) == 0)
{
lean_object* v___x_553_; 
v___x_553_ = lean_unsigned_to_nat(0u);
v___y_529_ = v___y_542_;
v___y_530_ = v___y_544_;
v___y_531_ = v___y_543_;
v___y_532_ = v_ref_551_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_550_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_549_;
v___y_537_ = v___y_548_;
v___y_538_ = v___x_553_;
goto v___jp_528_;
}
else
{
lean_object* v_val_554_; 
v_val_554_ = lean_ctor_get(v___x_552_, 0);
lean_inc(v_val_554_);
lean_dec_ref_known(v___x_552_, 1);
v___y_529_ = v___y_542_;
v___y_530_ = v___y_544_;
v___y_531_ = v___y_543_;
v___y_532_ = v_ref_551_;
v___y_533_ = v___y_546_;
v___y_534_ = v___y_550_;
v___y_535_ = v___y_547_;
v___y_536_ = v___y_549_;
v___y_537_ = v___y_548_;
v___y_538_ = v_val_554_;
goto v___jp_528_;
}
}
v___jp_556_:
{
if (v___y_565_ == 0)
{
v___y_542_ = v___y_557_;
v___y_543_ = v___y_559_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_562_;
v___y_546_ = v___y_563_;
v___y_547_ = v___y_560_;
v___y_548_ = v___y_564_;
v___y_549_ = v___y_561_;
v___y_550_ = v_severity_461_;
goto v___jp_541_;
}
else
{
v___y_542_ = v___y_557_;
v___y_543_ = v___y_559_;
v___y_544_ = v___y_558_;
v___y_545_ = v___y_562_;
v___y_546_ = v___y_563_;
v___y_547_ = v___y_560_;
v___y_548_ = v___y_564_;
v___y_549_ = v___y_561_;
v___y_550_ = v___x_555_;
goto v___jp_541_;
}
}
v___jp_566_:
{
if (v___y_567_ == 0)
{
lean_object* v_toCold_568_; lean_object* v_ref_569_; uint8_t v_suppressElabErrors_570_; lean_object* v_fileName_571_; lean_object* v_fileMap_572_; lean_object* v_options_573_; lean_object* v_currNamespace_574_; lean_object* v_openDecls_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___f_578_; uint8_t v___x_579_; uint8_t v___x_580_; 
v_toCold_568_ = lean_ctor_get(v___y_463_, 0);
v_ref_569_ = lean_ctor_get(v___y_463_, 2);
v_suppressElabErrors_570_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 1);
v_fileName_571_ = lean_ctor_get(v_toCold_568_, 0);
v_fileMap_572_ = lean_ctor_get(v_toCold_568_, 1);
v_options_573_ = lean_ctor_get(v_toCold_568_, 2);
v_currNamespace_574_ = lean_ctor_get(v_toCold_568_, 4);
v_openDecls_575_ = lean_ctor_get(v_toCold_568_, 5);
v___x_576_ = lean_box(v_suppressElabErrors_570_);
v___x_577_ = lean_box(v___y_567_);
v___f_578_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_578_, 0, v___x_576_);
lean_closure_set(v___f_578_, 1, v___x_577_);
v___x_579_ = 1;
v___x_580_ = l_Lean_instBEqMessageSeverity_beq(v_severity_461_, v___x_579_);
if (v___x_580_ == 0)
{
v___y_557_ = v_openDecls_575_;
v___y_558_ = v_currNamespace_574_;
v___y_559_ = v___f_578_;
v___y_560_ = v_fileName_571_;
v___y_561_ = v_fileMap_572_;
v___y_562_ = v_ref_569_;
v___y_563_ = v_suppressElabErrors_570_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_580_;
goto v___jp_556_;
}
else
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = l_Lean_warningAsError;
v___x_582_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_573_, v___x_581_);
v___y_557_ = v_openDecls_575_;
v___y_558_ = v_currNamespace_574_;
v___y_559_ = v___f_578_;
v___y_560_ = v_fileName_571_;
v___y_561_ = v_fileMap_572_;
v___y_562_ = v_ref_569_;
v___y_563_ = v_suppressElabErrors_570_;
v___y_564_ = v___y_567_;
v___y_565_ = v___x_582_;
goto v___jp_556_;
}
}
else
{
lean_object* v___x_583_; lean_object* v___x_584_; 
lean_dec_ref(v_msgData_460_);
v___x_583_ = lean_box(0);
v___x_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_584_, 0, v___x_583_);
return v___x_584_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_587_, lean_object* v_msgData_588_, lean_object* v_severity_589_, lean_object* v_isSilent_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v_severity_boxed_594_; uint8_t v_isSilent_boxed_595_; lean_object* v_res_596_; 
v_severity_boxed_594_ = lean_unbox(v_severity_589_);
v_isSilent_boxed_595_ = lean_unbox(v_isSilent_590_);
v_res_596_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_587_, v_msgData_588_, v_severity_boxed_594_, v_isSilent_boxed_595_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
lean_dec(v_ref_587_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_597_, uint8_t v_severity_598_, uint8_t v_isSilent_599_, lean_object* v___y_600_, lean_object* v___y_601_){
_start:
{
lean_object* v_ref_603_; lean_object* v___x_604_; 
v_ref_603_ = lean_ctor_get(v___y_600_, 2);
v___x_604_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_603_, v_msgData_597_, v_severity_598_, v_isSilent_599_, v___y_600_, v___y_601_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_605_, lean_object* v_severity_606_, lean_object* v_isSilent_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_){
_start:
{
uint8_t v_severity_boxed_611_; uint8_t v_isSilent_boxed_612_; lean_object* v_res_613_; 
v_severity_boxed_611_ = lean_unbox(v_severity_606_);
v_isSilent_boxed_612_ = lean_unbox(v_isSilent_607_);
v_res_613_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_605_, v_severity_boxed_611_, v_isSilent_boxed_612_, v___y_608_, v___y_609_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_614_, lean_object* v___y_615_, lean_object* v___y_616_){
_start:
{
uint8_t v___x_618_; uint8_t v___x_619_; lean_object* v___x_620_; 
v___x_618_ = 1;
v___x_619_ = 0;
v___x_620_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_614_, v___x_618_, v___x_619_, v___y_615_, v___y_616_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_621_, v___y_622_, v___y_623_);
lean_dec(v___y_623_);
lean_dec_ref(v___y_622_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_629_, size_t v_sz_630_, size_t v_i_631_, lean_object* v_b_632_){
_start:
{
uint8_t v___x_633_; 
v___x_633_ = lean_usize_dec_lt(v_i_631_, v_sz_630_);
if (v___x_633_ == 0)
{
lean_inc_ref(v_b_632_);
return v_b_632_;
}
else
{
lean_object* v_a_634_; lean_object* v_fst_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v_a_634_ = lean_array_uget_borrowed(v_as_629_, v_i_631_);
v_fst_635_ = lean_ctor_get(v_a_634_, 0);
v___x_636_ = lean_box(0);
v___x_637_ = lean_unbox(v_fst_635_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; size_t v___x_639_; size_t v___x_640_; 
v___x_638_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_639_ = ((size_t)1ULL);
v___x_640_ = lean_usize_add(v_i_631_, v___x_639_);
v_i_631_ = v___x_640_;
v_b_632_ = v___x_638_;
goto _start;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
lean_inc(v_a_634_);
v___x_642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_642_, 0, v_a_634_);
v___x_643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_643_, 0, v___x_642_);
v___x_644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
lean_ctor_set(v___x_644_, 1, v___x_636_);
return v___x_644_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_645_, lean_object* v_sz_646_, lean_object* v_i_647_, lean_object* v_b_648_){
_start:
{
size_t v_sz_boxed_649_; size_t v_i_boxed_650_; lean_object* v_res_651_; 
v_sz_boxed_649_ = lean_unbox_usize(v_sz_646_);
lean_dec(v_sz_646_);
v_i_boxed_650_ = lean_unbox_usize(v_i_647_);
lean_dec(v_i_647_);
v_res_651_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_645_, v_sz_boxed_649_, v_i_boxed_650_, v_b_648_);
lean_dec_ref(v_b_648_);
lean_dec_ref(v_as_645_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_652_, lean_object* v_e_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_){
_start:
{
lean_object* v___x_660_; 
v___x_660_ = l_Lean_Expr_getSorry_x3f(v_e_653_);
if (lean_obj_tag(v___x_660_) == 1)
{
lean_object* v_val_661_; lean_object* v___x_662_; 
v_val_661_ = lean_ctor_get(v___x_660_, 0);
lean_inc(v_val_661_);
lean_dec_ref_known(v___x_660_, 1);
lean_inc(v___y_658_);
lean_inc_ref(v___y_657_);
lean_inc(v___y_656_);
lean_inc_ref(v___y_655_);
lean_inc(v___y_654_);
v___x_662_ = lean_apply_7(v_fn_652_, v_val_661_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, lean_box(0));
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_671_; 
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_662_, 0);
lean_dec(v_unused_672_);
v___x_664_ = v___x_662_;
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
else
{
lean_dec(v___x_662_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
uint8_t v___x_666_; lean_object* v___x_667_; lean_object* v___x_669_; 
v___x_666_ = 0;
v___x_667_ = lean_box(v___x_666_);
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 0, v___x_667_);
v___x_669_ = v___x_664_;
goto v_reusejp_668_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v___x_667_);
v___x_669_ = v_reuseFailAlloc_670_;
goto v_reusejp_668_;
}
v_reusejp_668_:
{
return v___x_669_;
}
}
}
else
{
lean_object* v_a_673_; lean_object* v___x_675_; uint8_t v_isShared_676_; uint8_t v_isSharedCheck_680_; 
v_a_673_ = lean_ctor_get(v___x_662_, 0);
v_isSharedCheck_680_ = !lean_is_exclusive(v___x_662_);
if (v_isSharedCheck_680_ == 0)
{
v___x_675_ = v___x_662_;
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
else
{
lean_inc(v_a_673_);
lean_dec(v___x_662_);
v___x_675_ = lean_box(0);
v_isShared_676_ = v_isSharedCheck_680_;
goto v_resetjp_674_;
}
v_resetjp_674_:
{
lean_object* v___x_678_; 
if (v_isShared_676_ == 0)
{
v___x_678_ = v___x_675_;
goto v_reusejp_677_;
}
else
{
lean_object* v_reuseFailAlloc_679_; 
v_reuseFailAlloc_679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_679_, 0, v_a_673_);
v___x_678_ = v_reuseFailAlloc_679_;
goto v_reusejp_677_;
}
v_reusejp_677_:
{
return v___x_678_;
}
}
}
}
else
{
uint8_t v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; 
lean_dec(v___x_660_);
lean_dec_ref(v_fn_652_);
v___x_681_ = 1;
v___x_682_ = lean_box(v___x_681_);
v___x_683_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_683_, 0, v___x_682_);
return v___x_683_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_684_, lean_object* v_e_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_684_, v_e_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v_e_685_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_693_, lean_object* v_x_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_){
_start:
{
lean_object* v___x_701_; lean_object* v___x_702_; 
v___x_701_ = lean_apply_1(v_x_694_, lean_box(0));
v___x_702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_703_, lean_object* v_x_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_703_, v_x_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec_ref(v___y_706_);
lean_dec(v___y_705_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v_b_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
lean_object* v___x_721_; 
lean_inc(v___y_719_);
lean_inc_ref(v___y_718_);
lean_inc(v___y_717_);
lean_inc_ref(v___y_716_);
lean_inc(v___y_714_);
lean_inc(v___y_713_);
v___x_721_ = lean_apply_8(v_k_712_, v_b_715_, v___y_713_, v___y_714_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, lean_box(0));
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v_b_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_){
_start:
{
lean_object* v_res_731_; 
v_res_731_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_722_, v___y_723_, v___y_724_, v_b_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec_ref(v___y_726_);
lean_dec(v___y_724_);
lean_dec(v___y_723_);
return v_res_731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_732_, lean_object* v_type_733_, lean_object* v_val_734_, lean_object* v_k_735_, uint8_t v_nondep_736_, uint8_t v_kind_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_){
_start:
{
lean_object* v___f_745_; lean_object* v___x_746_; 
lean_inc(v___y_739_);
lean_inc(v___y_738_);
v___f_745_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_745_, 0, v_k_735_);
lean_closure_set(v___f_745_, 1, v___y_738_);
lean_closure_set(v___f_745_, 2, v___y_739_);
v___x_746_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_732_, v_type_733_, v_val_734_, v___f_745_, v_nondep_736_, v_kind_737_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
return v___x_746_;
}
else
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_755_, lean_object* v_type_756_, lean_object* v_val_757_, lean_object* v_k_758_, lean_object* v_nondep_759_, lean_object* v_kind_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_){
_start:
{
uint8_t v_nondep_boxed_768_; uint8_t v_kind_boxed_769_; lean_object* v_res_770_; 
v_nondep_boxed_768_ = lean_unbox(v_nondep_759_);
v_kind_boxed_769_ = lean_unbox(v_kind_760_);
v_res_770_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_755_, v_type_756_, v_val_757_, v_k_758_, v_nondep_boxed_768_, v_kind_boxed_769_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec(v___y_761_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_771_, lean_object* v_f_772_, lean_object* v_body_773_, lean_object* v_x_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_, lean_object* v___y_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_771_, v_f_772_, v_body_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_, v___y_780_);
lean_dec(v___y_780_);
lean_dec_ref(v___y_779_);
lean_dec(v___y_778_);
lean_dec_ref(v___y_777_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_783_, lean_object* v_fvars_784_, lean_object* v_a_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_){
_start:
{
if (lean_obj_tag(v_a_785_) == 8)
{
lean_object* v_declName_793_; lean_object* v_type_794_; lean_object* v_value_795_; lean_object* v_body_796_; lean_object* v___f_797_; lean_object* v_d_798_; lean_object* v_v_799_; lean_object* v___x_800_; 
v_declName_793_ = lean_ctor_get(v_a_785_, 0);
lean_inc(v_declName_793_);
v_type_794_ = lean_ctor_get(v_a_785_, 1);
lean_inc_ref(v_type_794_);
v_value_795_ = lean_ctor_get(v_a_785_, 2);
lean_inc_ref(v_value_795_);
v_body_796_ = lean_ctor_get(v_a_785_, 3);
lean_inc_ref(v_body_796_);
lean_dec_ref_known(v_a_785_, 4);
lean_inc_ref_n(v_f_783_, 2);
lean_inc_ref(v_fvars_784_);
v___f_797_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_797_, 0, v_fvars_784_);
lean_closure_set(v___f_797_, 1, v_f_783_);
lean_closure_set(v___f_797_, 2, v_body_796_);
v_d_798_ = lean_expr_instantiate_rev(v_type_794_, v_fvars_784_);
lean_dec_ref(v_type_794_);
v_v_799_ = lean_expr_instantiate_rev(v_value_795_, v_fvars_784_);
lean_dec_ref(v_fvars_784_);
lean_dec_ref(v_value_795_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v_d_798_);
v___x_800_ = lean_apply_8(v_f_783_, v_d_798_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
if (lean_obj_tag(v___x_800_) == 0)
{
lean_object* v___x_801_; 
lean_dec_ref_known(v___x_800_, 1);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v___y_786_);
lean_inc_ref(v_v_799_);
v___x_801_ = lean_apply_8(v_f_783_, v_v_799_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
if (lean_obj_tag(v___x_801_) == 0)
{
uint8_t v___x_802_; uint8_t v___x_803_; lean_object* v___x_804_; 
lean_dec_ref_known(v___x_801_, 1);
v___x_802_ = 0;
v___x_803_ = 0;
v___x_804_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_793_, v_d_798_, v_v_799_, v___f_797_, v___x_802_, v___x_803_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_);
return v___x_804_;
}
else
{
lean_dec_ref(v_v_799_);
lean_dec_ref(v_d_798_);
lean_dec_ref(v___f_797_);
lean_dec(v_declName_793_);
return v___x_801_;
}
}
else
{
lean_dec_ref(v_v_799_);
lean_dec_ref(v_d_798_);
lean_dec_ref(v___f_797_);
lean_dec(v_declName_793_);
lean_dec_ref(v_f_783_);
return v___x_800_;
}
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_805_ = lean_expr_instantiate_rev(v_a_785_, v_fvars_784_);
lean_dec_ref(v_fvars_784_);
lean_dec_ref(v_a_785_);
lean_inc(v___y_791_);
lean_inc_ref(v___y_790_);
lean_inc(v___y_789_);
lean_inc_ref(v___y_788_);
lean_inc(v___y_787_);
lean_inc(v___y_786_);
v___x_806_ = lean_apply_8(v_f_783_, v___x_805_, v___y_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_, v___y_791_, lean_box(0));
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_807_, lean_object* v_f_808_, lean_object* v_body_809_, lean_object* v_x_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_818_ = lean_array_push(v_fvars_807_, v_x_810_);
v___x_819_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_808_, v___x_818_, v_body_809_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_820_, lean_object* v_fvars_821_, lean_object* v_a_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_820_, v_fvars_821_, v_a_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
lean_dec(v___y_828_);
lean_dec_ref(v___y_827_);
lean_dec(v___y_826_);
lean_dec_ref(v___y_825_);
lean_dec(v___y_824_);
lean_dec(v___y_823_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_833_, lean_object* v_e_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_843_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_833_, v___x_842_, v_e_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_844_, lean_object* v_e_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_844_, v_e_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec(v___y_846_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_854_, uint8_t v_bi_855_, lean_object* v_type_856_, lean_object* v_k_857_, uint8_t v_kind_858_, lean_object* v___y_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_){
_start:
{
lean_object* v___f_866_; lean_object* v___x_867_; 
lean_inc(v___y_860_);
lean_inc(v___y_859_);
v___f_866_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_866_, 0, v_k_857_);
lean_closure_set(v___f_866_, 1, v___y_859_);
lean_closure_set(v___f_866_, 2, v___y_860_);
v___x_867_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_854_, v_bi_855_, v_type_856_, v___f_866_, v_kind_858_, v___y_861_, v___y_862_, v___y_863_, v___y_864_);
if (lean_obj_tag(v___x_867_) == 0)
{
return v___x_867_;
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_867_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_867_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_867_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_876_, lean_object* v_bi_877_, lean_object* v_type_878_, lean_object* v_k_879_, lean_object* v_kind_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_){
_start:
{
uint8_t v_bi_boxed_888_; uint8_t v_kind_boxed_889_; lean_object* v_res_890_; 
v_bi_boxed_888_ = lean_unbox(v_bi_877_);
v_kind_boxed_889_ = lean_unbox(v_kind_880_);
v_res_890_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_876_, v_bi_boxed_888_, v_type_878_, v_k_879_, v_kind_boxed_889_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_);
lean_dec(v___y_886_);
lean_dec_ref(v___y_885_);
lean_dec(v___y_884_);
lean_dec_ref(v___y_883_);
lean_dec(v___y_882_);
lean_dec(v___y_881_);
return v_res_890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_891_, lean_object* v_f_892_, lean_object* v_body_893_, lean_object* v_x_894_, lean_object* v___y_895_, lean_object* v___y_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_891_, v_f_892_, v_body_893_, v_x_894_, v___y_895_, v___y_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_);
lean_dec(v___y_900_);
lean_dec_ref(v___y_899_);
lean_dec(v___y_898_);
lean_dec_ref(v___y_897_);
lean_dec(v___y_896_);
lean_dec(v___y_895_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_903_, lean_object* v_fvars_904_, lean_object* v_a_905_, lean_object* v___y_906_, lean_object* v___y_907_, lean_object* v___y_908_, lean_object* v___y_909_, lean_object* v___y_910_, lean_object* v___y_911_){
_start:
{
if (lean_obj_tag(v_a_905_) == 7)
{
lean_object* v_binderName_913_; lean_object* v_binderType_914_; lean_object* v_body_915_; uint8_t v_binderInfo_916_; lean_object* v___f_917_; lean_object* v_d_918_; lean_object* v___x_919_; 
v_binderName_913_ = lean_ctor_get(v_a_905_, 0);
lean_inc(v_binderName_913_);
v_binderType_914_ = lean_ctor_get(v_a_905_, 1);
lean_inc_ref(v_binderType_914_);
v_body_915_ = lean_ctor_get(v_a_905_, 2);
lean_inc_ref(v_body_915_);
v_binderInfo_916_ = lean_ctor_get_uint8(v_a_905_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_905_, 3);
lean_inc_ref(v_f_903_);
lean_inc_ref(v_fvars_904_);
v___f_917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_917_, 0, v_fvars_904_);
lean_closure_set(v___f_917_, 1, v_f_903_);
lean_closure_set(v___f_917_, 2, v_body_915_);
v_d_918_ = lean_expr_instantiate_rev(v_binderType_914_, v_fvars_904_);
lean_dec_ref(v_fvars_904_);
lean_dec_ref(v_binderType_914_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc(v___y_906_);
lean_inc_ref(v_d_918_);
v___x_919_ = lean_apply_8(v_f_903_, v_d_918_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
if (lean_obj_tag(v___x_919_) == 0)
{
uint8_t v___x_920_; lean_object* v___x_921_; 
lean_dec_ref_known(v___x_919_, 1);
v___x_920_ = 0;
v___x_921_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_913_, v_binderInfo_916_, v_d_918_, v___f_917_, v___x_920_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_);
return v___x_921_;
}
else
{
lean_dec_ref(v_d_918_);
lean_dec_ref(v___f_917_);
lean_dec(v_binderName_913_);
return v___x_919_;
}
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_expr_instantiate_rev(v_a_905_, v_fvars_904_);
lean_dec_ref(v_fvars_904_);
lean_dec_ref(v_a_905_);
lean_inc(v___y_911_);
lean_inc_ref(v___y_910_);
lean_inc(v___y_909_);
lean_inc_ref(v___y_908_);
lean_inc(v___y_907_);
lean_inc(v___y_906_);
v___x_923_ = lean_apply_8(v_f_903_, v___x_922_, v___y_906_, v___y_907_, v___y_908_, v___y_909_, v___y_910_, v___y_911_, lean_box(0));
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_924_, lean_object* v_f_925_, lean_object* v_body_926_, lean_object* v_x_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_){
_start:
{
lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_935_ = lean_array_push(v_fvars_924_, v_x_927_);
v___x_936_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_925_, v___x_935_, v_body_926_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_937_, lean_object* v_fvars_938_, lean_object* v_a_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_, lean_object* v___y_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_937_, v_fvars_938_, v_a_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_, v___y_944_, v___y_945_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec(v___y_943_);
lean_dec_ref(v___y_942_);
lean_dec(v___y_941_);
lean_dec(v___y_940_);
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_948_, lean_object* v_e_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_958_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_948_, v___x_957_, v_e_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_, v___y_955_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_959_, lean_object* v_e_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_, lean_object* v___y_965_, lean_object* v___y_966_, lean_object* v___y_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_959_, v_e_960_, v___y_961_, v___y_962_, v___y_963_, v___y_964_, v___y_965_, v___y_966_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
lean_dec(v___y_964_);
lean_dec_ref(v___y_963_);
lean_dec(v___y_962_);
lean_dec(v___y_961_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_969_, lean_object* v_f_970_, lean_object* v_body_971_, lean_object* v_x_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_969_, v_f_970_, v_body_971_, v_x_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
lean_dec(v___y_974_);
lean_dec(v___y_973_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_981_, lean_object* v_fvars_982_, lean_object* v_a_983_, lean_object* v___y_984_, lean_object* v___y_985_, lean_object* v___y_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_){
_start:
{
if (lean_obj_tag(v_a_983_) == 6)
{
lean_object* v_binderName_991_; lean_object* v_binderType_992_; lean_object* v_body_993_; uint8_t v_binderInfo_994_; lean_object* v___f_995_; lean_object* v_d_996_; lean_object* v___x_997_; 
v_binderName_991_ = lean_ctor_get(v_a_983_, 0);
lean_inc(v_binderName_991_);
v_binderType_992_ = lean_ctor_get(v_a_983_, 1);
lean_inc_ref(v_binderType_992_);
v_body_993_ = lean_ctor_get(v_a_983_, 2);
lean_inc_ref(v_body_993_);
v_binderInfo_994_ = lean_ctor_get_uint8(v_a_983_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_983_, 3);
lean_inc_ref(v_f_981_);
lean_inc_ref(v_fvars_982_);
v___f_995_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_995_, 0, v_fvars_982_);
lean_closure_set(v___f_995_, 1, v_f_981_);
lean_closure_set(v___f_995_, 2, v_body_993_);
v_d_996_ = lean_expr_instantiate_rev(v_binderType_992_, v_fvars_982_);
lean_dec_ref(v_fvars_982_);
lean_dec_ref(v_binderType_992_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc(v___y_984_);
lean_inc_ref(v_d_996_);
v___x_997_ = lean_apply_8(v_f_981_, v_d_996_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, lean_box(0));
if (lean_obj_tag(v___x_997_) == 0)
{
uint8_t v___x_998_; lean_object* v___x_999_; 
lean_dec_ref_known(v___x_997_, 1);
v___x_998_ = 0;
v___x_999_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_991_, v_binderInfo_994_, v_d_996_, v___f_995_, v___x_998_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_);
return v___x_999_;
}
else
{
lean_dec_ref(v_d_996_);
lean_dec_ref(v___f_995_);
lean_dec(v_binderName_991_);
return v___x_997_;
}
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; 
v___x_1000_ = lean_expr_instantiate_rev(v_a_983_, v_fvars_982_);
lean_dec_ref(v_fvars_982_);
lean_dec_ref(v_a_983_);
lean_inc(v___y_989_);
lean_inc_ref(v___y_988_);
lean_inc(v___y_987_);
lean_inc_ref(v___y_986_);
lean_inc(v___y_985_);
lean_inc(v___y_984_);
v___x_1001_ = lean_apply_8(v_f_981_, v___x_1000_, v___y_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_, v___y_989_, lean_box(0));
return v___x_1001_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_1002_, lean_object* v_f_1003_, lean_object* v_body_1004_, lean_object* v_x_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_, lean_object* v___y_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_array_push(v_fvars_1002_, v_x_1005_);
v___x_1014_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1003_, v___x_1013_, v_body_1004_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_, v___y_1010_, v___y_1011_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_1015_, lean_object* v_fvars_1016_, lean_object* v_a_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1015_, v_fvars_1016_, v_a_1017_, v___y_1018_, v___y_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1026_, lean_object* v_e_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1036_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1026_, v___x_1035_, v_e_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1037_, lean_object* v_e_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_){
_start:
{
lean_object* v_res_1046_; 
v_res_1046_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1037_, v_e_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_, v___y_1044_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec(v___y_1039_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1047_, lean_object* v_x_1048_){
_start:
{
if (lean_obj_tag(v_x_1048_) == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = lean_box(0);
return v___x_1049_;
}
else
{
lean_object* v_key_1050_; lean_object* v_value_1051_; lean_object* v_tail_1052_; uint8_t v___x_1053_; 
v_key_1050_ = lean_ctor_get(v_x_1048_, 0);
v_value_1051_ = lean_ctor_get(v_x_1048_, 1);
v_tail_1052_ = lean_ctor_get(v_x_1048_, 2);
v___x_1053_ = lean_expr_eqv(v_key_1050_, v_a_1047_);
if (v___x_1053_ == 0)
{
v_x_1048_ = v_tail_1052_;
goto _start;
}
else
{
lean_object* v___x_1055_; 
lean_inc(v_value_1051_);
v___x_1055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1055_, 0, v_value_1051_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1056_, lean_object* v_x_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1056_, v_x_1057_);
lean_dec(v_x_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1059_, lean_object* v_a_1060_){
_start:
{
lean_object* v_buckets_1061_; lean_object* v___x_1062_; uint64_t v___x_1063_; uint64_t v___x_1064_; uint64_t v___x_1065_; uint64_t v_fold_1066_; uint64_t v___x_1067_; uint64_t v___x_1068_; uint64_t v___x_1069_; size_t v___x_1070_; size_t v___x_1071_; size_t v___x_1072_; size_t v___x_1073_; size_t v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v_buckets_1061_ = lean_ctor_get(v_m_1059_, 1);
v___x_1062_ = lean_array_get_size(v_buckets_1061_);
v___x_1063_ = l_Lean_Expr_hash(v_a_1060_);
v___x_1064_ = 32ULL;
v___x_1065_ = lean_uint64_shift_right(v___x_1063_, v___x_1064_);
v_fold_1066_ = lean_uint64_xor(v___x_1063_, v___x_1065_);
v___x_1067_ = 16ULL;
v___x_1068_ = lean_uint64_shift_right(v_fold_1066_, v___x_1067_);
v___x_1069_ = lean_uint64_xor(v_fold_1066_, v___x_1068_);
v___x_1070_ = lean_uint64_to_usize(v___x_1069_);
v___x_1071_ = lean_usize_of_nat(v___x_1062_);
v___x_1072_ = ((size_t)1ULL);
v___x_1073_ = lean_usize_sub(v___x_1071_, v___x_1072_);
v___x_1074_ = lean_usize_land(v___x_1070_, v___x_1073_);
v___x_1075_ = lean_array_uget_borrowed(v_buckets_1061_, v___x_1074_);
v___x_1076_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1060_, v___x_1075_);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1077_, v_a_1078_);
lean_dec_ref(v_a_1078_);
lean_dec_ref(v_m_1077_);
return v_res_1079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1080_, lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
v___x_1088_ = lean_apply_1(v_x_1081_, lean_box(0));
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1090_, lean_object* v_x_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v_res_1098_; 
v_res_1098_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1090_, v_x_1091_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec(v___y_1092_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1099_, lean_object* v_x_1100_){
_start:
{
if (lean_obj_tag(v_x_1100_) == 0)
{
return v_x_1099_;
}
else
{
lean_object* v_key_1101_; lean_object* v_value_1102_; lean_object* v_tail_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1126_; 
v_key_1101_ = lean_ctor_get(v_x_1100_, 0);
v_value_1102_ = lean_ctor_get(v_x_1100_, 1);
v_tail_1103_ = lean_ctor_get(v_x_1100_, 2);
v_isSharedCheck_1126_ = !lean_is_exclusive(v_x_1100_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1105_ = v_x_1100_;
v_isShared_1106_ = v_isSharedCheck_1126_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_tail_1103_);
lean_inc(v_value_1102_);
lean_inc(v_key_1101_);
lean_dec(v_x_1100_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1126_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1107_; uint64_t v___x_1108_; uint64_t v___x_1109_; uint64_t v___x_1110_; uint64_t v_fold_1111_; uint64_t v___x_1112_; uint64_t v___x_1113_; uint64_t v___x_1114_; size_t v___x_1115_; size_t v___x_1116_; size_t v___x_1117_; size_t v___x_1118_; size_t v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1122_; 
v___x_1107_ = lean_array_get_size(v_x_1099_);
v___x_1108_ = l_Lean_Expr_hash(v_key_1101_);
v___x_1109_ = 32ULL;
v___x_1110_ = lean_uint64_shift_right(v___x_1108_, v___x_1109_);
v_fold_1111_ = lean_uint64_xor(v___x_1108_, v___x_1110_);
v___x_1112_ = 16ULL;
v___x_1113_ = lean_uint64_shift_right(v_fold_1111_, v___x_1112_);
v___x_1114_ = lean_uint64_xor(v_fold_1111_, v___x_1113_);
v___x_1115_ = lean_uint64_to_usize(v___x_1114_);
v___x_1116_ = lean_usize_of_nat(v___x_1107_);
v___x_1117_ = ((size_t)1ULL);
v___x_1118_ = lean_usize_sub(v___x_1116_, v___x_1117_);
v___x_1119_ = lean_usize_land(v___x_1115_, v___x_1118_);
v___x_1120_ = lean_array_uget_borrowed(v_x_1099_, v___x_1119_);
lean_inc(v___x_1120_);
if (v_isShared_1106_ == 0)
{
lean_ctor_set(v___x_1105_, 2, v___x_1120_);
v___x_1122_ = v___x_1105_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_key_1101_);
lean_ctor_set(v_reuseFailAlloc_1125_, 1, v_value_1102_);
lean_ctor_set(v_reuseFailAlloc_1125_, 2, v___x_1120_);
v___x_1122_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
lean_object* v___x_1123_; 
v___x_1123_ = lean_array_uset(v_x_1099_, v___x_1119_, v___x_1122_);
v_x_1099_ = v___x_1123_;
v_x_1100_ = v_tail_1103_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1127_, lean_object* v_source_1128_, lean_object* v_target_1129_){
_start:
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = lean_array_get_size(v_source_1128_);
v___x_1131_ = lean_nat_dec_lt(v_i_1127_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec_ref(v_source_1128_);
lean_dec(v_i_1127_);
return v_target_1129_;
}
else
{
lean_object* v_es_1132_; lean_object* v___x_1133_; lean_object* v_source_1134_; lean_object* v_target_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_es_1132_ = lean_array_fget(v_source_1128_, v_i_1127_);
v___x_1133_ = lean_box(0);
v_source_1134_ = lean_array_fset(v_source_1128_, v_i_1127_, v___x_1133_);
v_target_1135_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1129_, v_es_1132_);
v___x_1136_ = lean_unsigned_to_nat(1u);
v___x_1137_ = lean_nat_add(v_i_1127_, v___x_1136_);
lean_dec(v_i_1127_);
v_i_1127_ = v___x_1137_;
v_source_1128_ = v_source_1134_;
v_target_1129_ = v_target_1135_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1139_){
_start:
{
lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v_nbuckets_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1140_ = lean_array_get_size(v_data_1139_);
v___x_1141_ = lean_unsigned_to_nat(2u);
v_nbuckets_1142_ = lean_nat_mul(v___x_1140_, v___x_1141_);
v___x_1143_ = lean_unsigned_to_nat(0u);
v___x_1144_ = lean_box(0);
v___x_1145_ = lean_mk_array(v_nbuckets_1142_, v___x_1144_);
v___x_1146_ = lean_array_propagate_mark(v_data_1139_, v___x_1145_);
v___x_1147_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1143_, v_data_1139_, v___x_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1148_, lean_object* v_b_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
lean_dec(v_b_1149_);
lean_dec_ref(v_a_1148_);
return v_x_1150_;
}
else
{
lean_object* v_key_1151_; lean_object* v_value_1152_; lean_object* v_tail_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1165_; 
v_key_1151_ = lean_ctor_get(v_x_1150_, 0);
v_value_1152_ = lean_ctor_get(v_x_1150_, 1);
v_tail_1153_ = lean_ctor_get(v_x_1150_, 2);
v_isSharedCheck_1165_ = !lean_is_exclusive(v_x_1150_);
if (v_isSharedCheck_1165_ == 0)
{
v___x_1155_ = v_x_1150_;
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_tail_1153_);
lean_inc(v_value_1152_);
lean_inc(v_key_1151_);
lean_dec(v_x_1150_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1165_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = lean_expr_eqv(v_key_1151_, v_a_1148_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1158_; lean_object* v___x_1160_; 
v___x_1158_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1148_, v_b_1149_, v_tail_1153_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 2, v___x_1158_);
v___x_1160_ = v___x_1155_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_key_1151_);
lean_ctor_set(v_reuseFailAlloc_1161_, 1, v_value_1152_);
lean_ctor_set(v_reuseFailAlloc_1161_, 2, v___x_1158_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
else
{
lean_object* v___x_1163_; 
lean_dec(v_value_1152_);
lean_dec(v_key_1151_);
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 1, v_b_1149_);
lean_ctor_set(v___x_1155_, 0, v_a_1148_);
v___x_1163_ = v___x_1155_;
goto v_reusejp_1162_;
}
else
{
lean_object* v_reuseFailAlloc_1164_; 
v_reuseFailAlloc_1164_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1148_);
lean_ctor_set(v_reuseFailAlloc_1164_, 1, v_b_1149_);
lean_ctor_set(v_reuseFailAlloc_1164_, 2, v_tail_1153_);
v___x_1163_ = v_reuseFailAlloc_1164_;
goto v_reusejp_1162_;
}
v_reusejp_1162_:
{
return v___x_1163_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1166_, lean_object* v_x_1167_){
_start:
{
if (lean_obj_tag(v_x_1167_) == 0)
{
uint8_t v___x_1168_; 
v___x_1168_ = 0;
return v___x_1168_;
}
else
{
lean_object* v_key_1169_; lean_object* v_tail_1170_; uint8_t v___x_1171_; 
v_key_1169_ = lean_ctor_get(v_x_1167_, 0);
v_tail_1170_ = lean_ctor_get(v_x_1167_, 2);
v___x_1171_ = lean_expr_eqv(v_key_1169_, v_a_1166_);
if (v___x_1171_ == 0)
{
v_x_1167_ = v_tail_1170_;
goto _start;
}
else
{
return v___x_1171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1173_, lean_object* v_x_1174_){
_start:
{
uint8_t v_res_1175_; lean_object* v_r_1176_; 
v_res_1175_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1173_, v_x_1174_);
lean_dec(v_x_1174_);
lean_dec_ref(v_a_1173_);
v_r_1176_ = lean_box(v_res_1175_);
return v_r_1176_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1177_, lean_object* v_a_1178_, lean_object* v_b_1179_){
_start:
{
lean_object* v_size_1180_; lean_object* v_buckets_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1224_; 
v_size_1180_ = lean_ctor_get(v_m_1177_, 0);
v_buckets_1181_ = lean_ctor_get(v_m_1177_, 1);
v_isSharedCheck_1224_ = !lean_is_exclusive(v_m_1177_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1183_ = v_m_1177_;
v_isShared_1184_ = v_isSharedCheck_1224_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_buckets_1181_);
lean_inc(v_size_1180_);
lean_dec(v_m_1177_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1224_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; uint64_t v___x_1186_; uint64_t v___x_1187_; uint64_t v___x_1188_; uint64_t v_fold_1189_; uint64_t v___x_1190_; uint64_t v___x_1191_; uint64_t v___x_1192_; size_t v___x_1193_; size_t v___x_1194_; size_t v___x_1195_; size_t v___x_1196_; size_t v___x_1197_; lean_object* v_bkt_1198_; uint8_t v___x_1199_; 
v___x_1185_ = lean_array_get_size(v_buckets_1181_);
v___x_1186_ = l_Lean_Expr_hash(v_a_1178_);
v___x_1187_ = 32ULL;
v___x_1188_ = lean_uint64_shift_right(v___x_1186_, v___x_1187_);
v_fold_1189_ = lean_uint64_xor(v___x_1186_, v___x_1188_);
v___x_1190_ = 16ULL;
v___x_1191_ = lean_uint64_shift_right(v_fold_1189_, v___x_1190_);
v___x_1192_ = lean_uint64_xor(v_fold_1189_, v___x_1191_);
v___x_1193_ = lean_uint64_to_usize(v___x_1192_);
v___x_1194_ = lean_usize_of_nat(v___x_1185_);
v___x_1195_ = ((size_t)1ULL);
v___x_1196_ = lean_usize_sub(v___x_1194_, v___x_1195_);
v___x_1197_ = lean_usize_land(v___x_1193_, v___x_1196_);
v_bkt_1198_ = lean_array_uget_borrowed(v_buckets_1181_, v___x_1197_);
v___x_1199_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1178_, v_bkt_1198_);
if (v___x_1199_ == 0)
{
lean_object* v___x_1200_; lean_object* v_size_x27_1201_; lean_object* v___x_1202_; lean_object* v_buckets_x27_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1200_ = lean_unsigned_to_nat(1u);
v_size_x27_1201_ = lean_nat_add(v_size_1180_, v___x_1200_);
lean_dec(v_size_1180_);
lean_inc(v_bkt_1198_);
v___x_1202_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1202_, 0, v_a_1178_);
lean_ctor_set(v___x_1202_, 1, v_b_1179_);
lean_ctor_set(v___x_1202_, 2, v_bkt_1198_);
v_buckets_x27_1203_ = lean_array_uset(v_buckets_1181_, v___x_1197_, v___x_1202_);
v___x_1204_ = lean_unsigned_to_nat(4u);
v___x_1205_ = lean_nat_mul(v_size_x27_1201_, v___x_1204_);
v___x_1206_ = lean_unsigned_to_nat(3u);
v___x_1207_ = lean_nat_div(v___x_1205_, v___x_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_array_get_size(v_buckets_x27_1203_);
v___x_1209_ = lean_nat_dec_le(v___x_1207_, v___x_1208_);
lean_dec(v___x_1207_);
if (v___x_1209_ == 0)
{
lean_object* v_val_1210_; lean_object* v___x_1212_; 
v_val_1210_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1203_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_val_1210_);
lean_ctor_set(v___x_1183_, 0, v_size_x27_1201_);
v___x_1212_ = v___x_1183_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_size_x27_1201_);
lean_ctor_set(v_reuseFailAlloc_1213_, 1, v_val_1210_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
else
{
lean_object* v___x_1215_; 
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v_buckets_x27_1203_);
lean_ctor_set(v___x_1183_, 0, v_size_x27_1201_);
v___x_1215_ = v___x_1183_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_size_x27_1201_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v_buckets_x27_1203_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
else
{
lean_object* v___x_1217_; lean_object* v_buckets_x27_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1222_; 
lean_inc(v_bkt_1198_);
v___x_1217_ = lean_box(0);
v_buckets_x27_1218_ = lean_array_uset(v_buckets_1181_, v___x_1197_, v___x_1217_);
v___x_1219_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1178_, v_b_1179_, v_bkt_1198_);
v___x_1220_ = lean_array_uset(v_buckets_x27_1218_, v___x_1197_, v___x_1219_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 1, v___x_1220_);
v___x_1222_ = v___x_1183_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_size_1180_);
lean_ctor_set(v_reuseFailAlloc_1223_, 1, v___x_1220_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1225_, lean_object* v_e_1226_, lean_object* v_a_1227_){
_start:
{
lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; 
v___x_1229_ = lean_st_ref_take(v_a_1225_);
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1229_, v_e_1226_, v_a_1227_);
v___x_1232_ = lean_st_ref_put(v_a_1225_, v___x_1231_);
return v___x_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1233_, lean_object* v_e_1234_, lean_object* v_a_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v_res_1237_; 
v_res_1237_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1233_, v_e_1234_, v_a_1235_);
lean_dec(v_a_1233_);
return v_res_1237_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1238_, lean_object* v_e_1239_, lean_object* v_a_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v_res_1247_; 
v_res_1247_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1238_, v_e_1239_, v_a_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec(v___y_1243_);
lean_dec_ref(v___y_1242_);
lean_dec(v___y_1241_);
lean_dec(v_a_1240_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1248_, lean_object* v_e_1249_, lean_object* v_a_1250_, lean_object* v___y_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_){
_start:
{
lean_object* v_a_1258_; lean_object* v___y_1270_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
lean_inc(v_a_1250_);
v___x_1272_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1272_, 0, lean_box(0));
lean_closure_set(v___x_1272_, 1, lean_box(0));
lean_closure_set(v___x_1272_, 2, v_a_1250_);
v___x_1273_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1272_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1273_) == 0)
{
lean_object* v_a_1274_; lean_object* v___x_1276_; uint8_t v_isShared_1277_; uint8_t v_isSharedCheck_1310_; 
v_a_1274_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1310_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1310_ == 0)
{
v___x_1276_ = v___x_1273_;
v_isShared_1277_ = v_isSharedCheck_1310_;
goto v_resetjp_1275_;
}
else
{
lean_inc(v_a_1274_);
lean_dec(v___x_1273_);
v___x_1276_ = lean_box(0);
v_isShared_1277_ = v_isSharedCheck_1310_;
goto v_resetjp_1275_;
}
v_resetjp_1275_:
{
lean_object* v___x_1278_; 
v___x_1278_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1274_, v_e_1249_);
lean_dec(v_a_1274_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v___x_1279_; 
lean_del_object(v___x_1276_);
lean_inc_ref(v_fn_1248_);
lean_inc(v___y_1255_);
lean_inc_ref(v___y_1254_);
lean_inc(v___y_1253_);
lean_inc_ref(v___y_1252_);
lean_inc(v___y_1251_);
lean_inc_ref(v_e_1249_);
v___x_1279_ = lean_apply_7(v_fn_1248_, v_e_1249_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_, lean_box(0));
if (lean_obj_tag(v___x_1279_) == 0)
{
lean_object* v_a_1280_; uint8_t v___x_1281_; 
v_a_1280_ = lean_ctor_get(v___x_1279_, 0);
lean_inc(v_a_1280_);
lean_dec_ref_known(v___x_1279_, 1);
v___x_1281_ = lean_unbox(v_a_1280_);
lean_dec(v_a_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; 
lean_dec_ref(v_fn_1248_);
v___x_1282_ = lean_box(0);
v_a_1258_ = v___x_1282_;
goto v___jp_1257_;
}
else
{
switch(lean_obj_tag(v_e_1249_))
{
case 7:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1283_, 0, v_fn_1248_);
lean_inc_ref(v_e_1249_);
v___x_1284_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1283_, v_e_1249_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1284_;
goto v___jp_1269_;
}
case 6:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1285_, 0, v_fn_1248_);
lean_inc_ref(v_e_1249_);
v___x_1286_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1285_, v_e_1249_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1286_;
goto v___jp_1269_;
}
case 8:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1287_, 0, v_fn_1248_);
lean_inc_ref(v_e_1249_);
v___x_1288_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1287_, v_e_1249_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1288_;
goto v___jp_1269_;
}
case 5:
{
lean_object* v_fn_1289_; lean_object* v_arg_1290_; lean_object* v___x_1291_; 
v_fn_1289_ = lean_ctor_get(v_e_1249_, 0);
v_arg_1290_ = lean_ctor_get(v_e_1249_, 1);
lean_inc_ref(v_fn_1289_);
lean_inc_ref(v_fn_1248_);
v___x_1291_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1248_, v_fn_1289_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v___x_1292_; 
lean_dec_ref_known(v___x_1291_, 1);
lean_inc_ref(v_arg_1290_);
v___x_1292_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1248_, v_arg_1290_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1292_;
goto v___jp_1269_;
}
else
{
lean_dec_ref(v_fn_1248_);
v___y_1270_ = v___x_1291_;
goto v___jp_1269_;
}
}
case 10:
{
lean_object* v_expr_1293_; lean_object* v___x_1294_; 
v_expr_1293_ = lean_ctor_get(v_e_1249_, 1);
lean_inc_ref(v_expr_1293_);
v___x_1294_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1248_, v_expr_1293_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1294_;
goto v___jp_1269_;
}
case 11:
{
lean_object* v_struct_1295_; lean_object* v___x_1296_; 
v_struct_1295_ = lean_ctor_get(v_e_1249_, 2);
lean_inc_ref(v_struct_1295_);
v___x_1296_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1248_, v_struct_1295_, v_a_1250_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
v___y_1270_ = v___x_1296_;
goto v___jp_1269_;
}
default: 
{
lean_object* v___x_1297_; 
lean_dec_ref(v_fn_1248_);
v___x_1297_ = lean_box(0);
v_a_1258_ = v___x_1297_;
goto v___jp_1257_;
}
}
}
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec_ref(v_e_1249_);
lean_dec_ref(v_fn_1248_);
v_a_1298_ = lean_ctor_get(v___x_1279_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1279_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1279_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1279_);
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
}
else
{
lean_object* v_val_1306_; lean_object* v___x_1308_; 
lean_dec_ref(v_e_1249_);
lean_dec_ref(v_fn_1248_);
v_val_1306_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_val_1306_);
lean_dec_ref_known(v___x_1278_, 1);
if (v_isShared_1277_ == 0)
{
lean_ctor_set(v___x_1276_, 0, v_val_1306_);
v___x_1308_ = v___x_1276_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_val_1306_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_dec_ref(v_e_1249_);
lean_dec_ref(v_fn_1248_);
v_a_1311_ = lean_ctor_get(v___x_1273_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1273_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1273_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1273_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
v___jp_1257_:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; 
lean_inc(v_a_1250_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1259_, 0, v_a_1250_);
lean_closure_set(v___f_1259_, 1, v_e_1249_);
lean_closure_set(v___f_1259_, 2, v_a_1258_);
v___x_1260_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1259_, v___y_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
if (lean_obj_tag(v___x_1260_) == 0)
{
lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1267_ == 0)
{
lean_object* v_unused_1268_; 
v_unused_1268_ = lean_ctor_get(v___x_1260_, 0);
lean_dec(v_unused_1268_);
v___x_1262_ = v___x_1260_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_dec(v___x_1260_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
lean_ctor_set(v___x_1262_, 0, v_a_1258_);
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1258_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
else
{
return v___x_1260_;
}
}
v___jp_1269_:
{
if (lean_obj_tag(v___y_1270_) == 0)
{
lean_object* v_a_1271_; 
v_a_1271_ = lean_ctor_get(v___y_1270_, 0);
lean_inc(v_a_1271_);
lean_dec_ref_known(v___y_1270_, 1);
v_a_1258_ = v_a_1271_;
goto v___jp_1257_;
}
else
{
lean_dec_ref(v_e_1249_);
return v___y_1270_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; 
v___x_1319_ = lean_box(0);
v___x_1320_ = lean_unsigned_to_nat(16u);
v___x_1321_ = lean_mk_array(v___x_1320_, v___x_1319_);
return v___x_1321_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
v___x_1322_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1323_ = lean_unsigned_to_nat(0u);
v___x_1324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
lean_ctor_set(v___x_1324_, 1, v___x_1322_);
return v___x_1324_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; 
v___x_1325_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1326_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1326_, 0, lean_box(0));
lean_closure_set(v___x_1326_, 1, lean_box(0));
lean_closure_set(v___x_1326_, 2, v___x_1325_);
return v___x_1326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1327_, lean_object* v_fn_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v_a_1337_; lean_object* v___x_1338_; 
v___x_1335_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1336_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1335_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
v_a_1337_ = lean_ctor_get(v___x_1336_, 0);
lean_inc(v_a_1337_);
lean_dec_ref(v___x_1336_);
v___x_1338_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1328_, v_input_1327_, v_a_1337_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v_a_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
v_a_1339_ = lean_ctor_get(v___x_1338_, 0);
lean_inc(v_a_1339_);
lean_dec_ref_known(v___x_1338_, 1);
v___x_1340_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1340_, 0, lean_box(0));
lean_closure_set(v___x_1340_, 1, lean_box(0));
lean_closure_set(v___x_1340_, 2, v_a_1337_);
v___x_1341_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1340_, v___y_1329_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v___x_1341_, 0);
lean_dec(v_unused_1349_);
v___x_1343_ = v___x_1341_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_dec(v___x_1341_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v_a_1339_);
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1339_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
else
{
lean_dec(v_a_1337_);
return v___x_1338_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1350_, lean_object* v_fn_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1350_, v_fn_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
lean_dec(v___y_1352_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1359_, lean_object* v_fn_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___f_1367_; lean_object* v___x_1368_; 
v___f_1367_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1367_, 0, v_fn_1360_);
v___x_1368_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1359_, v___f_1367_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1369_, lean_object* v_fn_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_){
_start:
{
lean_object* v_res_1377_; 
v_res_1377_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1369_, v_fn_1370_, v___y_1371_, v___y_1372_, v___y_1373_, v___y_1374_, v___y_1375_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1378_, lean_object* v_x_1379_, lean_object* v_x_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
if (lean_obj_tag(v_x_1380_) == 0)
{
lean_object* v___x_1387_; 
lean_dec_ref(v_fn_1378_);
v___x_1387_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1387_, 0, v_x_1379_);
return v___x_1387_;
}
else
{
lean_object* v_head_1388_; lean_object* v_tail_1389_; lean_object* v_type_1390_; lean_object* v___x_1391_; 
v_head_1388_ = lean_ctor_get(v_x_1380_, 0);
lean_inc(v_head_1388_);
v_tail_1389_ = lean_ctor_get(v_x_1380_, 1);
lean_inc(v_tail_1389_);
lean_dec_ref_known(v_x_1380_, 2);
v_type_1390_ = lean_ctor_get(v_head_1388_, 1);
lean_inc_ref(v_type_1390_);
lean_dec(v_head_1388_);
lean_inc_ref(v_fn_1378_);
v___x_1391_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1390_, v_fn_1378_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_, v___y_1385_);
if (lean_obj_tag(v___x_1391_) == 0)
{
lean_object* v_a_1392_; 
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_x_1379_ = v_a_1392_;
v_x_1380_ = v_tail_1389_;
goto _start;
}
else
{
lean_dec(v_tail_1389_);
lean_dec_ref(v_fn_1378_);
return v___x_1391_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1394_, lean_object* v_x_1395_, lean_object* v_x_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1394_, v_x_1395_, v_x_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1404_, lean_object* v_x_1405_, lean_object* v_x_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_){
_start:
{
if (lean_obj_tag(v_x_1406_) == 0)
{
lean_object* v___x_1413_; 
lean_dec_ref(v_fn_1404_);
v___x_1413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1413_, 0, v_x_1405_);
return v___x_1413_;
}
else
{
lean_object* v_head_1414_; lean_object* v_tail_1415_; lean_object* v___y_1417_; lean_object* v_type_1420_; lean_object* v_ctors_1421_; lean_object* v___x_1422_; 
v_head_1414_ = lean_ctor_get(v_x_1406_, 0);
lean_inc(v_head_1414_);
v_tail_1415_ = lean_ctor_get(v_x_1406_, 1);
lean_inc(v_tail_1415_);
lean_dec_ref_known(v_x_1406_, 2);
v_type_1420_ = lean_ctor_get(v_head_1414_, 1);
lean_inc_ref(v_type_1420_);
v_ctors_1421_ = lean_ctor_get(v_head_1414_, 2);
lean_inc(v_ctors_1421_);
lean_dec(v_head_1414_);
lean_inc_ref(v_fn_1404_);
v___x_1422_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1420_, v_fn_1404_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v___x_1424_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
lean_inc_ref(v_fn_1404_);
v___x_1424_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1404_, v_a_1423_, v_ctors_1421_, v___y_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_);
v___y_1417_ = v___x_1424_;
goto v___jp_1416_;
}
else
{
lean_dec(v_ctors_1421_);
v___y_1417_ = v___x_1422_;
goto v___jp_1416_;
}
v___jp_1416_:
{
if (lean_obj_tag(v___y_1417_) == 0)
{
lean_object* v_a_1418_; 
v_a_1418_ = lean_ctor_get(v___y_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___y_1417_, 1);
v_x_1405_ = v_a_1418_;
v_x_1406_ = v_tail_1415_;
goto _start;
}
else
{
lean_dec(v_tail_1415_);
lean_dec_ref(v_fn_1404_);
return v___y_1417_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1425_, lean_object* v_x_1426_, lean_object* v_x_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_){
_start:
{
lean_object* v_res_1434_; 
v_res_1434_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1425_, v_x_1426_, v_x_1427_, v___y_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_);
lean_dec(v___y_1432_);
lean_dec_ref(v___y_1431_);
lean_dec(v___y_1430_);
lean_dec_ref(v___y_1429_);
lean_dec(v___y_1428_);
return v_res_1434_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1435_, lean_object* v_x_1436_, lean_object* v_x_1437_, lean_object* v___y_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_){
_start:
{
if (lean_obj_tag(v_x_1437_) == 0)
{
lean_object* v___x_1444_; 
lean_dec_ref(v_fn_1435_);
v___x_1444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1444_, 0, v_x_1436_);
return v___x_1444_;
}
else
{
lean_object* v_head_1445_; lean_object* v_tail_1446_; lean_object* v___y_1448_; lean_object* v_toConstantVal_1451_; lean_object* v_value_1452_; lean_object* v_type_1453_; lean_object* v___x_1454_; 
v_head_1445_ = lean_ctor_get(v_x_1437_, 0);
lean_inc(v_head_1445_);
v_tail_1446_ = lean_ctor_get(v_x_1437_, 1);
lean_inc(v_tail_1446_);
lean_dec_ref_known(v_x_1437_, 2);
v_toConstantVal_1451_ = lean_ctor_get(v_head_1445_, 0);
lean_inc_ref(v_toConstantVal_1451_);
v_value_1452_ = lean_ctor_get(v_head_1445_, 1);
lean_inc_ref(v_value_1452_);
lean_dec(v_head_1445_);
v_type_1453_ = lean_ctor_get(v_toConstantVal_1451_, 2);
lean_inc_ref(v_type_1453_);
lean_dec_ref(v_toConstantVal_1451_);
lean_inc_ref(v_fn_1435_);
v___x_1454_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1453_, v_fn_1435_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
if (lean_obj_tag(v___x_1454_) == 0)
{
lean_object* v___x_1455_; 
lean_dec_ref_known(v___x_1454_, 1);
lean_inc_ref(v_fn_1435_);
v___x_1455_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1452_, v_fn_1435_, v___y_1438_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_);
v___y_1448_ = v___x_1455_;
goto v___jp_1447_;
}
else
{
lean_dec_ref(v_value_1452_);
v___y_1448_ = v___x_1454_;
goto v___jp_1447_;
}
v___jp_1447_:
{
if (lean_obj_tag(v___y_1448_) == 0)
{
lean_object* v_a_1449_; 
v_a_1449_ = lean_ctor_get(v___y_1448_, 0);
lean_inc(v_a_1449_);
lean_dec_ref_known(v___y_1448_, 1);
v_x_1436_ = v_a_1449_;
v_x_1437_ = v_tail_1446_;
goto _start;
}
else
{
lean_dec(v_tail_1446_);
lean_dec_ref(v_fn_1435_);
return v___y_1448_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1456_, lean_object* v_x_1457_, lean_object* v_x_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_){
_start:
{
lean_object* v_res_1465_; 
v_res_1465_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1456_, v_x_1457_, v_x_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_, v___y_1463_);
lean_dec(v___y_1463_);
lean_dec_ref(v___y_1462_);
lean_dec(v___y_1461_);
lean_dec_ref(v___y_1460_);
lean_dec(v___y_1459_);
return v_res_1465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1466_, lean_object* v_d_1467_, lean_object* v_a_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_){
_start:
{
switch(lean_obj_tag(v_d_1467_))
{
case 0:
{
lean_object* v_val_1475_; lean_object* v_toConstantVal_1476_; lean_object* v_type_1477_; lean_object* v___x_1478_; 
v_val_1475_ = lean_ctor_get(v_d_1467_, 0);
lean_inc_ref(v_val_1475_);
lean_dec_ref_known(v_d_1467_, 1);
v_toConstantVal_1476_ = lean_ctor_get(v_val_1475_, 0);
lean_inc_ref(v_toConstantVal_1476_);
lean_dec_ref(v_val_1475_);
v_type_1477_ = lean_ctor_get(v_toConstantVal_1476_, 2);
lean_inc_ref(v_type_1477_);
lean_dec_ref(v_toConstantVal_1476_);
v___x_1478_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1477_, v_fn_1466_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1478_;
}
case 4:
{
lean_object* v___x_1479_; 
lean_dec_ref(v_fn_1466_);
v___x_1479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1479_, 0, v_a_1468_);
return v___x_1479_;
}
case 5:
{
lean_object* v_defns_1480_; lean_object* v___x_1481_; 
v_defns_1480_ = lean_ctor_get(v_d_1467_, 0);
lean_inc(v_defns_1480_);
lean_dec_ref_known(v_d_1467_, 1);
v___x_1481_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1466_, v_a_1468_, v_defns_1480_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1481_;
}
case 6:
{
lean_object* v_types_1482_; lean_object* v___x_1483_; 
v_types_1482_ = lean_ctor_get(v_d_1467_, 2);
lean_inc(v_types_1482_);
lean_dec_ref_known(v_d_1467_, 3);
v___x_1483_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1466_, v_a_1468_, v_types_1482_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1483_;
}
default: 
{
lean_object* v_val_1484_; lean_object* v_toConstantVal_1485_; lean_object* v_value_1486_; lean_object* v_type_1487_; lean_object* v___x_1488_; 
v_val_1484_ = lean_ctor_get(v_d_1467_, 0);
lean_inc_ref(v_val_1484_);
lean_dec(v_d_1467_);
v_toConstantVal_1485_ = lean_ctor_get(v_val_1484_, 0);
lean_inc_ref(v_toConstantVal_1485_);
v_value_1486_ = lean_ctor_get(v_val_1484_, 1);
lean_inc_ref(v_value_1486_);
lean_dec_ref(v_val_1484_);
v_type_1487_ = lean_ctor_get(v_toConstantVal_1485_, 2);
lean_inc_ref(v_type_1487_);
lean_dec_ref(v_toConstantVal_1485_);
lean_inc_ref(v_fn_1466_);
v___x_1488_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1487_, v_fn_1466_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v___x_1489_; 
lean_dec_ref_known(v___x_1488_, 1);
v___x_1489_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1486_, v_fn_1466_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_, v___y_1473_);
return v___x_1489_;
}
else
{
lean_dec_ref(v_value_1486_);
lean_dec_ref(v_fn_1466_);
return v___x_1488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1490_, lean_object* v_d_1491_, lean_object* v_a_1492_, lean_object* v___y_1493_, lean_object* v___y_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_){
_start:
{
lean_object* v_res_1499_; 
v_res_1499_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1490_, v_d_1491_, v_a_1492_, v___y_1493_, v___y_1494_, v___y_1495_, v___y_1496_, v___y_1497_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
lean_dec_ref(v___y_1494_);
lean_dec(v___y_1493_);
return v_res_1499_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1500_, lean_object* v_fn_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = lean_box(0);
v___x_1509_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1501_, v_decl_1500_, v___x_1508_, v___y_1502_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1510_, lean_object* v_fn_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1510_, v_fn_1511_, v___y_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec(v___y_1512_);
return v_res_1518_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
v___x_1524_ = lean_box(1);
v___x_1525_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1526_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1527_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
lean_ctor_set(v___x_1527_, 1, v___x_1525_);
lean_ctor_set(v___x_1527_, 2, v___x_1524_);
return v___x_1527_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1530_, 0, v___x_1529_);
lean_ctor_set(v___x_1530_, 1, v___x_1529_);
lean_ctor_set(v___x_1530_, 2, v___x_1529_);
lean_ctor_set(v___x_1530_, 3, v___x_1529_);
lean_ctor_set(v___x_1530_, 4, v___x_1528_);
lean_ctor_set(v___x_1530_, 5, v___x_1528_);
lean_ctor_set(v___x_1530_, 6, v___x_1528_);
lean_ctor_set(v___x_1530_, 7, v___x_1528_);
lean_ctor_set(v___x_1530_, 8, v___x_1528_);
lean_ctor_set(v___x_1530_, 9, v___x_1528_);
lean_ctor_set(v___x_1530_, 10, v___x_1528_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1532_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
lean_ctor_set(v___x_1532_, 1, v___x_1531_);
lean_ctor_set(v___x_1532_, 2, v___x_1531_);
lean_ctor_set(v___x_1532_, 3, v___x_1531_);
lean_ctor_set(v___x_1532_, 4, v___x_1531_);
lean_ctor_set(v___x_1532_, 5, v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1533_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1534_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1534_, 0, v___x_1533_);
lean_ctor_set(v___x_1534_, 1, v___x_1533_);
lean_ctor_set(v___x_1534_, 2, v___x_1533_);
lean_ctor_set(v___x_1534_, 3, v___x_1533_);
lean_ctor_set(v___x_1534_, 4, v___x_1533_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1535_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1536_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1537_ = lean_box(1);
v___x_1538_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1539_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1540_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1540_, 0, v___x_1539_);
lean_ctor_set(v___x_1540_, 1, v___x_1538_);
lean_ctor_set(v___x_1540_, 2, v___x_1537_);
lean_ctor_set(v___x_1540_, 3, v___x_1536_);
lean_ctor_set(v___x_1540_, 4, v___x_1535_);
return v___x_1540_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1552_ = l_Lean_stringToMessageData(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; 
v___x_1553_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1554_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1555_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1555_, 0, v___x_1554_);
lean_ctor_set(v___x_1555_, 1, v___x_1553_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_){
_start:
{
lean_object* v_toCold_1563_; lean_object* v_options_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v_toCold_1563_ = lean_ctor_get(v_a_1560_, 0);
v_options_1564_ = lean_ctor_get(v_toCold_1563_, 2);
v___x_1565_ = l_Lean_warn_sorry;
v___x_1566_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1564_, v___x_1565_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; 
lean_dec(v_decl_1559_);
v___x_1567_ = lean_box(0);
v___x_1568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1568_, 0, v___x_1567_);
return v___x_1568_;
}
else
{
lean_object* v___f_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v_messages_1575_; uint8_t v___x_1576_; 
v___f_1569_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1570_ = lean_box(1);
v___x_1571_ = lean_st_ref_get(v_a_1561_);
v_messages_1575_ = lean_ctor_get(v___x_1571_, 6);
lean_inc_ref(v_messages_1575_);
lean_dec(v___x_1571_);
v___x_1576_ = l_Lean_MessageLog_hasErrors(v_messages_1575_);
lean_dec_ref(v_messages_1575_);
if (v___x_1576_ == 0)
{
if (v___x_1566_ == 0)
{
lean_dec(v_decl_1559_);
goto v___jp_1572_;
}
else
{
uint8_t v___x_1577_; 
v___x_1577_ = l_Lean_Declaration_hasSorry(v_decl_1559_);
if (v___x_1577_ == 0)
{
lean_dec(v_decl_1559_);
goto v___jp_1572_;
}
else
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; uint8_t v___x_1581_; uint8_t v___x_1582_; lean_object* v___x_1583_; uint64_t v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1578_ = lean_unsigned_to_nat(0u);
v___x_1579_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1580_ = 1;
v___x_1581_ = 0;
v___x_1582_ = 2;
v___x_1583_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1583_, 0, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 1, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 2, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 3, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 4, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 5, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 6, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 7, v___x_1576_);
lean_ctor_set_uint8(v___x_1583_, 8, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 9, v___x_1580_);
lean_ctor_set_uint8(v___x_1583_, 10, v___x_1581_);
lean_ctor_set_uint8(v___x_1583_, 11, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 12, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 13, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 14, v___x_1582_);
lean_ctor_set_uint8(v___x_1583_, 15, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 16, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 17, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 18, v___x_1577_);
lean_ctor_set_uint8(v___x_1583_, 19, v___x_1576_);
v___x_1584_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1583_);
v___x_1585_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1585_, 0, v___x_1583_);
lean_ctor_set_uint64(v___x_1585_, sizeof(void*)*1, v___x_1584_);
v___x_1586_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1587_ = lean_box(0);
v___x_1588_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1588_, 0, v___x_1585_);
lean_ctor_set(v___x_1588_, 1, v___x_1570_);
lean_ctor_set(v___x_1588_, 2, v___x_1586_);
lean_ctor_set(v___x_1588_, 3, v___x_1579_);
lean_ctor_set(v___x_1588_, 4, v___x_1587_);
lean_ctor_set(v___x_1588_, 5, v___x_1578_);
lean_ctor_set(v___x_1588_, 6, v___x_1587_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*7, v___x_1576_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*7 + 1, v___x_1576_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*7 + 2, v___x_1576_);
lean_ctor_set_uint8(v___x_1588_, sizeof(void*)*7 + 3, v___x_1566_);
v___x_1589_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1590_ = lean_st_mk_ref(v___x_1589_);
v___x_1591_ = lean_st_mk_ref(v___x_1579_);
v___x_1592_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1559_, v___f_1569_, v___x_1591_, v___x_1588_, v___x_1590_, v_a_1560_, v_a_1561_);
lean_dec_ref_known(v___x_1588_, 7);
if (lean_obj_tag(v___x_1592_) == 0)
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v_val_1596_; lean_object* v___x_1618_; size_t v_sz_1619_; size_t v___x_1620_; lean_object* v___x_1621_; lean_object* v_fst_1622_; 
lean_dec_ref_known(v___x_1592_, 1);
v___x_1593_ = lean_st_ref_get(v___x_1591_);
lean_dec(v___x_1591_);
v___x_1594_ = lean_st_ref_get(v___x_1590_);
lean_dec(v___x_1590_);
lean_dec(v___x_1594_);
v___x_1618_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1619_ = lean_array_size(v___x_1593_);
v___x_1620_ = ((size_t)0ULL);
v___x_1621_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1593_, v_sz_1619_, v___x_1620_, v___x_1618_);
v_fst_1622_ = lean_ctor_get(v___x_1621_, 0);
lean_inc(v_fst_1622_);
lean_dec_ref(v___x_1621_);
if (lean_obj_tag(v_fst_1622_) == 0)
{
goto v___jp_1612_;
}
else
{
lean_object* v_val_1623_; 
v_val_1623_ = lean_ctor_get(v_fst_1622_, 0);
lean_inc(v_val_1623_);
lean_dec_ref_known(v_fst_1622_, 1);
if (lean_obj_tag(v_val_1623_) == 0)
{
goto v___jp_1612_;
}
else
{
lean_object* v_val_1624_; 
lean_dec(v___x_1593_);
v_val_1624_ = lean_ctor_get(v_val_1623_, 0);
lean_inc(v_val_1624_);
lean_dec_ref_known(v_val_1623_, 1);
v_val_1596_ = v_val_1624_;
goto v___jp_1595_;
}
}
v___jp_1595_:
{
lean_object* v_snd_1597_; lean_object* v___x_1599_; uint8_t v_isShared_1600_; uint8_t v_isSharedCheck_1610_; 
v_snd_1597_ = lean_ctor_get(v_val_1596_, 1);
v_isSharedCheck_1610_ = !lean_is_exclusive(v_val_1596_);
if (v_isSharedCheck_1610_ == 0)
{
lean_object* v_unused_1611_; 
v_unused_1611_ = lean_ctor_get(v_val_1596_, 0);
lean_dec(v_unused_1611_);
v___x_1599_ = v_val_1596_;
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
else
{
lean_inc(v_snd_1597_);
lean_dec(v_val_1596_);
v___x_1599_ = lean_box(0);
v_isShared_1600_ = v_isSharedCheck_1610_;
goto v_resetjp_1598_;
}
v_resetjp_1598_:
{
lean_object* v___x_1601_; lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1601_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1602_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1600_ == 0)
{
lean_ctor_set_tag(v___x_1599_, 7);
lean_ctor_set(v___x_1599_, 0, v___x_1602_);
v___x_1604_ = v___x_1599_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_snd_1597_);
v___x_1604_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1605_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1606_, 0, v___x_1604_);
lean_ctor_set(v___x_1606_, 1, v___x_1605_);
v___x_1607_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1607_, 0, v___x_1601_);
lean_ctor_set(v___x_1607_, 1, v___x_1606_);
v___x_1608_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1607_, v_a_1560_, v_a_1561_);
return v___x_1608_;
}
}
}
v___jp_1612_:
{
lean_object* v___x_1613_; uint8_t v___x_1614_; 
v___x_1613_ = lean_array_get_size(v___x_1593_);
v___x_1614_ = lean_nat_dec_lt(v___x_1578_, v___x_1613_);
if (v___x_1614_ == 0)
{
lean_object* v___x_1615_; lean_object* v___x_1616_; 
lean_dec(v___x_1593_);
v___x_1615_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1616_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1615_, v_a_1560_, v_a_1561_);
return v___x_1616_;
}
else
{
lean_object* v___x_1617_; 
v___x_1617_ = lean_array_fget(v___x_1593_, v___x_1578_);
lean_dec(v___x_1593_);
v_val_1596_ = v___x_1617_;
goto v___jp_1595_;
}
}
}
else
{
lean_dec(v___x_1591_);
lean_dec(v___x_1590_);
return v___x_1592_;
}
}
}
}
else
{
lean_dec(v_decl_1559_);
goto v___jp_1572_;
}
v___jp_1572_:
{
lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1573_ = lean_box(0);
v___x_1574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1574_, 0, v___x_1573_);
return v___x_1574_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_warnIfUsesSorry(v_decl_1625_, v_a_1626_, v_a_1627_);
lean_dec(v_a_1627_);
lean_dec_ref(v_a_1626_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1630_, lean_object* v_m_1631_, lean_object* v_a_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1631_, v_a_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_m_1635_, lean_object* v_a_1636_){
_start:
{
lean_object* v_res_1637_; 
v_res_1637_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1634_, v_m_1635_, v_a_1636_);
lean_dec_ref(v_a_1636_);
lean_dec_ref(v_m_1635_);
return v_res_1637_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1638_, lean_object* v_m_1639_, lean_object* v_a_1640_, lean_object* v_b_1641_){
_start:
{
lean_object* v___x_1642_; 
v___x_1642_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1639_, v_a_1640_, v_b_1641_);
return v___x_1642_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1643_, lean_object* v_a_1644_, lean_object* v_x_1645_){
_start:
{
lean_object* v___x_1646_; 
v___x_1646_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1644_, v_x_1645_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1647_, lean_object* v_a_1648_, lean_object* v_x_1649_){
_start:
{
lean_object* v_res_1650_; 
v_res_1650_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1647_, v_a_1648_, v_x_1649_);
lean_dec(v_x_1649_);
lean_dec_ref(v_a_1648_);
return v_res_1650_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1651_, lean_object* v_a_1652_, lean_object* v_x_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1652_, v_x_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1655_, lean_object* v_a_1656_, lean_object* v_x_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1655_, v_a_1656_, v_x_1657_);
lean_dec(v_x_1657_);
lean_dec_ref(v_a_1656_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1660_, lean_object* v_data_1661_){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1661_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1663_, lean_object* v_a_1664_, lean_object* v_b_1665_, lean_object* v_x_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1664_, v_b_1665_, v_x_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1668_, lean_object* v_name_1669_, uint8_t v_bi_1670_, lean_object* v_type_1671_, lean_object* v_k_1672_, uint8_t v_kind_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_){
_start:
{
lean_object* v___x_1681_; 
v___x_1681_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1669_, v_bi_1670_, v_type_1671_, v_k_1672_, v_kind_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1682_, lean_object* v_name_1683_, lean_object* v_bi_1684_, lean_object* v_type_1685_, lean_object* v_k_1686_, lean_object* v_kind_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_){
_start:
{
uint8_t v_bi_boxed_1695_; uint8_t v_kind_boxed_1696_; lean_object* v_res_1697_; 
v_bi_boxed_1695_ = lean_unbox(v_bi_1684_);
v_kind_boxed_1696_ = lean_unbox(v_kind_1687_);
v_res_1697_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1682_, v_name_1683_, v_bi_boxed_1695_, v_type_1685_, v_k_1686_, v_kind_boxed_1696_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec_ref(v___y_1690_);
lean_dec(v___y_1689_);
lean_dec(v___y_1688_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1698_, lean_object* v_name_1699_, lean_object* v_type_1700_, lean_object* v_val_1701_, lean_object* v_k_1702_, uint8_t v_nondep_1703_, uint8_t v_kind_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_, lean_object* v___y_1709_, lean_object* v___y_1710_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1699_, v_type_1700_, v_val_1701_, v_k_1702_, v_nondep_1703_, v_kind_1704_, v___y_1705_, v___y_1706_, v___y_1707_, v___y_1708_, v___y_1709_, v___y_1710_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1713_, lean_object* v_name_1714_, lean_object* v_type_1715_, lean_object* v_val_1716_, lean_object* v_k_1717_, lean_object* v_nondep_1718_, lean_object* v_kind_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_, lean_object* v___y_1726_){
_start:
{
uint8_t v_nondep_boxed_1727_; uint8_t v_kind_boxed_1728_; lean_object* v_res_1729_; 
v_nondep_boxed_1727_ = lean_unbox(v_nondep_1718_);
v_kind_boxed_1728_ = lean_unbox(v_kind_1719_);
v_res_1729_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1713_, v_name_1714_, v_type_1715_, v_val_1716_, v_k_1717_, v_nondep_boxed_1727_, v_kind_boxed_1728_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_);
lean_dec(v___y_1725_);
lean_dec_ref(v___y_1724_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec(v___y_1720_);
return v_res_1729_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1730_, lean_object* v_i_1731_, lean_object* v_source_1732_, lean_object* v_target_1733_){
_start:
{
lean_object* v___x_1734_; 
v___x_1734_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1731_, v_source_1732_, v_target_1733_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1735_, lean_object* v_x_1736_, lean_object* v_x_1737_){
_start:
{
lean_object* v___x_1738_; 
v___x_1738_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1736_, v_x_1737_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1788_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1789_ = 0;
v___x_1790_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1791_ = l_Lean_registerTraceClass(v___x_1788_, v___x_1789_, v___x_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1794_, lean_object* v___y_1795_){
_start:
{
lean_object* v___x_1797_; lean_object* v_nextMacroScope_1798_; lean_object* v_ngen_1799_; lean_object* v_auxDeclNGen_1800_; lean_object* v_traceState_1801_; lean_object* v_messages_1802_; lean_object* v_infoState_1803_; lean_object* v_snapshotTasks_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1815_; 
v___x_1797_ = lean_st_ref_take(v___y_1795_);
v_nextMacroScope_1798_ = lean_ctor_get(v___x_1797_, 1);
v_ngen_1799_ = lean_ctor_get(v___x_1797_, 2);
v_auxDeclNGen_1800_ = lean_ctor_get(v___x_1797_, 3);
v_traceState_1801_ = lean_ctor_get(v___x_1797_, 4);
v_messages_1802_ = lean_ctor_get(v___x_1797_, 6);
v_infoState_1803_ = lean_ctor_get(v___x_1797_, 7);
v_snapshotTasks_1804_ = lean_ctor_get(v___x_1797_, 8);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1797_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; lean_object* v_unused_1817_; 
v_unused_1816_ = lean_ctor_get(v___x_1797_, 5);
lean_dec(v_unused_1816_);
v_unused_1817_ = lean_ctor_get(v___x_1797_, 0);
lean_dec(v_unused_1817_);
v___x_1806_ = v___x_1797_;
v_isShared_1807_ = v_isSharedCheck_1815_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_snapshotTasks_1804_);
lean_inc(v_infoState_1803_);
lean_inc(v_messages_1802_);
lean_inc(v_traceState_1801_);
lean_inc(v_auxDeclNGen_1800_);
lean_inc(v_ngen_1799_);
lean_inc(v_nextMacroScope_1798_);
lean_dec(v___x_1797_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1815_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1811_; 
v___x_1808_ = lean_box(0);
v___x_1809_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1807_ == 0)
{
lean_ctor_set(v___x_1806_, 5, v___x_1809_);
lean_ctor_set(v___x_1806_, 0, v_env_1794_);
v___x_1811_ = v___x_1806_;
goto v_reusejp_1810_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_env_1794_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_nextMacroScope_1798_);
lean_ctor_set(v_reuseFailAlloc_1814_, 2, v_ngen_1799_);
lean_ctor_set(v_reuseFailAlloc_1814_, 3, v_auxDeclNGen_1800_);
lean_ctor_set(v_reuseFailAlloc_1814_, 4, v_traceState_1801_);
lean_ctor_set(v_reuseFailAlloc_1814_, 5, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1814_, 6, v_messages_1802_);
lean_ctor_set(v_reuseFailAlloc_1814_, 7, v_infoState_1803_);
lean_ctor_set(v_reuseFailAlloc_1814_, 8, v_snapshotTasks_1804_);
v___x_1811_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1810_;
}
v_reusejp_1810_:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; 
v___x_1812_ = lean_st_ref_put(v___y_1795_, v___x_1811_);
v___x_1813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1813_, 0, v___x_1808_);
return v___x_1813_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1818_, v___y_1819_);
lean_dec(v___y_1819_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1822_, lean_object* v___y_1823_, lean_object* v___y_1824_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1822_, v___y_1824_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_){
_start:
{
lean_object* v_res_1831_; 
v_res_1831_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1827_, v___y_1828_, v___y_1829_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
return v_res_1831_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; 
v___x_1832_ = lean_box(0);
v___x_1833_ = l_Lean_interruptExceptionId;
v___x_1834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
lean_ctor_set(v___x_1834_, 1, v___x_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1837_, 0, v___x_1836_);
return v___x_1837_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1838_){
_start:
{
lean_object* v_res_1839_; 
v_res_1839_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1839_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_ref_1844_; lean_object* v___x_1845_; lean_object* v_a_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1854_; 
v_ref_1844_ = lean_ctor_get(v___y_1841_, 2);
v___x_1845_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1840_, v___y_1841_, v___y_1842_);
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1854_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1854_ == 0)
{
v___x_1848_ = v___x_1845_;
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_a_1846_);
lean_dec(v___x_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1854_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1852_; 
lean_inc(v_ref_1844_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v_ref_1844_);
lean_ctor_set(v___x_1850_, 1, v_a_1846_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set_tag(v___x_1848_, 1);
lean_ctor_set(v___x_1848_, 0, v___x_1850_);
v___x_1852_ = v___x_1848_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1853_; 
v_reuseFailAlloc_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1853_, 0, v___x_1850_);
v___x_1852_ = v_reuseFailAlloc_1853_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
return v___x_1852_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v_res_1859_; 
v_res_1859_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1855_, v___y_1856_, v___y_1857_);
lean_dec(v___y_1857_);
lean_dec_ref(v___y_1856_);
return v_res_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v___y_1865_; lean_object* v___y_1866_; 
if (lean_obj_tag(v_ex_1860_) == 16)
{
lean_object* v___x_1871_; lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
v___x_1871_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1871_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1871_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
else
{
v___y_1865_ = v___y_1861_;
v___y_1866_ = v___y_1862_;
goto v___jp_1864_;
}
v___jp_1864_:
{
lean_object* v_toCold_1867_; lean_object* v_options_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v_toCold_1867_ = lean_ctor_get(v___y_1865_, 0);
v_options_1868_ = lean_ctor_get(v_toCold_1867_, 2);
lean_inc_ref(v_options_1868_);
v___x_1869_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1860_, v_options_1868_);
v___x_1870_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1869_, v___y_1865_, v___y_1866_);
return v___x_1870_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1880_, lean_object* v___y_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_){
_start:
{
lean_object* v_res_1884_; 
v_res_1884_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1880_, v___y_1881_, v___y_1882_);
lean_dec(v___y_1882_);
lean_dec_ref(v___y_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1885_, lean_object* v___y_1886_, lean_object* v___y_1887_){
_start:
{
if (lean_obj_tag(v_x_1885_) == 0)
{
lean_object* v_a_1889_; lean_object* v___x_1890_; 
v_a_1889_ = lean_ctor_get(v_x_1885_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v_x_1885_, 1);
v___x_1890_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1889_, v___y_1886_, v___y_1887_);
return v___x_1890_;
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v_x_1885_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v_x_1885_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v_x_1885_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v_x_1885_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
lean_ctor_set_tag(v___x_1893_, 0);
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1899_, lean_object* v___y_1900_, lean_object* v___y_1901_, lean_object* v___y_1902_){
_start:
{
lean_object* v_res_1903_; 
v_res_1903_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1899_, v___y_1900_, v___y_1901_);
lean_dec(v___y_1901_);
lean_dec_ref(v___y_1900_);
return v_res_1903_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1910_ = lean_unsigned_to_nat(1u);
v___x_1911_ = l_Lean_Level_ofNat(v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_box(0);
v___x_1913_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1914_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1913_);
lean_ctor_set(v___x_1914_, 1, v___x_1912_);
return v___x_1914_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; 
v___x_1915_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1916_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1917_ = l_Lean_mkConst(v___x_1916_, v___x_1915_);
return v___x_1917_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1918_ = lean_unsigned_to_nat(0u);
v___x_1919_ = l_Lean_Level_ofNat(v___x_1918_);
return v___x_1919_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1920_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1921_ = l_Lean_mkSort(v___x_1920_);
return v___x_1921_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1927_ = lean_box(0);
v___x_1928_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1929_ = l_Lean_mkConst(v___x_1928_, v___x_1927_);
return v___x_1929_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; 
v___x_1930_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1931_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1932_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1933_ = l_Lean_mkAppB(v___x_1932_, v___x_1931_, v___x_1930_);
return v___x_1933_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1939_, lean_object* v_b_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
if (lean_obj_tag(v_as_x27_1939_) == 0)
{
lean_object* v___x_1944_; 
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v_b_1940_);
return v___x_1944_;
}
else
{
lean_object* v_head_1945_; lean_object* v_tail_1946_; lean_object* v___x_1947_; lean_object* v___y_1949_; uint8_t v___y_1950_; lean_object* v_a_1954_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; lean_object* v___x_1963_; lean_object* v_toCold_1964_; lean_object* v_env_1965_; lean_object* v_options_1966_; lean_object* v_cancelTk_x3f_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
lean_dec_ref(v_b_1940_);
v_head_1945_ = lean_ctor_get(v_as_x27_1939_, 0);
v_tail_1946_ = lean_ctor_get(v_as_x27_1939_, 1);
v___x_1947_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1957_ = lean_box(0);
v___x_1958_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1945_);
v___x_1959_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1959_, 0, v_head_1945_);
lean_ctor_set(v___x_1959_, 1, v___x_1957_);
lean_ctor_set(v___x_1959_, 2, v___x_1958_);
v___x_1960_ = 0;
v___x_1961_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1961_, 0, v___x_1959_);
lean_ctor_set_uint8(v___x_1961_, sizeof(void*)*1, v___x_1960_);
v___x_1962_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1962_, 0, v___x_1961_);
v___x_1963_ = lean_st_ref_get(v___y_1942_);
v_toCold_1964_ = lean_ctor_get(v___y_1941_, 0);
v_env_1965_ = lean_ctor_get(v___x_1963_, 0);
lean_inc_ref(v_env_1965_);
lean_dec(v___x_1963_);
v_options_1966_ = lean_ctor_get(v_toCold_1964_, 2);
v_cancelTk_x3f_1967_ = lean_ctor_get(v_toCold_1964_, 10);
v___x_1968_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1965_, v_options_1966_, v___x_1962_, v_cancelTk_x3f_1967_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1969_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1968_, v___y_1941_, v___y_1942_);
if (lean_obj_tag(v___x_1969_) == 0)
{
lean_object* v_a_1970_; lean_object* v___x_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1979_; 
v_a_1970_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1970_);
lean_dec_ref_known(v___x_1969_, 1);
v___x_1971_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1970_, v___y_1942_);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1971_);
if (v_isSharedCheck_1979_ == 0)
{
lean_object* v_unused_1980_; 
v_unused_1980_ = lean_ctor_get(v___x_1971_, 0);
lean_dec(v_unused_1980_);
v___x_1973_ = v___x_1971_;
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
else
{
lean_dec(v___x_1971_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1979_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1975_; lean_object* v___x_1977_; 
v___x_1975_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1974_ == 0)
{
lean_ctor_set(v___x_1973_, 0, v___x_1975_);
v___x_1977_ = v___x_1973_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v___x_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
else
{
lean_object* v_a_1981_; 
v_a_1981_ = lean_ctor_get(v___x_1969_, 0);
lean_inc(v_a_1981_);
lean_dec_ref_known(v___x_1969_, 1);
v_a_1954_ = v_a_1981_;
goto v___jp_1953_;
}
v___jp_1948_:
{
if (v___y_1950_ == 0)
{
lean_dec_ref(v___y_1949_);
v_as_x27_1939_ = v_tail_1946_;
v_b_1940_ = v___x_1947_;
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
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1982_, lean_object* v_b_1983_, lean_object* v___y_1984_, lean_object* v___y_1985_, lean_object* v___y_1986_){
_start:
{
lean_object* v_res_1987_; 
v_res_1987_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1982_, v_b_1983_, v___y_1984_, v___y_1985_);
lean_dec(v___y_1985_);
lean_dec_ref(v___y_1984_);
lean_dec(v_as_x27_1982_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___y_1993_; lean_object* v___y_1994_; lean_object* v___y_2021_; uint8_t v___y_2022_; lean_object* v_a_2025_; lean_object* v___y_2029_; uint8_t v___y_2030_; lean_object* v_a_2033_; 
switch(lean_obj_tag(v_decl_1988_))
{
case 1:
{
lean_object* v_val_2036_; lean_object* v_toConstantVal_2037_; uint8_t v___x_2038_; lean_object* v___x_2039_; lean_object* v_fallbackDecl_2040_; lean_object* v___x_2041_; lean_object* v_toCold_2042_; lean_object* v_env_2043_; lean_object* v_options_2044_; lean_object* v_cancelTk_x3f_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v_val_2036_ = lean_ctor_get(v_decl_1988_, 0);
v_toConstantVal_2037_ = lean_ctor_get(v_val_2036_, 0);
v___x_2038_ = 0;
lean_inc_ref(v_toConstantVal_2037_);
v___x_2039_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2039_, 0, v_toConstantVal_2037_);
lean_ctor_set_uint8(v___x_2039_, sizeof(void*)*1, v___x_2038_);
v_fallbackDecl_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2040_, 0, v___x_2039_);
v___x_2041_ = lean_st_ref_get(v_a_1990_);
v_toCold_2042_ = lean_ctor_get(v_a_1989_, 0);
v_env_2043_ = lean_ctor_get(v___x_2041_, 0);
lean_inc_ref(v_env_2043_);
lean_dec(v___x_2041_);
v_options_2044_ = lean_ctor_get(v_toCold_2042_, 2);
v_cancelTk_x3f_2045_ = lean_ctor_get(v_toCold_2042_, 10);
v___x_2046_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2043_, v_options_2044_, v_fallbackDecl_2040_, v_cancelTk_x3f_2045_);
lean_dec_ref_known(v_fallbackDecl_2040_, 1);
v___x_2047_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2046_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2057_; 
lean_dec_ref_known(v_decl_1988_, 1);
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2048_);
lean_dec_ref_known(v___x_2047_, 1);
v___x_2049_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2048_, v_a_1990_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; 
v_unused_2058_ = lean_ctor_get(v___x_2049_, 0);
lean_dec(v_unused_2058_);
v___x_2051_ = v___x_2049_;
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
else
{
lean_dec(v___x_2049_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2057_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2053_; lean_object* v___x_2055_; 
v___x_2053_ = lean_box(0);
if (v_isShared_2052_ == 0)
{
lean_ctor_set(v___x_2051_, 0, v___x_2053_);
v___x_2055_ = v___x_2051_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2053_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
else
{
lean_object* v_a_2059_; 
v_a_2059_ = lean_ctor_get(v___x_2047_, 0);
lean_inc(v_a_2059_);
lean_dec_ref_known(v___x_2047_, 1);
v_a_2025_ = v_a_2059_;
goto v___jp_2024_;
}
}
case 2:
{
lean_object* v_val_2060_; lean_object* v_toConstantVal_2061_; uint8_t v___x_2062_; lean_object* v___x_2063_; lean_object* v_fallbackDecl_2064_; lean_object* v___x_2065_; lean_object* v_toCold_2066_; lean_object* v_env_2067_; lean_object* v_options_2068_; lean_object* v_cancelTk_x3f_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; 
v_val_2060_ = lean_ctor_get(v_decl_1988_, 0);
v_toConstantVal_2061_ = lean_ctor_get(v_val_2060_, 0);
v___x_2062_ = 0;
lean_inc_ref(v_toConstantVal_2061_);
v___x_2063_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2063_, 0, v_toConstantVal_2061_);
lean_ctor_set_uint8(v___x_2063_, sizeof(void*)*1, v___x_2062_);
v_fallbackDecl_2064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2064_, 0, v___x_2063_);
v___x_2065_ = lean_st_ref_get(v_a_1990_);
v_toCold_2066_ = lean_ctor_get(v_a_1989_, 0);
v_env_2067_ = lean_ctor_get(v___x_2065_, 0);
lean_inc_ref(v_env_2067_);
lean_dec(v___x_2065_);
v_options_2068_ = lean_ctor_get(v_toCold_2066_, 2);
v_cancelTk_x3f_2069_ = lean_ctor_get(v_toCold_2066_, 10);
v___x_2070_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2067_, v_options_2068_, v_fallbackDecl_2064_, v_cancelTk_x3f_2069_);
lean_dec_ref_known(v_fallbackDecl_2064_, 1);
v___x_2071_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2070_, v_a_1989_, v_a_1990_);
if (lean_obj_tag(v___x_2071_) == 0)
{
lean_object* v_a_2072_; lean_object* v___x_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2081_; 
lean_dec_ref_known(v_decl_1988_, 1);
v_a_2072_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2072_);
lean_dec_ref_known(v___x_2071_, 1);
v___x_2073_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2072_, v_a_1990_);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2081_ == 0)
{
lean_object* v_unused_2082_; 
v_unused_2082_ = lean_ctor_get(v___x_2073_, 0);
lean_dec(v_unused_2082_);
v___x_2075_ = v___x_2073_;
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
else
{
lean_dec(v___x_2073_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2081_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2077_; lean_object* v___x_2079_; 
v___x_2077_ = lean_box(0);
if (v_isShared_2076_ == 0)
{
lean_ctor_set(v___x_2075_, 0, v___x_2077_);
v___x_2079_ = v___x_2075_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v___x_2077_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
else
{
lean_object* v_a_2083_; 
v_a_2083_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_a_2083_);
lean_dec_ref_known(v___x_2071_, 1);
v_a_2033_ = v_a_2083_;
goto v___jp_2032_;
}
}
default: 
{
v___y_1993_ = v_a_1989_;
v___y_1994_ = v_a_1990_;
goto v___jp_1992_;
}
}
v___jp_1992_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = l_Lean_Declaration_getNames(v_decl_1988_);
v___x_1996_ = lean_box(0);
v___x_1997_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1998_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1995_, v___x_1997_, v___y_1993_, v___y_1994_);
lean_dec(v___x_1995_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2011_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2011_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2011_ == 0)
{
v___x_2001_ = v___x_1998_;
v_isShared_2002_ = v_isSharedCheck_2011_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___x_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2011_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_fst_2003_; 
v_fst_2003_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_fst_2003_);
lean_dec(v_a_1999_);
if (lean_obj_tag(v_fst_2003_) == 0)
{
lean_object* v___x_2005_; 
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v___x_1996_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v___x_1996_);
v___x_2005_ = v_reuseFailAlloc_2006_;
goto v_reusejp_2004_;
}
v_reusejp_2004_:
{
return v___x_2005_;
}
}
else
{
lean_object* v_val_2007_; lean_object* v___x_2009_; 
v_val_2007_ = lean_ctor_get(v_fst_2003_, 0);
lean_inc(v_val_2007_);
lean_dec_ref_known(v_fst_2003_, 1);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_val_2007_);
v___x_2009_ = v___x_2001_;
goto v_reusejp_2008_;
}
else
{
lean_object* v_reuseFailAlloc_2010_; 
v_reuseFailAlloc_2010_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_val_2007_);
v___x_2009_ = v_reuseFailAlloc_2010_;
goto v_reusejp_2008_;
}
v_reusejp_2008_:
{
return v___x_2009_;
}
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
v_a_2012_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_1998_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_1998_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
v___jp_2020_:
{
if (v___y_2022_ == 0)
{
lean_dec_ref(v___y_2021_);
v___y_1993_ = v_a_1989_;
v___y_1994_ = v_a_1990_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2023_; 
lean_dec(v_decl_1988_);
v___x_2023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2023_, 0, v___y_2021_);
return v___x_2023_;
}
}
v___jp_2024_:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Exception_isInterrupt(v_a_2025_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2027_; 
lean_inc_ref(v_a_2025_);
v___x_2027_ = l_Lean_Exception_isRuntime(v_a_2025_);
v___y_2021_ = v_a_2025_;
v___y_2022_ = v___x_2027_;
goto v___jp_2020_;
}
else
{
v___y_2021_ = v_a_2025_;
v___y_2022_ = v___x_2026_;
goto v___jp_2020_;
}
}
v___jp_2028_:
{
if (v___y_2030_ == 0)
{
lean_dec_ref(v___y_2029_);
v___y_1993_ = v_a_1989_;
v___y_1994_ = v_a_1990_;
goto v___jp_1992_;
}
else
{
lean_object* v___x_2031_; 
lean_dec(v_decl_1988_);
v___x_2031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2031_, 0, v___y_2029_);
return v___x_2031_;
}
}
v___jp_2032_:
{
uint8_t v___x_2034_; 
v___x_2034_ = l_Lean_Exception_isInterrupt(v_a_2033_);
if (v___x_2034_ == 0)
{
uint8_t v___x_2035_; 
lean_inc_ref(v_a_2033_);
v___x_2035_ = l_Lean_Exception_isRuntime(v_a_2033_);
v___y_2029_ = v_a_2033_;
v___y_2030_ = v___x_2035_;
goto v___jp_2028_;
}
else
{
v___y_2029_ = v_a_2033_;
v___y_2030_ = v___x_2034_;
goto v___jp_2028_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_, lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2086_);
lean_dec_ref(v_a_2085_);
return v_res_2088_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2089_, lean_object* v_x_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2090_, v___y_2091_, v___y_2092_);
return v___x_2094_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2095_, lean_object* v_x_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2095_, v_x_2096_, v___y_2097_, v___y_2098_);
lean_dec(v___y_2098_);
lean_dec_ref(v___y_2097_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2101_, lean_object* v_as_x27_2102_, lean_object* v_b_2103_, lean_object* v_a_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2102_, v_b_2103_, v___y_2105_, v___y_2106_);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2109_, lean_object* v_as_x27_2110_, lean_object* v_b_2111_, lean_object* v_a_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2109_, v_as_x27_2110_, v_b_2111_, v_a_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec(v_as_x27_2110_);
lean_dec(v_as_2109_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v___x_2121_; 
v___x_2121_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2122_, v___y_2123_, v___y_2124_);
lean_dec(v___y_2124_);
lean_dec_ref(v___y_2123_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2127_, lean_object* v_ex_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_){
_start:
{
lean_object* v___x_2132_; 
v___x_2132_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2128_, v___y_2129_, v___y_2130_);
return v___x_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2133_, lean_object* v_ex_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2133_, v_ex_2134_, v___y_2135_, v___y_2136_);
lean_dec(v___y_2136_);
lean_dec_ref(v___y_2135_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2139_, lean_object* v_msg_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; 
v___x_2144_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2140_, v___y_2141_, v___y_2142_);
return v___x_2144_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2145_, lean_object* v_msg_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_){
_start:
{
lean_object* v_res_2150_; 
v_res_2150_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2145_, v_msg_2146_, v___y_2147_, v___y_2148_);
lean_dec(v___y_2148_);
lean_dec_ref(v___y_2147_);
return v_res_2150_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = lean_unsigned_to_nat(32u);
v___x_2152_ = lean_mk_empty_array_with_capacity(v___x_2151_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v___x_2152_);
return v___x_2153_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2154_ = ((size_t)5ULL);
v___x_2155_ = lean_unsigned_to_nat(0u);
v___x_2156_ = lean_unsigned_to_nat(32u);
v___x_2157_ = lean_mk_empty_array_with_capacity(v___x_2156_);
v___x_2158_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2159_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2159_, 0, v___x_2158_);
lean_ctor_set(v___x_2159_, 1, v___x_2157_);
lean_ctor_set(v___x_2159_, 2, v___x_2155_);
lean_ctor_set(v___x_2159_, 3, v___x_2155_);
lean_ctor_set_usize(v___x_2159_, 4, v___x_2154_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2160_){
_start:
{
lean_object* v___x_2162_; lean_object* v_traceState_2163_; lean_object* v_traces_2164_; lean_object* v___x_2165_; lean_object* v_traceState_2166_; lean_object* v_env_2167_; lean_object* v_nextMacroScope_2168_; lean_object* v_ngen_2169_; lean_object* v_auxDeclNGen_2170_; lean_object* v_cache_2171_; lean_object* v_messages_2172_; lean_object* v_infoState_2173_; lean_object* v_snapshotTasks_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2193_; 
v___x_2162_ = lean_st_ref_get(v___y_2160_);
v_traceState_2163_ = lean_ctor_get(v___x_2162_, 4);
lean_inc_ref(v_traceState_2163_);
lean_dec(v___x_2162_);
v_traces_2164_ = lean_ctor_get(v_traceState_2163_, 0);
lean_inc_ref(v_traces_2164_);
lean_dec_ref(v_traceState_2163_);
v___x_2165_ = lean_st_ref_take(v___y_2160_);
v_traceState_2166_ = lean_ctor_get(v___x_2165_, 4);
v_env_2167_ = lean_ctor_get(v___x_2165_, 0);
v_nextMacroScope_2168_ = lean_ctor_get(v___x_2165_, 1);
v_ngen_2169_ = lean_ctor_get(v___x_2165_, 2);
v_auxDeclNGen_2170_ = lean_ctor_get(v___x_2165_, 3);
v_cache_2171_ = lean_ctor_get(v___x_2165_, 5);
v_messages_2172_ = lean_ctor_get(v___x_2165_, 6);
v_infoState_2173_ = lean_ctor_get(v___x_2165_, 7);
v_snapshotTasks_2174_ = lean_ctor_get(v___x_2165_, 8);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2176_ = v___x_2165_;
v_isShared_2177_ = v_isSharedCheck_2193_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_snapshotTasks_2174_);
lean_inc(v_infoState_2173_);
lean_inc(v_messages_2172_);
lean_inc(v_cache_2171_);
lean_inc(v_traceState_2166_);
lean_inc(v_auxDeclNGen_2170_);
lean_inc(v_ngen_2169_);
lean_inc(v_nextMacroScope_2168_);
lean_inc(v_env_2167_);
lean_dec(v___x_2165_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2193_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
uint64_t v_tid_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2191_; 
v_tid_2178_ = lean_ctor_get_uint64(v_traceState_2166_, sizeof(void*)*1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_traceState_2166_);
if (v_isSharedCheck_2191_ == 0)
{
lean_object* v_unused_2192_; 
v_unused_2192_ = lean_ctor_get(v_traceState_2166_, 0);
lean_dec(v_unused_2192_);
v___x_2180_ = v_traceState_2166_;
v_isShared_2181_ = v_isSharedCheck_2191_;
goto v_resetjp_2179_;
}
else
{
lean_dec(v_traceState_2166_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2191_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2182_; lean_object* v___x_2184_; 
v___x_2182_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2181_ == 0)
{
lean_ctor_set(v___x_2180_, 0, v___x_2182_);
v___x_2184_ = v___x_2180_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v___x_2182_);
lean_ctor_set_uint64(v_reuseFailAlloc_2190_, sizeof(void*)*1, v_tid_2178_);
v___x_2184_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
lean_object* v___x_2186_; 
if (v_isShared_2177_ == 0)
{
lean_ctor_set(v___x_2176_, 4, v___x_2184_);
v___x_2186_ = v___x_2176_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_env_2167_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_nextMacroScope_2168_);
lean_ctor_set(v_reuseFailAlloc_2189_, 2, v_ngen_2169_);
lean_ctor_set(v_reuseFailAlloc_2189_, 3, v_auxDeclNGen_2170_);
lean_ctor_set(v_reuseFailAlloc_2189_, 4, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2189_, 5, v_cache_2171_);
lean_ctor_set(v_reuseFailAlloc_2189_, 6, v_messages_2172_);
lean_ctor_set(v_reuseFailAlloc_2189_, 7, v_infoState_2173_);
lean_ctor_set(v_reuseFailAlloc_2189_, 8, v_snapshotTasks_2174_);
v___x_2186_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2187_ = lean_st_ref_put(v___y_2160_, v___x_2186_);
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v_traces_2164_);
return v___x_2188_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2194_, lean_object* v___y_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2194_);
lean_dec(v___y_2194_);
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2198_);
return v___x_2200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_res_2204_; 
v_res_2204_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
return v_res_2204_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2205_, lean_object* v_opts_2206_, lean_object* v_act_2207_, lean_object* v_decl_2208_, lean_object* v___y_2209_, lean_object* v___y_2210_){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_inc(v___y_2210_);
lean_inc_ref(v___y_2209_);
v___x_2212_ = lean_apply_2(v_act_2207_, v___y_2209_, v___y_2210_);
v___x_2213_ = l_Lean_profileitIOUnsafe___redArg(v_category_2205_, v_opts_2206_, v___x_2212_, v_decl_2208_);
return v___x_2213_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2214_, lean_object* v_opts_2215_, lean_object* v_act_2216_, lean_object* v_decl_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
lean_object* v_res_2221_; 
v_res_2221_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2214_, v_opts_2215_, v_act_2216_, v_decl_2217_, v___y_2218_, v___y_2219_);
lean_dec(v___y_2219_);
lean_dec_ref(v___y_2218_);
lean_dec_ref(v_opts_2215_);
lean_dec_ref(v_category_2214_);
return v_res_2221_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2222_, lean_object* v_category_2223_, lean_object* v_opts_2224_, lean_object* v_act_2225_, lean_object* v_decl_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v___x_2230_; 
v___x_2230_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2223_, v_opts_2224_, v_act_2225_, v_decl_2226_, v___y_2227_, v___y_2228_);
return v___x_2230_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2231_, lean_object* v_category_2232_, lean_object* v_opts_2233_, lean_object* v_act_2234_, lean_object* v_decl_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2231_, v_category_2232_, v_opts_2233_, v_act_2234_, v_decl_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_opts_2233_);
lean_dec_ref(v_category_2232_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2240_, lean_object* v_a_2241_){
_start:
{
if (lean_obj_tag(v_a_2240_) == 0)
{
lean_object* v___x_2242_; 
v___x_2242_ = l_List_reverse___redArg(v_a_2241_);
return v___x_2242_;
}
else
{
lean_object* v_head_2243_; lean_object* v_tail_2244_; lean_object* v___x_2246_; uint8_t v_isShared_2247_; uint8_t v_isSharedCheck_2253_; 
v_head_2243_ = lean_ctor_get(v_a_2240_, 0);
v_tail_2244_ = lean_ctor_get(v_a_2240_, 1);
v_isSharedCheck_2253_ = !lean_is_exclusive(v_a_2240_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2246_ = v_a_2240_;
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
else
{
lean_inc(v_tail_2244_);
lean_inc(v_head_2243_);
lean_dec(v_a_2240_);
v___x_2246_ = lean_box(0);
v_isShared_2247_ = v_isSharedCheck_2253_;
goto v_resetjp_2245_;
}
v_resetjp_2245_:
{
lean_object* v___x_2248_; lean_object* v___x_2250_; 
v___x_2248_ = l_Lean_MessageData_ofName(v_head_2243_);
if (v_isShared_2247_ == 0)
{
lean_ctor_set(v___x_2246_, 1, v_a_2241_);
lean_ctor_set(v___x_2246_, 0, v___x_2248_);
v___x_2250_ = v___x_2246_;
goto v_reusejp_2249_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v___x_2248_);
lean_ctor_set(v_reuseFailAlloc_2252_, 1, v_a_2241_);
v___x_2250_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2249_;
}
v_reusejp_2249_:
{
v_a_2240_ = v_tail_2244_;
v_a_2241_ = v___x_2250_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2256_ = l_Lean_stringToMessageData(v___x_2255_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2257_, lean_object* v_x_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2262_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2263_ = l_Lean_Declaration_getTopLevelNames(v_decl_2257_);
v___x_2264_ = lean_box(0);
v___x_2265_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2263_, v___x_2264_);
v___x_2266_ = l_Lean_MessageData_ofList(v___x_2265_);
v___x_2267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2267_, 0, v___x_2262_);
lean_ctor_set(v___x_2267_, 1, v___x_2266_);
v___x_2268_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2269_, lean_object* v_x_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2269_, v_x_2270_, v___y_2271_, v___y_2272_);
lean_dec(v___y_2272_);
lean_dec_ref(v___y_2271_);
lean_dec_ref(v_x_2270_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2275_, size_t v_i_2276_, lean_object* v_bs_2277_){
_start:
{
uint8_t v___x_2278_; 
v___x_2278_ = lean_usize_dec_lt(v_i_2276_, v_sz_2275_);
if (v___x_2278_ == 0)
{
return v_bs_2277_;
}
else
{
lean_object* v_v_2279_; lean_object* v_msg_2280_; lean_object* v___x_2281_; lean_object* v_bs_x27_2282_; size_t v___x_2283_; size_t v___x_2284_; lean_object* v___x_2285_; 
v_v_2279_ = lean_array_uget_borrowed(v_bs_2277_, v_i_2276_);
v_msg_2280_ = lean_ctor_get(v_v_2279_, 1);
lean_inc_ref(v_msg_2280_);
v___x_2281_ = lean_unsigned_to_nat(0u);
v_bs_x27_2282_ = lean_array_uset(v_bs_2277_, v_i_2276_, v___x_2281_);
v___x_2283_ = ((size_t)1ULL);
v___x_2284_ = lean_usize_add(v_i_2276_, v___x_2283_);
v___x_2285_ = lean_array_uset(v_bs_x27_2282_, v_i_2276_, v_msg_2280_);
v_i_2276_ = v___x_2284_;
v_bs_2277_ = v___x_2285_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2287_, lean_object* v_i_2288_, lean_object* v_bs_2289_){
_start:
{
size_t v_sz_boxed_2290_; size_t v_i_boxed_2291_; lean_object* v_res_2292_; 
v_sz_boxed_2290_ = lean_unbox_usize(v_sz_2287_);
lean_dec(v_sz_2287_);
v_i_boxed_2291_ = lean_unbox_usize(v_i_2288_);
lean_dec(v_i_2288_);
v_res_2292_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2290_, v_i_boxed_2291_, v_bs_2289_);
return v_res_2292_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2293_, lean_object* v_data_2294_, lean_object* v_ref_2295_, lean_object* v_msg_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_){
_start:
{
lean_object* v_toCold_2300_; lean_object* v_currRecDepth_2301_; lean_object* v_ref_2302_; uint8_t v_diag_2303_; uint8_t v_suppressElabErrors_2304_; lean_object* v_ref_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v_traceState_2308_; lean_object* v_traces_2309_; lean_object* v___x_2310_; size_t v_sz_2311_; size_t v___x_2312_; lean_object* v___x_2313_; lean_object* v_msg_2314_; lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2353_; 
v_toCold_2300_ = lean_ctor_get(v___y_2297_, 0);
v_currRecDepth_2301_ = lean_ctor_get(v___y_2297_, 1);
v_ref_2302_ = lean_ctor_get(v___y_2297_, 2);
v_diag_2303_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*3);
v_suppressElabErrors_2304_ = lean_ctor_get_uint8(v___y_2297_, sizeof(void*)*3 + 1);
v_ref_2305_ = l_Lean_replaceRef(v_ref_2295_, v_ref_2302_);
lean_inc(v_currRecDepth_2301_);
lean_inc_ref(v_toCold_2300_);
v___x_2306_ = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(v___x_2306_, 0, v_toCold_2300_);
lean_ctor_set(v___x_2306_, 1, v_currRecDepth_2301_);
lean_ctor_set(v___x_2306_, 2, v_ref_2305_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3, v_diag_2303_);
lean_ctor_set_uint8(v___x_2306_, sizeof(void*)*3 + 1, v_suppressElabErrors_2304_);
v___x_2307_ = lean_st_ref_get(v___y_2298_);
v_traceState_2308_ = lean_ctor_get(v___x_2307_, 4);
lean_inc_ref(v_traceState_2308_);
lean_dec(v___x_2307_);
v_traces_2309_ = lean_ctor_get(v_traceState_2308_, 0);
lean_inc_ref(v_traces_2309_);
lean_dec_ref(v_traceState_2308_);
v___x_2310_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2309_);
lean_dec_ref(v_traces_2309_);
v_sz_2311_ = lean_array_size(v___x_2310_);
v___x_2312_ = ((size_t)0ULL);
v___x_2313_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2311_, v___x_2312_, v___x_2310_);
v_msg_2314_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2314_, 0, v_data_2294_);
lean_ctor_set(v_msg_2314_, 1, v_msg_2296_);
lean_ctor_set(v_msg_2314_, 2, v___x_2313_);
v___x_2315_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2314_, v___x_2306_, v___y_2298_);
lean_dec_ref_known(v___x_2306_, 3);
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2318_ = v___x_2315_;
v_isShared_2319_ = v_isSharedCheck_2353_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2315_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2353_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2320_; lean_object* v_traceState_2321_; lean_object* v_env_2322_; lean_object* v_nextMacroScope_2323_; lean_object* v_ngen_2324_; lean_object* v_auxDeclNGen_2325_; lean_object* v_cache_2326_; lean_object* v_messages_2327_; lean_object* v_infoState_2328_; lean_object* v_snapshotTasks_2329_; lean_object* v___x_2331_; uint8_t v_isShared_2332_; uint8_t v_isSharedCheck_2352_; 
v___x_2320_ = lean_st_ref_take(v___y_2298_);
v_traceState_2321_ = lean_ctor_get(v___x_2320_, 4);
v_env_2322_ = lean_ctor_get(v___x_2320_, 0);
v_nextMacroScope_2323_ = lean_ctor_get(v___x_2320_, 1);
v_ngen_2324_ = lean_ctor_get(v___x_2320_, 2);
v_auxDeclNGen_2325_ = lean_ctor_get(v___x_2320_, 3);
v_cache_2326_ = lean_ctor_get(v___x_2320_, 5);
v_messages_2327_ = lean_ctor_get(v___x_2320_, 6);
v_infoState_2328_ = lean_ctor_get(v___x_2320_, 7);
v_snapshotTasks_2329_ = lean_ctor_get(v___x_2320_, 8);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2331_ = v___x_2320_;
v_isShared_2332_ = v_isSharedCheck_2352_;
goto v_resetjp_2330_;
}
else
{
lean_inc(v_snapshotTasks_2329_);
lean_inc(v_infoState_2328_);
lean_inc(v_messages_2327_);
lean_inc(v_cache_2326_);
lean_inc(v_traceState_2321_);
lean_inc(v_auxDeclNGen_2325_);
lean_inc(v_ngen_2324_);
lean_inc(v_nextMacroScope_2323_);
lean_inc(v_env_2322_);
lean_dec(v___x_2320_);
v___x_2331_ = lean_box(0);
v_isShared_2332_ = v_isSharedCheck_2352_;
goto v_resetjp_2330_;
}
v_resetjp_2330_:
{
uint64_t v_tid_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2350_; 
v_tid_2333_ = lean_ctor_get_uint64(v_traceState_2321_, sizeof(void*)*1);
v_isSharedCheck_2350_ = !lean_is_exclusive(v_traceState_2321_);
if (v_isSharedCheck_2350_ == 0)
{
lean_object* v_unused_2351_; 
v_unused_2351_ = lean_ctor_get(v_traceState_2321_, 0);
lean_dec(v_unused_2351_);
v___x_2335_ = v_traceState_2321_;
v_isShared_2336_ = v_isSharedCheck_2350_;
goto v_resetjp_2334_;
}
else
{
lean_dec(v_traceState_2321_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2350_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2341_; 
v___x_2337_ = lean_box(0);
v___x_2338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2338_, 0, v_ref_2295_);
lean_ctor_set(v___x_2338_, 1, v_a_2316_);
v___x_2339_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2293_, v___x_2338_);
if (v_isShared_2336_ == 0)
{
lean_ctor_set(v___x_2335_, 0, v___x_2339_);
v___x_2341_ = v___x_2335_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v___x_2339_);
lean_ctor_set_uint64(v_reuseFailAlloc_2349_, sizeof(void*)*1, v_tid_2333_);
v___x_2341_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2343_; 
if (v_isShared_2332_ == 0)
{
lean_ctor_set(v___x_2331_, 4, v___x_2341_);
v___x_2343_ = v___x_2331_;
goto v_reusejp_2342_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_env_2322_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_nextMacroScope_2323_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v_ngen_2324_);
lean_ctor_set(v_reuseFailAlloc_2348_, 3, v_auxDeclNGen_2325_);
lean_ctor_set(v_reuseFailAlloc_2348_, 4, v___x_2341_);
lean_ctor_set(v_reuseFailAlloc_2348_, 5, v_cache_2326_);
lean_ctor_set(v_reuseFailAlloc_2348_, 6, v_messages_2327_);
lean_ctor_set(v_reuseFailAlloc_2348_, 7, v_infoState_2328_);
lean_ctor_set(v_reuseFailAlloc_2348_, 8, v_snapshotTasks_2329_);
v___x_2343_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2342_;
}
v_reusejp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2346_; 
v___x_2344_ = lean_st_ref_put(v___y_2298_, v___x_2343_);
if (v_isShared_2319_ == 0)
{
lean_ctor_set(v___x_2318_, 0, v___x_2337_);
v___x_2346_ = v___x_2318_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v___x_2337_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2354_, lean_object* v_data_2355_, lean_object* v_ref_2356_, lean_object* v_msg_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_){
_start:
{
lean_object* v_res_2361_; 
v_res_2361_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2354_, v_data_2355_, v_ref_2356_, v_msg_2357_, v___y_2358_, v___y_2359_);
lean_dec(v___y_2359_);
lean_dec_ref(v___y_2358_);
return v_res_2361_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2362_){
_start:
{
if (lean_obj_tag(v_x_2362_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
v_a_2364_ = lean_ctor_get(v_x_2362_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_x_2362_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v_x_2362_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v_x_2362_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
lean_ctor_set_tag(v___x_2366_, 1);
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v_x_2362_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v_x_2362_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v_x_2362_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v_x_2362_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
lean_ctor_set_tag(v___x_2374_, 0);
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2380_, lean_object* v___y_2381_){
_start:
{
lean_object* v_res_2382_; 
v_res_2382_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2380_);
return v_res_2382_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2383_){
_start:
{
if (lean_obj_tag(v_e_2383_) == 0)
{
uint8_t v___x_2384_; 
v___x_2384_ = 2;
return v___x_2384_;
}
else
{
uint8_t v___x_2385_; 
v___x_2385_ = 0;
return v___x_2385_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2386_){
_start:
{
uint8_t v_res_2387_; lean_object* v_r_2388_; 
v_res_2387_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2386_);
lean_dec_ref(v_e_2386_);
v_r_2388_ = lean_box(v_res_2387_);
return v_r_2388_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2389_; double v___x_2390_; 
v___x_2389_ = lean_unsigned_to_nat(0u);
v___x_2390_ = lean_float_of_nat(v___x_2389_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2392_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2393_ = l_Lean_stringToMessageData(v___x_2392_);
return v___x_2393_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2394_; double v___x_2395_; 
v___x_2394_ = lean_unsigned_to_nat(1000u);
v___x_2395_ = lean_float_of_nat(v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2396_, uint8_t v_collapsed_2397_, lean_object* v_tag_2398_, lean_object* v_opts_2399_, uint8_t v_clsEnabled_2400_, lean_object* v_oldTraces_2401_, lean_object* v_msg_2402_, lean_object* v_resStartStop_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v_data_2412_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2417_; uint8_t v___x_2418_; lean_object* v___y_2420_; lean_object* v_a_2421_; uint8_t v___y_2436_; double v___y_2467_; 
v_fst_2407_ = lean_ctor_get(v_resStartStop_2403_, 0);
lean_inc(v_fst_2407_);
v_snd_2408_ = lean_ctor_get(v_resStartStop_2403_, 1);
lean_inc(v_snd_2408_);
lean_dec_ref(v_resStartStop_2403_);
v_fst_2415_ = lean_ctor_get(v_snd_2408_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_snd_2408_, 1);
lean_inc(v_snd_2416_);
lean_dec(v_snd_2408_);
v___x_2417_ = l_Lean_trace_profiler;
v___x_2418_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2399_, v___x_2417_);
if (v___x_2418_ == 0)
{
v___y_2436_ = v___x_2418_;
goto v___jp_2435_;
}
else
{
lean_object* v___x_2472_; uint8_t v___x_2473_; 
v___x_2472_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2473_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2399_, v___x_2472_);
if (v___x_2473_ == 0)
{
lean_object* v___x_2474_; lean_object* v___x_2475_; double v___x_2476_; double v___x_2477_; double v___x_2478_; 
v___x_2474_ = l_Lean_trace_profiler_threshold;
v___x_2475_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2399_, v___x_2474_);
v___x_2476_ = lean_float_of_nat(v___x_2475_);
v___x_2477_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2478_ = lean_float_div(v___x_2476_, v___x_2477_);
v___y_2467_ = v___x_2478_;
goto v___jp_2466_;
}
else
{
lean_object* v___x_2479_; lean_object* v___x_2480_; double v___x_2481_; 
v___x_2479_ = l_Lean_trace_profiler_threshold;
v___x_2480_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2399_, v___x_2479_);
v___x_2481_ = lean_float_of_nat(v___x_2480_);
v___y_2467_ = v___x_2481_;
goto v___jp_2466_;
}
}
v___jp_2409_:
{
lean_object* v___x_2413_; 
lean_inc(v___y_2410_);
v___x_2413_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2401_, v_data_2412_, v___y_2410_, v___y_2411_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v___x_2414_; 
lean_dec_ref_known(v___x_2413_, 1);
v___x_2414_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2407_);
return v___x_2414_;
}
else
{
lean_dec(v_fst_2407_);
return v___x_2413_;
}
}
v___jp_2419_:
{
uint8_t v_result_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; double v___x_2425_; lean_object* v_data_2426_; 
v_result_2422_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2407_);
v___x_2423_ = lean_box(v_result_2422_);
v___x_2424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2424_, 0, v___x_2423_);
v___x_2425_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2398_);
lean_inc_ref(v___x_2424_);
lean_inc(v_cls_2396_);
v_data_2426_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2426_, 0, v_cls_2396_);
lean_ctor_set(v_data_2426_, 1, v___x_2424_);
lean_ctor_set(v_data_2426_, 2, v_tag_2398_);
lean_ctor_set_float(v_data_2426_, sizeof(void*)*3, v___x_2425_);
lean_ctor_set_float(v_data_2426_, sizeof(void*)*3 + 8, v___x_2425_);
lean_ctor_set_uint8(v_data_2426_, sizeof(void*)*3 + 16, v_collapsed_2397_);
if (v___x_2418_ == 0)
{
lean_dec_ref_known(v___x_2424_, 1);
lean_dec(v_snd_2416_);
lean_dec(v_fst_2415_);
lean_dec_ref(v_tag_2398_);
lean_dec(v_cls_2396_);
v___y_2410_ = v___y_2420_;
v___y_2411_ = v_a_2421_;
v_data_2412_ = v_data_2426_;
goto v___jp_2409_;
}
else
{
lean_object* v_data_2427_; double v___x_2428_; double v___x_2429_; 
lean_dec_ref_known(v_data_2426_, 3);
v_data_2427_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2427_, 0, v_cls_2396_);
lean_ctor_set(v_data_2427_, 1, v___x_2424_);
lean_ctor_set(v_data_2427_, 2, v_tag_2398_);
v___x_2428_ = lean_unbox_float(v_fst_2415_);
lean_dec(v_fst_2415_);
lean_ctor_set_float(v_data_2427_, sizeof(void*)*3, v___x_2428_);
v___x_2429_ = lean_unbox_float(v_snd_2416_);
lean_dec(v_snd_2416_);
lean_ctor_set_float(v_data_2427_, sizeof(void*)*3 + 8, v___x_2429_);
lean_ctor_set_uint8(v_data_2427_, sizeof(void*)*3 + 16, v_collapsed_2397_);
v___y_2410_ = v___y_2420_;
v___y_2411_ = v_a_2421_;
v_data_2412_ = v_data_2427_;
goto v___jp_2409_;
}
}
v___jp_2430_:
{
lean_object* v_ref_2431_; lean_object* v___x_2432_; 
v_ref_2431_ = lean_ctor_get(v___y_2404_, 2);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v_fst_2407_);
v___x_2432_ = lean_apply_4(v_msg_2402_, v_fst_2407_, v___y_2404_, v___y_2405_, lean_box(0));
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___y_2420_ = v_ref_2431_;
v_a_2421_ = v_a_2433_;
goto v___jp_2419_;
}
else
{
lean_object* v___x_2434_; 
lean_dec_ref_known(v___x_2432_, 1);
v___x_2434_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2420_ = v_ref_2431_;
v_a_2421_ = v___x_2434_;
goto v___jp_2419_;
}
}
v___jp_2435_:
{
if (v_clsEnabled_2400_ == 0)
{
if (v___y_2436_ == 0)
{
lean_object* v___x_2437_; lean_object* v_traceState_2438_; lean_object* v_env_2439_; lean_object* v_nextMacroScope_2440_; lean_object* v_ngen_2441_; lean_object* v_auxDeclNGen_2442_; lean_object* v_cache_2443_; lean_object* v_messages_2444_; lean_object* v_infoState_2445_; lean_object* v_snapshotTasks_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2465_; 
lean_dec(v_snd_2416_);
lean_dec(v_fst_2415_);
lean_dec_ref(v_msg_2402_);
lean_dec_ref(v_tag_2398_);
lean_dec(v_cls_2396_);
v___x_2437_ = lean_st_ref_take(v___y_2405_);
v_traceState_2438_ = lean_ctor_get(v___x_2437_, 4);
v_env_2439_ = lean_ctor_get(v___x_2437_, 0);
v_nextMacroScope_2440_ = lean_ctor_get(v___x_2437_, 1);
v_ngen_2441_ = lean_ctor_get(v___x_2437_, 2);
v_auxDeclNGen_2442_ = lean_ctor_get(v___x_2437_, 3);
v_cache_2443_ = lean_ctor_get(v___x_2437_, 5);
v_messages_2444_ = lean_ctor_get(v___x_2437_, 6);
v_infoState_2445_ = lean_ctor_get(v___x_2437_, 7);
v_snapshotTasks_2446_ = lean_ctor_get(v___x_2437_, 8);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2448_ = v___x_2437_;
v_isShared_2449_ = v_isSharedCheck_2465_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_snapshotTasks_2446_);
lean_inc(v_infoState_2445_);
lean_inc(v_messages_2444_);
lean_inc(v_cache_2443_);
lean_inc(v_traceState_2438_);
lean_inc(v_auxDeclNGen_2442_);
lean_inc(v_ngen_2441_);
lean_inc(v_nextMacroScope_2440_);
lean_inc(v_env_2439_);
lean_dec(v___x_2437_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2465_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
uint64_t v_tid_2450_; lean_object* v_traces_2451_; lean_object* v___x_2453_; uint8_t v_isShared_2454_; uint8_t v_isSharedCheck_2464_; 
v_tid_2450_ = lean_ctor_get_uint64(v_traceState_2438_, sizeof(void*)*1);
v_traces_2451_ = lean_ctor_get(v_traceState_2438_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v_traceState_2438_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2453_ = v_traceState_2438_;
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
else
{
lean_inc(v_traces_2451_);
lean_dec(v_traceState_2438_);
v___x_2453_ = lean_box(0);
v_isShared_2454_ = v_isSharedCheck_2464_;
goto v_resetjp_2452_;
}
v_resetjp_2452_:
{
lean_object* v___x_2455_; lean_object* v___x_2457_; 
v___x_2455_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2401_, v_traces_2451_);
lean_dec_ref(v_traces_2451_);
if (v_isShared_2454_ == 0)
{
lean_ctor_set(v___x_2453_, 0, v___x_2455_);
v___x_2457_ = v___x_2453_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v___x_2455_);
lean_ctor_set_uint64(v_reuseFailAlloc_2463_, sizeof(void*)*1, v_tid_2450_);
v___x_2457_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
lean_object* v___x_2459_; 
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 4, v___x_2457_);
v___x_2459_ = v___x_2448_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_env_2439_);
lean_ctor_set(v_reuseFailAlloc_2462_, 1, v_nextMacroScope_2440_);
lean_ctor_set(v_reuseFailAlloc_2462_, 2, v_ngen_2441_);
lean_ctor_set(v_reuseFailAlloc_2462_, 3, v_auxDeclNGen_2442_);
lean_ctor_set(v_reuseFailAlloc_2462_, 4, v___x_2457_);
lean_ctor_set(v_reuseFailAlloc_2462_, 5, v_cache_2443_);
lean_ctor_set(v_reuseFailAlloc_2462_, 6, v_messages_2444_);
lean_ctor_set(v_reuseFailAlloc_2462_, 7, v_infoState_2445_);
lean_ctor_set(v_reuseFailAlloc_2462_, 8, v_snapshotTasks_2446_);
v___x_2459_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2460_ = lean_st_ref_put(v___y_2405_, v___x_2459_);
v___x_2461_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2407_);
return v___x_2461_;
}
}
}
}
}
else
{
goto v___jp_2430_;
}
}
else
{
goto v___jp_2430_;
}
}
v___jp_2466_:
{
double v___x_2468_; double v___x_2469_; double v___x_2470_; uint8_t v___x_2471_; 
v___x_2468_ = lean_unbox_float(v_snd_2416_);
v___x_2469_ = lean_unbox_float(v_fst_2415_);
v___x_2470_ = lean_float_sub(v___x_2468_, v___x_2469_);
v___x_2471_ = lean_float_decLt(v___y_2467_, v___x_2470_);
v___y_2436_ = v___x_2471_;
goto v___jp_2435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2482_, lean_object* v_collapsed_2483_, lean_object* v_tag_2484_, lean_object* v_opts_2485_, lean_object* v_clsEnabled_2486_, lean_object* v_oldTraces_2487_, lean_object* v_msg_2488_, lean_object* v_resStartStop_2489_, lean_object* v___y_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
uint8_t v_collapsed_boxed_2493_; uint8_t v_clsEnabled_boxed_2494_; lean_object* v_res_2495_; 
v_collapsed_boxed_2493_ = lean_unbox(v_collapsed_2483_);
v_clsEnabled_boxed_2494_ = lean_unbox(v_clsEnabled_2486_);
v_res_2495_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2482_, v_collapsed_boxed_2493_, v_tag_2484_, v_opts_2485_, v_clsEnabled_boxed_2494_, v_oldTraces_2487_, v_msg_2488_, v_resStartStop_2489_, v___y_2490_, v___y_2491_);
lean_dec(v___y_2491_);
lean_dec_ref(v___y_2490_);
lean_dec_ref(v_opts_2485_);
return v_res_2495_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2498_; double v___x_2499_; 
v___x_2498_ = lean_unsigned_to_nat(1000000000u);
v___x_2499_ = lean_float_of_nat(v___x_2498_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2500_, lean_object* v___x_2501_, uint8_t v___x_2502_, lean_object* v___x_2503_, lean_object* v___f_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v___y_2509_; lean_object* v___y_2510_; uint8_t v___y_2511_; lean_object* v___y_2522_; lean_object* v_a_2523_; lean_object* v___y_2527_; lean_object* v___y_2528_; uint8_t v___y_2529_; lean_object* v___y_2540_; lean_object* v_a_2541_; lean_object* v_toCold_2544_; lean_object* v_options_2545_; uint8_t v_hasTrace_2546_; 
v_toCold_2544_ = lean_ctor_get(v___y_2505_, 0);
v_options_2545_ = lean_ctor_get(v_toCold_2544_, 2);
v_hasTrace_2546_ = lean_ctor_get_uint8(v_options_2545_, sizeof(void*)*1);
if (v_hasTrace_2546_ == 0)
{
lean_object* v_cancelTk_x3f_2547_; lean_object* v___x_2548_; 
lean_dec_ref(v___f_2504_);
lean_dec_ref(v___x_2503_);
lean_dec(v___x_2501_);
v_cancelTk_x3f_2547_ = lean_ctor_get(v_toCold_2544_, 10);
lean_inc(v_decl_2500_);
v___x_2548_ = l_Lean_warnIfUsesSorry(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2548_) == 0)
{
lean_object* v___x_2549_; lean_object* v_env_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; 
lean_dec_ref_known(v___x_2548_, 1);
v___x_2549_ = lean_st_ref_get(v___y_2506_);
v_env_2550_ = lean_ctor_get(v___x_2549_, 0);
lean_inc_ref(v_env_2550_);
lean_dec(v___x_2549_);
v___x_2551_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2550_, v_options_2545_, v_decl_2500_, v_cancelTk_x3f_2547_);
v___x_2552_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2551_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
lean_dec(v_decl_2500_);
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v___x_2554_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2553_, v___y_2506_);
return v___x_2554_;
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_a_2555_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2552_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2552_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
lean_inc(v_a_2555_);
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
v___y_2540_ = v___x_2560_;
v_a_2541_ = v_a_2555_;
goto v___jp_2539_;
}
}
}
}
else
{
lean_dec(v_decl_2500_);
return v___x_2548_;
}
}
else
{
lean_object* v_cancelTk_x3f_2563_; lean_object* v_inheritedTraceOptions_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v_a_2571_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v_a_2586_; lean_object* v___y_2589_; lean_object* v___y_2590_; lean_object* v_a_2591_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v_a_2608_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v_a_2614_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v_a_2626_; lean_object* v___y_2629_; lean_object* v___y_2630_; lean_object* v_a_2631_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v_a_2648_; 
v_cancelTk_x3f_2563_ = lean_ctor_get(v_toCold_2544_, 10);
v_inheritedTraceOptions_2564_ = lean_ctor_get(v_toCold_2544_, 11);
v___x_2565_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2501_);
v___x_2566_ = l_Lean_Name_append(v___x_2565_, v___x_2501_);
v___x_2567_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2564_, v_options_2545_, v___x_2566_);
lean_dec(v___x_2566_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2676_; uint8_t v___x_2677_; 
v___x_2676_ = l_Lean_trace_profiler;
v___x_2677_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2545_, v___x_2676_);
if (v___x_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v___f_2504_);
lean_dec_ref(v___x_2503_);
lean_dec(v___x_2501_);
lean_inc(v_decl_2500_);
v___x_2678_ = l_Lean_warnIfUsesSorry(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2679_; lean_object* v_env_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; 
lean_dec_ref_known(v___x_2678_, 1);
v___x_2679_ = lean_st_ref_get(v___y_2506_);
v_env_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc_ref(v_env_2680_);
lean_dec(v___x_2679_);
v___x_2681_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2680_, v_options_2545_, v_decl_2500_, v_cancelTk_x3f_2563_);
v___x_2682_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2681_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; 
lean_dec(v_decl_2500_);
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2683_, v___y_2506_);
return v___x_2684_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_a_2685_ = lean_ctor_get(v___x_2682_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2682_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2682_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2682_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
lean_inc(v_a_2685_);
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
v___y_2522_ = v___x_2690_;
v_a_2523_ = v_a_2685_;
goto v___jp_2521_;
}
}
}
}
else
{
lean_dec(v_decl_2500_);
return v___x_2678_;
}
}
else
{
goto v___jp_2651_;
}
}
else
{
goto v___jp_2651_;
}
v___jp_2568_:
{
lean_object* v___x_2572_; double v___x_2573_; double v___x_2574_; double v___x_2575_; double v___x_2576_; double v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; 
v___x_2572_ = lean_io_mono_nanos_now();
v___x_2573_ = lean_float_of_nat(v___y_2569_);
v___x_2574_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2575_ = lean_float_div(v___x_2573_, v___x_2574_);
v___x_2576_ = lean_float_of_nat(v___x_2572_);
v___x_2577_ = lean_float_div(v___x_2576_, v___x_2574_);
v___x_2578_ = lean_box_float(v___x_2575_);
v___x_2579_ = lean_box_float(v___x_2577_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2578_);
lean_ctor_set(v___x_2580_, 1, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v_a_2571_);
lean_ctor_set(v___x_2581_, 1, v___x_2580_);
v___x_2582_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2501_, v___x_2502_, v___x_2503_, v_options_2545_, v___x_2567_, v___y_2570_, v___f_2504_, v___x_2581_, v___y_2505_, v___y_2506_);
return v___x_2582_;
}
v___jp_2583_:
{
lean_object* v___x_2587_; 
v___x_2587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2587_, 0, v_a_2586_);
v___y_2569_ = v___y_2584_;
v___y_2570_ = v___y_2585_;
v_a_2571_ = v___x_2587_;
goto v___jp_2568_;
}
v___jp_2588_:
{
lean_object* v___x_2592_; 
v___x_2592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2592_, 0, v_a_2591_);
v___y_2569_ = v___y_2589_;
v___y_2570_ = v___y_2590_;
v_a_2571_ = v___x_2592_;
goto v___jp_2568_;
}
v___jp_2593_:
{
if (lean_obj_tag(v___y_2596_) == 0)
{
lean_object* v_a_2597_; 
v_a_2597_ = lean_ctor_get(v___y_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___y_2596_, 1);
v___y_2589_ = v___y_2594_;
v___y_2590_ = v___y_2595_;
v_a_2591_ = v_a_2597_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2598_; 
v_a_2598_ = lean_ctor_get(v___y_2596_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___y_2596_, 1);
v___y_2584_ = v___y_2594_;
v___y_2585_ = v___y_2595_;
v_a_2586_ = v_a_2598_;
goto v___jp_2583_;
}
}
v___jp_2599_:
{
if (v___y_2603_ == 0)
{
lean_object* v___x_2604_; 
v___x_2604_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_dec_ref_known(v___x_2604_, 1);
v___y_2584_ = v___y_2600_;
v___y_2585_ = v___y_2602_;
v_a_2586_ = v___y_2601_;
goto v___jp_2583_;
}
else
{
lean_dec_ref(v___y_2601_);
v___y_2594_ = v___y_2600_;
v___y_2595_ = v___y_2602_;
v___y_2596_ = v___x_2604_;
goto v___jp_2593_;
}
}
else
{
lean_dec(v_decl_2500_);
v___y_2584_ = v___y_2600_;
v___y_2585_ = v___y_2602_;
v_a_2586_ = v___y_2601_;
goto v___jp_2583_;
}
}
v___jp_2605_:
{
uint8_t v___x_2609_; 
v___x_2609_ = l_Lean_Exception_isInterrupt(v_a_2608_);
if (v___x_2609_ == 0)
{
uint8_t v___x_2610_; 
lean_inc_ref(v_a_2608_);
v___x_2610_ = l_Lean_Exception_isRuntime(v_a_2608_);
v___y_2600_ = v___y_2606_;
v___y_2601_ = v_a_2608_;
v___y_2602_ = v___y_2607_;
v___y_2603_ = v___x_2610_;
goto v___jp_2599_;
}
else
{
v___y_2600_ = v___y_2606_;
v___y_2601_ = v_a_2608_;
v___y_2602_ = v___y_2607_;
v___y_2603_ = v___x_2609_;
goto v___jp_2599_;
}
}
v___jp_2611_:
{
lean_object* v___x_2615_; double v___x_2616_; double v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2615_ = lean_io_get_num_heartbeats();
v___x_2616_ = lean_float_of_nat(v___y_2612_);
v___x_2617_ = lean_float_of_nat(v___x_2615_);
v___x_2618_ = lean_box_float(v___x_2616_);
v___x_2619_ = lean_box_float(v___x_2617_);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2618_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2621_, 0, v_a_2614_);
lean_ctor_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2501_, v___x_2502_, v___x_2503_, v_options_2545_, v___x_2567_, v___y_2613_, v___f_2504_, v___x_2621_, v___y_2505_, v___y_2506_);
return v___x_2622_;
}
v___jp_2623_:
{
lean_object* v___x_2627_; 
v___x_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2627_, 0, v_a_2626_);
v___y_2612_ = v___y_2624_;
v___y_2613_ = v___y_2625_;
v_a_2614_ = v___x_2627_;
goto v___jp_2611_;
}
v___jp_2628_:
{
lean_object* v___x_2632_; 
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v_a_2631_);
v___y_2612_ = v___y_2629_;
v___y_2613_ = v___y_2630_;
v_a_2614_ = v___x_2632_;
goto v___jp_2611_;
}
v___jp_2633_:
{
if (lean_obj_tag(v___y_2636_) == 0)
{
lean_object* v_a_2637_; 
v_a_2637_ = lean_ctor_get(v___y_2636_, 0);
lean_inc(v_a_2637_);
lean_dec_ref_known(v___y_2636_, 1);
v___y_2629_ = v___y_2634_;
v___y_2630_ = v___y_2635_;
v_a_2631_ = v_a_2637_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2638_; 
v_a_2638_ = lean_ctor_get(v___y_2636_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___y_2636_, 1);
v___y_2624_ = v___y_2634_;
v___y_2625_ = v___y_2635_;
v_a_2626_ = v_a_2638_;
goto v___jp_2623_;
}
}
v___jp_2639_:
{
if (v___y_2643_ == 0)
{
lean_object* v___x_2644_; 
v___x_2644_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_dec_ref_known(v___x_2644_, 1);
v___y_2624_ = v___y_2640_;
v___y_2625_ = v___y_2642_;
v_a_2626_ = v___y_2641_;
goto v___jp_2623_;
}
else
{
lean_dec_ref(v___y_2641_);
v___y_2634_ = v___y_2640_;
v___y_2635_ = v___y_2642_;
v___y_2636_ = v___x_2644_;
goto v___jp_2633_;
}
}
else
{
lean_dec(v_decl_2500_);
v___y_2624_ = v___y_2640_;
v___y_2625_ = v___y_2642_;
v_a_2626_ = v___y_2641_;
goto v___jp_2623_;
}
}
v___jp_2645_:
{
uint8_t v___x_2649_; 
v___x_2649_ = l_Lean_Exception_isInterrupt(v_a_2648_);
if (v___x_2649_ == 0)
{
uint8_t v___x_2650_; 
lean_inc_ref(v_a_2648_);
v___x_2650_ = l_Lean_Exception_isRuntime(v_a_2648_);
v___y_2640_ = v___y_2646_;
v___y_2641_ = v_a_2648_;
v___y_2642_ = v___y_2647_;
v___y_2643_ = v___x_2650_;
goto v___jp_2639_;
}
else
{
v___y_2640_ = v___y_2646_;
v___y_2641_ = v_a_2648_;
v___y_2642_ = v___y_2647_;
v___y_2643_ = v___x_2649_;
goto v___jp_2639_;
}
}
v___jp_2651_:
{
lean_object* v___x_2652_; lean_object* v_a_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2652_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2506_);
v_a_2653_ = lean_ctor_get(v___x_2652_, 0);
lean_inc(v_a_2653_);
lean_dec_ref(v___x_2652_);
v___x_2654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2655_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2545_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; lean_object* v___x_2657_; 
v___x_2656_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2500_);
v___x_2657_ = l_Lean_warnIfUsesSorry(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v___x_2658_; lean_object* v_env_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; 
lean_dec_ref_known(v___x_2657_, 1);
v___x_2658_ = lean_st_ref_get(v___y_2506_);
v_env_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc_ref(v_env_2659_);
lean_dec(v___x_2658_);
v___x_2660_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2659_, v_options_2545_, v_decl_2500_, v_cancelTk_x3f_2563_);
v___x_2661_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2660_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2661_) == 0)
{
lean_object* v_a_2662_; lean_object* v___x_2663_; lean_object* v_a_2664_; 
lean_dec(v_decl_2500_);
v_a_2662_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2661_, 1);
v___x_2663_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2662_, v___y_2506_);
v_a_2664_ = lean_ctor_get(v___x_2663_, 0);
lean_inc(v_a_2664_);
lean_dec_ref(v___x_2663_);
v___y_2589_ = v___x_2656_;
v___y_2590_ = v_a_2653_;
v_a_2591_ = v_a_2664_;
goto v___jp_2588_;
}
else
{
lean_object* v_a_2665_; 
v_a_2665_ = lean_ctor_get(v___x_2661_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2661_, 1);
v___y_2606_ = v___x_2656_;
v___y_2607_ = v_a_2653_;
v_a_2608_ = v_a_2665_;
goto v___jp_2605_;
}
}
else
{
lean_dec(v_decl_2500_);
v___y_2594_ = v___x_2656_;
v___y_2595_ = v_a_2653_;
v___y_2596_ = v___x_2657_;
goto v___jp_2593_;
}
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; 
v___x_2666_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2500_);
v___x_2667_ = l_Lean_warnIfUsesSorry(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2668_; lean_object* v_env_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
lean_dec_ref_known(v___x_2667_, 1);
v___x_2668_ = lean_st_ref_get(v___y_2506_);
v_env_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_env_2669_);
lean_dec(v___x_2668_);
v___x_2670_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2669_, v_options_2545_, v_decl_2500_, v_cancelTk_x3f_2563_);
v___x_2671_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2670_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; lean_object* v_a_2674_; 
lean_dec(v_decl_2500_);
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2672_, v___y_2506_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2673_);
v___y_2629_ = v___x_2666_;
v___y_2630_ = v_a_2653_;
v_a_2631_ = v_a_2674_;
goto v___jp_2628_;
}
else
{
lean_object* v_a_2675_; 
v_a_2675_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2675_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2646_ = v___x_2666_;
v___y_2647_ = v_a_2653_;
v_a_2648_ = v_a_2675_;
goto v___jp_2645_;
}
}
else
{
lean_dec(v_decl_2500_);
v___y_2634_ = v___x_2666_;
v___y_2635_ = v_a_2653_;
v___y_2636_ = v___x_2667_;
goto v___jp_2633_;
}
}
}
}
v___jp_2508_:
{
if (v___y_2511_ == 0)
{
lean_object* v___x_2512_; 
lean_dec_ref(v___y_2509_);
v___x_2512_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2519_ == 0)
{
lean_object* v_unused_2520_; 
v_unused_2520_ = lean_ctor_get(v___x_2512_, 0);
lean_dec(v_unused_2520_);
v___x_2514_ = v___x_2512_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_dec(v___x_2512_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
lean_ctor_set_tag(v___x_2514_, 1);
lean_ctor_set(v___x_2514_, 0, v___y_2510_);
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v___y_2510_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
else
{
lean_dec_ref(v___y_2510_);
return v___x_2512_;
}
}
else
{
lean_dec_ref(v___y_2510_);
lean_dec(v_decl_2500_);
return v___y_2509_;
}
}
v___jp_2521_:
{
uint8_t v___x_2524_; 
v___x_2524_ = l_Lean_Exception_isInterrupt(v_a_2523_);
if (v___x_2524_ == 0)
{
uint8_t v___x_2525_; 
lean_inc_ref(v_a_2523_);
v___x_2525_ = l_Lean_Exception_isRuntime(v_a_2523_);
v___y_2509_ = v___y_2522_;
v___y_2510_ = v_a_2523_;
v___y_2511_ = v___x_2525_;
goto v___jp_2508_;
}
else
{
v___y_2509_ = v___y_2522_;
v___y_2510_ = v_a_2523_;
v___y_2511_ = v___x_2524_;
goto v___jp_2508_;
}
}
v___jp_2526_:
{
if (v___y_2529_ == 0)
{
lean_object* v___x_2530_; 
lean_dec_ref(v___y_2528_);
v___x_2530_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2500_, v___y_2505_, v___y_2506_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2537_ == 0)
{
lean_object* v_unused_2538_; 
v_unused_2538_ = lean_ctor_get(v___x_2530_, 0);
lean_dec(v_unused_2538_);
v___x_2532_ = v___x_2530_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_dec(v___x_2530_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
lean_ctor_set_tag(v___x_2532_, 1);
lean_ctor_set(v___x_2532_, 0, v___y_2527_);
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v___y_2527_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
else
{
lean_dec_ref(v___y_2527_);
return v___x_2530_;
}
}
else
{
lean_dec_ref(v___y_2527_);
lean_dec(v_decl_2500_);
return v___y_2528_;
}
}
v___jp_2539_:
{
uint8_t v___x_2542_; 
v___x_2542_ = l_Lean_Exception_isInterrupt(v_a_2541_);
if (v___x_2542_ == 0)
{
uint8_t v___x_2543_; 
lean_inc_ref(v_a_2541_);
v___x_2543_ = l_Lean_Exception_isRuntime(v_a_2541_);
v___y_2527_ = v_a_2541_;
v___y_2528_ = v___y_2540_;
v___y_2529_ = v___x_2543_;
goto v___jp_2526_;
}
else
{
v___y_2527_ = v_a_2541_;
v___y_2528_ = v___y_2540_;
v___y_2529_ = v___x_2542_;
goto v___jp_2526_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2693_, lean_object* v___x_2694_, lean_object* v___x_2695_, lean_object* v___x_2696_, lean_object* v___f_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_){
_start:
{
uint8_t v___x_7943__boxed_2701_; lean_object* v_res_2702_; 
v___x_7943__boxed_2701_ = lean_unbox(v___x_2695_);
v_res_2702_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2693_, v___x_2694_, v___x_7943__boxed_2701_, v___x_2696_, v___f_2697_, v___y_2698_, v___y_2699_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_){
_start:
{
lean_object* v_toCold_2711_; lean_object* v_options_2712_; lean_object* v___f_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; uint8_t v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___f_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_toCold_2711_ = lean_ctor_get(v_a_2708_, 0);
v_options_2712_ = lean_ctor_get(v_toCold_2711_, 2);
lean_inc(v_decl_2707_);
v___f_2713_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2713_, 0, v_decl_2707_);
v___x_2714_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2715_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2716_ = 1;
v___x_2717_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2718_ = lean_box(v___x_2716_);
v___f_2719_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2719_, 0, v_decl_2707_);
lean_closure_set(v___f_2719_, 1, v___x_2715_);
lean_closure_set(v___f_2719_, 2, v___x_2718_);
lean_closure_set(v___f_2719_, 3, v___x_2717_);
lean_closure_set(v___f_2719_, 4, v___f_2713_);
v___x_2720_ = lean_box(0);
v___x_2721_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2714_, v_options_2712_, v___f_2719_, v___x_2720_, v_a_2708_, v_a_2709_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2727_, lean_object* v_x_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2728_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2733_, lean_object* v_x_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2733_, v_x_2734_, v___y_2735_, v___y_2736_);
lean_dec(v___y_2736_);
lean_dec_ref(v___y_2735_);
return v_res_2738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2739_, lean_object* v_a_2740_, lean_object* v_ref_2741_, lean_object* v_a_x3f_2742_){
_start:
{
lean_object* v___x_2744_; lean_object* v_env_2745_; lean_object* v___x_2746_; 
v___x_2744_ = lean_st_ref_get(v___y_2739_);
v_env_2745_ = lean_ctor_get(v___x_2744_, 0);
lean_inc_ref(v_env_2745_);
lean_dec(v___x_2744_);
v___x_2746_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2740_, v_env_2745_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2749_; uint8_t v_isShared_2750_; uint8_t v_isSharedCheck_2754_; 
lean_dec(v_ref_2741_);
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2754_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2754_ == 0)
{
v___x_2749_ = v___x_2746_;
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
else
{
lean_inc(v_a_2747_);
lean_dec(v___x_2746_);
v___x_2749_ = lean_box(0);
v_isShared_2750_ = v_isSharedCheck_2754_;
goto v_resetjp_2748_;
}
v_resetjp_2748_:
{
lean_object* v___x_2752_; 
if (v_isShared_2750_ == 0)
{
v___x_2752_ = v___x_2749_;
goto v_reusejp_2751_;
}
else
{
lean_object* v_reuseFailAlloc_2753_; 
v_reuseFailAlloc_2753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
v___x_2752_ = v_reuseFailAlloc_2753_;
goto v_reusejp_2751_;
}
v_reusejp_2751_:
{
return v___x_2752_;
}
}
}
else
{
lean_object* v_a_2755_; lean_object* v___x_2757_; uint8_t v_isShared_2758_; uint8_t v_isSharedCheck_2766_; 
v_a_2755_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2757_ = v___x_2746_;
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
else
{
lean_inc(v_a_2755_);
lean_dec(v___x_2746_);
v___x_2757_ = lean_box(0);
v_isShared_2758_ = v_isSharedCheck_2766_;
goto v_resetjp_2756_;
}
v_resetjp_2756_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; 
v___x_2759_ = lean_io_error_to_string(v_a_2755_);
v___x_2760_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2760_, 0, v___x_2759_);
v___x_2761_ = l_Lean_MessageData_ofFormat(v___x_2760_);
v___x_2762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2762_, 0, v_ref_2741_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
if (v_isShared_2758_ == 0)
{
lean_ctor_set(v___x_2757_, 0, v___x_2762_);
v___x_2764_ = v___x_2757_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2767_, lean_object* v_a_2768_, lean_object* v_ref_2769_, lean_object* v_a_x3f_2770_, lean_object* v___y_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2767_, v_a_2768_, v_ref_2769_, v_a_x3f_2770_);
lean_dec(v_a_x3f_2770_);
lean_dec(v___y_2767_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2773_, lean_object* v___y_2774_, lean_object* v_a_2775_, lean_object* v_a_x3f_2776_){
_start:
{
lean_object* v___x_2778_; lean_object* v_env_2779_; lean_object* v_ref_2780_; lean_object* v___x_2781_; 
v___x_2778_ = lean_st_ref_get(v___y_2773_);
v_env_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc_ref(v_env_2779_);
lean_dec(v___x_2778_);
v_ref_2780_ = lean_ctor_get(v___y_2774_, 2);
v___x_2781_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2775_, v_env_2779_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v_a_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2789_; 
v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2789_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2789_ == 0)
{
v___x_2784_ = v___x_2781_;
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
else
{
lean_inc(v_a_2782_);
lean_dec(v___x_2781_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2789_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2787_; 
if (v_isShared_2785_ == 0)
{
v___x_2787_ = v___x_2784_;
goto v_reusejp_2786_;
}
else
{
lean_object* v_reuseFailAlloc_2788_; 
v_reuseFailAlloc_2788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2788_, 0, v_a_2782_);
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
lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2801_; 
v_a_2790_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2792_ = v___x_2781_;
v_isShared_2793_ = v_isSharedCheck_2801_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_dec(v___x_2781_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2801_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2794_ = lean_io_error_to_string(v_a_2790_);
v___x_2795_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2795_, 0, v___x_2794_);
v___x_2796_ = l_Lean_MessageData_ofFormat(v___x_2795_);
lean_inc(v_ref_2780_);
v___x_2797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2797_, 0, v_ref_2780_);
lean_ctor_set(v___x_2797_, 1, v___x_2796_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2797_);
v___x_2799_ = v___x_2792_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v_a_2804_, lean_object* v_a_x3f_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v_res_2807_; 
v_res_2807_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2802_, v___y_2803_, v_a_2804_, v_a_x3f_2805_);
lean_dec(v_a_x3f_2805_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
return v_res_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2808_, lean_object* v_asyncEnv_2809_, lean_object* v_decl_2810_, lean_object* v_x_2811_, lean_object* v___y_2812_, lean_object* v___y_2813_){
_start:
{
lean_object* v___x_2815_; lean_object* v_r_2816_; 
v___x_2815_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2809_, v___y_2813_);
lean_dec_ref(v___x_2815_);
v_r_2816_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2810_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v_r_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2833_; 
v_a_2817_ = lean_ctor_get(v_r_2816_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v_r_2816_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2819_ = v_r_2816_;
v_isShared_2820_ = v_isSharedCheck_2833_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v_r_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2833_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
lean_inc(v_a_2817_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set_tag(v___x_2819_, 1);
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
lean_object* v___x_2823_; 
v___x_2823_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2813_, v___y_2812_, v_a_2808_, v___x_2822_);
lean_dec_ref(v___x_2822_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v___x_2825_; uint8_t v_isShared_2826_; uint8_t v_isSharedCheck_2830_; 
v_isSharedCheck_2830_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2830_ == 0)
{
lean_object* v_unused_2831_; 
v_unused_2831_ = lean_ctor_get(v___x_2823_, 0);
lean_dec(v_unused_2831_);
v___x_2825_ = v___x_2823_;
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
else
{
lean_dec(v___x_2823_);
v___x_2825_ = lean_box(0);
v_isShared_2826_ = v_isSharedCheck_2830_;
goto v_resetjp_2824_;
}
v_resetjp_2824_:
{
lean_object* v___x_2828_; 
if (v_isShared_2826_ == 0)
{
lean_ctor_set(v___x_2825_, 0, v_a_2817_);
v___x_2828_ = v___x_2825_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2817_);
v___x_2828_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
return v___x_2828_;
}
}
}
else
{
lean_dec(v_a_2817_);
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v_a_2834_ = lean_ctor_get(v_r_2816_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v_r_2816_, 1);
v___x_2835_ = lean_box(0);
v___x_2836_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2813_, v___y_2812_, v_a_2808_, v___x_2835_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2843_; 
v_isSharedCheck_2843_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2843_ == 0)
{
lean_object* v_unused_2844_; 
v_unused_2844_ = lean_ctor_get(v___x_2836_, 0);
lean_dec(v_unused_2844_);
v___x_2838_ = v___x_2836_;
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v___x_2836_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2843_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
if (v_isShared_2839_ == 0)
{
lean_ctor_set_tag(v___x_2838_, 1);
lean_ctor_set(v___x_2838_, 0, v_a_2834_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2842_; 
v_reuseFailAlloc_2842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2834_);
v___x_2841_ = v_reuseFailAlloc_2842_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
return v___x_2841_;
}
}
}
else
{
lean_dec(v_a_2834_);
return v___x_2836_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2845_, lean_object* v_asyncEnv_2846_, lean_object* v_decl_2847_, lean_object* v_x_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2845_, v_asyncEnv_2846_, v_decl_2847_, v_x_2848_, v___y_2849_, v___y_2850_);
lean_dec(v___y_2850_);
lean_dec_ref(v___y_2849_);
lean_dec_ref(v_x_2848_);
return v_res_2852_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2854_; lean_object* v___x_2855_; 
v___x_2854_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2855_ = l_Lean_stringToMessageData(v___x_2854_);
return v___x_2855_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2856_, lean_object* v_x_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2861_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2862_ = l_Lean_Declaration_getNames(v_decl_2856_);
v___x_2863_ = lean_box(0);
v___x_2864_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2862_, v___x_2863_);
v___x_2865_ = l_Lean_MessageData_ofList(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2861_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2866_);
return v___x_2867_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2868_, lean_object* v_x_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2868_, v_x_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec_ref(v_x_2869_);
return v_res_2873_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2876_, lean_object* v_msg_2877_, lean_object* v___y_2878_, lean_object* v___y_2879_){
_start:
{
lean_object* v_ref_2881_; lean_object* v___x_2882_; lean_object* v_a_2883_; lean_object* v___x_2885_; uint8_t v_isShared_2886_; uint8_t v_isSharedCheck_2927_; 
v_ref_2881_ = lean_ctor_get(v___y_2878_, 2);
v___x_2882_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2877_, v___y_2878_, v___y_2879_);
v_a_2883_ = lean_ctor_get(v___x_2882_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2882_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2885_ = v___x_2882_;
v_isShared_2886_ = v_isSharedCheck_2927_;
goto v_resetjp_2884_;
}
else
{
lean_inc(v_a_2883_);
lean_dec(v___x_2882_);
v___x_2885_ = lean_box(0);
v_isShared_2886_ = v_isSharedCheck_2927_;
goto v_resetjp_2884_;
}
v_resetjp_2884_:
{
lean_object* v___x_2887_; lean_object* v_traceState_2888_; lean_object* v_env_2889_; lean_object* v_nextMacroScope_2890_; lean_object* v_ngen_2891_; lean_object* v_auxDeclNGen_2892_; lean_object* v_cache_2893_; lean_object* v_messages_2894_; lean_object* v_infoState_2895_; lean_object* v_snapshotTasks_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2926_; 
v___x_2887_ = lean_st_ref_take(v___y_2879_);
v_traceState_2888_ = lean_ctor_get(v___x_2887_, 4);
v_env_2889_ = lean_ctor_get(v___x_2887_, 0);
v_nextMacroScope_2890_ = lean_ctor_get(v___x_2887_, 1);
v_ngen_2891_ = lean_ctor_get(v___x_2887_, 2);
v_auxDeclNGen_2892_ = lean_ctor_get(v___x_2887_, 3);
v_cache_2893_ = lean_ctor_get(v___x_2887_, 5);
v_messages_2894_ = lean_ctor_get(v___x_2887_, 6);
v_infoState_2895_ = lean_ctor_get(v___x_2887_, 7);
v_snapshotTasks_2896_ = lean_ctor_get(v___x_2887_, 8);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2898_ = v___x_2887_;
v_isShared_2899_ = v_isSharedCheck_2926_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_snapshotTasks_2896_);
lean_inc(v_infoState_2895_);
lean_inc(v_messages_2894_);
lean_inc(v_cache_2893_);
lean_inc(v_traceState_2888_);
lean_inc(v_auxDeclNGen_2892_);
lean_inc(v_ngen_2891_);
lean_inc(v_nextMacroScope_2890_);
lean_inc(v_env_2889_);
lean_dec(v___x_2887_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2926_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
uint64_t v_tid_2900_; lean_object* v_traces_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2925_; 
v_tid_2900_ = lean_ctor_get_uint64(v_traceState_2888_, sizeof(void*)*1);
v_traces_2901_ = lean_ctor_get(v_traceState_2888_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_traceState_2888_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2903_ = v_traceState_2888_;
v_isShared_2904_ = v_isSharedCheck_2925_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_traces_2901_);
lean_dec(v_traceState_2888_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2925_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; double v___x_2907_; uint8_t v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v___x_2916_; 
v___x_2905_ = lean_box(0);
v___x_2906_ = lean_box(0);
v___x_2907_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2908_ = 0;
v___x_2909_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2910_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2910_, 0, v_cls_2876_);
lean_ctor_set(v___x_2910_, 1, v___x_2906_);
lean_ctor_set(v___x_2910_, 2, v___x_2909_);
lean_ctor_set_float(v___x_2910_, sizeof(void*)*3, v___x_2907_);
lean_ctor_set_float(v___x_2910_, sizeof(void*)*3 + 8, v___x_2907_);
lean_ctor_set_uint8(v___x_2910_, sizeof(void*)*3 + 16, v___x_2908_);
v___x_2911_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2912_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2910_);
lean_ctor_set(v___x_2912_, 1, v_a_2883_);
lean_ctor_set(v___x_2912_, 2, v___x_2911_);
lean_inc(v_ref_2881_);
v___x_2913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2913_, 0, v_ref_2881_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_PersistentArray_push___redArg(v_traces_2901_, v___x_2913_);
if (v_isShared_2904_ == 0)
{
lean_ctor_set(v___x_2903_, 0, v___x_2914_);
v___x_2916_ = v___x_2903_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v___x_2914_);
lean_ctor_set_uint64(v_reuseFailAlloc_2924_, sizeof(void*)*1, v_tid_2900_);
v___x_2916_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
lean_object* v___x_2918_; 
if (v_isShared_2899_ == 0)
{
lean_ctor_set(v___x_2898_, 4, v___x_2916_);
v___x_2918_ = v___x_2898_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_env_2889_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v_nextMacroScope_2890_);
lean_ctor_set(v_reuseFailAlloc_2923_, 2, v_ngen_2891_);
lean_ctor_set(v_reuseFailAlloc_2923_, 3, v_auxDeclNGen_2892_);
lean_ctor_set(v_reuseFailAlloc_2923_, 4, v___x_2916_);
lean_ctor_set(v_reuseFailAlloc_2923_, 5, v_cache_2893_);
lean_ctor_set(v_reuseFailAlloc_2923_, 6, v_messages_2894_);
lean_ctor_set(v_reuseFailAlloc_2923_, 7, v_infoState_2895_);
lean_ctor_set(v_reuseFailAlloc_2923_, 8, v_snapshotTasks_2896_);
v___x_2918_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
lean_object* v___x_2919_; lean_object* v___x_2921_; 
v___x_2919_ = lean_st_ref_put(v___y_2879_, v___x_2918_);
if (v_isShared_2886_ == 0)
{
lean_ctor_set(v___x_2885_, 0, v___x_2905_);
v___x_2921_ = v___x_2885_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v___x_2905_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2928_, lean_object* v_msg_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_, lean_object* v___y_2932_){
_start:
{
lean_object* v_res_2933_; 
v_res_2933_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2928_, v_msg_2929_, v___y_2930_, v___y_2931_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
return v_res_2933_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2936_ = l_Lean_stringToMessageData(v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2937_, lean_object* v_cls_2938_, lean_object* v_x_2939_, lean_object* v___y_2940_, lean_object* v___y_2941_){
_start:
{
lean_object* v_toCold_2943_; lean_object* v_options_2944_; uint8_t v_hasTrace_2945_; 
v_toCold_2943_ = lean_ctor_get(v___y_2940_, 0);
v_options_2944_ = lean_ctor_get(v_toCold_2943_, 2);
v_hasTrace_2945_ = lean_ctor_get_uint8(v_options_2944_, sizeof(void*)*1);
if (v_hasTrace_2945_ == 0)
{
lean_object* v___x_2946_; 
lean_dec(v_cls_2938_);
v___x_2946_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2937_, v___y_2940_, v___y_2941_);
return v___x_2946_;
}
else
{
lean_object* v_inheritedTraceOptions_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v_inheritedTraceOptions_2947_ = lean_ctor_get(v_toCold_2943_, 11);
v___x_2948_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2938_);
v___x_2949_ = l_Lean_Name_append(v___x_2948_, v_cls_2938_);
v___x_2950_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2947_, v_options_2944_, v___x_2949_);
lean_dec(v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; 
lean_dec(v_cls_2938_);
v___x_2951_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2937_, v___y_2940_, v___y_2941_);
return v___x_2951_;
}
else
{
lean_object* v___x_2952_; lean_object* v___x_2953_; 
v___x_2952_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2953_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2938_, v___x_2952_, v___y_2940_, v___y_2941_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v___x_2954_; 
lean_dec_ref_known(v___x_2953_, 1);
v___x_2954_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2937_, v___y_2940_, v___y_2941_);
return v___x_2954_;
}
else
{
lean_dec(v_decl_2937_);
return v___x_2953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2955_, lean_object* v_cls_2956_, lean_object* v_x_2957_, lean_object* v___y_2958_, lean_object* v___y_2959_, lean_object* v___y_2960_){
_start:
{
lean_object* v_res_2961_; 
v_res_2961_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2955_, v_cls_2956_, v_x_2957_, v___y_2958_, v___y_2959_);
lean_dec(v___y_2959_);
lean_dec_ref(v___y_2958_);
lean_dec(v_x_2957_);
return v_res_2961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2962_, lean_object* v___y_2963_){
_start:
{
lean_object* v_toCold_2965_; lean_object* v_options_2966_; uint8_t v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_toCold_2965_ = lean_ctor_get(v___y_2963_, 0);
v_options_2966_ = lean_ctor_get(v_toCold_2965_, 2);
v___x_2967_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2966_, v_opt_2962_);
v___x_2968_ = lean_box(v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
return v___x_2969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2970_, lean_object* v___y_2971_, lean_object* v___y_2972_){
_start:
{
lean_object* v_res_2973_; 
v_res_2973_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2970_, v___y_2971_);
lean_dec_ref(v___y_2971_);
lean_dec_ref(v_opt_2970_);
return v_res_2973_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2974_){
_start:
{
if (lean_obj_tag(v_x_2974_) == 0)
{
uint8_t v___x_2975_; 
v___x_2975_ = 1;
return v___x_2975_;
}
else
{
lean_object* v_head_2976_; lean_object* v_tail_2977_; uint8_t v___x_2978_; 
v_head_2976_ = lean_ctor_get(v_x_2974_, 0);
v_tail_2977_ = lean_ctor_get(v_x_2974_, 1);
v___x_2978_ = l_Lean_isPrivateName(v_head_2976_);
if (v___x_2978_ == 0)
{
return v___x_2978_;
}
else
{
v_x_2974_ = v_tail_2977_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2980_){
_start:
{
uint8_t v_res_2981_; lean_object* v_r_2982_; 
v_res_2981_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2980_);
lean_dec(v_x_2980_);
v_r_2982_ = lean_box(v_res_2981_);
return v_r_2982_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2988_; lean_object* v___x_2989_; 
v___x_2988_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2989_ = l_Lean_stringToMessageData(v___x_2988_);
return v___x_2989_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2991_; lean_object* v___x_2992_; 
v___x_2991_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2992_ = l_Lean_stringToMessageData(v___x_2991_);
return v___x_2992_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2994_; lean_object* v___x_2995_; 
v___x_2994_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2995_ = l_Lean_stringToMessageData(v___x_2994_);
return v___x_2995_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2996_, uint8_t v_hasTrace_2997_, uint8_t v___x_2998_, lean_object* v___x_2999_, lean_object* v_cls_3000_, lean_object* v___x_3001_, lean_object* v_____x_3002_, lean_object* v_exportedInfo_x3f_3003_, lean_object* v___y_3004_, lean_object* v___y_3005_){
_start:
{
lean_object* v___y_3008_; lean_object* v___y_3009_; lean_object* v_a_3010_; lean_object* v___y_3021_; lean_object* v___y_3022_; lean_object* v_a_3023_; lean_object* v___y_3034_; lean_object* v___y_3035_; lean_object* v___y_3036_; lean_object* v___y_3037_; lean_object* v___y_3038_; lean_object* v___y_3039_; lean_object* v___y_3040_; lean_object* v___y_3041_; lean_object* v___y_3042_; lean_object* v___y_3043_; lean_object* v___y_3044_; lean_object* v___y_3045_; lean_object* v_snd_3107_; lean_object* v_fst_3108_; lean_object* v___x_3110_; uint8_t v_isShared_3111_; uint8_t v_isSharedCheck_3237_; 
v_snd_3107_ = lean_ctor_get(v_____x_3002_, 1);
v_fst_3108_ = lean_ctor_get(v_____x_3002_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_____x_3002_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3110_ = v_____x_3002_;
v_isShared_3111_ = v_isSharedCheck_3237_;
goto v_resetjp_3109_;
}
else
{
lean_inc(v_snd_3107_);
lean_inc(v_fst_3108_);
lean_dec(v_____x_3002_);
v___x_3110_ = lean_box(0);
v_isShared_3111_ = v_isSharedCheck_3237_;
goto v_resetjp_3109_;
}
v___jp_3007_:
{
lean_object* v___x_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
v___x_3011_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3008_, v___y_3009_);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3018_ == 0)
{
lean_object* v_unused_3019_; 
v_unused_3019_ = lean_ctor_get(v___x_3011_, 0);
lean_dec(v_unused_3019_);
v___x_3013_ = v___x_3011_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_dec(v___x_3011_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
lean_ctor_set_tag(v___x_3013_, 1);
lean_ctor_set(v___x_3013_, 0, v_a_3010_);
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3010_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
v___jp_3020_:
{
lean_object* v___x_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3031_; 
v___x_3024_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3021_, v___y_3022_);
v_isSharedCheck_3031_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3031_ == 0)
{
lean_object* v_unused_3032_; 
v_unused_3032_ = lean_ctor_get(v___x_3024_, 0);
lean_dec(v_unused_3032_);
v___x_3026_ = v___x_3024_;
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
else
{
lean_dec(v___x_3024_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3031_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v_a_3023_);
v___x_3029_ = v___x_3026_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v_a_3023_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
return v___x_3029_;
}
}
}
v___jp_3033_:
{
lean_object* v___x_3046_; 
lean_inc_ref(v___y_3044_);
v___x_3046_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3035_, v___y_3044_, v___y_3038_, v___y_3045_);
if (lean_obj_tag(v___x_3046_) == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3093_; 
lean_dec_ref_known(v___x_3046_, 1);
lean_dec(v___y_3034_);
lean_inc_ref(v___y_3036_);
v___x_3047_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3036_, v___y_3040_);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3093_ == 0)
{
lean_object* v_unused_3094_; 
v_unused_3094_ = lean_ctor_get(v___x_3047_, 0);
lean_dec(v_unused_3094_);
v___x_3049_ = v___x_3047_;
v_isShared_3050_ = v_isSharedCheck_3093_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v___x_3047_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3093_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v_options_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_options_3051_ = lean_ctor_get(v___y_3037_, 2);
v___x_3052_ = l_Lean_Elab_async;
v___x_3053_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3051_, v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v_r_3055_; 
lean_del_object(v___x_3049_);
lean_dec_ref(v___y_3043_);
lean_dec_ref(v___y_3042_);
v___x_3054_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3044_, v___y_3040_);
lean_dec_ref(v___x_3054_);
v_r_3055_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2996_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v_r_3055_) == 0)
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3065_; 
v_a_3056_ = lean_ctor_get(v_r_3055_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v_r_3055_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3058_ = v_r_3055_;
v_isShared_3059_ = v_isSharedCheck_3065_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v_r_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3065_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
lean_inc(v_a_3056_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set_tag(v___x_3058_, 1);
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
lean_object* v___x_3062_; 
v___x_3062_ = lean_apply_2(v___y_3041_, v___x_3061_, lean_box(0));
if (lean_obj_tag(v___x_3062_) == 0)
{
lean_dec_ref_known(v___x_3062_, 1);
v___y_3021_ = v___y_3036_;
v___y_3022_ = v___y_3040_;
v_a_3023_ = v_a_3056_;
goto v___jp_3020_;
}
else
{
lean_object* v_a_3063_; 
lean_dec(v_a_3056_);
v_a_3063_ = lean_ctor_get(v___x_3062_, 0);
lean_inc(v_a_3063_);
lean_dec_ref_known(v___x_3062_, 1);
v___y_3008_ = v___y_3036_;
v___y_3009_ = v___y_3040_;
v_a_3010_ = v_a_3063_;
goto v___jp_3007_;
}
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; 
v_a_3066_ = lean_ctor_get(v_r_3055_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v_r_3055_, 1);
v___x_3067_ = lean_box(0);
v___x_3068_ = lean_apply_2(v___y_3041_, v___x_3067_, lean_box(0));
if (lean_obj_tag(v___x_3068_) == 0)
{
lean_dec_ref_known(v___x_3068_, 1);
v___y_3008_ = v___y_3036_;
v___y_3009_ = v___y_3040_;
v_a_3010_ = v_a_3066_;
goto v___jp_3007_;
}
else
{
lean_object* v_a_3069_; 
lean_dec(v_a_3066_);
v_a_3069_ = lean_ctor_get(v___x_3068_, 0);
lean_inc(v_a_3069_);
lean_dec_ref_known(v___x_3068_, 1);
v___y_3008_ = v___y_3036_;
v___y_3009_ = v___y_3040_;
v_a_3010_ = v_a_3069_;
goto v___jp_3007_;
}
}
}
else
{
lean_object* v___x_3070_; lean_object* v___x_3072_; 
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___y_3041_);
lean_dec_ref(v___y_3036_);
lean_dec(v_decl_2996_);
v___x_3070_ = l_IO_CancelToken_new();
if (v_isShared_3050_ == 0)
{
lean_ctor_set_tag(v___x_3049_, 1);
lean_ctor_set(v___x_3049_, 0, v___x_3070_);
v___x_3072_ = v___x_3049_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3070_);
v___x_3072_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v___x_3073_ = lean_unsigned_to_nat(0u);
v___x_3074_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3075_ = l_Lean_Name_toString(v___x_3074_, v_hasTrace_2997_);
lean_inc_ref(v___x_3072_);
v___x_3076_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3043_, v___x_3072_, v___x_3075_, v___y_3039_, v___y_3040_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; lean_object* v_checked_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v_checked_3078_ = lean_ctor_get(v___y_3042_, 2);
lean_inc_ref(v_checked_3078_);
lean_dec_ref(v___y_3042_);
v___x_3079_ = lean_io_map_task(v_a_3077_, v_checked_3078_, v___x_3073_, v___x_2998_);
v___x_3080_ = lean_box(0);
v___x_3081_ = lean_box(2);
v___x_3082_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3080_);
lean_ctor_set(v___x_3082_, 1, v___x_3081_);
lean_ctor_set(v___x_3082_, 2, v___x_3072_);
lean_ctor_set(v___x_3082_, 3, v___x_3079_);
v___x_3083_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3082_, v___y_3040_);
return v___x_3083_;
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_dec_ref(v___x_3072_);
lean_dec_ref(v___y_3042_);
v_a_3084_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3076_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3076_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3106_; 
lean_dec_ref(v___y_3044_);
lean_dec_ref(v___y_3043_);
lean_dec_ref(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec_ref(v___y_3036_);
lean_dec(v_decl_2996_);
v_a_3095_ = lean_ctor_get(v___x_3046_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___x_3046_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3097_ = v___x_3046_;
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3046_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3106_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3104_; 
v___x_3099_ = lean_io_error_to_string(v_a_3095_);
v___x_3100_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
v___x_3101_ = l_Lean_MessageData_ofFormat(v___x_3100_);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v___y_3034_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3102_);
v___x_3104_ = v___x_3097_;
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
v_resetjp_3109_:
{
lean_object* v_fst_3112_; lean_object* v_snd_3113_; lean_object* v___x_3115_; uint8_t v_isShared_3116_; uint8_t v_isSharedCheck_3236_; 
v_fst_3112_ = lean_ctor_get(v_snd_3107_, 0);
v_snd_3113_ = lean_ctor_get(v_snd_3107_, 1);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_snd_3107_);
if (v_isSharedCheck_3236_ == 0)
{
v___x_3115_ = v_snd_3107_;
v_isShared_3116_ = v_isSharedCheck_3236_;
goto v_resetjp_3114_;
}
else
{
lean_inc(v_snd_3113_);
lean_inc(v_fst_3112_);
lean_dec(v_snd_3107_);
v___x_3115_ = lean_box(0);
v_isShared_3116_ = v_isSharedCheck_3236_;
goto v_resetjp_3114_;
}
v_resetjp_3114_:
{
lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v_exportedInfo_x3f_3148_; lean_object* v___y_3149_; lean_object* v___y_3150_; lean_object* v___y_3160_; lean_object* v___y_3161_; lean_object* v___y_3164_; lean_object* v___y_3165_; lean_object* v___y_3168_; lean_object* v___y_3169_; lean_object* v___y_3191_; lean_object* v___y_3192_; lean_object* v___x_3226_; lean_object* v_env_3227_; uint8_t v___x_3228_; 
v___x_3226_ = lean_st_ref_get(v___y_3005_);
v_env_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc_ref(v_env_3227_);
lean_dec(v___x_3226_);
v___x_3228_ = l_Lean_Environment_containsOnBranch(v_env_3227_, v_fst_3108_);
lean_dec_ref(v_env_3227_);
if (v___x_3228_ == 0)
{
lean_del_object(v___x_3110_);
v___y_3191_ = v___y_3004_;
v___y_3192_ = v___y_3005_;
goto v___jp_3190_;
}
else
{
lean_object* v___x_3229_; lean_object* v_env_3230_; lean_object* v___x_3231_; lean_object* v___x_3233_; 
lean_del_object(v___x_3115_);
lean_dec(v_snd_3113_);
lean_dec(v_fst_3112_);
lean_dec(v_exportedInfo_x3f_3003_);
lean_dec(v___x_3001_);
lean_dec(v_cls_3000_);
lean_dec_ref(v___x_2999_);
lean_dec(v_decl_2996_);
v___x_3229_ = lean_st_ref_get(v___y_3005_);
v_env_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc_ref(v_env_3230_);
lean_dec(v___x_3229_);
v___x_3231_ = lean_elab_environment_to_kernel_env(v_env_3230_);
if (v_isShared_3111_ == 0)
{
lean_ctor_set_tag(v___x_3110_, 1);
lean_ctor_set(v___x_3110_, 1, v_fst_3108_);
lean_ctor_set(v___x_3110_, 0, v___x_3231_);
v___x_3233_ = v___x_3110_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3235_; 
v_reuseFailAlloc_3235_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3235_, 0, v___x_3231_);
lean_ctor_set(v_reuseFailAlloc_3235_, 1, v_fst_3108_);
v___x_3233_ = v_reuseFailAlloc_3235_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
lean_object* v___x_3234_; 
v___x_3234_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3233_, v___y_3004_, v___y_3005_);
return v___x_3234_;
}
}
v___jp_3117_:
{
lean_object* v_toCold_3123_; lean_object* v_ref_3124_; uint8_t v___x_3125_; lean_object* v___x_3126_; 
v_toCold_3123_ = lean_ctor_get(v___y_3118_, 0);
v_ref_3124_ = lean_ctor_get(v___y_3118_, 2);
v___x_3125_ = lean_unbox(v_snd_3113_);
lean_dec(v_snd_3113_);
lean_inc_ref(v___y_3121_);
v___x_3126_ = l_Lean_Environment_addConstAsync(v___y_3121_, v_fst_3108_, v___x_3125_, v___y_3122_, v___x_2998_, v_hasTrace_2997_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_mainEnv_3128_; lean_object* v_asyncEnv_3129_; lean_object* v___f_3130_; lean_object* v___f_3131_; lean_object* v___x_3132_; 
lean_del_object(v___x_3115_);
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc_n(v_a_3127_, 3);
lean_dec_ref_known(v___x_3126_, 1);
v_mainEnv_3128_ = lean_ctor_get(v_a_3127_, 0);
lean_inc_ref(v_mainEnv_3128_);
v_asyncEnv_3129_ = lean_ctor_get(v_a_3127_, 1);
lean_inc_ref_n(v_asyncEnv_3129_, 2);
lean_inc(v_ref_3124_);
lean_inc(v___y_3119_);
v___f_3130_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3130_, 0, v___y_3119_);
lean_closure_set(v___f_3130_, 1, v_a_3127_);
lean_closure_set(v___f_3130_, 2, v_ref_3124_);
lean_inc(v_decl_2996_);
v___f_3131_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3131_, 0, v_a_3127_);
lean_closure_set(v___f_3131_, 1, v_asyncEnv_3129_);
lean_closure_set(v___f_3131_, 2, v_decl_2996_);
v___x_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_fst_3112_);
if (lean_obj_tag(v___y_3120_) == 0)
{
lean_inc_ref(v___x_3132_);
lean_inc(v_ref_3124_);
v___y_3034_ = v_ref_3124_;
v___y_3035_ = v_a_3127_;
v___y_3036_ = v_mainEnv_3128_;
v___y_3037_ = v_toCold_3123_;
v___y_3038_ = v___x_3132_;
v___y_3039_ = v___y_3118_;
v___y_3040_ = v___y_3119_;
v___y_3041_ = v___f_3130_;
v___y_3042_ = v___y_3121_;
v___y_3043_ = v___f_3131_;
v___y_3044_ = v_asyncEnv_3129_;
v___y_3045_ = v___x_3132_;
goto v___jp_3033_;
}
else
{
lean_inc(v_ref_3124_);
v___y_3034_ = v_ref_3124_;
v___y_3035_ = v_a_3127_;
v___y_3036_ = v_mainEnv_3128_;
v___y_3037_ = v_toCold_3123_;
v___y_3038_ = v___x_3132_;
v___y_3039_ = v___y_3118_;
v___y_3040_ = v___y_3119_;
v___y_3041_ = v___f_3130_;
v___y_3042_ = v___y_3121_;
v___y_3043_ = v___f_3131_;
v___y_3044_ = v_asyncEnv_3129_;
v___y_3045_ = v___y_3120_;
goto v___jp_3033_;
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3146_; 
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3120_);
lean_dec(v_fst_3112_);
lean_dec(v_decl_2996_);
v_a_3133_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3135_ = v___x_3126_;
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3126_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3146_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3141_; 
v___x_3137_ = lean_io_error_to_string(v_a_3133_);
v___x_3138_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
v___x_3139_ = l_Lean_MessageData_ofFormat(v___x_3138_);
lean_inc(v_ref_3124_);
if (v_isShared_3116_ == 0)
{
lean_ctor_set(v___x_3115_, 1, v___x_3139_);
lean_ctor_set(v___x_3115_, 0, v_ref_3124_);
v___x_3141_ = v___x_3115_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_ref_3124_);
lean_ctor_set(v_reuseFailAlloc_3145_, 1, v___x_3139_);
v___x_3141_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
lean_object* v___x_3143_; 
if (v_isShared_3136_ == 0)
{
lean_ctor_set(v___x_3135_, 0, v___x_3141_);
v___x_3143_ = v___x_3135_;
goto v_reusejp_3142_;
}
else
{
lean_object* v_reuseFailAlloc_3144_; 
v_reuseFailAlloc_3144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3144_, 0, v___x_3141_);
v___x_3143_ = v_reuseFailAlloc_3144_;
goto v_reusejp_3142_;
}
v_reusejp_3142_:
{
return v___x_3143_;
}
}
}
}
}
v___jp_3147_:
{
lean_object* v___x_3151_; 
v___x_3151_ = lean_st_ref_get(v___y_3150_);
if (lean_obj_tag(v_exportedInfo_x3f_3148_) == 0)
{
lean_object* v_env_3152_; lean_object* v___x_3153_; 
v_env_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_ref(v_env_3152_);
lean_dec(v___x_3151_);
v___x_3153_ = lean_box(0);
v___y_3118_ = v___y_3149_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v_exportedInfo_x3f_3148_;
v___y_3121_ = v_env_3152_;
v___y_3122_ = v___x_3153_;
goto v___jp_3117_;
}
else
{
lean_object* v_env_3154_; lean_object* v_val_3155_; uint8_t v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; 
v_env_3154_ = lean_ctor_get(v___x_3151_, 0);
lean_inc_ref(v_env_3154_);
lean_dec(v___x_3151_);
v_val_3155_ = lean_ctor_get(v_exportedInfo_x3f_3148_, 0);
v___x_3156_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3155_);
v___x_3157_ = lean_box(v___x_3156_);
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v___x_3157_);
v___y_3118_ = v___y_3149_;
v___y_3119_ = v___y_3150_;
v___y_3120_ = v_exportedInfo_x3f_3148_;
v___y_3121_ = v_env_3154_;
v___y_3122_ = v___x_3158_;
goto v___jp_3117_;
}
}
v___jp_3159_:
{
lean_object* v___x_3162_; 
lean_inc(v_fst_3112_);
v___x_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3162_, 0, v_fst_3112_);
v_exportedInfo_x3f_3148_ = v___x_3162_;
v___y_3149_ = v___y_3160_;
v___y_3150_ = v___y_3161_;
goto v___jp_3147_;
}
v___jp_3163_:
{
lean_object* v___x_3166_; 
lean_inc(v_fst_3112_);
v___x_3166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3166_, 0, v_fst_3112_);
v_exportedInfo_x3f_3148_ = v___x_3166_;
v___y_3149_ = v___y_3164_;
v___y_3150_ = v___y_3165_;
goto v___jp_3147_;
}
v___jp_3167_:
{
lean_object* v___x_3170_; lean_object* v_env_3171_; lean_object* v_nextMacroScope_3172_; lean_object* v_ngen_3173_; lean_object* v_auxDeclNGen_3174_; lean_object* v_traceState_3175_; lean_object* v_messages_3176_; lean_object* v_infoState_3177_; lean_object* v_snapshotTasks_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3188_; 
v___x_3170_ = lean_st_ref_take(v___y_3168_);
v_env_3171_ = lean_ctor_get(v___x_3170_, 0);
v_nextMacroScope_3172_ = lean_ctor_get(v___x_3170_, 1);
v_ngen_3173_ = lean_ctor_get(v___x_3170_, 2);
v_auxDeclNGen_3174_ = lean_ctor_get(v___x_3170_, 3);
v_traceState_3175_ = lean_ctor_get(v___x_3170_, 4);
v_messages_3176_ = lean_ctor_get(v___x_3170_, 6);
v_infoState_3177_ = lean_ctor_get(v___x_3170_, 7);
v_snapshotTasks_3178_ = lean_ctor_get(v___x_3170_, 8);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3170_);
if (v_isSharedCheck_3188_ == 0)
{
lean_object* v_unused_3189_; 
v_unused_3189_ = lean_ctor_get(v___x_3170_, 5);
lean_dec(v_unused_3189_);
v___x_3180_ = v___x_3170_;
v_isShared_3181_ = v_isSharedCheck_3188_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_snapshotTasks_3178_);
lean_inc(v_infoState_3177_);
lean_inc(v_messages_3176_);
lean_inc(v_traceState_3175_);
lean_inc(v_auxDeclNGen_3174_);
lean_inc(v_ngen_3173_);
lean_inc(v_nextMacroScope_3172_);
lean_inc(v_env_3171_);
lean_dec(v___x_3170_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3188_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3185_; 
v___x_3182_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3113_);
lean_inc(v_fst_3108_);
v___x_3183_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3182_, v_env_3171_, v_fst_3108_, v_snd_3113_);
if (v_isShared_3181_ == 0)
{
lean_ctor_set(v___x_3180_, 5, v___x_2999_);
lean_ctor_set(v___x_3180_, 0, v___x_3183_);
v___x_3185_ = v___x_3180_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v___x_3183_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_nextMacroScope_3172_);
lean_ctor_set(v_reuseFailAlloc_3187_, 2, v_ngen_3173_);
lean_ctor_set(v_reuseFailAlloc_3187_, 3, v_auxDeclNGen_3174_);
lean_ctor_set(v_reuseFailAlloc_3187_, 4, v_traceState_3175_);
lean_ctor_set(v_reuseFailAlloc_3187_, 5, v___x_2999_);
lean_ctor_set(v_reuseFailAlloc_3187_, 6, v_messages_3176_);
lean_ctor_set(v_reuseFailAlloc_3187_, 7, v_infoState_3177_);
lean_ctor_set(v_reuseFailAlloc_3187_, 8, v_snapshotTasks_3178_);
v___x_3185_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
lean_object* v___x_3186_; 
v___x_3186_ = lean_st_ref_put(v___y_3168_, v___x_3185_);
v_exportedInfo_x3f_3148_ = v_exportedInfo_x3f_3003_;
v___y_3149_ = v___y_3169_;
v___y_3150_ = v___y_3168_;
goto v___jp_3147_;
}
}
}
v___jp_3190_:
{
lean_object* v___x_3193_; uint8_t v___x_3194_; 
lean_inc(v_decl_2996_);
v___x_3193_ = l_Lean_Declaration_getTopLevelNames(v_decl_2996_);
v___x_3194_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3193_);
lean_dec(v___x_3193_);
if (v___x_3194_ == 0)
{
lean_dec(v___x_3001_);
if (lean_obj_tag(v_exportedInfo_x3f_3003_) == 0)
{
if (v___x_3194_ == 0)
{
lean_object* v_toCold_3195_; lean_object* v_options_3196_; uint8_t v_hasTrace_3197_; 
lean_dec_ref(v___x_2999_);
v_toCold_3195_ = lean_ctor_get(v___y_3191_, 0);
v_options_3196_ = lean_ctor_get(v_toCold_3195_, 2);
v_hasTrace_3197_ = lean_ctor_get_uint8(v_options_3196_, sizeof(void*)*1);
if (v_hasTrace_3197_ == 0)
{
lean_dec(v_cls_3000_);
v___y_3160_ = v___y_3191_;
v___y_3161_ = v___y_3192_;
goto v___jp_3159_;
}
else
{
lean_object* v_inheritedTraceOptions_3198_; lean_object* v___x_3199_; lean_object* v___x_3200_; uint8_t v___x_3201_; 
v_inheritedTraceOptions_3198_ = lean_ctor_get(v_toCold_3195_, 11);
v___x_3199_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3000_);
v___x_3200_ = l_Lean_Name_append(v___x_3199_, v_cls_3000_);
v___x_3201_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3198_, v_options_3196_, v___x_3200_);
lean_dec(v___x_3200_);
if (v___x_3201_ == 0)
{
lean_dec(v_cls_3000_);
v___y_3160_ = v___y_3191_;
v___y_3161_ = v___y_3192_;
goto v___jp_3159_;
}
else
{
lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3202_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3203_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3000_, v___x_3202_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_dec_ref_known(v___x_3203_, 1);
v___y_3160_ = v___y_3191_;
v___y_3161_ = v___y_3192_;
goto v___jp_3159_;
}
else
{
lean_del_object(v___x_3115_);
lean_dec(v_snd_3113_);
lean_dec(v_fst_3112_);
lean_dec(v_fst_3108_);
lean_dec(v_decl_2996_);
return v___x_3203_;
}
}
}
}
else
{
lean_dec(v_cls_3000_);
v___y_3168_ = v___y_3192_;
v___y_3169_ = v___y_3191_;
goto v___jp_3167_;
}
}
else
{
lean_dec(v_cls_3000_);
v___y_3168_ = v___y_3192_;
v___y_3169_ = v___y_3191_;
goto v___jp_3167_;
}
}
else
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v_a_3206_; uint8_t v___x_3207_; 
lean_dec(v_exportedInfo_x3f_3003_);
lean_dec_ref(v___x_2999_);
v___x_3204_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3205_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3204_, v___y_3191_);
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
lean_dec_ref(v___x_3205_);
v___x_3207_ = lean_unbox(v_a_3206_);
lean_dec(v_a_3206_);
if (v___x_3207_ == 0)
{
lean_object* v_toCold_3208_; lean_object* v_options_3209_; uint8_t v_hasTrace_3210_; 
v_toCold_3208_ = lean_ctor_get(v___y_3191_, 0);
v_options_3209_ = lean_ctor_get(v_toCold_3208_, 2);
v_hasTrace_3210_ = lean_ctor_get_uint8(v_options_3209_, sizeof(void*)*1);
if (v_hasTrace_3210_ == 0)
{
lean_dec(v_cls_3000_);
v_exportedInfo_x3f_3148_ = v___x_3001_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3192_;
goto v___jp_3147_;
}
else
{
lean_object* v_inheritedTraceOptions_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; uint8_t v___x_3214_; 
v_inheritedTraceOptions_3211_ = lean_ctor_get(v_toCold_3208_, 11);
v___x_3212_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3000_);
v___x_3213_ = l_Lean_Name_append(v___x_3212_, v_cls_3000_);
v___x_3214_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3211_, v_options_3209_, v___x_3213_);
lean_dec(v___x_3213_);
if (v___x_3214_ == 0)
{
lean_dec(v_cls_3000_);
v_exportedInfo_x3f_3148_ = v___x_3001_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3192_;
goto v___jp_3147_;
}
else
{
lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3215_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3216_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3000_, v___x_3215_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3216_) == 0)
{
lean_dec_ref_known(v___x_3216_, 1);
v_exportedInfo_x3f_3148_ = v___x_3001_;
v___y_3149_ = v___y_3191_;
v___y_3150_ = v___y_3192_;
goto v___jp_3147_;
}
else
{
lean_del_object(v___x_3115_);
lean_dec(v_snd_3113_);
lean_dec(v_fst_3112_);
lean_dec(v_fst_3108_);
lean_dec(v___x_3001_);
lean_dec(v_decl_2996_);
return v___x_3216_;
}
}
}
}
else
{
lean_object* v_toCold_3217_; lean_object* v_options_3218_; uint8_t v_hasTrace_3219_; 
lean_dec(v___x_3001_);
v_toCold_3217_ = lean_ctor_get(v___y_3191_, 0);
v_options_3218_ = lean_ctor_get(v_toCold_3217_, 2);
v_hasTrace_3219_ = lean_ctor_get_uint8(v_options_3218_, sizeof(void*)*1);
if (v_hasTrace_3219_ == 0)
{
lean_dec(v_cls_3000_);
v___y_3164_ = v___y_3191_;
v___y_3165_ = v___y_3192_;
goto v___jp_3163_;
}
else
{
lean_object* v_inheritedTraceOptions_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; uint8_t v___x_3223_; 
v_inheritedTraceOptions_3220_ = lean_ctor_get(v_toCold_3217_, 11);
v___x_3221_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3000_);
v___x_3222_ = l_Lean_Name_append(v___x_3221_, v_cls_3000_);
v___x_3223_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3220_, v_options_3218_, v___x_3222_);
lean_dec(v___x_3222_);
if (v___x_3223_ == 0)
{
lean_dec(v_cls_3000_);
v___y_3164_ = v___y_3191_;
v___y_3165_ = v___y_3192_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3225_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3000_, v___x_3224_, v___y_3191_, v___y_3192_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_dec_ref_known(v___x_3225_, 1);
v___y_3164_ = v___y_3191_;
v___y_3165_ = v___y_3192_;
goto v___jp_3163_;
}
else
{
lean_del_object(v___x_3115_);
lean_dec(v_snd_3113_);
lean_dec(v_fst_3112_);
lean_dec(v_fst_3108_);
lean_dec(v_decl_2996_);
return v___x_3225_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3238_, lean_object* v_hasTrace_3239_, lean_object* v___x_3240_, lean_object* v___x_3241_, lean_object* v_cls_3242_, lean_object* v___x_3243_, lean_object* v_____x_3244_, lean_object* v_exportedInfo_x3f_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_, lean_object* v___y_3248_){
_start:
{
uint8_t v_hasTrace_boxed_3249_; uint8_t v___x_53158__boxed_3250_; lean_object* v_res_3251_; 
v_hasTrace_boxed_3249_ = lean_unbox(v_hasTrace_3239_);
v___x_53158__boxed_3250_ = lean_unbox(v___x_3240_);
v_res_3251_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3238_, v_hasTrace_boxed_3249_, v___x_53158__boxed_3250_, v___x_3241_, v_cls_3242_, v___x_3243_, v_____x_3244_, v_exportedInfo_x3f_3245_, v___y_3246_, v___y_3247_);
lean_dec(v___y_3247_);
lean_dec_ref(v___y_3246_);
return v_res_3251_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
v___x_3256_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3257_ = l_Lean_stringToMessageData(v___x_3256_);
return v___x_3257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3258_, uint8_t v___x_3259_, lean_object* v_cls_3260_, lean_object* v___x_3261_, uint8_t v_forceExpose_3262_, lean_object* v_defn_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_){
_start:
{
lean_object* v_exportedInfo_x3f_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; lean_object* v___y_3280_; lean_object* v___y_3281_; lean_object* v___y_3282_; uint8_t v___y_3283_; uint8_t v___y_3288_; lean_object* v___x_3293_; lean_object* v_env_3294_; lean_object* v___x_3295_; uint8_t v___y_3297_; lean_object* v_env_3313_; 
v___x_3293_ = lean_st_ref_get(v___y_3265_);
v_env_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_ref(v_env_3294_);
lean_dec(v___x_3293_);
v___x_3295_ = lean_st_ref_get(v___y_3265_);
v_env_3313_ = lean_ctor_get(v___x_3295_, 0);
lean_inc_ref(v_env_3313_);
lean_dec(v___x_3295_);
if (v_forceExpose_3262_ == 0)
{
goto v___jp_3314_;
}
else
{
if (v___x_3259_ == 0)
{
lean_dec_ref(v_env_3313_);
lean_dec_ref(v_env_3294_);
lean_dec(v_cls_3260_);
v_exportedInfo_x3f_3268_ = v___x_3261_;
v___y_3269_ = v___y_3264_;
v___y_3270_ = v___y_3265_;
goto v___jp_3267_;
}
else
{
goto v___jp_3314_;
}
}
v___jp_3267_:
{
lean_object* v_toConstantVal_3271_; lean_object* v_name_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_toConstantVal_3271_ = lean_ctor_get(v_defn_3263_, 0);
v_name_3272_ = lean_ctor_get(v_toConstantVal_3271_, 0);
lean_inc(v_name_3272_);
v___x_3273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3273_, 0, v_defn_3263_);
v___x_3274_ = 0;
v___x_3275_ = lean_box(v___x_3274_);
v___x_3276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3273_);
lean_ctor_set(v___x_3276_, 1, v___x_3275_);
v___x_3277_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3277_, 0, v_name_3272_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
lean_inc(v___y_3270_);
lean_inc_ref(v___y_3269_);
v___x_3278_ = lean_apply_5(v___f_3258_, v___x_3277_, v_exportedInfo_x3f_3268_, v___y_3269_, v___y_3270_, lean_box(0));
return v___x_3278_;
}
v___jp_3279_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; lean_object* v___x_3286_; 
v___x_3284_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3284_, 0, v___y_3280_);
lean_ctor_set_uint8(v___x_3284_, sizeof(void*)*1, v___y_3283_);
v___x_3285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3285_, 0, v___x_3284_);
v___x_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3286_, 0, v___x_3285_);
v_exportedInfo_x3f_3268_ = v___x_3286_;
v___y_3269_ = v___y_3281_;
v___y_3270_ = v___y_3282_;
goto v___jp_3267_;
}
v___jp_3287_:
{
lean_object* v_toConstantVal_3289_; uint8_t v_safety_3290_; uint8_t v___x_3291_; uint8_t v___x_3292_; 
v_toConstantVal_3289_ = lean_ctor_get(v_defn_3263_, 0);
v_safety_3290_ = lean_ctor_get_uint8(v_defn_3263_, sizeof(void*)*4);
v___x_3291_ = 1;
v___x_3292_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3290_, v___x_3291_);
if (v___x_3292_ == 0)
{
lean_inc_ref(v_toConstantVal_3289_);
v___y_3280_ = v_toConstantVal_3289_;
v___y_3281_ = v___y_3264_;
v___y_3282_ = v___y_3265_;
v___y_3283_ = v___y_3288_;
goto v___jp_3279_;
}
else
{
lean_inc_ref(v_toConstantVal_3289_);
v___y_3280_ = v_toConstantVal_3289_;
v___y_3281_ = v___y_3264_;
v___y_3282_ = v___y_3265_;
v___y_3283_ = v___x_3259_;
goto v___jp_3279_;
}
}
v___jp_3296_:
{
lean_object* v_toCold_3298_; lean_object* v_options_3299_; uint8_t v_hasTrace_3300_; 
v_toCold_3298_ = lean_ctor_get(v___y_3264_, 0);
v_options_3299_ = lean_ctor_get(v_toCold_3298_, 2);
v_hasTrace_3300_ = lean_ctor_get_uint8(v_options_3299_, sizeof(void*)*1);
if (v_hasTrace_3300_ == 0)
{
lean_dec(v_cls_3260_);
v___y_3288_ = v___y_3297_;
goto v___jp_3287_;
}
else
{
lean_object* v_inheritedTraceOptions_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; uint8_t v___x_3304_; 
v_inheritedTraceOptions_3301_ = lean_ctor_get(v_toCold_3298_, 11);
v___x_3302_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3260_);
v___x_3303_ = l_Lean_Name_append(v___x_3302_, v_cls_3260_);
v___x_3304_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3301_, v_options_3299_, v___x_3303_);
lean_dec(v___x_3303_);
if (v___x_3304_ == 0)
{
lean_dec(v_cls_3260_);
v___y_3288_ = v___y_3297_;
goto v___jp_3287_;
}
else
{
lean_object* v_toConstantVal_3305_; lean_object* v_name_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_toConstantVal_3305_ = lean_ctor_get(v_defn_3263_, 0);
v_name_3306_ = lean_ctor_get(v_toConstantVal_3305_, 0);
v___x_3307_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3306_);
v___x_3308_ = l_Lean_MessageData_ofName(v_name_3306_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3307_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3260_, v___x_3311_, v___y_3264_, v___y_3265_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_dec_ref_known(v___x_3312_, 1);
v___y_3288_ = v___y_3297_;
goto v___jp_3287_;
}
else
{
lean_dec_ref(v_defn_3263_);
lean_dec_ref(v___f_3258_);
return v___x_3312_;
}
}
}
}
v___jp_3314_:
{
lean_object* v___x_3315_; uint8_t v_isModule_3316_; 
v___x_3315_ = l_Lean_Environment_header(v_env_3294_);
lean_dec_ref(v_env_3294_);
v_isModule_3316_ = lean_ctor_get_uint8(v___x_3315_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3315_);
if (v_isModule_3316_ == 0)
{
lean_dec_ref(v_env_3313_);
lean_dec(v_cls_3260_);
v_exportedInfo_x3f_3268_ = v___x_3261_;
v___y_3269_ = v___y_3264_;
v___y_3270_ = v___y_3265_;
goto v___jp_3267_;
}
else
{
uint8_t v_isExporting_3317_; 
v_isExporting_3317_ = lean_ctor_get_uint8(v_env_3313_, sizeof(void*)*8);
lean_dec_ref(v_env_3313_);
if (v_isExporting_3317_ == 0)
{
lean_dec(v___x_3261_);
v___y_3297_ = v_isModule_3316_;
goto v___jp_3296_;
}
else
{
if (v___x_3259_ == 0)
{
lean_dec(v_cls_3260_);
v_exportedInfo_x3f_3268_ = v___x_3261_;
v___y_3269_ = v___y_3264_;
v___y_3270_ = v___y_3265_;
goto v___jp_3267_;
}
else
{
lean_dec(v___x_3261_);
v___y_3297_ = v___x_3259_;
goto v___jp_3296_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3318_, lean_object* v___x_3319_, lean_object* v_cls_3320_, lean_object* v___x_3321_, lean_object* v_forceExpose_3322_, lean_object* v_defn_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_){
_start:
{
uint8_t v___x_53630__boxed_3327_; uint8_t v_forceExpose_boxed_3328_; lean_object* v_res_3329_; 
v___x_53630__boxed_3327_ = lean_unbox(v___x_3319_);
v_forceExpose_boxed_3328_ = lean_unbox(v_forceExpose_3322_);
v_res_3329_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3318_, v___x_53630__boxed_3327_, v_cls_3320_, v___x_3321_, v_forceExpose_boxed_3328_, v_defn_3323_, v___y_3324_, v___y_3325_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3329_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3330_, lean_object* v___f_3331_, lean_object* v_____r_3332_, lean_object* v_exportedInfo_x3f_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_){
_start:
{
lean_object* v_toConstantVal_3337_; lean_object* v_name_3338_; lean_object* v___x_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_toConstantVal_3337_ = lean_ctor_get(v_val_3330_, 0);
v_name_3338_ = lean_ctor_get(v_toConstantVal_3337_, 0);
lean_inc(v_name_3338_);
v___x_3339_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3339_, 0, v_val_3330_);
v___x_3340_ = 1;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3345_, lean_object* v___f_3346_, lean_object* v_____r_3347_, lean_object* v_exportedInfo_x3f_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v_res_3352_; 
v_res_3352_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3345_, v___f_3346_, v_____r_3347_, v_exportedInfo_x3f_3348_, v___y_3349_, v___y_3350_);
lean_dec(v___y_3350_);
lean_dec_ref(v___y_3349_);
return v_res_3352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3353_, uint8_t v___x_3354_, lean_object* v___f_3355_, lean_object* v_____r_3356_, lean_object* v___y_3357_, lean_object* v___y_3358_){
_start:
{
lean_object* v_toConstantVal_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_toConstantVal_3360_ = lean_ctor_get(v_val_3353_, 0);
lean_inc_ref(v_toConstantVal_3360_);
v___x_3361_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3361_, 0, v_toConstantVal_3360_);
lean_ctor_set_uint8(v___x_3361_, sizeof(void*)*1, v___x_3354_);
v___x_3362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3362_, 0, v___x_3361_);
v___x_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3363_, 0, v___x_3362_);
v___x_3364_ = lean_box(0);
lean_inc(v___y_3358_);
lean_inc_ref(v___y_3357_);
v___x_3365_ = lean_apply_5(v___f_3355_, v___x_3364_, v___x_3363_, v___y_3357_, v___y_3358_, lean_box(0));
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3366_, lean_object* v___x_3367_, lean_object* v___f_3368_, lean_object* v_____r_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
uint8_t v___x_53761__boxed_3373_; lean_object* v_res_3374_; 
v___x_53761__boxed_3373_ = lean_unbox(v___x_3367_);
v_res_3374_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3366_, v___x_53761__boxed_3373_, v___f_3368_, v_____r_3369_, v___y_3370_, v___y_3371_);
lean_dec(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec_ref(v_val_3366_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3375_, lean_object* v___f_3376_, lean_object* v_____r_3377_, lean_object* v_exportedInfo_x3f_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v_toConstantVal_3382_; lean_object* v_name_3383_; lean_object* v___x_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_toConstantVal_3382_ = lean_ctor_get(v_val_3375_, 0);
v_name_3383_ = lean_ctor_get(v_toConstantVal_3382_, 0);
lean_inc(v_name_3383_);
v___x_3384_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3384_, 0, v_val_3375_);
v___x_3385_ = 3;
v___x_3386_ = lean_box(v___x_3385_);
v___x_3387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3387_, 0, v___x_3384_);
lean_ctor_set(v___x_3387_, 1, v___x_3386_);
v___x_3388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3388_, 0, v_name_3383_);
lean_ctor_set(v___x_3388_, 1, v___x_3387_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
v___x_3389_ = lean_apply_5(v___f_3376_, v___x_3388_, v_exportedInfo_x3f_3378_, v___y_3379_, v___y_3380_, lean_box(0));
return v___x_3389_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3390_, lean_object* v___f_3391_, lean_object* v_____r_3392_, lean_object* v_exportedInfo_x3f_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v_res_3397_; 
v_res_3397_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3390_, v___f_3391_, v_____r_3392_, v_exportedInfo_x3f_3393_, v___y_3394_, v___y_3395_);
lean_dec(v___y_3395_);
lean_dec_ref(v___y_3394_);
return v_res_3397_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3398_, lean_object* v___f_3399_, lean_object* v_____r_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_toConstantVal_3404_; uint8_t v_isUnsafe_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v_toConstantVal_3404_ = lean_ctor_get(v_val_3398_, 0);
v_isUnsafe_3405_ = lean_ctor_get_uint8(v_val_3398_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3404_);
v___x_3406_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3406_, 0, v_toConstantVal_3404_);
lean_ctor_set_uint8(v___x_3406_, sizeof(void*)*1, v_isUnsafe_3405_);
v___x_3407_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
v___x_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3408_, 0, v___x_3407_);
v___x_3409_ = lean_box(0);
lean_inc(v___y_3402_);
lean_inc_ref(v___y_3401_);
v___x_3410_ = lean_apply_5(v___f_3399_, v___x_3409_, v___x_3408_, v___y_3401_, v___y_3402_, lean_box(0));
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3411_, lean_object* v___f_3412_, lean_object* v_____r_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3411_, v___f_3412_, v_____r_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec_ref(v_val_3411_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3418_, uint8_t v___x_3419_, lean_object* v_cls_3420_, lean_object* v___x_3421_, lean_object* v___x_3422_, lean_object* v_____x_3423_, lean_object* v_exportedInfo_x3f_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v_a_3431_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v_a_3444_; lean_object* v___y_3455_; uint8_t v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; lean_object* v___y_3460_; lean_object* v___y_3461_; lean_object* v___y_3462_; lean_object* v___y_3463_; lean_object* v___y_3464_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v_snd_3529_; lean_object* v_fst_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3661_; 
v_snd_3529_ = lean_ctor_get(v_____x_3423_, 1);
v_fst_3530_ = lean_ctor_get(v_____x_3423_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v_____x_3423_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3532_ = v_____x_3423_;
v_isShared_3533_ = v_isSharedCheck_3661_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_snd_3529_);
lean_inc(v_fst_3530_);
lean_dec(v_____x_3423_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3661_;
goto v_resetjp_3531_;
}
v___jp_3428_:
{
lean_object* v___x_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3439_; 
v___x_3432_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3430_, v___y_3429_);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3439_ == 0)
{
lean_object* v_unused_3440_; 
v_unused_3440_ = lean_ctor_get(v___x_3432_, 0);
lean_dec(v_unused_3440_);
v___x_3434_ = v___x_3432_;
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
else
{
lean_dec(v___x_3432_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3439_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3437_; 
if (v_isShared_3435_ == 0)
{
lean_ctor_set_tag(v___x_3434_, 1);
lean_ctor_set(v___x_3434_, 0, v_a_3431_);
v___x_3437_ = v___x_3434_;
goto v_reusejp_3436_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_a_3431_);
v___x_3437_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3436_;
}
v_reusejp_3436_:
{
return v___x_3437_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
v___x_3445_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3443_, v___y_3442_);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3452_ == 0)
{
lean_object* v_unused_3453_; 
v_unused_3453_ = lean_ctor_get(v___x_3445_, 0);
lean_dec(v_unused_3453_);
v___x_3447_ = v___x_3445_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_dec(v___x_3445_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
lean_ctor_set(v___x_3447_, 0, v_a_3444_);
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3444_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
v___jp_3454_:
{
lean_object* v___x_3468_; 
lean_inc_ref(v___y_3460_);
v___x_3468_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3465_, v___y_3460_, v___y_3459_, v___y_3467_);
if (lean_obj_tag(v___x_3468_) == 0)
{
lean_object* v___x_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref_known(v___x_3468_, 1);
lean_dec(v___y_3461_);
lean_inc_ref(v___y_3458_);
v___x_3469_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3458_, v___y_3464_);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3469_);
if (v_isSharedCheck_3515_ == 0)
{
lean_object* v_unused_3516_; 
v_unused_3516_ = lean_ctor_get(v___x_3469_, 0);
lean_dec(v_unused_3516_);
v___x_3471_ = v___x_3469_;
v_isShared_3472_ = v_isSharedCheck_3515_;
goto v_resetjp_3470_;
}
else
{
lean_dec(v___x_3469_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3515_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v_options_3473_; lean_object* v___x_3474_; uint8_t v___x_3475_; 
v_options_3473_ = lean_ctor_get(v___y_3462_, 2);
v___x_3474_ = l_Lean_Elab_async;
v___x_3475_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3473_, v___x_3474_);
if (v___x_3475_ == 0)
{
lean_object* v___x_3476_; lean_object* v_r_3477_; 
lean_del_object(v___x_3471_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3455_);
v___x_3476_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3460_, v___y_3464_);
lean_dec_ref(v___x_3476_);
v_r_3477_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3418_, v___y_3457_, v___y_3464_);
if (lean_obj_tag(v_r_3477_) == 0)
{
lean_object* v_a_3478_; lean_object* v___x_3480_; uint8_t v_isShared_3481_; uint8_t v_isSharedCheck_3487_; 
v_a_3478_ = lean_ctor_get(v_r_3477_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v_r_3477_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3480_ = v_r_3477_;
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
else
{
lean_inc(v_a_3478_);
lean_dec(v_r_3477_);
v___x_3480_ = lean_box(0);
v_isShared_3481_ = v_isSharedCheck_3487_;
goto v_resetjp_3479_;
}
v_resetjp_3479_:
{
lean_object* v___x_3483_; 
lean_inc(v_a_3478_);
if (v_isShared_3481_ == 0)
{
lean_ctor_set_tag(v___x_3480_, 1);
v___x_3483_ = v___x_3480_;
goto v_reusejp_3482_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3478_);
v___x_3483_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3482_;
}
v_reusejp_3482_:
{
lean_object* v___x_3484_; 
v___x_3484_ = lean_apply_2(v___y_3466_, v___x_3483_, lean_box(0));
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_dec_ref_known(v___x_3484_, 1);
v___y_3442_ = v___y_3464_;
v___y_3443_ = v___y_3458_;
v_a_3444_ = v_a_3478_;
goto v___jp_3441_;
}
else
{
lean_object* v_a_3485_; 
lean_dec(v_a_3478_);
v_a_3485_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_a_3485_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_3429_ = v___y_3464_;
v___y_3430_ = v___y_3458_;
v_a_3431_ = v_a_3485_;
goto v___jp_3428_;
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; 
v_a_3488_ = lean_ctor_get(v_r_3477_, 0);
lean_inc(v_a_3488_);
lean_dec_ref_known(v_r_3477_, 1);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_apply_2(v___y_3466_, v___x_3489_, lean_box(0));
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_dec_ref_known(v___x_3490_, 1);
v___y_3429_ = v___y_3464_;
v___y_3430_ = v___y_3458_;
v_a_3431_ = v_a_3488_;
goto v___jp_3428_;
}
else
{
lean_object* v_a_3491_; 
lean_dec(v_a_3488_);
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
lean_inc(v_a_3491_);
lean_dec_ref_known(v___x_3490_, 1);
v___y_3429_ = v___y_3464_;
v___y_3430_ = v___y_3458_;
v_a_3431_ = v_a_3491_;
goto v___jp_3428_;
}
}
}
else
{
lean_object* v___x_3492_; lean_object* v___x_3494_; 
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3458_);
lean_dec(v_decl_3418_);
v___x_3492_ = l_IO_CancelToken_new();
if (v_isShared_3472_ == 0)
{
lean_ctor_set_tag(v___x_3471_, 1);
lean_ctor_set(v___x_3471_, 0, v___x_3492_);
v___x_3494_ = v___x_3471_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3514_; 
v_reuseFailAlloc_3514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3514_, 0, v___x_3492_);
v___x_3494_ = v_reuseFailAlloc_3514_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3495_ = lean_unsigned_to_nat(0u);
v___x_3496_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3497_ = l_Lean_Name_toString(v___x_3496_, v___x_3419_);
lean_inc_ref(v___x_3494_);
v___x_3498_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3463_, v___x_3494_, v___x_3497_, v___y_3457_, v___y_3464_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v_checked_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
lean_inc(v_a_3499_);
lean_dec_ref_known(v___x_3498_, 1);
v_checked_3500_ = lean_ctor_get(v___y_3455_, 2);
lean_inc_ref(v_checked_3500_);
lean_dec_ref(v___y_3455_);
v___x_3501_ = lean_io_map_task(v_a_3499_, v_checked_3500_, v___x_3495_, v___y_3456_);
v___x_3502_ = lean_box(0);
v___x_3503_ = lean_box(2);
v___x_3504_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3504_, 0, v___x_3502_);
lean_ctor_set(v___x_3504_, 1, v___x_3503_);
lean_ctor_set(v___x_3504_, 2, v___x_3494_);
lean_ctor_set(v___x_3504_, 3, v___x_3501_);
v___x_3505_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3504_, v___y_3464_);
return v___x_3505_;
}
else
{
lean_object* v_a_3506_; lean_object* v___x_3508_; uint8_t v_isShared_3509_; uint8_t v_isSharedCheck_3513_; 
lean_dec_ref(v___x_3494_);
lean_dec_ref(v___y_3455_);
v_a_3506_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3513_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3513_ == 0)
{
v___x_3508_ = v___x_3498_;
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
else
{
lean_inc(v_a_3506_);
lean_dec(v___x_3498_);
v___x_3508_ = lean_box(0);
v_isShared_3509_ = v_isSharedCheck_3513_;
goto v_resetjp_3507_;
}
v_resetjp_3507_:
{
lean_object* v___x_3511_; 
if (v_isShared_3509_ == 0)
{
v___x_3511_ = v___x_3508_;
goto v_reusejp_3510_;
}
else
{
lean_object* v_reuseFailAlloc_3512_; 
v_reuseFailAlloc_3512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3512_, 0, v_a_3506_);
v___x_3511_ = v_reuseFailAlloc_3512_;
goto v_reusejp_3510_;
}
v_reusejp_3510_:
{
return v___x_3511_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3528_; 
lean_dec_ref(v___y_3466_);
lean_dec_ref(v___y_3463_);
lean_dec_ref(v___y_3460_);
lean_dec_ref(v___y_3458_);
lean_dec_ref(v___y_3455_);
lean_dec(v_decl_3418_);
v_a_3517_ = lean_ctor_get(v___x_3468_, 0);
v_isSharedCheck_3528_ = !lean_is_exclusive(v___x_3468_);
if (v_isSharedCheck_3528_ == 0)
{
v___x_3519_ = v___x_3468_;
v_isShared_3520_ = v_isSharedCheck_3528_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_a_3517_);
lean_dec(v___x_3468_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3528_;
goto v_resetjp_3518_;
}
v_resetjp_3518_:
{
lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3526_; 
v___x_3521_ = lean_io_error_to_string(v_a_3517_);
v___x_3522_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___x_3523_ = l_Lean_MessageData_ofFormat(v___x_3522_);
v___x_3524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___y_3461_);
lean_ctor_set(v___x_3524_, 1, v___x_3523_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set(v___x_3519_, 0, v___x_3524_);
v___x_3526_ = v___x_3519_;
goto v_reusejp_3525_;
}
else
{
lean_object* v_reuseFailAlloc_3527_; 
v_reuseFailAlloc_3527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3527_, 0, v___x_3524_);
v___x_3526_ = v_reuseFailAlloc_3527_;
goto v_reusejp_3525_;
}
v_reusejp_3525_:
{
return v___x_3526_;
}
}
}
}
v_resetjp_3531_:
{
lean_object* v_fst_3534_; lean_object* v_snd_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3660_; 
v_fst_3534_ = lean_ctor_get(v_snd_3529_, 0);
v_snd_3535_ = lean_ctor_get(v_snd_3529_, 1);
v_isSharedCheck_3660_ = !lean_is_exclusive(v_snd_3529_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3537_ = v_snd_3529_;
v_isShared_3538_ = v_isSharedCheck_3660_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_snd_3535_);
lean_inc(v_fst_3534_);
lean_dec(v_snd_3529_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3660_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___y_3540_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v_exportedInfo_x3f_3571_; lean_object* v___y_3572_; lean_object* v___y_3573_; lean_object* v___y_3583_; lean_object* v___y_3584_; lean_object* v___y_3587_; lean_object* v___y_3588_; lean_object* v___y_3591_; lean_object* v___y_3592_; uint8_t v___y_3593_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___x_3650_; lean_object* v_env_3651_; uint8_t v___x_3652_; 
v___x_3650_ = lean_st_ref_get(v___y_3426_);
v_env_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc_ref(v_env_3651_);
lean_dec(v___x_3650_);
v___x_3652_ = l_Lean_Environment_containsOnBranch(v_env_3651_, v_fst_3530_);
lean_dec_ref(v_env_3651_);
if (v___x_3652_ == 0)
{
lean_del_object(v___x_3532_);
v___y_3624_ = v___y_3425_;
v___y_3625_ = v___y_3426_;
goto v___jp_3623_;
}
else
{
lean_object* v___x_3653_; lean_object* v_env_3654_; lean_object* v___x_3655_; lean_object* v___x_3657_; 
lean_del_object(v___x_3537_);
lean_dec(v_snd_3535_);
lean_dec(v_fst_3534_);
lean_dec(v_exportedInfo_x3f_3424_);
lean_dec(v___x_3422_);
lean_dec_ref(v___x_3421_);
lean_dec(v_cls_3420_);
lean_dec(v_decl_3418_);
v___x_3653_ = lean_st_ref_get(v___y_3426_);
v_env_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc_ref(v_env_3654_);
lean_dec(v___x_3653_);
v___x_3655_ = lean_elab_environment_to_kernel_env(v_env_3654_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set_tag(v___x_3532_, 1);
lean_ctor_set(v___x_3532_, 1, v_fst_3530_);
lean_ctor_set(v___x_3532_, 0, v___x_3655_);
v___x_3657_ = v___x_3532_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3659_; 
v_reuseFailAlloc_3659_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3659_, 0, v___x_3655_);
lean_ctor_set(v_reuseFailAlloc_3659_, 1, v_fst_3530_);
v___x_3657_ = v_reuseFailAlloc_3659_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
lean_object* v___x_3658_; 
v___x_3658_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3657_, v___y_3425_, v___y_3426_);
return v___x_3658_;
}
}
v___jp_3539_:
{
lean_object* v_toCold_3545_; lean_object* v_ref_3546_; uint8_t v___x_3547_; uint8_t v___x_3548_; lean_object* v___x_3549_; 
v_toCold_3545_ = lean_ctor_get(v___y_3542_, 0);
v_ref_3546_ = lean_ctor_get(v___y_3542_, 2);
v___x_3547_ = 0;
v___x_3548_ = lean_unbox(v_snd_3535_);
lean_dec(v_snd_3535_);
lean_inc_ref(v___y_3543_);
v___x_3549_ = l_Lean_Environment_addConstAsync(v___y_3543_, v_fst_3530_, v___x_3548_, v___y_3544_, v___x_3547_, v___x_3419_);
if (lean_obj_tag(v___x_3549_) == 0)
{
lean_object* v_a_3550_; lean_object* v_mainEnv_3551_; lean_object* v_asyncEnv_3552_; lean_object* v___f_3553_; lean_object* v___f_3554_; lean_object* v___x_3555_; 
lean_del_object(v___x_3537_);
v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
lean_inc_n(v_a_3550_, 3);
lean_dec_ref_known(v___x_3549_, 1);
v_mainEnv_3551_ = lean_ctor_get(v_a_3550_, 0);
lean_inc_ref(v_mainEnv_3551_);
v_asyncEnv_3552_ = lean_ctor_get(v_a_3550_, 1);
lean_inc_ref_n(v_asyncEnv_3552_, 2);
lean_inc(v_ref_3546_);
lean_inc(v___y_3541_);
v___f_3553_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3553_, 0, v___y_3541_);
lean_closure_set(v___f_3553_, 1, v_a_3550_);
lean_closure_set(v___f_3553_, 2, v_ref_3546_);
lean_inc(v_decl_3418_);
v___f_3554_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3554_, 0, v_a_3550_);
lean_closure_set(v___f_3554_, 1, v_asyncEnv_3552_);
lean_closure_set(v___f_3554_, 2, v_decl_3418_);
v___x_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_fst_3534_);
if (lean_obj_tag(v___y_3540_) == 0)
{
lean_inc(v_ref_3546_);
lean_inc_ref(v___x_3555_);
v___y_3455_ = v___y_3543_;
v___y_3456_ = v___x_3547_;
v___y_3457_ = v___y_3542_;
v___y_3458_ = v_mainEnv_3551_;
v___y_3459_ = v___x_3555_;
v___y_3460_ = v_asyncEnv_3552_;
v___y_3461_ = v_ref_3546_;
v___y_3462_ = v_toCold_3545_;
v___y_3463_ = v___f_3554_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v_a_3550_;
v___y_3466_ = v___f_3553_;
v___y_3467_ = v___x_3555_;
goto v___jp_3454_;
}
else
{
lean_inc(v_ref_3546_);
v___y_3455_ = v___y_3543_;
v___y_3456_ = v___x_3547_;
v___y_3457_ = v___y_3542_;
v___y_3458_ = v_mainEnv_3551_;
v___y_3459_ = v___x_3555_;
v___y_3460_ = v_asyncEnv_3552_;
v___y_3461_ = v_ref_3546_;
v___y_3462_ = v_toCold_3545_;
v___y_3463_ = v___f_3554_;
v___y_3464_ = v___y_3541_;
v___y_3465_ = v_a_3550_;
v___y_3466_ = v___f_3553_;
v___y_3467_ = v___y_3540_;
goto v___jp_3454_;
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3569_; 
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3540_);
lean_dec(v_fst_3534_);
lean_dec(v_decl_3418_);
v_a_3556_ = lean_ctor_get(v___x_3549_, 0);
v_isSharedCheck_3569_ = !lean_is_exclusive(v___x_3549_);
if (v_isSharedCheck_3569_ == 0)
{
v___x_3558_ = v___x_3549_;
v_isShared_3559_ = v_isSharedCheck_3569_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3549_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3569_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3562_; lean_object* v___x_3564_; 
v___x_3560_ = lean_io_error_to_string(v_a_3556_);
v___x_3561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3561_, 0, v___x_3560_);
v___x_3562_ = l_Lean_MessageData_ofFormat(v___x_3561_);
lean_inc(v_ref_3546_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 1, v___x_3562_);
lean_ctor_set(v___x_3537_, 0, v_ref_3546_);
v___x_3564_ = v___x_3537_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v_ref_3546_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v___x_3562_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
lean_object* v___x_3566_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 0, v___x_3564_);
v___x_3566_ = v___x_3558_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v___x_3564_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
}
v___jp_3570_:
{
lean_object* v___x_3574_; 
v___x_3574_ = lean_st_ref_get(v___y_3573_);
if (lean_obj_tag(v_exportedInfo_x3f_3571_) == 0)
{
lean_object* v_env_3575_; lean_object* v___x_3576_; 
v_env_3575_ = lean_ctor_get(v___x_3574_, 0);
lean_inc_ref(v_env_3575_);
lean_dec(v___x_3574_);
v___x_3576_ = lean_box(0);
v___y_3540_ = v_exportedInfo_x3f_3571_;
v___y_3541_ = v___y_3573_;
v___y_3542_ = v___y_3572_;
v___y_3543_ = v_env_3575_;
v___y_3544_ = v___x_3576_;
goto v___jp_3539_;
}
else
{
lean_object* v_env_3577_; lean_object* v_val_3578_; uint8_t v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v_env_3577_ = lean_ctor_get(v___x_3574_, 0);
lean_inc_ref(v_env_3577_);
lean_dec(v___x_3574_);
v_val_3578_ = lean_ctor_get(v_exportedInfo_x3f_3571_, 0);
v___x_3579_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3578_);
v___x_3580_ = lean_box(v___x_3579_);
v___x_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
v___y_3540_ = v_exportedInfo_x3f_3571_;
v___y_3541_ = v___y_3573_;
v___y_3542_ = v___y_3572_;
v___y_3543_ = v_env_3577_;
v___y_3544_ = v___x_3581_;
goto v___jp_3539_;
}
}
v___jp_3582_:
{
lean_object* v___x_3585_; 
lean_inc(v_fst_3534_);
v___x_3585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3585_, 0, v_fst_3534_);
v_exportedInfo_x3f_3571_ = v___x_3585_;
v___y_3572_ = v___y_3583_;
v___y_3573_ = v___y_3584_;
goto v___jp_3570_;
}
v___jp_3586_:
{
lean_object* v___x_3589_; 
lean_inc(v_fst_3534_);
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v_fst_3534_);
v_exportedInfo_x3f_3571_ = v___x_3589_;
v___y_3572_ = v___y_3587_;
v___y_3573_ = v___y_3588_;
goto v___jp_3570_;
}
v___jp_3590_:
{
if (v___y_3593_ == 0)
{
lean_object* v_toCold_3594_; lean_object* v_options_3595_; uint8_t v_hasTrace_3596_; 
lean_dec(v_exportedInfo_x3f_3424_);
lean_dec_ref(v___x_3421_);
v_toCold_3594_ = lean_ctor_get(v___y_3591_, 0);
v_options_3595_ = lean_ctor_get(v_toCold_3594_, 2);
v_hasTrace_3596_ = lean_ctor_get_uint8(v_options_3595_, sizeof(void*)*1);
if (v_hasTrace_3596_ == 0)
{
lean_dec(v_cls_3420_);
v___y_3583_ = v___y_3591_;
v___y_3584_ = v___y_3592_;
goto v___jp_3582_;
}
else
{
lean_object* v_inheritedTraceOptions_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; uint8_t v___x_3600_; 
v_inheritedTraceOptions_3597_ = lean_ctor_get(v_toCold_3594_, 11);
v___x_3598_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3420_);
v___x_3599_ = l_Lean_Name_append(v___x_3598_, v_cls_3420_);
v___x_3600_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3597_, v_options_3595_, v___x_3599_);
lean_dec(v___x_3599_);
if (v___x_3600_ == 0)
{
lean_dec(v_cls_3420_);
v___y_3583_ = v___y_3591_;
v___y_3584_ = v___y_3592_;
goto v___jp_3582_;
}
else
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3602_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3420_, v___x_3601_, v___y_3591_, v___y_3592_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_dec_ref_known(v___x_3602_, 1);
v___y_3583_ = v___y_3591_;
v___y_3584_ = v___y_3592_;
goto v___jp_3582_;
}
else
{
lean_del_object(v___x_3537_);
lean_dec(v_snd_3535_);
lean_dec(v_fst_3534_);
lean_dec(v_fst_3530_);
lean_dec(v_decl_3418_);
return v___x_3602_;
}
}
}
}
else
{
lean_object* v___x_3603_; lean_object* v_env_3604_; lean_object* v_nextMacroScope_3605_; lean_object* v_ngen_3606_; lean_object* v_auxDeclNGen_3607_; lean_object* v_traceState_3608_; lean_object* v_messages_3609_; lean_object* v_infoState_3610_; lean_object* v_snapshotTasks_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3621_; 
lean_dec(v_cls_3420_);
v___x_3603_ = lean_st_ref_take(v___y_3592_);
v_env_3604_ = lean_ctor_get(v___x_3603_, 0);
v_nextMacroScope_3605_ = lean_ctor_get(v___x_3603_, 1);
v_ngen_3606_ = lean_ctor_get(v___x_3603_, 2);
v_auxDeclNGen_3607_ = lean_ctor_get(v___x_3603_, 3);
v_traceState_3608_ = lean_ctor_get(v___x_3603_, 4);
v_messages_3609_ = lean_ctor_get(v___x_3603_, 6);
v_infoState_3610_ = lean_ctor_get(v___x_3603_, 7);
v_snapshotTasks_3611_ = lean_ctor_get(v___x_3603_, 8);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3603_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v___x_3603_, 5);
lean_dec(v_unused_3622_);
v___x_3613_ = v___x_3603_;
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_snapshotTasks_3611_);
lean_inc(v_infoState_3610_);
lean_inc(v_messages_3609_);
lean_inc(v_traceState_3608_);
lean_inc(v_auxDeclNGen_3607_);
lean_inc(v_ngen_3606_);
lean_inc(v_nextMacroScope_3605_);
lean_inc(v_env_3604_);
lean_dec(v___x_3603_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3621_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3618_; 
v___x_3615_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3535_);
lean_inc(v_fst_3530_);
v___x_3616_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3615_, v_env_3604_, v_fst_3530_, v_snd_3535_);
if (v_isShared_3614_ == 0)
{
lean_ctor_set(v___x_3613_, 5, v___x_3421_);
lean_ctor_set(v___x_3613_, 0, v___x_3616_);
v___x_3618_ = v___x_3613_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3616_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_nextMacroScope_3605_);
lean_ctor_set(v_reuseFailAlloc_3620_, 2, v_ngen_3606_);
lean_ctor_set(v_reuseFailAlloc_3620_, 3, v_auxDeclNGen_3607_);
lean_ctor_set(v_reuseFailAlloc_3620_, 4, v_traceState_3608_);
lean_ctor_set(v_reuseFailAlloc_3620_, 5, v___x_3421_);
lean_ctor_set(v_reuseFailAlloc_3620_, 6, v_messages_3609_);
lean_ctor_set(v_reuseFailAlloc_3620_, 7, v_infoState_3610_);
lean_ctor_set(v_reuseFailAlloc_3620_, 8, v_snapshotTasks_3611_);
v___x_3618_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_st_ref_put(v___y_3592_, v___x_3618_);
v_exportedInfo_x3f_3571_ = v_exportedInfo_x3f_3424_;
v___y_3572_ = v___y_3591_;
v___y_3573_ = v___y_3592_;
goto v___jp_3570_;
}
}
}
}
v___jp_3623_:
{
lean_object* v___x_3626_; uint8_t v___x_3627_; 
lean_inc(v_decl_3418_);
v___x_3626_ = l_Lean_Declaration_getTopLevelNames(v_decl_3418_);
v___x_3627_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3626_);
lean_dec(v___x_3626_);
if (v___x_3627_ == 0)
{
lean_dec(v___x_3422_);
if (lean_obj_tag(v_exportedInfo_x3f_3424_) == 0)
{
v___y_3591_ = v___y_3624_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v___x_3627_;
goto v___jp_3590_;
}
else
{
v___y_3591_ = v___y_3624_;
v___y_3592_ = v___y_3625_;
v___y_3593_ = v___x_3419_;
goto v___jp_3590_;
}
}
else
{
lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v_a_3630_; uint8_t v___x_3631_; 
lean_dec(v_exportedInfo_x3f_3424_);
lean_dec_ref(v___x_3421_);
v___x_3628_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3629_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3628_, v___y_3624_);
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
lean_inc(v_a_3630_);
lean_dec_ref(v___x_3629_);
v___x_3631_ = lean_unbox(v_a_3630_);
lean_dec(v_a_3630_);
if (v___x_3631_ == 0)
{
lean_object* v_toCold_3632_; lean_object* v_options_3633_; uint8_t v_hasTrace_3634_; 
v_toCold_3632_ = lean_ctor_get(v___y_3624_, 0);
v_options_3633_ = lean_ctor_get(v_toCold_3632_, 2);
v_hasTrace_3634_ = lean_ctor_get_uint8(v_options_3633_, sizeof(void*)*1);
if (v_hasTrace_3634_ == 0)
{
lean_dec(v_cls_3420_);
v_exportedInfo_x3f_3571_ = v___x_3422_;
v___y_3572_ = v___y_3624_;
v___y_3573_ = v___y_3625_;
goto v___jp_3570_;
}
else
{
lean_object* v_inheritedTraceOptions_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; uint8_t v___x_3638_; 
v_inheritedTraceOptions_3635_ = lean_ctor_get(v_toCold_3632_, 11);
v___x_3636_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3420_);
v___x_3637_ = l_Lean_Name_append(v___x_3636_, v_cls_3420_);
v___x_3638_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3635_, v_options_3633_, v___x_3637_);
lean_dec(v___x_3637_);
if (v___x_3638_ == 0)
{
lean_dec(v_cls_3420_);
v_exportedInfo_x3f_3571_ = v___x_3422_;
v___y_3572_ = v___y_3624_;
v___y_3573_ = v___y_3625_;
goto v___jp_3570_;
}
else
{
lean_object* v___x_3639_; lean_object* v___x_3640_; 
v___x_3639_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3640_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3420_, v___x_3639_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_dec_ref_known(v___x_3640_, 1);
v_exportedInfo_x3f_3571_ = v___x_3422_;
v___y_3572_ = v___y_3624_;
v___y_3573_ = v___y_3625_;
goto v___jp_3570_;
}
else
{
lean_del_object(v___x_3537_);
lean_dec(v_snd_3535_);
lean_dec(v_fst_3534_);
lean_dec(v_fst_3530_);
lean_dec(v___x_3422_);
lean_dec(v_decl_3418_);
return v___x_3640_;
}
}
}
}
else
{
lean_object* v_toCold_3641_; lean_object* v_options_3642_; uint8_t v_hasTrace_3643_; 
lean_dec(v___x_3422_);
v_toCold_3641_ = lean_ctor_get(v___y_3624_, 0);
v_options_3642_ = lean_ctor_get(v_toCold_3641_, 2);
v_hasTrace_3643_ = lean_ctor_get_uint8(v_options_3642_, sizeof(void*)*1);
if (v_hasTrace_3643_ == 0)
{
lean_dec(v_cls_3420_);
v___y_3587_ = v___y_3624_;
v___y_3588_ = v___y_3625_;
goto v___jp_3586_;
}
else
{
lean_object* v_inheritedTraceOptions_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; uint8_t v___x_3647_; 
v_inheritedTraceOptions_3644_ = lean_ctor_get(v_toCold_3641_, 11);
v___x_3645_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3420_);
v___x_3646_ = l_Lean_Name_append(v___x_3645_, v_cls_3420_);
v___x_3647_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3644_, v_options_3642_, v___x_3646_);
lean_dec(v___x_3646_);
if (v___x_3647_ == 0)
{
lean_dec(v_cls_3420_);
v___y_3587_ = v___y_3624_;
v___y_3588_ = v___y_3625_;
goto v___jp_3586_;
}
else
{
lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3648_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3649_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3420_, v___x_3648_, v___y_3624_, v___y_3625_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_dec_ref_known(v___x_3649_, 1);
v___y_3587_ = v___y_3624_;
v___y_3588_ = v___y_3625_;
goto v___jp_3586_;
}
else
{
lean_del_object(v___x_3537_);
lean_dec(v_snd_3535_);
lean_dec(v_fst_3534_);
lean_dec(v_fst_3530_);
lean_dec(v_decl_3418_);
return v___x_3649_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3662_, lean_object* v___x_3663_, lean_object* v_cls_3664_, lean_object* v___x_3665_, lean_object* v___x_3666_, lean_object* v_____x_3667_, lean_object* v_exportedInfo_x3f_3668_, lean_object* v___y_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_){
_start:
{
uint8_t v___x_53892__boxed_3672_; lean_object* v_res_3673_; 
v___x_53892__boxed_3672_ = lean_unbox(v___x_3663_);
v_res_3673_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3662_, v___x_53892__boxed_3672_, v_cls_3664_, v___x_3665_, v___x_3666_, v_____x_3667_, v_exportedInfo_x3f_3668_, v___y_3669_, v___y_3670_);
lean_dec(v___y_3670_);
lean_dec_ref(v___y_3669_);
return v_res_3673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3674_, uint8_t v_forceExpose_3675_, uint8_t v___x_3676_, lean_object* v___x_3677_, lean_object* v_cls_3678_, lean_object* v_defn_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_exportedInfo_x3f_3684_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3696_; lean_object* v___y_3697_; lean_object* v___y_3698_; uint8_t v___y_3699_; lean_object* v___x_3703_; lean_object* v_env_3704_; lean_object* v___x_3705_; 
v___x_3703_ = lean_st_ref_get(v___y_3681_);
v_env_3704_ = lean_ctor_get(v___x_3703_, 0);
lean_inc_ref(v_env_3704_);
lean_dec(v___x_3703_);
v___x_3705_ = lean_st_ref_get(v___y_3681_);
if (v_forceExpose_3675_ == 0)
{
if (v___x_3676_ == 0)
{
lean_dec(v___x_3705_);
lean_dec_ref(v_env_3704_);
lean_dec(v_cls_3678_);
v_exportedInfo_x3f_3684_ = v___x_3677_;
v___y_3685_ = v___y_3680_;
v___y_3686_ = v___y_3681_;
goto v___jp_3683_;
}
else
{
lean_object* v_env_3706_; lean_object* v___x_3707_; uint8_t v_isModule_3708_; 
v_env_3706_ = lean_ctor_get(v___x_3705_, 0);
lean_inc_ref(v_env_3706_);
lean_dec(v___x_3705_);
v___x_3707_ = l_Lean_Environment_header(v_env_3704_);
lean_dec_ref(v_env_3704_);
v_isModule_3708_ = lean_ctor_get_uint8(v___x_3707_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3707_);
if (v_isModule_3708_ == 0)
{
lean_dec_ref(v_env_3706_);
lean_dec(v_cls_3678_);
v_exportedInfo_x3f_3684_ = v___x_3677_;
v___y_3685_ = v___y_3680_;
v___y_3686_ = v___y_3681_;
goto v___jp_3683_;
}
else
{
uint8_t v_isExporting_3709_; lean_object* v___y_3711_; lean_object* v___y_3712_; 
v_isExporting_3709_ = lean_ctor_get_uint8(v_env_3706_, sizeof(void*)*8);
lean_dec_ref(v_env_3706_);
if (v_isExporting_3709_ == 0)
{
lean_object* v_toCold_3717_; lean_object* v_options_3718_; uint8_t v_hasTrace_3719_; 
lean_dec(v___x_3677_);
v_toCold_3717_ = lean_ctor_get(v___y_3680_, 0);
v_options_3718_ = lean_ctor_get(v_toCold_3717_, 2);
v_hasTrace_3719_ = lean_ctor_get_uint8(v_options_3718_, sizeof(void*)*1);
if (v_hasTrace_3719_ == 0)
{
lean_dec(v_cls_3678_);
v___y_3711_ = v___y_3680_;
v___y_3712_ = v___y_3681_;
goto v___jp_3710_;
}
else
{
lean_object* v_inheritedTraceOptions_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; uint8_t v___x_3723_; 
v_inheritedTraceOptions_3720_ = lean_ctor_get(v_toCold_3717_, 11);
v___x_3721_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3678_);
v___x_3722_ = l_Lean_Name_append(v___x_3721_, v_cls_3678_);
v___x_3723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3720_, v_options_3718_, v___x_3722_);
lean_dec(v___x_3722_);
if (v___x_3723_ == 0)
{
lean_dec(v_cls_3678_);
v___y_3711_ = v___y_3680_;
v___y_3712_ = v___y_3681_;
goto v___jp_3710_;
}
else
{
lean_object* v_toConstantVal_3724_; lean_object* v_name_3725_; lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; 
v_toConstantVal_3724_ = lean_ctor_get(v_defn_3679_, 0);
v_name_3725_ = lean_ctor_get(v_toConstantVal_3724_, 0);
v___x_3726_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3725_);
v___x_3727_ = l_Lean_MessageData_ofName(v_name_3725_);
v___x_3728_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3728_, 0, v___x_3726_);
lean_ctor_set(v___x_3728_, 1, v___x_3727_);
v___x_3729_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3730_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3730_, 0, v___x_3728_);
lean_ctor_set(v___x_3730_, 1, v___x_3729_);
v___x_3731_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3678_, v___x_3730_, v___y_3680_, v___y_3681_);
if (lean_obj_tag(v___x_3731_) == 0)
{
lean_dec_ref_known(v___x_3731_, 1);
v___y_3711_ = v___y_3680_;
v___y_3712_ = v___y_3681_;
goto v___jp_3710_;
}
else
{
lean_dec_ref(v_defn_3679_);
lean_dec_ref(v___f_3674_);
return v___x_3731_;
}
}
}
}
else
{
lean_dec(v_cls_3678_);
v_exportedInfo_x3f_3684_ = v___x_3677_;
v___y_3685_ = v___y_3680_;
v___y_3686_ = v___y_3681_;
goto v___jp_3683_;
}
v___jp_3710_:
{
lean_object* v_toConstantVal_3713_; uint8_t v_safety_3714_; uint8_t v___x_3715_; uint8_t v___x_3716_; 
v_toConstantVal_3713_ = lean_ctor_get(v_defn_3679_, 0);
v_safety_3714_ = lean_ctor_get_uint8(v_defn_3679_, sizeof(void*)*4);
v___x_3715_ = 1;
v___x_3716_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3714_, v___x_3715_);
if (v___x_3716_ == 0)
{
lean_inc_ref(v_toConstantVal_3713_);
v___y_3696_ = v_toConstantVal_3713_;
v___y_3697_ = v___y_3711_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v_isModule_3708_;
goto v___jp_3695_;
}
else
{
lean_inc_ref(v_toConstantVal_3713_);
v___y_3696_ = v_toConstantVal_3713_;
v___y_3697_ = v___y_3711_;
v___y_3698_ = v___y_3712_;
v___y_3699_ = v_isExporting_3709_;
goto v___jp_3695_;
}
}
}
}
}
else
{
lean_dec(v___x_3705_);
lean_dec_ref(v_env_3704_);
lean_dec(v_cls_3678_);
v_exportedInfo_x3f_3684_ = v___x_3677_;
v___y_3685_ = v___y_3680_;
v___y_3686_ = v___y_3681_;
goto v___jp_3683_;
}
v___jp_3683_:
{
lean_object* v_toConstantVal_3687_; lean_object* v_name_3688_; lean_object* v___x_3689_; uint8_t v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; lean_object* v___x_3694_; 
v_toConstantVal_3687_ = lean_ctor_get(v_defn_3679_, 0);
v_name_3688_ = lean_ctor_get(v_toConstantVal_3687_, 0);
lean_inc(v_name_3688_);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_defn_3679_);
v___x_3690_ = 0;
v___x_3691_ = lean_box(v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3689_);
lean_ctor_set(v___x_3692_, 1, v___x_3691_);
v___x_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3693_, 0, v_name_3688_);
lean_ctor_set(v___x_3693_, 1, v___x_3692_);
lean_inc(v___y_3686_);
lean_inc_ref(v___y_3685_);
v___x_3694_ = lean_apply_5(v___f_3674_, v___x_3693_, v_exportedInfo_x3f_3684_, v___y_3685_, v___y_3686_, lean_box(0));
return v___x_3694_;
}
v___jp_3695_:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3700_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3700_, 0, v___y_3696_);
lean_ctor_set_uint8(v___x_3700_, sizeof(void*)*1, v___y_3699_);
v___x_3701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3700_);
v___x_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3702_, 0, v___x_3701_);
v_exportedInfo_x3f_3684_ = v___x_3702_;
v___y_3685_ = v___y_3697_;
v___y_3686_ = v___y_3698_;
goto v___jp_3683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3732_, lean_object* v_forceExpose_3733_, lean_object* v___x_3734_, lean_object* v___x_3735_, lean_object* v_cls_3736_, lean_object* v_defn_3737_, lean_object* v___y_3738_, lean_object* v___y_3739_, lean_object* v___y_3740_){
_start:
{
uint8_t v_forceExpose_boxed_3741_; uint8_t v___x_54367__boxed_3742_; lean_object* v_res_3743_; 
v_forceExpose_boxed_3741_ = lean_unbox(v_forceExpose_3733_);
v___x_54367__boxed_3742_ = lean_unbox(v___x_3734_);
v_res_3743_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3732_, v_forceExpose_boxed_3741_, v___x_54367__boxed_3742_, v___x_3735_, v_cls_3736_, v_defn_3737_, v___y_3738_, v___y_3739_);
lean_dec(v___y_3739_);
lean_dec_ref(v___y_3738_);
return v_res_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3744_, lean_object* v___f_3745_, lean_object* v_____r_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_){
_start:
{
lean_object* v_toConstantVal_3750_; uint8_t v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v_toConstantVal_3750_ = lean_ctor_get(v_val_3744_, 0);
v___x_3751_ = 0;
lean_inc_ref(v_toConstantVal_3750_);
v___x_3752_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3752_, 0, v_toConstantVal_3750_);
lean_ctor_set_uint8(v___x_3752_, sizeof(void*)*1, v___x_3751_);
v___x_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
v___x_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3753_);
v___x_3755_ = lean_box(0);
lean_inc(v___y_3748_);
lean_inc_ref(v___y_3747_);
v___x_3756_ = lean_apply_5(v___f_3745_, v___x_3755_, v___x_3754_, v___y_3747_, v___y_3748_, lean_box(0));
return v___x_3756_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3757_, lean_object* v___f_3758_, lean_object* v_____r_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_, lean_object* v___y_3762_){
_start:
{
lean_object* v_res_3763_; 
v_res_3763_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3757_, v___f_3758_, v_____r_3759_, v___y_3760_, v___y_3761_);
lean_dec(v___y_3761_);
lean_dec_ref(v___y_3760_);
lean_dec_ref(v_val_3757_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3764_, lean_object* v_x_3765_){
_start:
{
if (lean_obj_tag(v_x_3765_) == 0)
{
return v_x_3764_;
}
else
{
lean_object* v_head_3766_; lean_object* v_tail_3767_; lean_object* v___x_3768_; 
v_head_3766_ = lean_ctor_get(v_x_3765_, 0);
lean_inc(v_head_3766_);
v_tail_3767_ = lean_ctor_get(v_x_3765_, 1);
lean_inc(v_tail_3767_);
lean_dec_ref_known(v_x_3765_, 2);
v___x_3768_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3764_, v_head_3766_);
v_x_3764_ = v___x_3768_;
v_x_3765_ = v_tail_3767_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; 
v_cls_3770_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3771_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3772_ = l_Lean_Name_append(v___x_3771_, v_cls_3770_);
return v___x_3772_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3774_; lean_object* v___x_3775_; 
v___x_3774_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3775_ = l_Lean_stringToMessageData(v___x_3774_);
return v___x_3775_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; 
v___x_3777_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3778_ = l_Lean_stringToMessageData(v___x_3777_);
return v___x_3778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3779_, uint8_t v_forceExpose_3780_, lean_object* v_a_3781_, lean_object* v_a_3782_){
_start:
{
lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v_a_3787_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v_a_3800_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_a_3813_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v_a_3826_; lean_object* v_toCold_3836_; lean_object* v_options_3837_; lean_object* v_inheritedTraceOptions_3838_; uint8_t v_hasTrace_3839_; lean_object* v___y_3841_; lean_object* v___y_3842_; lean_object* v___y_3843_; lean_object* v___y_3844_; lean_object* v___y_3845_; lean_object* v___y_3846_; uint8_t v___y_3847_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; lean_object* v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3916_; lean_object* v___y_3917_; lean_object* v___y_3918_; lean_object* v___y_3919_; uint8_t v___y_3920_; lean_object* v___y_3921_; lean_object* v___y_3922_; lean_object* v___y_3923_; uint8_t v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v_exportedInfo_x3f_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3962_; lean_object* v___y_3963_; lean_object* v___y_3964_; lean_object* v___y_3965_; lean_object* v___y_3966_; uint8_t v___y_3969_; lean_object* v___y_3970_; lean_object* v___y_3971_; lean_object* v___y_3972_; lean_object* v___y_3973_; lean_object* v_cls_3975_; lean_object* v___y_3977_; lean_object* v_options_3978_; lean_object* v_inheritedTraceOptions_3979_; lean_object* v___y_3980_; 
v_toCold_3836_ = lean_ctor_get(v_a_3781_, 0);
v_options_3837_ = lean_ctor_get(v_toCold_3836_, 2);
v_inheritedTraceOptions_3838_ = lean_ctor_get(v_toCold_3836_, 11);
v_hasTrace_3839_ = lean_ctor_get_uint8(v_options_3837_, sizeof(void*)*1);
v_cls_3975_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3839_ == 0)
{
lean_object* v___x_3987_; lean_object* v_env_3988_; lean_object* v_nextMacroScope_3989_; lean_object* v_ngen_3990_; lean_object* v_auxDeclNGen_3991_; lean_object* v_traceState_3992_; lean_object* v_messages_3993_; lean_object* v_infoState_3994_; lean_object* v_snapshotTasks_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4197_; 
v___x_3987_ = lean_st_ref_take(v_a_3782_);
v_env_3988_ = lean_ctor_get(v___x_3987_, 0);
v_nextMacroScope_3989_ = lean_ctor_get(v___x_3987_, 1);
v_ngen_3990_ = lean_ctor_get(v___x_3987_, 2);
v_auxDeclNGen_3991_ = lean_ctor_get(v___x_3987_, 3);
v_traceState_3992_ = lean_ctor_get(v___x_3987_, 4);
v_messages_3993_ = lean_ctor_get(v___x_3987_, 6);
v_infoState_3994_ = lean_ctor_get(v___x_3987_, 7);
v_snapshotTasks_3995_ = lean_ctor_get(v___x_3987_, 8);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_3987_);
if (v_isSharedCheck_4197_ == 0)
{
lean_object* v_unused_4198_; 
v_unused_4198_ = lean_ctor_get(v___x_3987_, 5);
lean_dec(v_unused_4198_);
v___x_3997_ = v___x_3987_;
v_isShared_3998_ = v_isSharedCheck_4197_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_snapshotTasks_3995_);
lean_inc(v_infoState_3994_);
lean_inc(v_messages_3993_);
lean_inc(v_traceState_3992_);
lean_inc(v_auxDeclNGen_3991_);
lean_inc(v_ngen_3990_);
lean_inc(v_nextMacroScope_3989_);
lean_inc(v_env_3988_);
lean_dec(v___x_3987_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4197_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; lean_object* v___x_4000_; lean_object* v___x_4001_; uint8_t v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; lean_object* v___y_4008_; lean_object* v___x_4031_; 
lean_inc(v_decl_3779_);
v___x_3999_ = l_Lean_Declaration_getNames(v_decl_3779_);
v___x_4000_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3988_, v___x_3999_);
v___x_4001_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 5, v___x_4001_);
lean_ctor_set(v___x_3997_, 0, v___x_4000_);
v___x_4031_ = v___x_3997_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v___x_4000_);
lean_ctor_set(v_reuseFailAlloc_4196_, 1, v_nextMacroScope_3989_);
lean_ctor_set(v_reuseFailAlloc_4196_, 2, v_ngen_3990_);
lean_ctor_set(v_reuseFailAlloc_4196_, 3, v_auxDeclNGen_3991_);
lean_ctor_set(v_reuseFailAlloc_4196_, 4, v_traceState_3992_);
lean_ctor_set(v_reuseFailAlloc_4196_, 5, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4196_, 6, v_messages_3993_);
lean_ctor_set(v_reuseFailAlloc_4196_, 7, v_infoState_3994_);
lean_ctor_set(v_reuseFailAlloc_4196_, 8, v_snapshotTasks_3995_);
v___x_4031_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4030_;
}
v___jp_4002_:
{
lean_object* v___x_4009_; lean_object* v_env_4010_; lean_object* v_nextMacroScope_4011_; lean_object* v_ngen_4012_; lean_object* v_auxDeclNGen_4013_; lean_object* v_traceState_4014_; lean_object* v_messages_4015_; lean_object* v_infoState_4016_; lean_object* v_snapshotTasks_4017_; lean_object* v___x_4019_; uint8_t v_isShared_4020_; uint8_t v_isSharedCheck_4028_; 
v___x_4009_ = lean_st_ref_take(v___y_4006_);
v_env_4010_ = lean_ctor_get(v___x_4009_, 0);
v_nextMacroScope_4011_ = lean_ctor_get(v___x_4009_, 1);
v_ngen_4012_ = lean_ctor_get(v___x_4009_, 2);
v_auxDeclNGen_4013_ = lean_ctor_get(v___x_4009_, 3);
v_traceState_4014_ = lean_ctor_get(v___x_4009_, 4);
v_messages_4015_ = lean_ctor_get(v___x_4009_, 6);
v_infoState_4016_ = lean_ctor_get(v___x_4009_, 7);
v_snapshotTasks_4017_ = lean_ctor_get(v___x_4009_, 8);
v_isSharedCheck_4028_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4028_ == 0)
{
lean_object* v_unused_4029_; 
v_unused_4029_ = lean_ctor_get(v___x_4009_, 5);
lean_dec(v_unused_4029_);
v___x_4019_ = v___x_4009_;
v_isShared_4020_ = v_isSharedCheck_4028_;
goto v_resetjp_4018_;
}
else
{
lean_inc(v_snapshotTasks_4017_);
lean_inc(v_infoState_4016_);
lean_inc(v_messages_4015_);
lean_inc(v_traceState_4014_);
lean_inc(v_auxDeclNGen_4013_);
lean_inc(v_ngen_4012_);
lean_inc(v_nextMacroScope_4011_);
lean_inc(v_env_4010_);
lean_dec(v___x_4009_);
v___x_4019_ = lean_box(0);
v_isShared_4020_ = v_isSharedCheck_4028_;
goto v_resetjp_4018_;
}
v_resetjp_4018_:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4025_; 
v___x_4021_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4022_ = lean_box(v___y_4003_);
lean_inc(v___y_4008_);
v___x_4023_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4021_, v_env_4010_, v___y_4008_, v___x_4022_);
if (v_isShared_4020_ == 0)
{
lean_ctor_set(v___x_4019_, 5, v___x_4001_);
lean_ctor_set(v___x_4019_, 0, v___x_4023_);
v___x_4025_ = v___x_4019_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4023_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_nextMacroScope_4011_);
lean_ctor_set(v_reuseFailAlloc_4027_, 2, v_ngen_4012_);
lean_ctor_set(v_reuseFailAlloc_4027_, 3, v_auxDeclNGen_4013_);
lean_ctor_set(v_reuseFailAlloc_4027_, 4, v_traceState_4014_);
lean_ctor_set(v_reuseFailAlloc_4027_, 5, v___x_4001_);
lean_ctor_set(v_reuseFailAlloc_4027_, 6, v_messages_4015_);
lean_ctor_set(v_reuseFailAlloc_4027_, 7, v_infoState_4016_);
lean_ctor_set(v_reuseFailAlloc_4027_, 8, v_snapshotTasks_4017_);
v___x_4025_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
lean_object* v___x_4026_; 
v___x_4026_ = lean_st_ref_put(v___y_4006_, v___x_4025_);
v___y_3947_ = v___y_4003_;
v___y_3948_ = v___y_4005_;
v___y_3949_ = v___y_4008_;
v_exportedInfo_x3f_3950_ = v___y_4007_;
v___y_3951_ = v___y_4004_;
v___y_3952_ = v___y_4006_;
goto v___jp_3946_;
}
}
}
v_reusejp_4030_:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; lean_object* v_fst_4072_; lean_object* v_fst_4073_; uint8_t v_snd_4074_; lean_object* v_exportedInfo_x3f_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4087_; lean_object* v_exportedInfo_x3f_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; uint8_t v___y_4105_; lean_object* v___y_4106_; lean_object* v_toConstantVal_4107_; uint8_t v_safety_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; lean_object* v_defn_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; 
v___x_4032_ = lean_st_ref_put(v_a_3782_, v___x_4031_);
v___x_4033_ = lean_box(0);
switch(lean_obj_tag(v_decl_3779_))
{
case 2:
{
lean_object* v_val_4146_; lean_object* v_exportedInfo_x3f_4148_; lean_object* v___y_4149_; lean_object* v___y_4150_; lean_object* v___x_4155_; 
v_val_4146_ = lean_ctor_get(v_decl_3779_, 0);
v___x_4155_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4156_; lean_object* v___x_4157_; uint8_t v_isModule_4158_; 
v_env_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc_ref(v_env_4156_);
lean_dec(v___x_4155_);
v___x_4157_ = l_Lean_Environment_header(v_env_4156_);
lean_dec_ref(v_env_4156_);
v_isModule_4158_ = lean_ctor_get_uint8(v___x_4157_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4157_);
if (v_isModule_4158_ == 0)
{
v_exportedInfo_x3f_4148_ = v___x_4033_;
v___y_4149_ = v_a_3781_;
v___y_4150_ = v_a_3782_;
goto v___jp_4147_;
}
else
{
lean_object* v_toConstantVal_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_toConstantVal_4159_ = lean_ctor_get(v_val_4146_, 0);
lean_inc_ref(v_toConstantVal_4159_);
v___x_4160_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4160_, 0, v_toConstantVal_4159_);
lean_ctor_set_uint8(v___x_4160_, sizeof(void*)*1, v_hasTrace_3839_);
v___x_4161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4160_);
v___x_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4162_, 0, v___x_4161_);
v_exportedInfo_x3f_4148_ = v___x_4162_;
v___y_4149_ = v_a_3781_;
v___y_4150_ = v_a_3782_;
goto v___jp_4147_;
}
}
else
{
lean_dec(v___x_4155_);
v_exportedInfo_x3f_4148_ = v___x_4033_;
v___y_4149_ = v_a_3781_;
v___y_4150_ = v_a_3782_;
goto v___jp_4147_;
}
v___jp_4147_:
{
lean_object* v_toConstantVal_4151_; lean_object* v_name_4152_; lean_object* v___x_4153_; uint8_t v___x_4154_; 
v_toConstantVal_4151_ = lean_ctor_get(v_val_4146_, 0);
v_name_4152_ = lean_ctor_get(v_toConstantVal_4151_, 0);
lean_inc_ref(v_val_4146_);
v___x_4153_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4153_, 0, v_val_4146_);
v___x_4154_ = 1;
lean_inc(v_name_4152_);
v_fst_4072_ = v_name_4152_;
v_fst_4073_ = v___x_4153_;
v_snd_4074_ = v___x_4154_;
v_exportedInfo_x3f_4075_ = v_exportedInfo_x3f_4148_;
v___y_4076_ = v___y_4149_;
v___y_4077_ = v___y_4150_;
goto v___jp_4071_;
}
}
case 1:
{
lean_object* v_val_4163_; 
v_val_4163_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref(v_val_4163_);
v_defn_4121_ = v_val_4163_;
v___y_4122_ = v_a_3781_;
v___y_4123_ = v_a_3782_;
goto v___jp_4120_;
}
case 5:
{
lean_object* v_defns_4164_; 
v_defns_4164_ = lean_ctor_get(v_decl_3779_, 0);
if (lean_obj_tag(v_defns_4164_) == 1)
{
lean_object* v_tail_4165_; 
v_tail_4165_ = lean_ctor_get(v_defns_4164_, 1);
if (lean_obj_tag(v_tail_4165_) == 0)
{
lean_object* v_head_4166_; 
v_head_4166_ = lean_ctor_get(v_defns_4164_, 0);
lean_inc(v_head_4166_);
v_defn_4121_ = v_head_4166_;
v___y_4122_ = v_a_3781_;
v___y_4123_ = v_a_3782_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4167_; 
v___x_4167_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v_a_3781_, v_a_3782_);
return v___x_4167_;
}
}
else
{
lean_object* v___x_4168_; 
v___x_4168_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v_a_3781_, v_a_3782_);
return v___x_4168_;
}
}
case 3:
{
lean_object* v_val_4169_; lean_object* v_exportedInfo_x3f_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___x_4178_; lean_object* v_env_4179_; lean_object* v___x_4180_; 
v_val_4169_ = lean_ctor_get(v_decl_3779_, 0);
v___x_4178_ = lean_st_ref_get(v_a_3782_);
v_env_4179_ = lean_ctor_get(v___x_4178_, 0);
lean_inc_ref(v_env_4179_);
lean_dec(v___x_4178_);
v___x_4180_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4181_; lean_object* v___x_4182_; uint8_t v_isModule_4183_; 
v_env_4181_ = lean_ctor_get(v___x_4180_, 0);
lean_inc_ref(v_env_4181_);
lean_dec(v___x_4180_);
v___x_4182_ = l_Lean_Environment_header(v_env_4179_);
lean_dec_ref(v_env_4179_);
v_isModule_4183_ = lean_ctor_get_uint8(v___x_4182_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4182_);
if (v_isModule_4183_ == 0)
{
lean_dec_ref(v_env_4181_);
v_exportedInfo_x3f_4171_ = v___x_4033_;
v___y_4172_ = v_a_3781_;
v___y_4173_ = v_a_3782_;
goto v___jp_4170_;
}
else
{
uint8_t v_isExporting_4184_; 
v_isExporting_4184_ = lean_ctor_get_uint8(v_env_4181_, sizeof(void*)*8);
lean_dec_ref(v_env_4181_);
if (v_isExporting_4184_ == 0)
{
lean_object* v_toConstantVal_4185_; uint8_t v_isUnsafe_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; 
v_toConstantVal_4185_ = lean_ctor_get(v_val_4169_, 0);
v_isUnsafe_4186_ = lean_ctor_get_uint8(v_val_4169_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4185_);
v___x_4187_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4187_, 0, v_toConstantVal_4185_);
lean_ctor_set_uint8(v___x_4187_, sizeof(void*)*1, v_isUnsafe_4186_);
v___x_4188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
v___x_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4188_);
v_exportedInfo_x3f_4171_ = v___x_4189_;
v___y_4172_ = v_a_3781_;
v___y_4173_ = v_a_3782_;
goto v___jp_4170_;
}
else
{
v_exportedInfo_x3f_4171_ = v___x_4033_;
v___y_4172_ = v_a_3781_;
v___y_4173_ = v_a_3782_;
goto v___jp_4170_;
}
}
}
else
{
lean_dec(v___x_4180_);
lean_dec_ref(v_env_4179_);
v_exportedInfo_x3f_4171_ = v___x_4033_;
v___y_4172_ = v_a_3781_;
v___y_4173_ = v_a_3782_;
goto v___jp_4170_;
}
v___jp_4170_:
{
lean_object* v_toConstantVal_4174_; lean_object* v_name_4175_; lean_object* v___x_4176_; uint8_t v___x_4177_; 
v_toConstantVal_4174_ = lean_ctor_get(v_val_4169_, 0);
v_name_4175_ = lean_ctor_get(v_toConstantVal_4174_, 0);
lean_inc_ref(v_val_4169_);
v___x_4176_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4176_, 0, v_val_4169_);
v___x_4177_ = 3;
lean_inc(v_name_4175_);
v_fst_4072_ = v_name_4175_;
v_fst_4073_ = v___x_4176_;
v_snd_4074_ = v___x_4177_;
v_exportedInfo_x3f_4075_ = v_exportedInfo_x3f_4171_;
v___y_4076_ = v___y_4172_;
v___y_4077_ = v___y_4173_;
goto v___jp_4071_;
}
}
case 0:
{
lean_object* v_val_4190_; lean_object* v_toConstantVal_4191_; lean_object* v_name_4192_; lean_object* v___x_4193_; uint8_t v___x_4194_; 
v_val_4190_ = lean_ctor_get(v_decl_3779_, 0);
v_toConstantVal_4191_ = lean_ctor_get(v_val_4190_, 0);
v_name_4192_ = lean_ctor_get(v_toConstantVal_4191_, 0);
lean_inc_ref(v_val_4190_);
v___x_4193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4193_, 0, v_val_4190_);
v___x_4194_ = 2;
lean_inc(v_name_4192_);
v_fst_4072_ = v_name_4192_;
v_fst_4073_ = v___x_4193_;
v_snd_4074_ = v___x_4194_;
v_exportedInfo_x3f_4075_ = v___x_4033_;
v___y_4076_ = v_a_3781_;
v___y_4077_ = v_a_3782_;
goto v___jp_4071_;
}
default: 
{
lean_object* v___x_4195_; 
v___x_4195_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v_a_3781_, v_a_3782_);
return v___x_4195_;
}
}
v___jp_4034_:
{
lean_object* v___x_4041_; uint8_t v___x_4042_; 
lean_inc(v_decl_3779_);
v___x_4041_ = l_Lean_Declaration_getTopLevelNames(v_decl_3779_);
v___x_4042_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4041_);
lean_dec(v___x_4041_);
if (v___x_4042_ == 0)
{
if (lean_obj_tag(v___y_4037_) == 0)
{
if (v___x_4042_ == 0)
{
lean_object* v_toCold_4043_; lean_object* v_options_4044_; uint8_t v_hasTrace_4045_; 
v_toCold_4043_ = lean_ctor_get(v___y_4039_, 0);
v_options_4044_ = lean_ctor_get(v_toCold_4043_, 2);
v_hasTrace_4045_ = lean_ctor_get_uint8(v_options_4044_, sizeof(void*)*1);
if (v_hasTrace_4045_ == 0)
{
v___y_3969_ = v___y_4035_;
v___y_3970_ = v___y_4036_;
v___y_3971_ = v___y_4038_;
v___y_3972_ = v___y_4039_;
v___y_3973_ = v___y_4040_;
goto v___jp_3968_;
}
else
{
lean_object* v_inheritedTraceOptions_4046_; lean_object* v___x_4047_; uint8_t v___x_4048_; 
v_inheritedTraceOptions_4046_ = lean_ctor_get(v_toCold_4043_, 11);
v___x_4047_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4048_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4046_, v_options_4044_, v___x_4047_);
if (v___x_4048_ == 0)
{
v___y_3969_ = v___y_4035_;
v___y_3970_ = v___y_4036_;
v___y_3971_ = v___y_4038_;
v___y_3972_ = v___y_4039_;
v___y_3973_ = v___y_4040_;
goto v___jp_3968_;
}
else
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4050_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4049_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_dec_ref_known(v___x_4050_, 1);
v___y_3969_ = v___y_4035_;
v___y_3970_ = v___y_4036_;
v___y_3971_ = v___y_4038_;
v___y_3972_ = v___y_4039_;
v___y_3973_ = v___y_4040_;
goto v___jp_3968_;
}
else
{
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4036_);
lean_dec(v_decl_3779_);
return v___x_4050_;
}
}
}
}
else
{
v___y_4003_ = v___y_4035_;
v___y_4004_ = v___y_4039_;
v___y_4005_ = v___y_4036_;
v___y_4006_ = v___y_4040_;
v___y_4007_ = v___y_4037_;
v___y_4008_ = v___y_4038_;
goto v___jp_4002_;
}
}
else
{
v___y_4003_ = v___y_4035_;
v___y_4004_ = v___y_4039_;
v___y_4005_ = v___y_4036_;
v___y_4006_ = v___y_4040_;
v___y_4007_ = v___y_4037_;
v___y_4008_ = v___y_4038_;
goto v___jp_4002_;
}
}
else
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v_a_4053_; uint8_t v___x_4054_; 
lean_dec(v___y_4037_);
v___x_4051_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4052_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4051_, v___y_4039_);
v_a_4053_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4053_);
lean_dec_ref(v___x_4052_);
v___x_4054_ = lean_unbox(v_a_4053_);
lean_dec(v_a_4053_);
if (v___x_4054_ == 0)
{
lean_object* v_toCold_4055_; lean_object* v_options_4056_; uint8_t v_hasTrace_4057_; 
v_toCold_4055_ = lean_ctor_get(v___y_4039_, 0);
v_options_4056_ = lean_ctor_get(v_toCold_4055_, 2);
v_hasTrace_4057_ = lean_ctor_get_uint8(v_options_4056_, sizeof(void*)*1);
if (v_hasTrace_4057_ == 0)
{
v___y_3947_ = v___y_4035_;
v___y_3948_ = v___y_4036_;
v___y_3949_ = v___y_4038_;
v_exportedInfo_x3f_3950_ = v___x_4033_;
v___y_3951_ = v___y_4039_;
v___y_3952_ = v___y_4040_;
goto v___jp_3946_;
}
else
{
lean_object* v_inheritedTraceOptions_4058_; lean_object* v___x_4059_; uint8_t v___x_4060_; 
v_inheritedTraceOptions_4058_ = lean_ctor_get(v_toCold_4055_, 11);
v___x_4059_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4060_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4058_, v_options_4056_, v___x_4059_);
if (v___x_4060_ == 0)
{
v___y_3947_ = v___y_4035_;
v___y_3948_ = v___y_4036_;
v___y_3949_ = v___y_4038_;
v_exportedInfo_x3f_3950_ = v___x_4033_;
v___y_3951_ = v___y_4039_;
v___y_3952_ = v___y_4040_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4061_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4062_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4061_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4062_) == 0)
{
lean_dec_ref_known(v___x_4062_, 1);
v___y_3947_ = v___y_4035_;
v___y_3948_ = v___y_4036_;
v___y_3949_ = v___y_4038_;
v_exportedInfo_x3f_3950_ = v___x_4033_;
v___y_3951_ = v___y_4039_;
v___y_3952_ = v___y_4040_;
goto v___jp_3946_;
}
else
{
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4036_);
lean_dec(v_decl_3779_);
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_toCold_4063_; lean_object* v_options_4064_; uint8_t v_hasTrace_4065_; 
v_toCold_4063_ = lean_ctor_get(v___y_4039_, 0);
v_options_4064_ = lean_ctor_get(v_toCold_4063_, 2);
v_hasTrace_4065_ = lean_ctor_get_uint8(v_options_4064_, sizeof(void*)*1);
if (v_hasTrace_4065_ == 0)
{
v___y_3962_ = v___y_4035_;
v___y_3963_ = v___y_4036_;
v___y_3964_ = v___y_4038_;
v___y_3965_ = v___y_4039_;
v___y_3966_ = v___y_4040_;
goto v___jp_3961_;
}
else
{
lean_object* v_inheritedTraceOptions_4066_; lean_object* v___x_4067_; uint8_t v___x_4068_; 
v_inheritedTraceOptions_4066_ = lean_ctor_get(v_toCold_4063_, 11);
v___x_4067_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4068_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4066_, v_options_4064_, v___x_4067_);
if (v___x_4068_ == 0)
{
v___y_3962_ = v___y_4035_;
v___y_3963_ = v___y_4036_;
v___y_3964_ = v___y_4038_;
v___y_3965_ = v___y_4039_;
v___y_3966_ = v___y_4040_;
goto v___jp_3961_;
}
else
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4070_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4069_, v___y_4039_, v___y_4040_);
if (lean_obj_tag(v___x_4070_) == 0)
{
lean_dec_ref_known(v___x_4070_, 1);
v___y_3962_ = v___y_4035_;
v___y_3963_ = v___y_4036_;
v___y_3964_ = v___y_4038_;
v___y_3965_ = v___y_4039_;
v___y_3966_ = v___y_4040_;
goto v___jp_3961_;
}
else
{
lean_dec(v___y_4038_);
lean_dec_ref(v___y_4036_);
lean_dec(v_decl_3779_);
return v___x_4070_;
}
}
}
}
}
}
v___jp_4071_:
{
lean_object* v___x_4078_; lean_object* v_env_4079_; uint8_t v___x_4080_; 
v___x_4078_ = lean_st_ref_get(v___y_4077_);
v_env_4079_ = lean_ctor_get(v___x_4078_, 0);
lean_inc_ref(v_env_4079_);
lean_dec(v___x_4078_);
v___x_4080_ = l_Lean_Environment_containsOnBranch(v_env_4079_, v_fst_4072_);
lean_dec_ref(v_env_4079_);
if (v___x_4080_ == 0)
{
v___y_4035_ = v_snd_4074_;
v___y_4036_ = v_fst_4073_;
v___y_4037_ = v_exportedInfo_x3f_4075_;
v___y_4038_ = v_fst_4072_;
v___y_4039_ = v___y_4076_;
v___y_4040_ = v___y_4077_;
goto v___jp_4034_;
}
else
{
lean_object* v___x_4081_; lean_object* v_env_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; 
lean_dec(v_exportedInfo_x3f_4075_);
lean_dec_ref(v_fst_4073_);
lean_dec(v_decl_3779_);
v___x_4081_ = lean_st_ref_get(v___y_4077_);
v_env_4082_ = lean_ctor_get(v___x_4081_, 0);
lean_inc_ref(v_env_4082_);
lean_dec(v___x_4081_);
v___x_4083_ = lean_elab_environment_to_kernel_env(v_env_4082_);
v___x_4084_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
lean_ctor_set(v___x_4084_, 1, v_fst_4072_);
v___x_4085_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4084_, v___y_4076_, v___y_4077_);
return v___x_4085_;
}
}
v___jp_4086_:
{
lean_object* v_toConstantVal_4091_; lean_object* v_name_4092_; lean_object* v___x_4093_; uint8_t v___x_4094_; 
v_toConstantVal_4091_ = lean_ctor_get(v___y_4087_, 0);
v_name_4092_ = lean_ctor_get(v_toConstantVal_4091_, 0);
lean_inc(v_name_4092_);
v___x_4093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4093_, 0, v___y_4087_);
v___x_4094_ = 0;
v_fst_4072_ = v_name_4092_;
v_fst_4073_ = v___x_4093_;
v_snd_4074_ = v___x_4094_;
v_exportedInfo_x3f_4075_ = v_exportedInfo_x3f_4088_;
v___y_4076_ = v___y_4089_;
v___y_4077_ = v___y_4090_;
goto v___jp_4071_;
}
v___jp_4095_:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4101_, 0, v___y_4096_);
lean_ctor_set_uint8(v___x_4101_, sizeof(void*)*1, v___y_4100_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4101_);
v___x_4103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
v___y_4087_ = v___y_4099_;
v_exportedInfo_x3f_4088_ = v___x_4103_;
v___y_4089_ = v___y_4097_;
v___y_4090_ = v___y_4098_;
goto v___jp_4086_;
}
v___jp_4104_:
{
uint8_t v___x_4111_; uint8_t v___x_4112_; 
v___x_4111_ = 1;
v___x_4112_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4108_, v___x_4111_);
if (v___x_4112_ == 0)
{
v___y_4096_ = v_toConstantVal_4107_;
v___y_4097_ = v___y_4109_;
v___y_4098_ = v___y_4110_;
v___y_4099_ = v___y_4106_;
v___y_4100_ = v___y_4105_;
goto v___jp_4095_;
}
else
{
v___y_4096_ = v_toConstantVal_4107_;
v___y_4097_ = v___y_4109_;
v___y_4098_ = v___y_4110_;
v___y_4099_ = v___y_4106_;
v___y_4100_ = v_hasTrace_3839_;
goto v___jp_4095_;
}
}
v___jp_4113_:
{
lean_object* v_toConstantVal_4118_; uint8_t v_safety_4119_; 
v_toConstantVal_4118_ = lean_ctor_get(v___y_4115_, 0);
lean_inc_ref(v_toConstantVal_4118_);
v_safety_4119_ = lean_ctor_get_uint8(v___y_4115_, sizeof(void*)*4);
v___y_4105_ = v___y_4114_;
v___y_4106_ = v___y_4115_;
v_toConstantVal_4107_ = v_toConstantVal_4118_;
v_safety_4108_ = v_safety_4119_;
v___y_4109_ = v___y_4116_;
v___y_4110_ = v___y_4117_;
goto v___jp_4104_;
}
v___jp_4120_:
{
lean_object* v___x_4124_; lean_object* v_env_4125_; lean_object* v___x_4126_; 
v___x_4124_ = lean_st_ref_get(v___y_4123_);
v_env_4125_ = lean_ctor_get(v___x_4124_, 0);
lean_inc_ref(v_env_4125_);
lean_dec(v___x_4124_);
v___x_4126_ = lean_st_ref_get(v___y_4123_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4127_; lean_object* v___x_4128_; uint8_t v_isModule_4129_; 
v_env_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_ref(v_env_4127_);
lean_dec(v___x_4126_);
v___x_4128_ = l_Lean_Environment_header(v_env_4125_);
lean_dec_ref(v_env_4125_);
v_isModule_4129_ = lean_ctor_get_uint8(v___x_4128_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4128_);
if (v_isModule_4129_ == 0)
{
lean_dec_ref(v_env_4127_);
v___y_4087_ = v_defn_4121_;
v_exportedInfo_x3f_4088_ = v___x_4033_;
v___y_4089_ = v___y_4122_;
v___y_4090_ = v___y_4123_;
goto v___jp_4086_;
}
else
{
uint8_t v_isExporting_4130_; 
v_isExporting_4130_ = lean_ctor_get_uint8(v_env_4127_, sizeof(void*)*8);
lean_dec_ref(v_env_4127_);
if (v_isExporting_4130_ == 0)
{
lean_object* v_toCold_4131_; lean_object* v_options_4132_; uint8_t v_hasTrace_4133_; 
v_toCold_4131_ = lean_ctor_get(v___y_4122_, 0);
v_options_4132_ = lean_ctor_get(v_toCold_4131_, 2);
v_hasTrace_4133_ = lean_ctor_get_uint8(v_options_4132_, sizeof(void*)*1);
if (v_hasTrace_4133_ == 0)
{
v___y_4114_ = v_isModule_4129_;
v___y_4115_ = v_defn_4121_;
v___y_4116_ = v___y_4122_;
v___y_4117_ = v___y_4123_;
goto v___jp_4113_;
}
else
{
lean_object* v_inheritedTraceOptions_4134_; lean_object* v___x_4135_; uint8_t v___x_4136_; 
v_inheritedTraceOptions_4134_ = lean_ctor_get(v_toCold_4131_, 11);
v___x_4135_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4136_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4134_, v_options_4132_, v___x_4135_);
if (v___x_4136_ == 0)
{
v___y_4114_ = v_isModule_4129_;
v___y_4115_ = v_defn_4121_;
v___y_4116_ = v___y_4122_;
v___y_4117_ = v___y_4123_;
goto v___jp_4113_;
}
else
{
lean_object* v_toConstantVal_4137_; uint8_t v_safety_4138_; lean_object* v_name_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; 
v_toConstantVal_4137_ = lean_ctor_get(v_defn_4121_, 0);
lean_inc_ref(v_toConstantVal_4137_);
v_safety_4138_ = lean_ctor_get_uint8(v_defn_4121_, sizeof(void*)*4);
v_name_4139_ = lean_ctor_get(v_toConstantVal_4137_, 0);
v___x_4140_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4139_);
v___x_4141_ = l_Lean_MessageData_ofName(v_name_4139_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4144_, v___y_4122_, v___y_4123_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_dec_ref_known(v___x_4145_, 1);
v___y_4105_ = v_isModule_4129_;
v___y_4106_ = v_defn_4121_;
v_toConstantVal_4107_ = v_toConstantVal_4137_;
v_safety_4108_ = v_safety_4138_;
v___y_4109_ = v___y_4122_;
v___y_4110_ = v___y_4123_;
goto v___jp_4104_;
}
else
{
lean_dec_ref(v_toConstantVal_4137_);
lean_dec_ref(v_defn_4121_);
lean_dec(v_decl_3779_);
return v___x_4145_;
}
}
}
}
else
{
v___y_4087_ = v_defn_4121_;
v_exportedInfo_x3f_4088_ = v___x_4033_;
v___y_4089_ = v___y_4122_;
v___y_4090_ = v___y_4123_;
goto v___jp_4086_;
}
}
}
else
{
lean_dec(v___x_4126_);
lean_dec_ref(v_env_4125_);
v___y_4087_ = v_defn_4121_;
v_exportedInfo_x3f_4088_ = v___x_4033_;
v___y_4089_ = v___y_4122_;
v___y_4090_ = v___y_4123_;
goto v___jp_4086_;
}
}
}
}
}
else
{
lean_object* v___f_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; uint8_t v___x_4202_; lean_object* v___y_4204_; lean_object* v___y_4205_; lean_object* v_a_4206_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4246_; lean_object* v___y_4247_; lean_object* v___y_4248_; lean_object* v___y_4249_; lean_object* v___y_4250_; lean_object* v___y_4251_; lean_object* v___y_4252_; lean_object* v___y_4268_; lean_object* v___y_4269_; lean_object* v___y_4270_; lean_object* v___y_4271_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v___y_4294_; uint8_t v___y_4295_; lean_object* v___y_4296_; lean_object* v___y_4297_; lean_object* v___y_4298_; lean_object* v___y_4299_; lean_object* v___y_4300_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v_a_4307_; lean_object* v___y_4317_; lean_object* v___y_4318_; lean_object* v___y_4319_; lean_object* v___y_4337_; lean_object* v___y_4338_; lean_object* v___y_4339_; lean_object* v___y_4340_; lean_object* v___y_4344_; lean_object* v___y_4345_; lean_object* v___y_4346_; lean_object* v___y_4347_; 
lean_inc(v_decl_3779_);
v___f_4199_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4199_, 0, v_decl_3779_);
v___x_4200_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4201_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3838_, v_options_3837_, v___x_4201_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4504_; uint8_t v___x_4505_; lean_object* v___y_4507_; lean_object* v___y_4508_; lean_object* v___y_4509_; lean_object* v___y_4510_; lean_object* v___y_4511_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___y_4516_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4581_; uint8_t v___y_4582_; lean_object* v___y_4583_; lean_object* v___y_4584_; lean_object* v___y_4585_; lean_object* v___y_4586_; lean_object* v___y_4587_; lean_object* v___y_4588_; lean_object* v___y_4611_; uint8_t v___y_4612_; lean_object* v___y_4613_; lean_object* v_exportedInfo_x3f_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4626_; uint8_t v___y_4627_; lean_object* v___y_4628_; lean_object* v___y_4629_; lean_object* v___y_4630_; lean_object* v___y_4633_; uint8_t v___y_4634_; lean_object* v___y_4635_; lean_object* v___y_4636_; lean_object* v___y_4637_; 
v___x_4504_ = l_Lean_trace_profiler;
v___x_4505_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3837_, v___x_4504_);
if (v___x_4505_ == 0)
{
lean_object* v___x_4639_; lean_object* v_env_4640_; lean_object* v_nextMacroScope_4641_; lean_object* v_ngen_4642_; lean_object* v_auxDeclNGen_4643_; lean_object* v_traceState_4644_; lean_object* v_messages_4645_; lean_object* v_infoState_4646_; lean_object* v_snapshotTasks_4647_; lean_object* v___x_4649_; uint8_t v_isShared_4650_; uint8_t v_isSharedCheck_4879_; 
lean_dec_ref(v___f_4199_);
v___x_4639_ = lean_st_ref_take(v_a_3782_);
v_env_4640_ = lean_ctor_get(v___x_4639_, 0);
v_nextMacroScope_4641_ = lean_ctor_get(v___x_4639_, 1);
v_ngen_4642_ = lean_ctor_get(v___x_4639_, 2);
v_auxDeclNGen_4643_ = lean_ctor_get(v___x_4639_, 3);
v_traceState_4644_ = lean_ctor_get(v___x_4639_, 4);
v_messages_4645_ = lean_ctor_get(v___x_4639_, 6);
v_infoState_4646_ = lean_ctor_get(v___x_4639_, 7);
v_snapshotTasks_4647_ = lean_ctor_get(v___x_4639_, 8);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4639_);
if (v_isSharedCheck_4879_ == 0)
{
lean_object* v_unused_4880_; 
v_unused_4880_ = lean_ctor_get(v___x_4639_, 5);
lean_dec(v_unused_4880_);
v___x_4649_ = v___x_4639_;
v_isShared_4650_ = v_isSharedCheck_4879_;
goto v_resetjp_4648_;
}
else
{
lean_inc(v_snapshotTasks_4647_);
lean_inc(v_infoState_4646_);
lean_inc(v_messages_4645_);
lean_inc(v_traceState_4644_);
lean_inc(v_auxDeclNGen_4643_);
lean_inc(v_ngen_4642_);
lean_inc(v_nextMacroScope_4641_);
lean_inc(v_env_4640_);
lean_dec(v___x_4639_);
v___x_4649_ = lean_box(0);
v_isShared_4650_ = v_isSharedCheck_4879_;
goto v_resetjp_4648_;
}
v_resetjp_4648_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___y_4655_; lean_object* v___y_4656_; uint8_t v___y_4657_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___x_4683_; 
lean_inc(v_decl_3779_);
v___x_4651_ = l_Lean_Declaration_getNames(v_decl_3779_);
v___x_4652_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4640_, v___x_4651_);
v___x_4653_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4650_ == 0)
{
lean_ctor_set(v___x_4649_, 5, v___x_4653_);
lean_ctor_set(v___x_4649_, 0, v___x_4652_);
v___x_4683_ = v___x_4649_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v___x_4652_);
lean_ctor_set(v_reuseFailAlloc_4878_, 1, v_nextMacroScope_4641_);
lean_ctor_set(v_reuseFailAlloc_4878_, 2, v_ngen_4642_);
lean_ctor_set(v_reuseFailAlloc_4878_, 3, v_auxDeclNGen_4643_);
lean_ctor_set(v_reuseFailAlloc_4878_, 4, v_traceState_4644_);
lean_ctor_set(v_reuseFailAlloc_4878_, 5, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4878_, 6, v_messages_4645_);
lean_ctor_set(v_reuseFailAlloc_4878_, 7, v_infoState_4646_);
lean_ctor_set(v_reuseFailAlloc_4878_, 8, v_snapshotTasks_4647_);
v___x_4683_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4682_;
}
v___jp_4654_:
{
lean_object* v___x_4661_; lean_object* v_env_4662_; lean_object* v_nextMacroScope_4663_; lean_object* v_ngen_4664_; lean_object* v_auxDeclNGen_4665_; lean_object* v_traceState_4666_; lean_object* v_messages_4667_; lean_object* v_infoState_4668_; lean_object* v_snapshotTasks_4669_; lean_object* v___x_4671_; uint8_t v_isShared_4672_; uint8_t v_isSharedCheck_4680_; 
v___x_4661_ = lean_st_ref_take(v___y_4659_);
v_env_4662_ = lean_ctor_get(v___x_4661_, 0);
v_nextMacroScope_4663_ = lean_ctor_get(v___x_4661_, 1);
v_ngen_4664_ = lean_ctor_get(v___x_4661_, 2);
v_auxDeclNGen_4665_ = lean_ctor_get(v___x_4661_, 3);
v_traceState_4666_ = lean_ctor_get(v___x_4661_, 4);
v_messages_4667_ = lean_ctor_get(v___x_4661_, 6);
v_infoState_4668_ = lean_ctor_get(v___x_4661_, 7);
v_snapshotTasks_4669_ = lean_ctor_get(v___x_4661_, 8);
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4661_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v___x_4661_, 5);
lean_dec(v_unused_4681_);
v___x_4671_ = v___x_4661_;
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
else
{
lean_inc(v_snapshotTasks_4669_);
lean_inc(v_infoState_4668_);
lean_inc(v_messages_4667_);
lean_inc(v_traceState_4666_);
lean_inc(v_auxDeclNGen_4665_);
lean_inc(v_ngen_4664_);
lean_inc(v_nextMacroScope_4663_);
lean_inc(v_env_4662_);
lean_dec(v___x_4661_);
v___x_4671_ = lean_box(0);
v_isShared_4672_ = v_isSharedCheck_4680_;
goto v_resetjp_4670_;
}
v_resetjp_4670_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; lean_object* v___x_4675_; lean_object* v___x_4677_; 
v___x_4673_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4674_ = lean_box(v___y_4657_);
lean_inc(v___y_4655_);
v___x_4675_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4673_, v_env_4662_, v___y_4655_, v___x_4674_);
if (v_isShared_4672_ == 0)
{
lean_ctor_set(v___x_4671_, 5, v___x_4653_);
lean_ctor_set(v___x_4671_, 0, v___x_4675_);
v___x_4677_ = v___x_4671_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v___x_4675_);
lean_ctor_set(v_reuseFailAlloc_4679_, 1, v_nextMacroScope_4663_);
lean_ctor_set(v_reuseFailAlloc_4679_, 2, v_ngen_4664_);
lean_ctor_set(v_reuseFailAlloc_4679_, 3, v_auxDeclNGen_4665_);
lean_ctor_set(v_reuseFailAlloc_4679_, 4, v_traceState_4666_);
lean_ctor_set(v_reuseFailAlloc_4679_, 5, v___x_4653_);
lean_ctor_set(v_reuseFailAlloc_4679_, 6, v_messages_4667_);
lean_ctor_set(v_reuseFailAlloc_4679_, 7, v_infoState_4668_);
lean_ctor_set(v_reuseFailAlloc_4679_, 8, v_snapshotTasks_4669_);
v___x_4677_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
lean_object* v___x_4678_; 
v___x_4678_ = lean_st_ref_put(v___y_4659_, v___x_4677_);
v___y_4611_ = v___y_4655_;
v___y_4612_ = v___y_4657_;
v___y_4613_ = v___y_4658_;
v_exportedInfo_x3f_4614_ = v___y_4656_;
v___y_4615_ = v___y_4660_;
v___y_4616_ = v___y_4659_;
goto v___jp_4610_;
}
}
}
v_reusejp_4682_:
{
lean_object* v___x_4684_; lean_object* v___x_4685_; lean_object* v___y_4687_; lean_object* v___y_4688_; uint8_t v___y_4689_; lean_object* v___y_4690_; lean_object* v___y_4691_; lean_object* v___y_4692_; lean_object* v_fst_4721_; lean_object* v_fst_4722_; uint8_t v_snd_4723_; lean_object* v_exportedInfo_x3f_4724_; lean_object* v___y_4725_; lean_object* v___y_4726_; lean_object* v___y_4736_; lean_object* v_exportedInfo_x3f_4737_; lean_object* v___y_4738_; lean_object* v___y_4739_; lean_object* v___y_4745_; lean_object* v___y_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___y_4749_; lean_object* v___y_4754_; lean_object* v_toConstantVal_4755_; uint8_t v_safety_4756_; uint8_t v___y_4757_; lean_object* v___y_4758_; lean_object* v___y_4759_; lean_object* v___y_4763_; uint8_t v___y_4764_; lean_object* v___y_4765_; lean_object* v___y_4766_; lean_object* v___y_4770_; lean_object* v___y_4771_; lean_object* v___y_4772_; uint8_t v___y_4773_; lean_object* v___y_4789_; lean_object* v___y_4790_; lean_object* v___y_4791_; lean_object* v___y_4792_; lean_object* v___y_4793_; lean_object* v_defn_4798_; lean_object* v___y_4799_; lean_object* v___y_4800_; 
v___x_4684_ = lean_st_ref_put(v_a_3782_, v___x_4683_);
v___x_4685_ = lean_box(0);
switch(lean_obj_tag(v_decl_3779_))
{
case 2:
{
lean_object* v_val_4806_; lean_object* v_exportedInfo_x3f_4808_; lean_object* v___y_4809_; lean_object* v___y_4810_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___x_4822_; lean_object* v_env_4823_; 
v_val_4806_ = lean_ctor_get(v_decl_3779_, 0);
v___x_4822_ = lean_st_ref_get(v_a_3782_);
v_env_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc_ref(v_env_4823_);
lean_dec(v___x_4822_);
if (v_forceExpose_3780_ == 0)
{
goto v___jp_4824_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec_ref(v_env_4823_);
v_exportedInfo_x3f_4808_ = v___x_4685_;
v___y_4809_ = v_a_3781_;
v___y_4810_ = v_a_3782_;
goto v___jp_4807_;
}
else
{
goto v___jp_4824_;
}
}
v___jp_4807_:
{
lean_object* v_toConstantVal_4811_; lean_object* v_name_4812_; lean_object* v___x_4813_; uint8_t v___x_4814_; 
v_toConstantVal_4811_ = lean_ctor_get(v_val_4806_, 0);
v_name_4812_ = lean_ctor_get(v_toConstantVal_4811_, 0);
lean_inc_ref(v_val_4806_);
v___x_4813_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4813_, 0, v_val_4806_);
v___x_4814_ = 1;
lean_inc(v_name_4812_);
v_fst_4721_ = v_name_4812_;
v_fst_4722_ = v___x_4813_;
v_snd_4723_ = v___x_4814_;
v_exportedInfo_x3f_4724_ = v_exportedInfo_x3f_4808_;
v___y_4725_ = v___y_4809_;
v___y_4726_ = v___y_4810_;
goto v___jp_4720_;
}
v___jp_4815_:
{
lean_object* v_toConstantVal_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; 
v_toConstantVal_4818_ = lean_ctor_get(v_val_4806_, 0);
lean_inc_ref(v_toConstantVal_4818_);
v___x_4819_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4819_, 0, v_toConstantVal_4818_);
lean_ctor_set_uint8(v___x_4819_, sizeof(void*)*1, v___x_4505_);
v___x_4820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4819_);
v___x_4821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4821_, 0, v___x_4820_);
v_exportedInfo_x3f_4808_ = v___x_4821_;
v___y_4809_ = v___y_4816_;
v___y_4810_ = v___y_4817_;
goto v___jp_4807_;
}
v___jp_4824_:
{
lean_object* v___x_4825_; uint8_t v_isModule_4826_; 
v___x_4825_ = l_Lean_Environment_header(v_env_4823_);
lean_dec_ref(v_env_4823_);
v_isModule_4826_ = lean_ctor_get_uint8(v___x_4825_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4825_);
if (v_isModule_4826_ == 0)
{
v_exportedInfo_x3f_4808_ = v___x_4685_;
v___y_4809_ = v_a_3781_;
v___y_4810_ = v_a_3782_;
goto v___jp_4807_;
}
else
{
if (v___x_4202_ == 0)
{
v___y_4816_ = v_a_3781_;
v___y_4817_ = v_a_3782_;
goto v___jp_4815_;
}
else
{
lean_object* v_toConstantVal_4827_; lean_object* v_name_4828_; lean_object* v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; lean_object* v___x_4834_; 
v_toConstantVal_4827_ = lean_ctor_get(v_val_4806_, 0);
v_name_4828_ = lean_ctor_get(v_toConstantVal_4827_, 0);
v___x_4829_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4828_);
v___x_4830_ = l_Lean_MessageData_ofName(v_name_4828_);
v___x_4831_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4829_);
lean_ctor_set(v___x_4831_, 1, v___x_4830_);
v___x_4832_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4833_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4833_, 0, v___x_4831_);
lean_ctor_set(v___x_4833_, 1, v___x_4832_);
v___x_4834_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4833_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4834_) == 0)
{
lean_dec_ref_known(v___x_4834_, 1);
v___y_4816_ = v_a_3781_;
v___y_4817_ = v_a_3782_;
goto v___jp_4815_;
}
else
{
lean_dec_ref_known(v_decl_3779_, 1);
return v___x_4834_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4835_; 
v_val_4835_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref(v_val_4835_);
v_defn_4798_ = v_val_4835_;
v___y_4799_ = v_a_3781_;
v___y_4800_ = v_a_3782_;
goto v___jp_4797_;
}
case 5:
{
lean_object* v_defns_4836_; 
v_defns_4836_ = lean_ctor_get(v_decl_3779_, 0);
if (lean_obj_tag(v_defns_4836_) == 1)
{
lean_object* v_tail_4837_; 
v_tail_4837_ = lean_ctor_get(v_defns_4836_, 1);
if (lean_obj_tag(v_tail_4837_) == 0)
{
lean_object* v_head_4838_; 
v_head_4838_ = lean_ctor_get(v_defns_4836_, 0);
lean_inc(v_head_4838_);
v_defn_4798_ = v_head_4838_;
v___y_4799_ = v_a_3781_;
v___y_4800_ = v_a_3782_;
goto v___jp_4797_;
}
else
{
v___y_3977_ = v_a_3781_;
v_options_3978_ = v_options_3837_;
v_inheritedTraceOptions_3979_ = v_inheritedTraceOptions_3838_;
v___y_3980_ = v_a_3782_;
goto v___jp_3976_;
}
}
else
{
v___y_3977_ = v_a_3781_;
v_options_3978_ = v_options_3837_;
v_inheritedTraceOptions_3979_ = v_inheritedTraceOptions_3838_;
v___y_3980_ = v_a_3782_;
goto v___jp_3976_;
}
}
case 3:
{
lean_object* v_val_4839_; lean_object* v_exportedInfo_x3f_4841_; lean_object* v___y_4842_; lean_object* v___y_4843_; lean_object* v___y_4849_; lean_object* v___y_4850_; lean_object* v___x_4856_; lean_object* v_env_4857_; lean_object* v___x_4858_; lean_object* v_env_4868_; 
v_val_4839_ = lean_ctor_get(v_decl_3779_, 0);
v___x_4856_ = lean_st_ref_get(v_a_3782_);
v_env_4857_ = lean_ctor_get(v___x_4856_, 0);
lean_inc_ref(v_env_4857_);
lean_dec(v___x_4856_);
v___x_4858_ = lean_st_ref_get(v_a_3782_);
v_env_4868_ = lean_ctor_get(v___x_4858_, 0);
lean_inc_ref(v_env_4868_);
lean_dec(v___x_4858_);
if (v_forceExpose_3780_ == 0)
{
goto v___jp_4869_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec_ref(v_env_4868_);
lean_dec_ref(v_env_4857_);
v_exportedInfo_x3f_4841_ = v___x_4685_;
v___y_4842_ = v_a_3781_;
v___y_4843_ = v_a_3782_;
goto v___jp_4840_;
}
else
{
goto v___jp_4869_;
}
}
v___jp_4840_:
{
lean_object* v_toConstantVal_4844_; lean_object* v_name_4845_; lean_object* v___x_4846_; uint8_t v___x_4847_; 
v_toConstantVal_4844_ = lean_ctor_get(v_val_4839_, 0);
v_name_4845_ = lean_ctor_get(v_toConstantVal_4844_, 0);
lean_inc_ref(v_val_4839_);
v___x_4846_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4846_, 0, v_val_4839_);
v___x_4847_ = 3;
lean_inc(v_name_4845_);
v_fst_4721_ = v_name_4845_;
v_fst_4722_ = v___x_4846_;
v_snd_4723_ = v___x_4847_;
v_exportedInfo_x3f_4724_ = v_exportedInfo_x3f_4841_;
v___y_4725_ = v___y_4842_;
v___y_4726_ = v___y_4843_;
goto v___jp_4720_;
}
v___jp_4848_:
{
lean_object* v_toConstantVal_4851_; uint8_t v_isUnsafe_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; 
v_toConstantVal_4851_ = lean_ctor_get(v_val_4839_, 0);
v_isUnsafe_4852_ = lean_ctor_get_uint8(v_val_4839_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4851_);
v___x_4853_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4853_, 0, v_toConstantVal_4851_);
lean_ctor_set_uint8(v___x_4853_, sizeof(void*)*1, v_isUnsafe_4852_);
v___x_4854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4854_, 0, v___x_4853_);
v___x_4855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4854_);
v_exportedInfo_x3f_4841_ = v___x_4855_;
v___y_4842_ = v___y_4849_;
v___y_4843_ = v___y_4850_;
goto v___jp_4840_;
}
v___jp_4859_:
{
if (v___x_4202_ == 0)
{
v___y_4849_ = v_a_3781_;
v___y_4850_ = v_a_3782_;
goto v___jp_4848_;
}
else
{
lean_object* v_toConstantVal_4860_; lean_object* v_name_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; 
v_toConstantVal_4860_ = lean_ctor_get(v_val_4839_, 0);
v_name_4861_ = lean_ctor_get(v_toConstantVal_4860_, 0);
v___x_4862_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4861_);
v___x_4863_ = l_Lean_MessageData_ofName(v_name_4861_);
v___x_4864_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4864_, 0, v___x_4862_);
lean_ctor_set(v___x_4864_, 1, v___x_4863_);
v___x_4865_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4866_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4866_, 0, v___x_4864_);
lean_ctor_set(v___x_4866_, 1, v___x_4865_);
v___x_4867_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4866_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4867_) == 0)
{
lean_dec_ref_known(v___x_4867_, 1);
v___y_4849_ = v_a_3781_;
v___y_4850_ = v_a_3782_;
goto v___jp_4848_;
}
else
{
lean_dec_ref_known(v_decl_3779_, 1);
return v___x_4867_;
}
}
}
v___jp_4869_:
{
lean_object* v___x_4870_; uint8_t v_isModule_4871_; 
v___x_4870_ = l_Lean_Environment_header(v_env_4857_);
lean_dec_ref(v_env_4857_);
v_isModule_4871_ = lean_ctor_get_uint8(v___x_4870_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4870_);
if (v_isModule_4871_ == 0)
{
lean_dec_ref(v_env_4868_);
v_exportedInfo_x3f_4841_ = v___x_4685_;
v___y_4842_ = v_a_3781_;
v___y_4843_ = v_a_3782_;
goto v___jp_4840_;
}
else
{
uint8_t v_isExporting_4872_; 
v_isExporting_4872_ = lean_ctor_get_uint8(v_env_4868_, sizeof(void*)*8);
lean_dec_ref(v_env_4868_);
if (v_isExporting_4872_ == 0)
{
goto v___jp_4859_;
}
else
{
if (v___x_4505_ == 0)
{
v_exportedInfo_x3f_4841_ = v___x_4685_;
v___y_4842_ = v_a_3781_;
v___y_4843_ = v_a_3782_;
goto v___jp_4840_;
}
else
{
goto v___jp_4859_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4873_; lean_object* v_toConstantVal_4874_; lean_object* v_name_4875_; lean_object* v___x_4876_; uint8_t v___x_4877_; 
v_val_4873_ = lean_ctor_get(v_decl_3779_, 0);
v_toConstantVal_4874_ = lean_ctor_get(v_val_4873_, 0);
v_name_4875_ = lean_ctor_get(v_toConstantVal_4874_, 0);
lean_inc_ref(v_val_4873_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v_val_4873_);
v___x_4877_ = 2;
lean_inc(v_name_4875_);
v_fst_4721_ = v_name_4875_;
v_fst_4722_ = v___x_4876_;
v_snd_4723_ = v___x_4877_;
v_exportedInfo_x3f_4724_ = v___x_4685_;
v___y_4725_ = v_a_3781_;
v___y_4726_ = v_a_3782_;
goto v___jp_4720_;
}
default: 
{
v___y_3977_ = v_a_3781_;
v_options_3978_ = v_options_3837_;
v_inheritedTraceOptions_3979_ = v_inheritedTraceOptions_3838_;
v___y_3980_ = v_a_3782_;
goto v___jp_3976_;
}
}
v___jp_4686_:
{
lean_object* v___x_4693_; uint8_t v___x_4694_; 
lean_inc(v_decl_3779_);
v___x_4693_ = l_Lean_Declaration_getTopLevelNames(v_decl_3779_);
v___x_4694_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4693_);
lean_dec(v___x_4693_);
if (v___x_4694_ == 0)
{
if (lean_obj_tag(v___y_4688_) == 0)
{
if (v___x_4694_ == 0)
{
lean_object* v_toCold_4695_; lean_object* v_options_4696_; uint8_t v_hasTrace_4697_; 
v_toCold_4695_ = lean_ctor_get(v___y_4691_, 0);
v_options_4696_ = lean_ctor_get(v_toCold_4695_, 2);
v_hasTrace_4697_ = lean_ctor_get_uint8(v_options_4696_, sizeof(void*)*1);
if (v_hasTrace_4697_ == 0)
{
v___y_4633_ = v___y_4687_;
v___y_4634_ = v___y_4689_;
v___y_4635_ = v___y_4690_;
v___y_4636_ = v___y_4691_;
v___y_4637_ = v___y_4692_;
goto v___jp_4632_;
}
else
{
lean_object* v_inheritedTraceOptions_4698_; uint8_t v___x_4699_; 
v_inheritedTraceOptions_4698_ = lean_ctor_get(v_toCold_4695_, 11);
v___x_4699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4698_, v_options_4696_, v___x_4201_);
if (v___x_4699_ == 0)
{
v___y_4633_ = v___y_4687_;
v___y_4634_ = v___y_4689_;
v___y_4635_ = v___y_4690_;
v___y_4636_ = v___y_4691_;
v___y_4637_ = v___y_4692_;
goto v___jp_4632_;
}
else
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4701_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4700_, v___y_4691_, v___y_4692_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_dec_ref_known(v___x_4701_, 1);
v___y_4633_ = v___y_4687_;
v___y_4634_ = v___y_4689_;
v___y_4635_ = v___y_4690_;
v___y_4636_ = v___y_4691_;
v___y_4637_ = v___y_4692_;
goto v___jp_4632_;
}
else
{
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4687_);
lean_dec(v_decl_3779_);
return v___x_4701_;
}
}
}
}
else
{
v___y_4655_ = v___y_4687_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4689_;
v___y_4658_ = v___y_4690_;
v___y_4659_ = v___y_4692_;
v___y_4660_ = v___y_4691_;
goto v___jp_4654_;
}
}
else
{
v___y_4655_ = v___y_4687_;
v___y_4656_ = v___y_4688_;
v___y_4657_ = v___y_4689_;
v___y_4658_ = v___y_4690_;
v___y_4659_ = v___y_4692_;
v___y_4660_ = v___y_4691_;
goto v___jp_4654_;
}
}
else
{
lean_object* v___x_4702_; lean_object* v___x_4703_; lean_object* v_a_4704_; uint8_t v___x_4705_; 
lean_dec(v___y_4688_);
v___x_4702_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4703_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4702_, v___y_4691_);
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
lean_inc(v_a_4704_);
lean_dec_ref(v___x_4703_);
v___x_4705_ = lean_unbox(v_a_4704_);
lean_dec(v_a_4704_);
if (v___x_4705_ == 0)
{
lean_object* v_toCold_4706_; lean_object* v_options_4707_; uint8_t v_hasTrace_4708_; 
v_toCold_4706_ = lean_ctor_get(v___y_4691_, 0);
v_options_4707_ = lean_ctor_get(v_toCold_4706_, 2);
v_hasTrace_4708_ = lean_ctor_get_uint8(v_options_4707_, sizeof(void*)*1);
if (v_hasTrace_4708_ == 0)
{
v___y_4611_ = v___y_4687_;
v___y_4612_ = v___y_4689_;
v___y_4613_ = v___y_4690_;
v_exportedInfo_x3f_4614_ = v___x_4685_;
v___y_4615_ = v___y_4691_;
v___y_4616_ = v___y_4692_;
goto v___jp_4610_;
}
else
{
lean_object* v_inheritedTraceOptions_4709_; uint8_t v___x_4710_; 
v_inheritedTraceOptions_4709_ = lean_ctor_get(v_toCold_4706_, 11);
v___x_4710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4709_, v_options_4707_, v___x_4201_);
if (v___x_4710_ == 0)
{
v___y_4611_ = v___y_4687_;
v___y_4612_ = v___y_4689_;
v___y_4613_ = v___y_4690_;
v_exportedInfo_x3f_4614_ = v___x_4685_;
v___y_4615_ = v___y_4691_;
v___y_4616_ = v___y_4692_;
goto v___jp_4610_;
}
else
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4712_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4711_, v___y_4691_, v___y_4692_);
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_dec_ref_known(v___x_4712_, 1);
v___y_4611_ = v___y_4687_;
v___y_4612_ = v___y_4689_;
v___y_4613_ = v___y_4690_;
v_exportedInfo_x3f_4614_ = v___x_4685_;
v___y_4615_ = v___y_4691_;
v___y_4616_ = v___y_4692_;
goto v___jp_4610_;
}
else
{
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4687_);
lean_dec(v_decl_3779_);
return v___x_4712_;
}
}
}
}
else
{
lean_object* v_toCold_4713_; lean_object* v_options_4714_; uint8_t v_hasTrace_4715_; 
v_toCold_4713_ = lean_ctor_get(v___y_4691_, 0);
v_options_4714_ = lean_ctor_get(v_toCold_4713_, 2);
v_hasTrace_4715_ = lean_ctor_get_uint8(v_options_4714_, sizeof(void*)*1);
if (v_hasTrace_4715_ == 0)
{
v___y_4626_ = v___y_4687_;
v___y_4627_ = v___y_4689_;
v___y_4628_ = v___y_4690_;
v___y_4629_ = v___y_4691_;
v___y_4630_ = v___y_4692_;
goto v___jp_4625_;
}
else
{
lean_object* v_inheritedTraceOptions_4716_; uint8_t v___x_4717_; 
v_inheritedTraceOptions_4716_ = lean_ctor_get(v_toCold_4713_, 11);
v___x_4717_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4716_, v_options_4714_, v___x_4201_);
if (v___x_4717_ == 0)
{
v___y_4626_ = v___y_4687_;
v___y_4627_ = v___y_4689_;
v___y_4628_ = v___y_4690_;
v___y_4629_ = v___y_4691_;
v___y_4630_ = v___y_4692_;
goto v___jp_4625_;
}
else
{
lean_object* v___x_4718_; lean_object* v___x_4719_; 
v___x_4718_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4719_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4718_, v___y_4691_, v___y_4692_);
if (lean_obj_tag(v___x_4719_) == 0)
{
lean_dec_ref_known(v___x_4719_, 1);
v___y_4626_ = v___y_4687_;
v___y_4627_ = v___y_4689_;
v___y_4628_ = v___y_4690_;
v___y_4629_ = v___y_4691_;
v___y_4630_ = v___y_4692_;
goto v___jp_4625_;
}
else
{
lean_dec_ref(v___y_4690_);
lean_dec(v___y_4687_);
lean_dec(v_decl_3779_);
return v___x_4719_;
}
}
}
}
}
}
v___jp_4720_:
{
lean_object* v___x_4727_; lean_object* v_env_4728_; uint8_t v___x_4729_; 
v___x_4727_ = lean_st_ref_get(v___y_4726_);
v_env_4728_ = lean_ctor_get(v___x_4727_, 0);
lean_inc_ref(v_env_4728_);
lean_dec(v___x_4727_);
v___x_4729_ = l_Lean_Environment_containsOnBranch(v_env_4728_, v_fst_4721_);
lean_dec_ref(v_env_4728_);
if (v___x_4729_ == 0)
{
v___y_4687_ = v_fst_4721_;
v___y_4688_ = v_exportedInfo_x3f_4724_;
v___y_4689_ = v_snd_4723_;
v___y_4690_ = v_fst_4722_;
v___y_4691_ = v___y_4725_;
v___y_4692_ = v___y_4726_;
goto v___jp_4686_;
}
else
{
lean_object* v___x_4730_; lean_object* v_env_4731_; lean_object* v___x_4732_; lean_object* v___x_4733_; lean_object* v___x_4734_; 
lean_dec(v_exportedInfo_x3f_4724_);
lean_dec_ref(v_fst_4722_);
lean_dec(v_decl_3779_);
v___x_4730_ = lean_st_ref_get(v___y_4726_);
v_env_4731_ = lean_ctor_get(v___x_4730_, 0);
lean_inc_ref(v_env_4731_);
lean_dec(v___x_4730_);
v___x_4732_ = lean_elab_environment_to_kernel_env(v_env_4731_);
v___x_4733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4733_, 0, v___x_4732_);
lean_ctor_set(v___x_4733_, 1, v_fst_4721_);
v___x_4734_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4733_, v___y_4725_, v___y_4726_);
return v___x_4734_;
}
}
v___jp_4735_:
{
lean_object* v_toConstantVal_4740_; lean_object* v_name_4741_; lean_object* v___x_4742_; uint8_t v___x_4743_; 
v_toConstantVal_4740_ = lean_ctor_get(v___y_4736_, 0);
v_name_4741_ = lean_ctor_get(v_toConstantVal_4740_, 0);
lean_inc(v_name_4741_);
v___x_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4742_, 0, v___y_4736_);
v___x_4743_ = 0;
v_fst_4721_ = v_name_4741_;
v_fst_4722_ = v___x_4742_;
v_snd_4723_ = v___x_4743_;
v_exportedInfo_x3f_4724_ = v_exportedInfo_x3f_4737_;
v___y_4725_ = v___y_4738_;
v___y_4726_ = v___y_4739_;
goto v___jp_4720_;
}
v___jp_4744_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4750_, 0, v___y_4747_);
lean_ctor_set_uint8(v___x_4750_, sizeof(void*)*1, v___y_4749_);
v___x_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
v___x_4752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
v___y_4736_ = v___y_4745_;
v_exportedInfo_x3f_4737_ = v___x_4752_;
v___y_4738_ = v___y_4746_;
v___y_4739_ = v___y_4748_;
goto v___jp_4735_;
}
v___jp_4753_:
{
uint8_t v___x_4760_; uint8_t v___x_4761_; 
v___x_4760_ = 1;
v___x_4761_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4756_, v___x_4760_);
if (v___x_4761_ == 0)
{
v___y_4745_ = v___y_4754_;
v___y_4746_ = v___y_4758_;
v___y_4747_ = v_toConstantVal_4755_;
v___y_4748_ = v___y_4759_;
v___y_4749_ = v___y_4757_;
goto v___jp_4744_;
}
else
{
v___y_4745_ = v___y_4754_;
v___y_4746_ = v___y_4758_;
v___y_4747_ = v_toConstantVal_4755_;
v___y_4748_ = v___y_4759_;
v___y_4749_ = v___x_4505_;
goto v___jp_4744_;
}
}
v___jp_4762_:
{
lean_object* v_toConstantVal_4767_; uint8_t v_safety_4768_; 
v_toConstantVal_4767_ = lean_ctor_get(v___y_4763_, 0);
lean_inc_ref(v_toConstantVal_4767_);
v_safety_4768_ = lean_ctor_get_uint8(v___y_4763_, sizeof(void*)*4);
v___y_4754_ = v___y_4763_;
v_toConstantVal_4755_ = v_toConstantVal_4767_;
v_safety_4756_ = v_safety_4768_;
v___y_4757_ = v___y_4764_;
v___y_4758_ = v___y_4765_;
v___y_4759_ = v___y_4766_;
goto v___jp_4753_;
}
v___jp_4769_:
{
lean_object* v_toCold_4774_; lean_object* v_options_4775_; uint8_t v_hasTrace_4776_; 
v_toCold_4774_ = lean_ctor_get(v___y_4772_, 0);
v_options_4775_ = lean_ctor_get(v_toCold_4774_, 2);
v_hasTrace_4776_ = lean_ctor_get_uint8(v_options_4775_, sizeof(void*)*1);
if (v_hasTrace_4776_ == 0)
{
v___y_4763_ = v___y_4771_;
v___y_4764_ = v___y_4773_;
v___y_4765_ = v___y_4772_;
v___y_4766_ = v___y_4770_;
goto v___jp_4762_;
}
else
{
lean_object* v_inheritedTraceOptions_4777_; uint8_t v___x_4778_; 
v_inheritedTraceOptions_4777_ = lean_ctor_get(v_toCold_4774_, 11);
v___x_4778_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4777_, v_options_4775_, v___x_4201_);
if (v___x_4778_ == 0)
{
v___y_4763_ = v___y_4771_;
v___y_4764_ = v___y_4773_;
v___y_4765_ = v___y_4772_;
v___y_4766_ = v___y_4770_;
goto v___jp_4762_;
}
else
{
lean_object* v_toConstantVal_4779_; uint8_t v_safety_4780_; lean_object* v_name_4781_; lean_object* v___x_4782_; lean_object* v___x_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v_toConstantVal_4779_ = lean_ctor_get(v___y_4771_, 0);
lean_inc_ref(v_toConstantVal_4779_);
v_safety_4780_ = lean_ctor_get_uint8(v___y_4771_, sizeof(void*)*4);
v_name_4781_ = lean_ctor_get(v_toConstantVal_4779_, 0);
v___x_4782_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4781_);
v___x_4783_ = l_Lean_MessageData_ofName(v_name_4781_);
v___x_4784_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4784_, 0, v___x_4782_);
lean_ctor_set(v___x_4784_, 1, v___x_4783_);
v___x_4785_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4786_, v___y_4772_, v___y_4770_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_dec_ref_known(v___x_4787_, 1);
v___y_4754_ = v___y_4771_;
v_toConstantVal_4755_ = v_toConstantVal_4779_;
v_safety_4756_ = v_safety_4780_;
v___y_4757_ = v___y_4773_;
v___y_4758_ = v___y_4772_;
v___y_4759_ = v___y_4770_;
goto v___jp_4753_;
}
else
{
lean_dec_ref(v_toConstantVal_4779_);
lean_dec_ref(v___y_4771_);
lean_dec(v_decl_3779_);
return v___x_4787_;
}
}
}
}
v___jp_4788_:
{
lean_object* v___x_4794_; uint8_t v_isModule_4795_; 
v___x_4794_ = l_Lean_Environment_header(v___y_4792_);
lean_dec_ref(v___y_4792_);
v_isModule_4795_ = lean_ctor_get_uint8(v___x_4794_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4794_);
if (v_isModule_4795_ == 0)
{
lean_dec_ref(v___y_4793_);
v___y_4736_ = v___y_4790_;
v_exportedInfo_x3f_4737_ = v___x_4685_;
v___y_4738_ = v___y_4791_;
v___y_4739_ = v___y_4789_;
goto v___jp_4735_;
}
else
{
uint8_t v_isExporting_4796_; 
v_isExporting_4796_ = lean_ctor_get_uint8(v___y_4793_, sizeof(void*)*8);
lean_dec_ref(v___y_4793_);
if (v_isExporting_4796_ == 0)
{
v___y_4770_ = v___y_4789_;
v___y_4771_ = v___y_4790_;
v___y_4772_ = v___y_4791_;
v___y_4773_ = v_isModule_4795_;
goto v___jp_4769_;
}
else
{
if (v___x_4505_ == 0)
{
v___y_4736_ = v___y_4790_;
v_exportedInfo_x3f_4737_ = v___x_4685_;
v___y_4738_ = v___y_4791_;
v___y_4739_ = v___y_4789_;
goto v___jp_4735_;
}
else
{
v___y_4770_ = v___y_4789_;
v___y_4771_ = v___y_4790_;
v___y_4772_ = v___y_4791_;
v___y_4773_ = v___x_4505_;
goto v___jp_4769_;
}
}
}
}
v___jp_4797_:
{
lean_object* v___x_4801_; lean_object* v_env_4802_; lean_object* v___x_4803_; 
v___x_4801_ = lean_st_ref_get(v___y_4800_);
v_env_4802_ = lean_ctor_get(v___x_4801_, 0);
lean_inc_ref(v_env_4802_);
lean_dec(v___x_4801_);
v___x_4803_ = lean_st_ref_get(v___y_4800_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4804_; 
v_env_4804_ = lean_ctor_get(v___x_4803_, 0);
lean_inc_ref(v_env_4804_);
lean_dec(v___x_4803_);
v___y_4789_ = v___y_4800_;
v___y_4790_ = v_defn_4798_;
v___y_4791_ = v___y_4799_;
v___y_4792_ = v_env_4802_;
v___y_4793_ = v_env_4804_;
goto v___jp_4788_;
}
else
{
if (v___x_4505_ == 0)
{
lean_dec(v___x_4803_);
lean_dec_ref(v_env_4802_);
v___y_4736_ = v_defn_4798_;
v_exportedInfo_x3f_4737_ = v___x_4685_;
v___y_4738_ = v___y_4799_;
v___y_4739_ = v___y_4800_;
goto v___jp_4735_;
}
else
{
lean_object* v_env_4805_; 
v_env_4805_ = lean_ctor_get(v___x_4803_, 0);
lean_inc_ref(v_env_4805_);
lean_dec(v___x_4803_);
v___y_4789_ = v___y_4800_;
v___y_4790_ = v_defn_4798_;
v___y_4791_ = v___y_4799_;
v___y_4792_ = v_env_4802_;
v___y_4793_ = v_env_4805_;
goto v___jp_4788_;
}
}
}
}
}
}
else
{
goto v___jp_4350_;
}
v___jp_4506_:
{
lean_object* v___x_4519_; 
lean_inc_ref(v___y_4516_);
v___x_4519_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4517_, v___y_4516_, v___y_4510_, v___y_4518_);
if (lean_obj_tag(v___x_4519_) == 0)
{
lean_object* v___x_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4566_; 
lean_dec_ref_known(v___x_4519_, 1);
lean_dec(v___y_4511_);
lean_inc_ref(v___y_4509_);
v___x_4520_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4509_, v___y_4514_);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4520_);
if (v_isSharedCheck_4566_ == 0)
{
lean_object* v_unused_4567_; 
v_unused_4567_ = lean_ctor_get(v___x_4520_, 0);
lean_dec(v_unused_4567_);
v___x_4522_ = v___x_4520_;
v_isShared_4523_ = v_isSharedCheck_4566_;
goto v_resetjp_4521_;
}
else
{
lean_dec(v___x_4520_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4566_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v_options_4524_; lean_object* v___x_4525_; uint8_t v___x_4526_; 
v_options_4524_ = lean_ctor_get(v___y_4515_, 2);
v___x_4525_ = l_Lean_Elab_async;
v___x_4526_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4524_, v___x_4525_);
if (v___x_4526_ == 0)
{
lean_object* v___x_4527_; lean_object* v_r_4528_; 
lean_del_object(v___x_4522_);
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4512_);
v___x_4527_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4516_, v___y_4514_);
lean_dec_ref(v___x_4527_);
v_r_4528_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v___y_4508_, v___y_4514_);
if (lean_obj_tag(v_r_4528_) == 0)
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4538_; 
v_a_4529_ = lean_ctor_get(v_r_4528_, 0);
v_isSharedCheck_4538_ = !lean_is_exclusive(v_r_4528_);
if (v_isSharedCheck_4538_ == 0)
{
v___x_4531_ = v_r_4528_;
v_isShared_4532_ = v_isSharedCheck_4538_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v_r_4528_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4538_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
lean_inc(v_a_4529_);
if (v_isShared_4532_ == 0)
{
lean_ctor_set_tag(v___x_4531_, 1);
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
lean_object* v___x_4535_; 
v___x_4535_ = lean_apply_2(v___y_4507_, v___x_4534_, lean_box(0));
if (lean_obj_tag(v___x_4535_) == 0)
{
lean_dec_ref_known(v___x_4535_, 1);
v___y_3785_ = v___y_4509_;
v___y_3786_ = v___y_4514_;
v_a_3787_ = v_a_4529_;
goto v___jp_3784_;
}
else
{
lean_object* v_a_4536_; 
lean_dec(v_a_4529_);
v_a_4536_ = lean_ctor_get(v___x_4535_, 0);
lean_inc(v_a_4536_);
lean_dec_ref_known(v___x_4535_, 1);
v___y_3798_ = v___y_4509_;
v___y_3799_ = v___y_4514_;
v_a_3800_ = v_a_4536_;
goto v___jp_3797_;
}
}
}
}
else
{
lean_object* v_a_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
v_a_4539_ = lean_ctor_get(v_r_4528_, 0);
lean_inc(v_a_4539_);
lean_dec_ref_known(v_r_4528_, 1);
v___x_4540_ = lean_box(0);
v___x_4541_ = lean_apply_2(v___y_4507_, v___x_4540_, lean_box(0));
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_dec_ref_known(v___x_4541_, 1);
v___y_3798_ = v___y_4509_;
v___y_3799_ = v___y_4514_;
v_a_3800_ = v_a_4539_;
goto v___jp_3797_;
}
else
{
lean_object* v_a_4542_; 
lean_dec(v_a_4539_);
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
lean_inc(v_a_4542_);
lean_dec_ref_known(v___x_4541_, 1);
v___y_3798_ = v___y_4509_;
v___y_3799_ = v___y_4514_;
v_a_3800_ = v_a_4542_;
goto v___jp_3797_;
}
}
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4545_; 
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4509_);
lean_dec_ref(v___y_4507_);
lean_dec(v_decl_3779_);
v___x_4543_ = l_IO_CancelToken_new();
if (v_isShared_4523_ == 0)
{
lean_ctor_set_tag(v___x_4522_, 1);
lean_ctor_set(v___x_4522_, 0, v___x_4543_);
v___x_4545_ = v___x_4522_;
goto v_reusejp_4544_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4543_);
v___x_4545_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4544_;
}
v_reusejp_4544_:
{
lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; lean_object* v___x_4549_; 
v___x_4546_ = lean_unsigned_to_nat(0u);
v___x_4547_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4548_ = l_Lean_Name_toString(v___x_4547_, v_hasTrace_3839_);
lean_inc_ref(v___x_4545_);
v___x_4549_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4513_, v___x_4545_, v___x_4548_, v___y_4508_, v___y_4514_);
if (lean_obj_tag(v___x_4549_) == 0)
{
lean_object* v_a_4550_; lean_object* v_checked_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; lean_object* v___x_4554_; lean_object* v___x_4555_; lean_object* v___x_4556_; 
v_a_4550_ = lean_ctor_get(v___x_4549_, 0);
lean_inc(v_a_4550_);
lean_dec_ref_known(v___x_4549_, 1);
v_checked_4551_ = lean_ctor_get(v___y_4512_, 2);
lean_inc_ref(v_checked_4551_);
lean_dec_ref(v___y_4512_);
v___x_4552_ = lean_io_map_task(v_a_4550_, v_checked_4551_, v___x_4546_, v___x_4505_);
v___x_4553_ = lean_box(0);
v___x_4554_ = lean_box(2);
v___x_4555_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4555_, 0, v___x_4553_);
lean_ctor_set(v___x_4555_, 1, v___x_4554_);
lean_ctor_set(v___x_4555_, 2, v___x_4545_);
lean_ctor_set(v___x_4555_, 3, v___x_4552_);
v___x_4556_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4555_, v___y_4514_);
return v___x_4556_;
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec_ref(v___x_4545_);
lean_dec_ref(v___y_4512_);
v_a_4557_ = lean_ctor_get(v___x_4549_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4549_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4549_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4549_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
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
}
}
}
else
{
lean_object* v_a_4568_; lean_object* v___x_4570_; uint8_t v_isShared_4571_; uint8_t v_isSharedCheck_4579_; 
lean_dec_ref(v___y_4516_);
lean_dec_ref(v___y_4513_);
lean_dec_ref(v___y_4512_);
lean_dec_ref(v___y_4509_);
lean_dec_ref(v___y_4507_);
lean_dec(v_decl_3779_);
v_a_4568_ = lean_ctor_get(v___x_4519_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4519_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4570_ = v___x_4519_;
v_isShared_4571_ = v_isSharedCheck_4579_;
goto v_resetjp_4569_;
}
else
{
lean_inc(v_a_4568_);
lean_dec(v___x_4519_);
v___x_4570_ = lean_box(0);
v_isShared_4571_ = v_isSharedCheck_4579_;
goto v_resetjp_4569_;
}
v_resetjp_4569_:
{
lean_object* v___x_4572_; lean_object* v___x_4573_; lean_object* v___x_4574_; lean_object* v___x_4575_; lean_object* v___x_4577_; 
v___x_4572_ = lean_io_error_to_string(v_a_4568_);
v___x_4573_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4573_, 0, v___x_4572_);
v___x_4574_ = l_Lean_MessageData_ofFormat(v___x_4573_);
v___x_4575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4575_, 0, v___y_4511_);
lean_ctor_set(v___x_4575_, 1, v___x_4574_);
if (v_isShared_4571_ == 0)
{
lean_ctor_set(v___x_4570_, 0, v___x_4575_);
v___x_4577_ = v___x_4570_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4575_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
v___jp_4580_:
{
lean_object* v_toCold_4589_; lean_object* v_ref_4590_; lean_object* v___x_4591_; 
v_toCold_4589_ = lean_ctor_get(v___y_4581_, 0);
v_ref_4590_ = lean_ctor_get(v___y_4581_, 2);
lean_inc_ref(v___y_4587_);
v___x_4591_ = l_Lean_Environment_addConstAsync(v___y_4587_, v___y_4586_, v___y_4582_, v___y_4588_, v___x_4505_, v_hasTrace_3839_);
if (lean_obj_tag(v___x_4591_) == 0)
{
lean_object* v_a_4592_; lean_object* v_mainEnv_4593_; lean_object* v_asyncEnv_4594_; lean_object* v___f_4595_; lean_object* v___f_4596_; lean_object* v___x_4597_; 
v_a_4592_ = lean_ctor_get(v___x_4591_, 0);
lean_inc_n(v_a_4592_, 3);
lean_dec_ref_known(v___x_4591_, 1);
v_mainEnv_4593_ = lean_ctor_get(v_a_4592_, 0);
lean_inc_ref(v_mainEnv_4593_);
v_asyncEnv_4594_ = lean_ctor_get(v_a_4592_, 1);
lean_inc_ref_n(v_asyncEnv_4594_, 2);
lean_inc(v_ref_4590_);
lean_inc(v___y_4584_);
v___f_4595_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4595_, 0, v___y_4584_);
lean_closure_set(v___f_4595_, 1, v_a_4592_);
lean_closure_set(v___f_4595_, 2, v_ref_4590_);
lean_inc(v_decl_3779_);
v___f_4596_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4596_, 0, v_a_4592_);
lean_closure_set(v___f_4596_, 1, v_asyncEnv_4594_);
lean_closure_set(v___f_4596_, 2, v_decl_3779_);
v___x_4597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___y_4583_);
if (lean_obj_tag(v___y_4585_) == 0)
{
lean_inc(v_ref_4590_);
lean_inc_ref(v___x_4597_);
v___y_4507_ = v___f_4595_;
v___y_4508_ = v___y_4581_;
v___y_4509_ = v_mainEnv_4593_;
v___y_4510_ = v___x_4597_;
v___y_4511_ = v_ref_4590_;
v___y_4512_ = v___y_4587_;
v___y_4513_ = v___f_4596_;
v___y_4514_ = v___y_4584_;
v___y_4515_ = v_toCold_4589_;
v___y_4516_ = v_asyncEnv_4594_;
v___y_4517_ = v_a_4592_;
v___y_4518_ = v___x_4597_;
goto v___jp_4506_;
}
else
{
lean_inc(v_ref_4590_);
v___y_4507_ = v___f_4595_;
v___y_4508_ = v___y_4581_;
v___y_4509_ = v_mainEnv_4593_;
v___y_4510_ = v___x_4597_;
v___y_4511_ = v_ref_4590_;
v___y_4512_ = v___y_4587_;
v___y_4513_ = v___f_4596_;
v___y_4514_ = v___y_4584_;
v___y_4515_ = v_toCold_4589_;
v___y_4516_ = v_asyncEnv_4594_;
v___y_4517_ = v_a_4592_;
v___y_4518_ = v___y_4585_;
goto v___jp_4506_;
}
}
else
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4609_; 
lean_dec_ref(v___y_4587_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4583_);
lean_dec(v_decl_3779_);
v_a_4598_ = lean_ctor_get(v___x_4591_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4591_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4600_ = v___x_4591_;
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4591_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4609_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
lean_object* v___x_4602_; lean_object* v___x_4603_; lean_object* v___x_4604_; lean_object* v___x_4605_; lean_object* v___x_4607_; 
v___x_4602_ = lean_io_error_to_string(v_a_4598_);
v___x_4603_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4603_, 0, v___x_4602_);
v___x_4604_ = l_Lean_MessageData_ofFormat(v___x_4603_);
lean_inc(v_ref_4590_);
v___x_4605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4605_, 0, v_ref_4590_);
lean_ctor_set(v___x_4605_, 1, v___x_4604_);
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4605_);
v___x_4607_ = v___x_4600_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
v___jp_4610_:
{
lean_object* v___x_4617_; 
v___x_4617_ = lean_st_ref_get(v___y_4616_);
if (lean_obj_tag(v_exportedInfo_x3f_4614_) == 0)
{
lean_object* v_env_4618_; lean_object* v___x_4619_; 
v_env_4618_ = lean_ctor_get(v___x_4617_, 0);
lean_inc_ref(v_env_4618_);
lean_dec(v___x_4617_);
v___x_4619_ = lean_box(0);
v___y_4581_ = v___y_4615_;
v___y_4582_ = v___y_4612_;
v___y_4583_ = v___y_4613_;
v___y_4584_ = v___y_4616_;
v___y_4585_ = v_exportedInfo_x3f_4614_;
v___y_4586_ = v___y_4611_;
v___y_4587_ = v_env_4618_;
v___y_4588_ = v___x_4619_;
goto v___jp_4580_;
}
else
{
lean_object* v_env_4620_; lean_object* v_val_4621_; uint8_t v___x_4622_; lean_object* v___x_4623_; lean_object* v___x_4624_; 
v_env_4620_ = lean_ctor_get(v___x_4617_, 0);
lean_inc_ref(v_env_4620_);
lean_dec(v___x_4617_);
v_val_4621_ = lean_ctor_get(v_exportedInfo_x3f_4614_, 0);
v___x_4622_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4621_);
v___x_4623_ = lean_box(v___x_4622_);
v___x_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4624_, 0, v___x_4623_);
v___y_4581_ = v___y_4615_;
v___y_4582_ = v___y_4612_;
v___y_4583_ = v___y_4613_;
v___y_4584_ = v___y_4616_;
v___y_4585_ = v_exportedInfo_x3f_4614_;
v___y_4586_ = v___y_4611_;
v___y_4587_ = v_env_4620_;
v___y_4588_ = v___x_4624_;
goto v___jp_4580_;
}
}
v___jp_4625_:
{
lean_object* v___x_4631_; 
lean_inc_ref(v___y_4628_);
v___x_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4631_, 0, v___y_4628_);
v___y_4611_ = v___y_4626_;
v___y_4612_ = v___y_4627_;
v___y_4613_ = v___y_4628_;
v_exportedInfo_x3f_4614_ = v___x_4631_;
v___y_4615_ = v___y_4629_;
v___y_4616_ = v___y_4630_;
goto v___jp_4610_;
}
v___jp_4632_:
{
lean_object* v___x_4638_; 
lean_inc_ref(v___y_4635_);
v___x_4638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4638_, 0, v___y_4635_);
v___y_4611_ = v___y_4633_;
v___y_4612_ = v___y_4634_;
v___y_4613_ = v___y_4635_;
v_exportedInfo_x3f_4614_ = v___x_4638_;
v___y_4615_ = v___y_4636_;
v___y_4616_ = v___y_4637_;
goto v___jp_4610_;
}
}
else
{
goto v___jp_4350_;
}
v___jp_4203_:
{
lean_object* v___x_4207_; double v___x_4208_; double v___x_4209_; double v___x_4210_; double v___x_4211_; double v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4207_ = lean_io_mono_nanos_now();
v___x_4208_ = lean_float_of_nat(v___y_4204_);
v___x_4209_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4210_ = lean_float_div(v___x_4208_, v___x_4209_);
v___x_4211_ = lean_float_of_nat(v___x_4207_);
v___x_4212_ = lean_float_div(v___x_4211_, v___x_4209_);
v___x_4213_ = lean_box_float(v___x_4210_);
v___x_4214_ = lean_box_float(v___x_4212_);
v___x_4215_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4216_, 0, v_a_4206_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3975_, v_hasTrace_3839_, v___x_4200_, v_options_3837_, v___x_4202_, v___y_4205_, v___f_4199_, v___x_4216_, v_a_3781_, v_a_3782_);
return v___x_4217_;
}
v___jp_4218_:
{
if (lean_obj_tag(v___y_4221_) == 0)
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
v_a_4222_ = lean_ctor_get(v___y_4221_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___y_4221_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___y_4221_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___y_4221_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
lean_ctor_set_tag(v___x_4224_, 1);
v___x_4227_ = v___x_4224_;
goto v_reusejp_4226_;
}
else
{
lean_object* v_reuseFailAlloc_4228_; 
v_reuseFailAlloc_4228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4228_, 0, v_a_4222_);
v___x_4227_ = v_reuseFailAlloc_4228_;
goto v_reusejp_4226_;
}
v_reusejp_4226_:
{
v___y_4204_ = v___y_4219_;
v___y_4205_ = v___y_4220_;
v_a_4206_ = v___x_4227_;
goto v___jp_4203_;
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
v_a_4230_ = lean_ctor_get(v___y_4221_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___y_4221_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___y_4221_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___y_4221_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
lean_ctor_set_tag(v___x_4232_, 0);
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
v___y_4204_ = v___y_4219_;
v___y_4205_ = v___y_4220_;
v_a_4206_ = v___x_4235_;
goto v___jp_4203_;
}
}
}
}
v___jp_4238_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4244_ = lean_apply_5(v___y_4242_, v___x_4243_, v___y_4241_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4239_;
v___y_4220_ = v___y_4240_;
v___y_4221_ = v___x_4244_;
goto v___jp_4218_;
}
v___jp_4245_:
{
lean_object* v___x_4253_; uint8_t v_isModule_4254_; 
v___x_4253_ = l_Lean_Environment_header(v___y_4250_);
lean_dec_ref(v___y_4250_);
v_isModule_4254_ = lean_ctor_get_uint8(v___x_4253_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4253_);
if (v_isModule_4254_ == 0)
{
lean_dec_ref(v___y_4251_);
lean_dec_ref(v___y_4247_);
v___y_4239_ = v___y_4246_;
v___y_4240_ = v___y_4248_;
v___y_4241_ = v___y_4249_;
v___y_4242_ = v___y_4252_;
goto v___jp_4238_;
}
else
{
lean_dec_ref(v___y_4252_);
lean_dec(v___y_4249_);
if (v___x_4202_ == 0)
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
lean_dec_ref(v___y_4247_);
v___x_4255_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4256_ = lean_apply_4(v___y_4251_, v___x_4255_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4248_;
v___y_4221_ = v___x_4256_;
goto v___jp_4218_;
}
else
{
lean_object* v_toConstantVal_4257_; lean_object* v_name_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v_toConstantVal_4257_ = lean_ctor_get(v___y_4247_, 0);
lean_inc_ref(v_toConstantVal_4257_);
lean_dec_ref(v___y_4247_);
v_name_4258_ = lean_ctor_get(v_toConstantVal_4257_, 0);
lean_inc(v_name_4258_);
lean_dec_ref(v_toConstantVal_4257_);
v___x_4259_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4260_ = l_Lean_MessageData_ofName(v_name_4258_);
v___x_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4259_);
lean_ctor_set(v___x_4261_, 1, v___x_4260_);
v___x_4262_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4263_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4264_) == 0)
{
lean_object* v_a_4265_; lean_object* v___x_4266_; 
v_a_4265_ = lean_ctor_get(v___x_4264_, 0);
lean_inc(v_a_4265_);
lean_dec_ref_known(v___x_4264_, 1);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4266_ = lean_apply_4(v___y_4251_, v_a_4265_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4248_;
v___y_4221_ = v___x_4266_;
goto v___jp_4218_;
}
else
{
lean_dec_ref(v___y_4251_);
v___y_4219_ = v___y_4246_;
v___y_4220_ = v___y_4248_;
v___y_4221_ = v___x_4264_;
goto v___jp_4218_;
}
}
}
}
v___jp_4267_:
{
if (v___x_4202_ == 0)
{
lean_object* v___x_4272_; lean_object* v___x_4273_; 
lean_dec_ref(v___y_4269_);
v___x_4272_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4273_ = lean_apply_4(v___y_4271_, v___x_4272_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4268_;
v___y_4220_ = v___y_4270_;
v___y_4221_ = v___x_4273_;
goto v___jp_4218_;
}
else
{
lean_object* v_toConstantVal_4274_; lean_object* v_name_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v___x_4278_; lean_object* v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v_toConstantVal_4274_ = lean_ctor_get(v___y_4269_, 0);
lean_inc_ref(v_toConstantVal_4274_);
lean_dec_ref(v___y_4269_);
v_name_4275_ = lean_ctor_get(v_toConstantVal_4274_, 0);
lean_inc(v_name_4275_);
lean_dec_ref(v_toConstantVal_4274_);
v___x_4276_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4277_ = l_Lean_MessageData_ofName(v_name_4275_);
v___x_4278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4278_, 0, v___x_4276_);
lean_ctor_set(v___x_4278_, 1, v___x_4277_);
v___x_4279_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4280_, 0, v___x_4278_);
lean_ctor_set(v___x_4280_, 1, v___x_4279_);
v___x_4281_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4280_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4281_) == 0)
{
lean_object* v_a_4282_; lean_object* v___x_4283_; 
v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
lean_inc(v_a_4282_);
lean_dec_ref_known(v___x_4281_, 1);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4283_ = lean_apply_4(v___y_4271_, v_a_4282_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4268_;
v___y_4220_ = v___y_4270_;
v___y_4221_ = v___x_4283_;
goto v___jp_4218_;
}
else
{
lean_dec_ref(v___y_4271_);
v___y_4219_ = v___y_4268_;
v___y_4220_ = v___y_4270_;
v___y_4221_ = v___x_4281_;
goto v___jp_4218_;
}
}
}
v___jp_4284_:
{
lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4289_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4290_ = lean_apply_5(v___y_4286_, v___x_4289_, v___y_4288_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4219_ = v___y_4285_;
v___y_4220_ = v___y_4287_;
v___y_4221_ = v___x_4290_;
goto v___jp_4218_;
}
v___jp_4291_:
{
lean_object* v___x_4301_; uint8_t v_isModule_4302_; 
v___x_4301_ = l_Lean_Environment_header(v___y_4299_);
lean_dec_ref(v___y_4299_);
v_isModule_4302_ = lean_ctor_get_uint8(v___x_4301_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4301_);
if (v_isModule_4302_ == 0)
{
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4298_);
lean_dec_ref(v___y_4294_);
v___y_4285_ = v___y_4293_;
v___y_4286_ = v___y_4292_;
v___y_4287_ = v___y_4296_;
v___y_4288_ = v___y_4297_;
goto v___jp_4284_;
}
else
{
uint8_t v_isExporting_4303_; 
v_isExporting_4303_ = lean_ctor_get_uint8(v___y_4298_, sizeof(void*)*8);
lean_dec_ref(v___y_4298_);
if (v_isExporting_4303_ == 0)
{
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4292_);
v___y_4268_ = v___y_4293_;
v___y_4269_ = v___y_4294_;
v___y_4270_ = v___y_4296_;
v___y_4271_ = v___y_4300_;
goto v___jp_4267_;
}
else
{
if (v___y_4295_ == 0)
{
lean_dec_ref(v___y_4300_);
lean_dec_ref(v___y_4294_);
v___y_4285_ = v___y_4293_;
v___y_4286_ = v___y_4292_;
v___y_4287_ = v___y_4296_;
v___y_4288_ = v___y_4297_;
goto v___jp_4284_;
}
else
{
lean_dec(v___y_4297_);
lean_dec_ref(v___y_4292_);
v___y_4268_ = v___y_4293_;
v___y_4269_ = v___y_4294_;
v___y_4270_ = v___y_4296_;
v___y_4271_ = v___y_4300_;
goto v___jp_4267_;
}
}
}
}
v___jp_4304_:
{
lean_object* v___x_4308_; double v___x_4309_; double v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; 
v___x_4308_ = lean_io_get_num_heartbeats();
v___x_4309_ = lean_float_of_nat(v___y_4306_);
v___x_4310_ = lean_float_of_nat(v___x_4308_);
v___x_4311_ = lean_box_float(v___x_4309_);
v___x_4312_ = lean_box_float(v___x_4310_);
v___x_4313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4314_, 0, v_a_4307_);
lean_ctor_set(v___x_4314_, 1, v___x_4313_);
v___x_4315_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3975_, v_hasTrace_3839_, v___x_4200_, v_options_3837_, v___x_4202_, v___y_4305_, v___f_4199_, v___x_4314_, v_a_3781_, v_a_3782_);
return v___x_4315_;
}
v___jp_4316_:
{
if (lean_obj_tag(v___y_4319_) == 0)
{
lean_object* v_a_4320_; lean_object* v___x_4322_; uint8_t v_isShared_4323_; uint8_t v_isSharedCheck_4327_; 
v_a_4320_ = lean_ctor_get(v___y_4319_, 0);
v_isSharedCheck_4327_ = !lean_is_exclusive(v___y_4319_);
if (v_isSharedCheck_4327_ == 0)
{
v___x_4322_ = v___y_4319_;
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
else
{
lean_inc(v_a_4320_);
lean_dec(v___y_4319_);
v___x_4322_ = lean_box(0);
v_isShared_4323_ = v_isSharedCheck_4327_;
goto v_resetjp_4321_;
}
v_resetjp_4321_:
{
lean_object* v___x_4325_; 
if (v_isShared_4323_ == 0)
{
lean_ctor_set_tag(v___x_4322_, 1);
v___x_4325_ = v___x_4322_;
goto v_reusejp_4324_;
}
else
{
lean_object* v_reuseFailAlloc_4326_; 
v_reuseFailAlloc_4326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4326_, 0, v_a_4320_);
v___x_4325_ = v_reuseFailAlloc_4326_;
goto v_reusejp_4324_;
}
v_reusejp_4324_:
{
v___y_4305_ = v___y_4317_;
v___y_4306_ = v___y_4318_;
v_a_4307_ = v___x_4325_;
goto v___jp_4304_;
}
}
}
else
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4335_; 
v_a_4328_ = lean_ctor_get(v___y_4319_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v___y_4319_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4330_ = v___y_4319_;
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___y_4319_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4335_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v___x_4333_; 
if (v_isShared_4331_ == 0)
{
lean_ctor_set_tag(v___x_4330_, 0);
v___x_4333_ = v___x_4330_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v_a_4328_);
v___x_4333_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
v___y_4305_ = v___y_4317_;
v___y_4306_ = v___y_4318_;
v_a_4307_ = v___x_4333_;
goto v___jp_4304_;
}
}
}
}
v___jp_4336_:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4342_ = lean_apply_5(v___y_4339_, v___x_4341_, v___y_4338_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4317_ = v___y_4337_;
v___y_4318_ = v___y_4340_;
v___y_4319_ = v___x_4342_;
goto v___jp_4316_;
}
v___jp_4343_:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = lean_box(0);
lean_inc(v_a_3782_);
lean_inc_ref(v_a_3781_);
v___x_4349_ = lean_apply_5(v___y_4346_, v___x_4348_, v___y_4345_, v_a_3781_, v_a_3782_, lean_box(0));
v___y_4317_ = v___y_4344_;
v___y_4318_ = v___y_4347_;
v___y_4319_ = v___x_4349_;
goto v___jp_4316_;
}
v___jp_4350_:
{
lean_object* v___x_4351_; lean_object* v_a_4352_; lean_object* v___x_4354_; uint8_t v_isShared_4355_; uint8_t v_isSharedCheck_4503_; 
v___x_4351_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3782_);
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4354_ = v___x_4351_;
v_isShared_4355_ = v_isSharedCheck_4503_;
goto v_resetjp_4353_;
}
else
{
lean_inc(v_a_4352_);
lean_dec(v___x_4351_);
v___x_4354_ = lean_box(0);
v_isShared_4355_ = v_isSharedCheck_4503_;
goto v_resetjp_4353_;
}
v_resetjp_4353_:
{
lean_object* v___x_4356_; uint8_t v___x_4357_; 
v___x_4356_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4357_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3837_, v___x_4356_);
if (v___x_4357_ == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v_env_4360_; lean_object* v_nextMacroScope_4361_; lean_object* v_ngen_4362_; lean_object* v_auxDeclNGen_4363_; lean_object* v_traceState_4364_; lean_object* v_messages_4365_; lean_object* v_infoState_4366_; lean_object* v_snapshotTasks_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4417_; 
v___x_4358_ = lean_io_mono_nanos_now();
v___x_4359_ = lean_st_ref_take(v_a_3782_);
v_env_4360_ = lean_ctor_get(v___x_4359_, 0);
v_nextMacroScope_4361_ = lean_ctor_get(v___x_4359_, 1);
v_ngen_4362_ = lean_ctor_get(v___x_4359_, 2);
v_auxDeclNGen_4363_ = lean_ctor_get(v___x_4359_, 3);
v_traceState_4364_ = lean_ctor_get(v___x_4359_, 4);
v_messages_4365_ = lean_ctor_get(v___x_4359_, 6);
v_infoState_4366_ = lean_ctor_get(v___x_4359_, 7);
v_snapshotTasks_4367_ = lean_ctor_get(v___x_4359_, 8);
v_isSharedCheck_4417_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4417_ == 0)
{
lean_object* v_unused_4418_; 
v_unused_4418_ = lean_ctor_get(v___x_4359_, 5);
lean_dec(v_unused_4418_);
v___x_4369_ = v___x_4359_;
v_isShared_4370_ = v_isSharedCheck_4417_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_snapshotTasks_4367_);
lean_inc(v_infoState_4366_);
lean_inc(v_messages_4365_);
lean_inc(v_traceState_4364_);
lean_inc(v_auxDeclNGen_4363_);
lean_inc(v_ngen_4362_);
lean_inc(v_nextMacroScope_4361_);
lean_inc(v_env_4360_);
lean_dec(v___x_4359_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4417_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; lean_object* v___x_4373_; lean_object* v___x_4375_; 
lean_inc(v_decl_3779_);
v___x_4371_ = l_Lean_Declaration_getNames(v_decl_3779_);
v___x_4372_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4360_, v___x_4371_);
v___x_4373_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4370_ == 0)
{
lean_ctor_set(v___x_4369_, 5, v___x_4373_);
lean_ctor_set(v___x_4369_, 0, v___x_4372_);
v___x_4375_ = v___x_4369_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4416_; 
v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4416_, 0, v___x_4372_);
lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_nextMacroScope_4361_);
lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_ngen_4362_);
lean_ctor_set(v_reuseFailAlloc_4416_, 3, v_auxDeclNGen_4363_);
lean_ctor_set(v_reuseFailAlloc_4416_, 4, v_traceState_4364_);
lean_ctor_set(v_reuseFailAlloc_4416_, 5, v___x_4373_);
lean_ctor_set(v_reuseFailAlloc_4416_, 6, v_messages_4365_);
lean_ctor_set(v_reuseFailAlloc_4416_, 7, v_infoState_4366_);
lean_ctor_set(v_reuseFailAlloc_4416_, 8, v_snapshotTasks_4367_);
v___x_4375_ = v_reuseFailAlloc_4416_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
lean_object* v___x_4376_; lean_object* v___x_4377_; lean_object* v___x_4378_; lean_object* v___x_4379_; lean_object* v___f_4380_; 
v___x_4376_ = lean_st_ref_put(v_a_3782_, v___x_4375_);
v___x_4377_ = lean_box(0);
v___x_4378_ = lean_box(v_hasTrace_3839_);
v___x_4379_ = lean_box(v___x_4357_);
lean_inc(v_decl_3779_);
v___f_4380_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 11, 6);
lean_closure_set(v___f_4380_, 0, v_decl_3779_);
lean_closure_set(v___f_4380_, 1, v___x_4378_);
lean_closure_set(v___f_4380_, 2, v___x_4379_);
lean_closure_set(v___f_4380_, 3, v___x_4373_);
lean_closure_set(v___f_4380_, 4, v_cls_3975_);
lean_closure_set(v___f_4380_, 5, v___x_4377_);
switch(lean_obj_tag(v_decl_3779_))
{
case 2:
{
lean_object* v_val_4381_; lean_object* v___f_4382_; lean_object* v___x_4383_; lean_object* v___f_4384_; lean_object* v___x_4385_; 
lean_del_object(v___x_4354_);
v_val_4381_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref_n(v_val_4381_, 3);
lean_dec_ref_known(v_decl_3779_, 1);
v___f_4382_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4382_, 0, v_val_4381_);
lean_closure_set(v___f_4382_, 1, v___f_4380_);
v___x_4383_ = lean_box(v___x_4357_);
lean_inc_ref(v___f_4382_);
v___f_4384_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4384_, 0, v_val_4381_);
lean_closure_set(v___f_4384_, 1, v___x_4383_);
lean_closure_set(v___f_4384_, 2, v___f_4382_);
v___x_4385_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4386_; 
v_env_4386_ = lean_ctor_get(v___x_4385_, 0);
lean_inc_ref(v_env_4386_);
lean_dec(v___x_4385_);
v___y_4246_ = v___x_4358_;
v___y_4247_ = v_val_4381_;
v___y_4248_ = v_a_4352_;
v___y_4249_ = v___x_4377_;
v___y_4250_ = v_env_4386_;
v___y_4251_ = v___f_4384_;
v___y_4252_ = v___f_4382_;
goto v___jp_4245_;
}
else
{
if (v___x_4357_ == 0)
{
lean_dec(v___x_4385_);
lean_dec_ref(v___f_4384_);
lean_dec_ref(v_val_4381_);
v___y_4239_ = v___x_4358_;
v___y_4240_ = v_a_4352_;
v___y_4241_ = v___x_4377_;
v___y_4242_ = v___f_4382_;
goto v___jp_4238_;
}
else
{
lean_object* v_env_4387_; 
v_env_4387_ = lean_ctor_get(v___x_4385_, 0);
lean_inc_ref(v_env_4387_);
lean_dec(v___x_4385_);
v___y_4246_ = v___x_4358_;
v___y_4247_ = v_val_4381_;
v___y_4248_ = v_a_4352_;
v___y_4249_ = v___x_4377_;
v___y_4250_ = v_env_4387_;
v___y_4251_ = v___f_4384_;
v___y_4252_ = v___f_4382_;
goto v___jp_4245_;
}
}
}
case 1:
{
lean_object* v_val_4388_; lean_object* v___x_4389_; 
lean_del_object(v___x_4354_);
v_val_4388_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref(v_val_4388_);
lean_dec_ref_known(v_decl_3779_, 1);
v___x_4389_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4380_, v___x_4357_, v_cls_3975_, v___x_4377_, v_forceExpose_3780_, v_val_4388_, v_a_3781_, v_a_3782_);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4389_;
goto v___jp_4218_;
}
case 5:
{
lean_object* v_defns_4390_; 
lean_del_object(v___x_4354_);
v_defns_4390_ = lean_ctor_get(v_decl_3779_, 0);
if (lean_obj_tag(v_defns_4390_) == 1)
{
lean_object* v_tail_4391_; 
v_tail_4391_ = lean_ctor_get(v_defns_4390_, 1);
if (lean_obj_tag(v_tail_4391_) == 0)
{
lean_object* v_head_4392_; lean_object* v___x_4393_; 
lean_inc_ref(v_defns_4390_);
lean_dec_ref_known(v_decl_3779_, 1);
v_head_4392_ = lean_ctor_get(v_defns_4390_, 0);
lean_inc(v_head_4392_);
lean_dec_ref_known(v_defns_4390_, 2);
v___x_4393_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4380_, v___x_4357_, v_cls_3975_, v___x_4377_, v_forceExpose_3780_, v_head_4392_, v_a_3781_, v_a_3782_);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4393_;
goto v___jp_4218_;
}
else
{
lean_object* v___x_4394_; 
lean_dec_ref(v___f_4380_);
lean_inc_ref(v_decl_3779_);
v___x_4394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec_ref_known(v_decl_3779_, 1);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4394_;
goto v___jp_4218_;
}
}
else
{
lean_object* v___x_4395_; 
lean_dec_ref(v___f_4380_);
lean_inc_ref(v_decl_3779_);
v___x_4395_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec_ref_known(v_decl_3779_, 1);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4395_;
goto v___jp_4218_;
}
}
case 3:
{
lean_object* v_val_4396_; lean_object* v___f_4397_; lean_object* v___f_4398_; lean_object* v___x_4399_; lean_object* v_env_4400_; lean_object* v___x_4401_; 
lean_del_object(v___x_4354_);
v_val_4396_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref_n(v_val_4396_, 3);
lean_dec_ref_known(v_decl_3779_, 1);
v___f_4397_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4397_, 0, v_val_4396_);
lean_closure_set(v___f_4397_, 1, v___f_4380_);
lean_inc_ref(v___f_4397_);
v___f_4398_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4398_, 0, v_val_4396_);
lean_closure_set(v___f_4398_, 1, v___f_4397_);
v___x_4399_ = lean_st_ref_get(v_a_3782_);
v_env_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc_ref(v_env_4400_);
lean_dec(v___x_4399_);
v___x_4401_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
lean_object* v_env_4402_; 
v_env_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_ref(v_env_4402_);
lean_dec(v___x_4401_);
v___y_4292_ = v___f_4397_;
v___y_4293_ = v___x_4358_;
v___y_4294_ = v_val_4396_;
v___y_4295_ = v___x_4357_;
v___y_4296_ = v_a_4352_;
v___y_4297_ = v___x_4377_;
v___y_4298_ = v_env_4402_;
v___y_4299_ = v_env_4400_;
v___y_4300_ = v___f_4398_;
goto v___jp_4291_;
}
else
{
if (v___x_4357_ == 0)
{
lean_dec(v___x_4401_);
lean_dec_ref(v_env_4400_);
lean_dec_ref(v___f_4398_);
lean_dec_ref(v_val_4396_);
v___y_4285_ = v___x_4358_;
v___y_4286_ = v___f_4397_;
v___y_4287_ = v_a_4352_;
v___y_4288_ = v___x_4377_;
goto v___jp_4284_;
}
else
{
lean_object* v_env_4403_; 
v_env_4403_ = lean_ctor_get(v___x_4401_, 0);
lean_inc_ref(v_env_4403_);
lean_dec(v___x_4401_);
v___y_4292_ = v___f_4397_;
v___y_4293_ = v___x_4358_;
v___y_4294_ = v_val_4396_;
v___y_4295_ = v___x_4357_;
v___y_4296_ = v_a_4352_;
v___y_4297_ = v___x_4377_;
v___y_4298_ = v_env_4403_;
v___y_4299_ = v_env_4400_;
v___y_4300_ = v___f_4398_;
goto v___jp_4291_;
}
}
}
case 0:
{
lean_object* v_val_4404_; lean_object* v_toConstantVal_4405_; lean_object* v_name_4406_; lean_object* v___x_4408_; 
lean_dec_ref(v___f_4380_);
v_val_4404_ = lean_ctor_get(v_decl_3779_, 0);
v_toConstantVal_4405_ = lean_ctor_get(v_val_4404_, 0);
v_name_4406_ = lean_ctor_get(v_toConstantVal_4405_, 0);
lean_inc_ref(v_val_4404_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v_val_4404_);
v___x_4408_ = v___x_4354_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_val_4404_);
v___x_4408_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
uint8_t v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4409_ = 2;
v___x_4410_ = lean_box(v___x_4409_);
v___x_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4408_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
lean_inc(v_name_4406_);
v___x_4412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4412_, 0, v_name_4406_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3779_, v_hasTrace_3839_, v___x_4357_, v___x_4373_, v_cls_3975_, v___x_4377_, v___x_4412_, v___x_4377_, v_a_3781_, v_a_3782_);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4413_;
goto v___jp_4218_;
}
}
default: 
{
lean_object* v___x_4415_; 
lean_dec_ref(v___f_4380_);
lean_del_object(v___x_4354_);
lean_inc(v_decl_3779_);
v___x_4415_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec(v_decl_3779_);
v___y_4219_ = v___x_4358_;
v___y_4220_ = v_a_4352_;
v___y_4221_ = v___x_4415_;
goto v___jp_4218_;
}
}
}
}
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v_env_4421_; lean_object* v_nextMacroScope_4422_; lean_object* v_ngen_4423_; lean_object* v_auxDeclNGen_4424_; lean_object* v_traceState_4425_; lean_object* v_messages_4426_; lean_object* v_infoState_4427_; lean_object* v_snapshotTasks_4428_; lean_object* v___x_4430_; uint8_t v_isShared_4431_; uint8_t v_isSharedCheck_4501_; 
v___x_4419_ = lean_io_get_num_heartbeats();
v___x_4420_ = lean_st_ref_take(v_a_3782_);
v_env_4421_ = lean_ctor_get(v___x_4420_, 0);
v_nextMacroScope_4422_ = lean_ctor_get(v___x_4420_, 1);
v_ngen_4423_ = lean_ctor_get(v___x_4420_, 2);
v_auxDeclNGen_4424_ = lean_ctor_get(v___x_4420_, 3);
v_traceState_4425_ = lean_ctor_get(v___x_4420_, 4);
v_messages_4426_ = lean_ctor_get(v___x_4420_, 6);
v_infoState_4427_ = lean_ctor_get(v___x_4420_, 7);
v_snapshotTasks_4428_ = lean_ctor_get(v___x_4420_, 8);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4501_ == 0)
{
lean_object* v_unused_4502_; 
v_unused_4502_ = lean_ctor_get(v___x_4420_, 5);
lean_dec(v_unused_4502_);
v___x_4430_ = v___x_4420_;
v_isShared_4431_ = v_isSharedCheck_4501_;
goto v_resetjp_4429_;
}
else
{
lean_inc(v_snapshotTasks_4428_);
lean_inc(v_infoState_4427_);
lean_inc(v_messages_4426_);
lean_inc(v_traceState_4425_);
lean_inc(v_auxDeclNGen_4424_);
lean_inc(v_ngen_4423_);
lean_inc(v_nextMacroScope_4422_);
lean_inc(v_env_4421_);
lean_dec(v___x_4420_);
v___x_4430_ = lean_box(0);
v_isShared_4431_ = v_isSharedCheck_4501_;
goto v_resetjp_4429_;
}
v_resetjp_4429_:
{
lean_object* v___x_4432_; lean_object* v___x_4433_; lean_object* v___x_4434_; lean_object* v___x_4436_; 
lean_inc(v_decl_3779_);
v___x_4432_ = l_Lean_Declaration_getNames(v_decl_3779_);
v___x_4433_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4421_, v___x_4432_);
v___x_4434_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4431_ == 0)
{
lean_ctor_set(v___x_4430_, 5, v___x_4434_);
lean_ctor_set(v___x_4430_, 0, v___x_4433_);
v___x_4436_ = v___x_4430_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v___x_4433_);
lean_ctor_set(v_reuseFailAlloc_4500_, 1, v_nextMacroScope_4422_);
lean_ctor_set(v_reuseFailAlloc_4500_, 2, v_ngen_4423_);
lean_ctor_set(v_reuseFailAlloc_4500_, 3, v_auxDeclNGen_4424_);
lean_ctor_set(v_reuseFailAlloc_4500_, 4, v_traceState_4425_);
lean_ctor_set(v_reuseFailAlloc_4500_, 5, v___x_4434_);
lean_ctor_set(v_reuseFailAlloc_4500_, 6, v_messages_4426_);
lean_ctor_set(v_reuseFailAlloc_4500_, 7, v_infoState_4427_);
lean_ctor_set(v_reuseFailAlloc_4500_, 8, v_snapshotTasks_4428_);
v___x_4436_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___f_4440_; 
v___x_4437_ = lean_st_ref_put(v_a_3782_, v___x_4436_);
v___x_4438_ = lean_box(0);
v___x_4439_ = lean_box(v___x_4357_);
lean_inc(v_decl_3779_);
v___f_4440_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 10, 5);
lean_closure_set(v___f_4440_, 0, v_decl_3779_);
lean_closure_set(v___f_4440_, 1, v___x_4439_);
lean_closure_set(v___f_4440_, 2, v_cls_3975_);
lean_closure_set(v___f_4440_, 3, v___x_4434_);
lean_closure_set(v___f_4440_, 4, v___x_4438_);
switch(lean_obj_tag(v_decl_3779_))
{
case 2:
{
lean_object* v_val_4441_; lean_object* v___f_4442_; lean_object* v___x_4443_; 
lean_del_object(v___x_4354_);
v_val_4441_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref_n(v_val_4441_, 2);
lean_dec_ref_known(v_decl_3779_, 1);
v___f_4442_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4442_, 0, v_val_4441_);
lean_closure_set(v___f_4442_, 1, v___f_4440_);
v___x_4443_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
if (v___x_4357_ == 0)
{
lean_dec(v___x_4443_);
lean_dec_ref(v_val_4441_);
v___y_4344_ = v_a_4352_;
v___y_4345_ = v___x_4438_;
v___y_4346_ = v___f_4442_;
v___y_4347_ = v___x_4419_;
goto v___jp_4343_;
}
else
{
lean_object* v_env_4444_; lean_object* v___x_4445_; uint8_t v_isModule_4446_; 
v_env_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc_ref(v_env_4444_);
lean_dec(v___x_4443_);
v___x_4445_ = l_Lean_Environment_header(v_env_4444_);
lean_dec_ref(v_env_4444_);
v_isModule_4446_ = lean_ctor_get_uint8(v___x_4445_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4445_);
if (v_isModule_4446_ == 0)
{
lean_dec_ref(v_val_4441_);
v___y_4344_ = v_a_4352_;
v___y_4345_ = v___x_4438_;
v___y_4346_ = v___f_4442_;
v___y_4347_ = v___x_4419_;
goto v___jp_4343_;
}
else
{
if (v___x_4202_ == 0)
{
lean_object* v___x_4447_; lean_object* v___x_4448_; 
v___x_4447_ = lean_box(0);
v___x_4448_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4441_, v___f_4442_, v___x_4447_, v_a_3781_, v_a_3782_);
lean_dec_ref(v_val_4441_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4448_;
goto v___jp_4316_;
}
else
{
lean_object* v_toConstantVal_4449_; lean_object* v_name_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; lean_object* v___x_4455_; lean_object* v___x_4456_; 
v_toConstantVal_4449_ = lean_ctor_get(v_val_4441_, 0);
v_name_4450_ = lean_ctor_get(v_toConstantVal_4449_, 0);
v___x_4451_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4450_);
v___x_4452_ = l_Lean_MessageData_ofName(v_name_4450_);
v___x_4453_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4453_, 0, v___x_4451_);
lean_ctor_set(v___x_4453_, 1, v___x_4452_);
v___x_4454_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4455_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4455_, 0, v___x_4453_);
lean_ctor_set(v___x_4455_, 1, v___x_4454_);
v___x_4456_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4455_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4456_) == 0)
{
lean_object* v_a_4457_; lean_object* v___x_4458_; 
v_a_4457_ = lean_ctor_get(v___x_4456_, 0);
lean_inc(v_a_4457_);
lean_dec_ref_known(v___x_4456_, 1);
v___x_4458_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4441_, v___f_4442_, v_a_4457_, v_a_3781_, v_a_3782_);
lean_dec_ref(v_val_4441_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4458_;
goto v___jp_4316_;
}
else
{
lean_dec_ref(v___f_4442_);
lean_dec_ref(v_val_4441_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4456_;
goto v___jp_4316_;
}
}
}
}
}
else
{
lean_dec(v___x_4443_);
lean_dec_ref(v_val_4441_);
v___y_4344_ = v_a_4352_;
v___y_4345_ = v___x_4438_;
v___y_4346_ = v___f_4442_;
v___y_4347_ = v___x_4419_;
goto v___jp_4343_;
}
}
case 1:
{
lean_object* v_val_4459_; lean_object* v___x_4460_; 
lean_del_object(v___x_4354_);
v_val_4459_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref(v_val_4459_);
lean_dec_ref_known(v_decl_3779_, 1);
v___x_4460_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4440_, v_forceExpose_3780_, v___x_4357_, v___x_4438_, v_cls_3975_, v_val_4459_, v_a_3781_, v_a_3782_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4460_;
goto v___jp_4316_;
}
case 5:
{
lean_object* v_defns_4461_; 
lean_del_object(v___x_4354_);
v_defns_4461_ = lean_ctor_get(v_decl_3779_, 0);
if (lean_obj_tag(v_defns_4461_) == 1)
{
lean_object* v_tail_4462_; 
v_tail_4462_ = lean_ctor_get(v_defns_4461_, 1);
if (lean_obj_tag(v_tail_4462_) == 0)
{
lean_object* v_head_4463_; lean_object* v___x_4464_; 
lean_inc_ref(v_defns_4461_);
lean_dec_ref_known(v_decl_3779_, 1);
v_head_4463_ = lean_ctor_get(v_defns_4461_, 0);
lean_inc(v_head_4463_);
lean_dec_ref_known(v_defns_4461_, 2);
v___x_4464_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4440_, v_forceExpose_3780_, v___x_4357_, v___x_4438_, v_cls_3975_, v_head_4463_, v_a_3781_, v_a_3782_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4464_;
goto v___jp_4316_;
}
else
{
lean_object* v___x_4465_; 
lean_dec_ref(v___f_4440_);
lean_inc_ref(v_decl_3779_);
v___x_4465_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec_ref_known(v_decl_3779_, 1);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4465_;
goto v___jp_4316_;
}
}
else
{
lean_object* v___x_4466_; 
lean_dec_ref(v___f_4440_);
lean_inc_ref(v_decl_3779_);
v___x_4466_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec_ref_known(v_decl_3779_, 1);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4466_;
goto v___jp_4316_;
}
}
case 3:
{
lean_object* v_val_4467_; lean_object* v___f_4468_; lean_object* v___x_4469_; lean_object* v_env_4470_; lean_object* v___x_4471_; 
lean_del_object(v___x_4354_);
v_val_4467_ = lean_ctor_get(v_decl_3779_, 0);
lean_inc_ref_n(v_val_4467_, 2);
lean_dec_ref_known(v_decl_3779_, 1);
v___f_4468_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4468_, 0, v_val_4467_);
lean_closure_set(v___f_4468_, 1, v___f_4440_);
v___x_4469_ = lean_st_ref_get(v_a_3782_);
v_env_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc_ref(v_env_4470_);
lean_dec(v___x_4469_);
v___x_4471_ = lean_st_ref_get(v_a_3782_);
if (v_forceExpose_3780_ == 0)
{
if (v___x_4357_ == 0)
{
lean_dec(v___x_4471_);
lean_dec_ref(v_env_4470_);
lean_dec_ref(v_val_4467_);
v___y_4337_ = v_a_4352_;
v___y_4338_ = v___x_4438_;
v___y_4339_ = v___f_4468_;
v___y_4340_ = v___x_4419_;
goto v___jp_4336_;
}
else
{
lean_object* v_env_4472_; lean_object* v___x_4473_; uint8_t v_isModule_4474_; 
v_env_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc_ref(v_env_4472_);
lean_dec(v___x_4471_);
v___x_4473_ = l_Lean_Environment_header(v_env_4470_);
lean_dec_ref(v_env_4470_);
v_isModule_4474_ = lean_ctor_get_uint8(v___x_4473_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4473_);
if (v_isModule_4474_ == 0)
{
lean_dec_ref(v_env_4472_);
lean_dec_ref(v_val_4467_);
v___y_4337_ = v_a_4352_;
v___y_4338_ = v___x_4438_;
v___y_4339_ = v___f_4468_;
v___y_4340_ = v___x_4419_;
goto v___jp_4336_;
}
else
{
uint8_t v_isExporting_4475_; 
v_isExporting_4475_ = lean_ctor_get_uint8(v_env_4472_, sizeof(void*)*8);
lean_dec_ref(v_env_4472_);
if (v_isExporting_4475_ == 0)
{
if (v___x_4202_ == 0)
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_box(0);
v___x_4477_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4467_, v___f_4468_, v___x_4476_, v_a_3781_, v_a_3782_);
lean_dec_ref(v_val_4467_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4477_;
goto v___jp_4316_;
}
else
{
lean_object* v_toConstantVal_4478_; lean_object* v_name_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; 
v_toConstantVal_4478_ = lean_ctor_get(v_val_4467_, 0);
v_name_4479_ = lean_ctor_get(v_toConstantVal_4478_, 0);
v___x_4480_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4479_);
v___x_4481_ = l_Lean_MessageData_ofName(v_name_4479_);
v___x_4482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4482_, 0, v___x_4480_);
lean_ctor_set(v___x_4482_, 1, v___x_4481_);
v___x_4483_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4482_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
v___x_4485_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_4484_, v_a_3781_, v_a_3782_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4487_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
lean_inc(v_a_4486_);
lean_dec_ref_known(v___x_4485_, 1);
v___x_4487_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4467_, v___f_4468_, v_a_4486_, v_a_3781_, v_a_3782_);
lean_dec_ref(v_val_4467_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4487_;
goto v___jp_4316_;
}
else
{
lean_dec_ref(v___f_4468_);
lean_dec_ref(v_val_4467_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4485_;
goto v___jp_4316_;
}
}
}
else
{
lean_dec_ref(v_val_4467_);
v___y_4337_ = v_a_4352_;
v___y_4338_ = v___x_4438_;
v___y_4339_ = v___f_4468_;
v___y_4340_ = v___x_4419_;
goto v___jp_4336_;
}
}
}
}
else
{
lean_dec(v___x_4471_);
lean_dec_ref(v_env_4470_);
lean_dec_ref(v_val_4467_);
v___y_4337_ = v_a_4352_;
v___y_4338_ = v___x_4438_;
v___y_4339_ = v___f_4468_;
v___y_4340_ = v___x_4419_;
goto v___jp_4336_;
}
}
case 0:
{
lean_object* v_val_4488_; lean_object* v_toConstantVal_4489_; lean_object* v_name_4490_; lean_object* v___x_4492_; 
lean_dec_ref(v___f_4440_);
v_val_4488_ = lean_ctor_get(v_decl_3779_, 0);
v_toConstantVal_4489_ = lean_ctor_get(v_val_4488_, 0);
v_name_4490_ = lean_ctor_get(v_toConstantVal_4489_, 0);
lean_inc_ref(v_val_4488_);
if (v_isShared_4355_ == 0)
{
lean_ctor_set(v___x_4354_, 0, v_val_4488_);
v___x_4492_ = v___x_4354_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_val_4488_);
v___x_4492_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
uint8_t v___x_4493_; lean_object* v___x_4494_; lean_object* v___x_4495_; lean_object* v___x_4496_; lean_object* v___x_4497_; 
v___x_4493_ = 2;
v___x_4494_ = lean_box(v___x_4493_);
v___x_4495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4495_, 0, v___x_4492_);
lean_ctor_set(v___x_4495_, 1, v___x_4494_);
lean_inc(v_name_4490_);
v___x_4496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4496_, 0, v_name_4490_);
lean_ctor_set(v___x_4496_, 1, v___x_4495_);
v___x_4497_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3779_, v___x_4357_, v_cls_3975_, v___x_4434_, v___x_4438_, v___x_4496_, v___x_4438_, v_a_3781_, v_a_3782_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4497_;
goto v___jp_4316_;
}
}
default: 
{
lean_object* v___x_4499_; 
lean_dec_ref(v___f_4440_);
lean_del_object(v___x_4354_);
lean_inc(v_decl_3779_);
v___x_4499_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3779_, v_cls_3975_, v_decl_3779_, v_a_3781_, v_a_3782_);
lean_dec(v_decl_3779_);
v___y_4317_ = v_a_4352_;
v___y_4318_ = v___x_4419_;
v___y_4319_ = v___x_4499_;
goto v___jp_4316_;
}
}
}
}
}
}
}
}
v___jp_3784_:
{
lean_object* v___x_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v___x_3788_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3785_, v___y_3786_);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3788_);
if (v_isSharedCheck_3795_ == 0)
{
lean_object* v_unused_3796_; 
v_unused_3796_ = lean_ctor_get(v___x_3788_, 0);
lean_dec(v_unused_3796_);
v___x_3790_ = v___x_3788_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_dec(v___x_3788_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
lean_ctor_set(v___x_3790_, 0, v_a_3787_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3787_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
v___jp_3797_:
{
lean_object* v___x_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
v___x_3801_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3798_, v___y_3799_);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v___x_3801_, 0);
lean_dec(v_unused_3809_);
v___x_3803_ = v___x_3801_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_dec(v___x_3801_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
lean_ctor_set_tag(v___x_3803_, 1);
lean_ctor_set(v___x_3803_, 0, v_a_3800_);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3800_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
v___jp_3810_:
{
lean_object* v___x_3814_; lean_object* v___x_3816_; uint8_t v_isShared_3817_; uint8_t v_isSharedCheck_3821_; 
v___x_3814_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3812_, v___y_3811_);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; 
v_unused_3822_ = lean_ctor_get(v___x_3814_, 0);
lean_dec(v_unused_3822_);
v___x_3816_ = v___x_3814_;
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
else
{
lean_dec(v___x_3814_);
v___x_3816_ = lean_box(0);
v_isShared_3817_ = v_isSharedCheck_3821_;
goto v_resetjp_3815_;
}
v_resetjp_3815_:
{
lean_object* v___x_3819_; 
if (v_isShared_3817_ == 0)
{
lean_ctor_set(v___x_3816_, 0, v_a_3813_);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v_a_3813_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
v___jp_3823_:
{
lean_object* v___x_3827_; lean_object* v___x_3829_; uint8_t v_isShared_3830_; uint8_t v_isSharedCheck_3834_; 
v___x_3827_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3825_, v___y_3824_);
v_isSharedCheck_3834_ = !lean_is_exclusive(v___x_3827_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; 
v_unused_3835_ = lean_ctor_get(v___x_3827_, 0);
lean_dec(v_unused_3835_);
v___x_3829_ = v___x_3827_;
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
else
{
lean_dec(v___x_3827_);
v___x_3829_ = lean_box(0);
v_isShared_3830_ = v_isSharedCheck_3834_;
goto v_resetjp_3828_;
}
v_resetjp_3828_:
{
lean_object* v___x_3832_; 
if (v_isShared_3830_ == 0)
{
lean_ctor_set_tag(v___x_3829_, 1);
lean_ctor_set(v___x_3829_, 0, v_a_3826_);
v___x_3832_ = v___x_3829_;
goto v_reusejp_3831_;
}
else
{
lean_object* v_reuseFailAlloc_3833_; 
v_reuseFailAlloc_3833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3826_);
v___x_3832_ = v_reuseFailAlloc_3833_;
goto v_reusejp_3831_;
}
v_reusejp_3831_:
{
return v___x_3832_;
}
}
}
v___jp_3840_:
{
lean_object* v___x_3854_; 
lean_inc_ref(v___y_3845_);
v___x_3854_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3851_, v___y_3845_, v___y_3852_, v___y_3853_);
if (lean_obj_tag(v___x_3854_) == 0)
{
lean_object* v___x_3855_; lean_object* v___x_3857_; uint8_t v_isShared_3858_; uint8_t v_isSharedCheck_3901_; 
lean_dec_ref_known(v___x_3854_, 1);
lean_dec(v___y_3850_);
lean_inc_ref(v___y_3844_);
v___x_3855_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3844_, v___y_3843_);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3855_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v___x_3855_, 0);
lean_dec(v_unused_3902_);
v___x_3857_ = v___x_3855_;
v_isShared_3858_ = v_isSharedCheck_3901_;
goto v_resetjp_3856_;
}
else
{
lean_dec(v___x_3855_);
v___x_3857_ = lean_box(0);
v_isShared_3858_ = v_isSharedCheck_3901_;
goto v_resetjp_3856_;
}
v_resetjp_3856_:
{
lean_object* v_options_3859_; lean_object* v___x_3860_; uint8_t v___x_3861_; 
v_options_3859_ = lean_ctor_get(v___y_3849_, 2);
v___x_3860_ = l_Lean_Elab_async;
v___x_3861_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3859_, v___x_3860_);
if (v___x_3861_ == 0)
{
lean_object* v___x_3862_; lean_object* v_r_3863_; 
lean_del_object(v___x_3857_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
v___x_3862_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3845_, v___y_3843_);
lean_dec_ref(v___x_3862_);
v_r_3863_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v___y_3846_, v___y_3843_);
if (lean_obj_tag(v_r_3863_) == 0)
{
lean_object* v_a_3864_; lean_object* v___x_3866_; uint8_t v_isShared_3867_; uint8_t v_isSharedCheck_3873_; 
v_a_3864_ = lean_ctor_get(v_r_3863_, 0);
v_isSharedCheck_3873_ = !lean_is_exclusive(v_r_3863_);
if (v_isSharedCheck_3873_ == 0)
{
v___x_3866_ = v_r_3863_;
v_isShared_3867_ = v_isSharedCheck_3873_;
goto v_resetjp_3865_;
}
else
{
lean_inc(v_a_3864_);
lean_dec(v_r_3863_);
v___x_3866_ = lean_box(0);
v_isShared_3867_ = v_isSharedCheck_3873_;
goto v_resetjp_3865_;
}
v_resetjp_3865_:
{
lean_object* v___x_3869_; 
lean_inc(v_a_3864_);
if (v_isShared_3867_ == 0)
{
lean_ctor_set_tag(v___x_3866_, 1);
v___x_3869_ = v___x_3866_;
goto v_reusejp_3868_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v_a_3864_);
v___x_3869_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3868_;
}
v_reusejp_3868_:
{
lean_object* v___x_3870_; 
v___x_3870_ = lean_apply_2(v___y_3848_, v___x_3869_, lean_box(0));
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_dec_ref_known(v___x_3870_, 1);
v___y_3811_ = v___y_3843_;
v___y_3812_ = v___y_3844_;
v_a_3813_ = v_a_3864_;
goto v___jp_3810_;
}
else
{
lean_object* v_a_3871_; 
lean_dec(v_a_3864_);
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___y_3824_ = v___y_3843_;
v___y_3825_ = v___y_3844_;
v_a_3826_ = v_a_3871_;
goto v___jp_3823_;
}
}
}
}
else
{
lean_object* v_a_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; 
v_a_3874_ = lean_ctor_get(v_r_3863_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v_r_3863_, 1);
v___x_3875_ = lean_box(0);
v___x_3876_ = lean_apply_2(v___y_3848_, v___x_3875_, lean_box(0));
if (lean_obj_tag(v___x_3876_) == 0)
{
lean_dec_ref_known(v___x_3876_, 1);
v___y_3824_ = v___y_3843_;
v___y_3825_ = v___y_3844_;
v_a_3826_ = v_a_3874_;
goto v___jp_3823_;
}
else
{
lean_object* v_a_3877_; 
lean_dec(v_a_3874_);
v_a_3877_ = lean_ctor_get(v___x_3876_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v___x_3876_, 1);
v___y_3824_ = v___y_3843_;
v___y_3825_ = v___y_3844_;
v_a_3826_ = v_a_3877_;
goto v___jp_3823_;
}
}
}
else
{
lean_object* v___x_3878_; lean_object* v___x_3880_; 
lean_dec_ref(v___y_3848_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v_decl_3779_);
v___x_3878_ = l_IO_CancelToken_new();
if (v_isShared_3858_ == 0)
{
lean_ctor_set_tag(v___x_3857_, 1);
lean_ctor_set(v___x_3857_, 0, v___x_3878_);
v___x_3880_ = v___x_3857_;
goto v_reusejp_3879_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3878_);
v___x_3880_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3879_;
}
v_reusejp_3879_:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; 
v___x_3881_ = lean_unsigned_to_nat(0u);
v___x_3882_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3883_ = l_Lean_Name_toString(v___x_3882_, v___y_3847_);
lean_inc_ref(v___x_3880_);
v___x_3884_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3842_, v___x_3880_, v___x_3883_, v___y_3846_, v___y_3843_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; lean_object* v_checked_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
v_checked_3886_ = lean_ctor_get(v___y_3841_, 2);
lean_inc_ref(v_checked_3886_);
lean_dec_ref(v___y_3841_);
v___x_3887_ = lean_io_map_task(v_a_3885_, v_checked_3886_, v___x_3881_, v_hasTrace_3839_);
v___x_3888_ = lean_box(0);
v___x_3889_ = lean_box(2);
v___x_3890_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
lean_ctor_set(v___x_3890_, 2, v___x_3880_);
lean_ctor_set(v___x_3890_, 3, v___x_3887_);
v___x_3891_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3890_, v___y_3843_);
return v___x_3891_;
}
else
{
lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
lean_dec_ref(v___x_3880_);
lean_dec_ref(v___y_3841_);
v_a_3892_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3884_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3884_);
v___x_3894_ = lean_box(0);
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
v_resetjp_3893_:
{
lean_object* v___x_3897_; 
if (v_isShared_3895_ == 0)
{
v___x_3897_ = v___x_3894_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3898_; 
v_reuseFailAlloc_3898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3898_, 0, v_a_3892_);
v___x_3897_ = v_reuseFailAlloc_3898_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
return v___x_3897_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3914_; 
lean_dec_ref(v___y_3848_);
lean_dec_ref(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v_decl_3779_);
v_a_3903_ = lean_ctor_get(v___x_3854_, 0);
v_isSharedCheck_3914_ = !lean_is_exclusive(v___x_3854_);
if (v_isSharedCheck_3914_ == 0)
{
v___x_3905_ = v___x_3854_;
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_a_3903_);
lean_dec(v___x_3854_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3914_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3907_ = lean_io_error_to_string(v_a_3903_);
v___x_3908_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
v___x_3909_ = l_Lean_MessageData_ofFormat(v___x_3908_);
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___y_3850_);
lean_ctor_set(v___x_3910_, 1, v___x_3909_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3910_);
v___x_3912_ = v___x_3905_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
v___jp_3915_:
{
lean_object* v_toCold_3924_; lean_object* v_ref_3925_; uint8_t v___x_3926_; lean_object* v___x_3927_; 
v_toCold_3924_ = lean_ctor_get(v___y_3916_, 0);
v_ref_3925_ = lean_ctor_get(v___y_3916_, 2);
v___x_3926_ = 1;
lean_inc_ref(v___y_3922_);
v___x_3927_ = l_Lean_Environment_addConstAsync(v___y_3922_, v___y_3919_, v___y_3920_, v___y_3923_, v_hasTrace_3839_, v___x_3926_);
if (lean_obj_tag(v___x_3927_) == 0)
{
lean_object* v_a_3928_; lean_object* v_mainEnv_3929_; lean_object* v_asyncEnv_3930_; lean_object* v___f_3931_; lean_object* v___f_3932_; lean_object* v___x_3933_; 
v_a_3928_ = lean_ctor_get(v___x_3927_, 0);
lean_inc_n(v_a_3928_, 3);
lean_dec_ref_known(v___x_3927_, 1);
v_mainEnv_3929_ = lean_ctor_get(v_a_3928_, 0);
lean_inc_ref(v_mainEnv_3929_);
v_asyncEnv_3930_ = lean_ctor_get(v_a_3928_, 1);
lean_inc_ref_n(v_asyncEnv_3930_, 2);
lean_inc(v_ref_3925_);
lean_inc(v___y_3917_);
v___f_3931_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3931_, 0, v___y_3917_);
lean_closure_set(v___f_3931_, 1, v_a_3928_);
lean_closure_set(v___f_3931_, 2, v_ref_3925_);
lean_inc(v_decl_3779_);
v___f_3932_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3932_, 0, v_a_3928_);
lean_closure_set(v___f_3932_, 1, v_asyncEnv_3930_);
lean_closure_set(v___f_3932_, 2, v_decl_3779_);
v___x_3933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___y_3918_);
if (lean_obj_tag(v___y_3921_) == 0)
{
lean_inc_ref(v___x_3933_);
lean_inc(v_ref_3925_);
v___y_3841_ = v___y_3922_;
v___y_3842_ = v___f_3932_;
v___y_3843_ = v___y_3917_;
v___y_3844_ = v_mainEnv_3929_;
v___y_3845_ = v_asyncEnv_3930_;
v___y_3846_ = v___y_3916_;
v___y_3847_ = v___x_3926_;
v___y_3848_ = v___f_3931_;
v___y_3849_ = v_toCold_3924_;
v___y_3850_ = v_ref_3925_;
v___y_3851_ = v_a_3928_;
v___y_3852_ = v___x_3933_;
v___y_3853_ = v___x_3933_;
goto v___jp_3840_;
}
else
{
lean_inc(v_ref_3925_);
v___y_3841_ = v___y_3922_;
v___y_3842_ = v___f_3932_;
v___y_3843_ = v___y_3917_;
v___y_3844_ = v_mainEnv_3929_;
v___y_3845_ = v_asyncEnv_3930_;
v___y_3846_ = v___y_3916_;
v___y_3847_ = v___x_3926_;
v___y_3848_ = v___f_3931_;
v___y_3849_ = v_toCold_3924_;
v___y_3850_ = v_ref_3925_;
v___y_3851_ = v_a_3928_;
v___y_3852_ = v___x_3933_;
v___y_3853_ = v___y_3921_;
goto v___jp_3840_;
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3945_; 
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3918_);
lean_dec(v_decl_3779_);
v_a_3934_ = lean_ctor_get(v___x_3927_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3927_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3936_ = v___x_3927_;
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3927_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3945_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3938_ = lean_io_error_to_string(v_a_3934_);
v___x_3939_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3938_);
v___x_3940_ = l_Lean_MessageData_ofFormat(v___x_3939_);
lean_inc(v_ref_3925_);
v___x_3941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3941_, 0, v_ref_3925_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
if (v_isShared_3937_ == 0)
{
lean_ctor_set(v___x_3936_, 0, v___x_3941_);
v___x_3943_ = v___x_3936_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v___x_3941_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
v___jp_3946_:
{
lean_object* v___x_3953_; 
v___x_3953_ = lean_st_ref_get(v___y_3952_);
if (lean_obj_tag(v_exportedInfo_x3f_3950_) == 0)
{
lean_object* v_env_3954_; lean_object* v___x_3955_; 
v_env_3954_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_ref(v_env_3954_);
lean_dec(v___x_3953_);
v___x_3955_ = lean_box(0);
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3948_;
v___y_3919_ = v___y_3949_;
v___y_3920_ = v___y_3947_;
v___y_3921_ = v_exportedInfo_x3f_3950_;
v___y_3922_ = v_env_3954_;
v___y_3923_ = v___x_3955_;
goto v___jp_3915_;
}
else
{
lean_object* v_env_3956_; lean_object* v_val_3957_; uint8_t v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; 
v_env_3956_ = lean_ctor_get(v___x_3953_, 0);
lean_inc_ref(v_env_3956_);
lean_dec(v___x_3953_);
v_val_3957_ = lean_ctor_get(v_exportedInfo_x3f_3950_, 0);
v___x_3958_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3957_);
v___x_3959_ = lean_box(v___x_3958_);
v___x_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3960_, 0, v___x_3959_);
v___y_3916_ = v___y_3951_;
v___y_3917_ = v___y_3952_;
v___y_3918_ = v___y_3948_;
v___y_3919_ = v___y_3949_;
v___y_3920_ = v___y_3947_;
v___y_3921_ = v_exportedInfo_x3f_3950_;
v___y_3922_ = v_env_3956_;
v___y_3923_ = v___x_3960_;
goto v___jp_3915_;
}
}
v___jp_3961_:
{
lean_object* v___x_3967_; 
lean_inc_ref(v___y_3963_);
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___y_3963_);
v___y_3947_ = v___y_3962_;
v___y_3948_ = v___y_3963_;
v___y_3949_ = v___y_3964_;
v_exportedInfo_x3f_3950_ = v___x_3967_;
v___y_3951_ = v___y_3965_;
v___y_3952_ = v___y_3966_;
goto v___jp_3946_;
}
v___jp_3968_:
{
lean_object* v___x_3974_; 
lean_inc_ref(v___y_3970_);
v___x_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3974_, 0, v___y_3970_);
v___y_3947_ = v___y_3969_;
v___y_3948_ = v___y_3970_;
v___y_3949_ = v___y_3971_;
v_exportedInfo_x3f_3950_ = v___x_3974_;
v___y_3951_ = v___y_3972_;
v___y_3952_ = v___y_3973_;
goto v___jp_3946_;
}
v___jp_3976_:
{
lean_object* v___x_3981_; uint8_t v___x_3982_; 
v___x_3981_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3982_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3979_, v_options_3978_, v___x_3981_);
if (v___x_3982_ == 0)
{
lean_object* v___x_3983_; 
v___x_3983_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v___y_3977_, v___y_3980_);
return v___x_3983_;
}
else
{
lean_object* v___x_3984_; lean_object* v___x_3985_; 
v___x_3984_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3985_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3975_, v___x_3984_, v___y_3977_, v___y_3980_);
if (lean_obj_tag(v___x_3985_) == 0)
{
lean_object* v___x_3986_; 
lean_dec_ref_known(v___x_3985_, 1);
v___x_3986_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3779_, v___y_3977_, v___y_3980_);
return v___x_3986_;
}
else
{
lean_dec(v_decl_3779_);
return v___x_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4881_, lean_object* v_forceExpose_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_){
_start:
{
uint8_t v_forceExpose_boxed_4886_; lean_object* v_res_4887_; 
v_forceExpose_boxed_4886_ = lean_unbox(v_forceExpose_4882_);
v_res_4887_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4881_, v_forceExpose_boxed_4886_, v_a_4883_, v_a_4884_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
return v_res_4887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
lean_object* v___x_4892_; 
v___x_4892_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4888_, v___y_4889_);
return v___x_4892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_){
_start:
{
lean_object* v_res_4897_; 
v_res_4897_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4893_, v___y_4894_, v___y_4895_);
lean_dec(v___y_4895_);
lean_dec_ref(v___y_4894_);
lean_dec_ref(v_opt_4893_);
return v_res_4897_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4898_, lean_object* v_x_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_){
_start:
{
if (lean_obj_tag(v_x_4898_) == 0)
{
lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4903_ = l_List_reverse___redArg(v_x_4899_);
v___x_4904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4904_, 0, v___x_4903_);
return v___x_4904_;
}
else
{
lean_object* v_head_4905_; lean_object* v_tail_4906_; lean_object* v___x_4908_; uint8_t v_isShared_4909_; uint8_t v_isSharedCheck_4924_; 
v_head_4905_ = lean_ctor_get(v_x_4898_, 0);
v_tail_4906_ = lean_ctor_get(v_x_4898_, 1);
v_isSharedCheck_4924_ = !lean_is_exclusive(v_x_4898_);
if (v_isSharedCheck_4924_ == 0)
{
v___x_4908_ = v_x_4898_;
v_isShared_4909_ = v_isSharedCheck_4924_;
goto v_resetjp_4907_;
}
else
{
lean_inc(v_tail_4906_);
lean_inc(v_head_4905_);
lean_dec(v_x_4898_);
v___x_4908_ = lean_box(0);
v_isShared_4909_ = v_isSharedCheck_4924_;
goto v_resetjp_4907_;
}
v_resetjp_4907_:
{
lean_object* v___x_4910_; 
v___x_4910_ = l_Lean_snapshotEnvLinterOptions(v_head_4905_, v___y_4900_, v___y_4901_);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v_a_4911_; lean_object* v___x_4913_; 
v_a_4911_ = lean_ctor_get(v___x_4910_, 0);
lean_inc(v_a_4911_);
lean_dec_ref_known(v___x_4910_, 1);
if (v_isShared_4909_ == 0)
{
lean_ctor_set(v___x_4908_, 1, v_x_4899_);
lean_ctor_set(v___x_4908_, 0, v_a_4911_);
v___x_4913_ = v___x_4908_;
goto v_reusejp_4912_;
}
else
{
lean_object* v_reuseFailAlloc_4915_; 
v_reuseFailAlloc_4915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4915_, 0, v_a_4911_);
lean_ctor_set(v_reuseFailAlloc_4915_, 1, v_x_4899_);
v___x_4913_ = v_reuseFailAlloc_4915_;
goto v_reusejp_4912_;
}
v_reusejp_4912_:
{
v_x_4898_ = v_tail_4906_;
v_x_4899_ = v___x_4913_;
goto _start;
}
}
else
{
lean_object* v_a_4916_; lean_object* v___x_4918_; uint8_t v_isShared_4919_; uint8_t v_isSharedCheck_4923_; 
lean_del_object(v___x_4908_);
lean_dec(v_tail_4906_);
lean_dec(v_x_4899_);
v_a_4916_ = lean_ctor_get(v___x_4910_, 0);
v_isSharedCheck_4923_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4923_ == 0)
{
v___x_4918_ = v___x_4910_;
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
else
{
lean_inc(v_a_4916_);
lean_dec(v___x_4910_);
v___x_4918_ = lean_box(0);
v_isShared_4919_ = v_isSharedCheck_4923_;
goto v_resetjp_4917_;
}
v_resetjp_4917_:
{
lean_object* v___x_4921_; 
if (v_isShared_4919_ == 0)
{
v___x_4921_ = v___x_4918_;
goto v_reusejp_4920_;
}
else
{
lean_object* v_reuseFailAlloc_4922_; 
v_reuseFailAlloc_4922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_a_4916_);
v___x_4921_ = v_reuseFailAlloc_4922_;
goto v_reusejp_4920_;
}
v_reusejp_4920_:
{
return v___x_4921_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4925_, lean_object* v_x_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_){
_start:
{
lean_object* v_res_4930_; 
v_res_4930_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4925_, v_x_4926_, v___y_4927_, v___y_4928_);
lean_dec(v___y_4928_);
lean_dec_ref(v___y_4927_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4931_, uint8_t v_forceExpose_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v___x_4936_; 
lean_inc(v_decl_4931_);
v___x_4936_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4931_, v_forceExpose_4932_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4936_) == 0)
{
lean_object* v___x_4937_; lean_object* v___x_4938_; lean_object* v___x_4939_; lean_object* v___x_4940_; 
lean_dec_ref_known(v___x_4936_, 1);
v___x_4937_ = l_Lean_Declaration_getTopLevelNames(v_decl_4931_);
v___x_4938_ = lean_box(0);
v___x_4939_ = lean_box(0);
v___x_4940_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4937_, v___x_4938_, v_a_4933_, v_a_4934_);
if (lean_obj_tag(v___x_4940_) == 0)
{
lean_object* v___x_4942_; uint8_t v_isShared_4943_; uint8_t v_isSharedCheck_4947_; 
v_isSharedCheck_4947_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4947_ == 0)
{
lean_object* v_unused_4948_; 
v_unused_4948_ = lean_ctor_get(v___x_4940_, 0);
lean_dec(v_unused_4948_);
v___x_4942_ = v___x_4940_;
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
else
{
lean_dec(v___x_4940_);
v___x_4942_ = lean_box(0);
v_isShared_4943_ = v_isSharedCheck_4947_;
goto v_resetjp_4941_;
}
v_resetjp_4941_:
{
lean_object* v___x_4945_; 
if (v_isShared_4943_ == 0)
{
lean_ctor_set(v___x_4942_, 0, v___x_4939_);
v___x_4945_ = v___x_4942_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4946_; 
v_reuseFailAlloc_4946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4946_, 0, v___x_4939_);
v___x_4945_ = v_reuseFailAlloc_4946_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
return v___x_4945_;
}
}
}
else
{
lean_object* v_a_4949_; lean_object* v___x_4951_; uint8_t v_isShared_4952_; uint8_t v_isSharedCheck_4956_; 
v_a_4949_ = lean_ctor_get(v___x_4940_, 0);
v_isSharedCheck_4956_ = !lean_is_exclusive(v___x_4940_);
if (v_isSharedCheck_4956_ == 0)
{
v___x_4951_ = v___x_4940_;
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
else
{
lean_inc(v_a_4949_);
lean_dec(v___x_4940_);
v___x_4951_ = lean_box(0);
v_isShared_4952_ = v_isSharedCheck_4956_;
goto v_resetjp_4950_;
}
v_resetjp_4950_:
{
lean_object* v___x_4954_; 
if (v_isShared_4952_ == 0)
{
v___x_4954_ = v___x_4951_;
goto v_reusejp_4953_;
}
else
{
lean_object* v_reuseFailAlloc_4955_; 
v_reuseFailAlloc_4955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
v___x_4954_ = v_reuseFailAlloc_4955_;
goto v_reusejp_4953_;
}
v_reusejp_4953_:
{
return v___x_4954_;
}
}
}
}
else
{
lean_dec(v_decl_4931_);
return v___x_4936_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4957_, lean_object* v_forceExpose_4958_, lean_object* v_a_4959_, lean_object* v_a_4960_, lean_object* v_a_4961_){
_start:
{
uint8_t v_forceExpose_boxed_4962_; lean_object* v_res_4963_; 
v_forceExpose_boxed_4962_ = lean_unbox(v_forceExpose_4958_);
v_res_4963_ = l_Lean_addDecl(v_decl_4957_, v_forceExpose_boxed_4962_, v_a_4959_, v_a_4960_);
lean_dec(v_a_4960_);
lean_dec_ref(v_a_4959_);
return v_res_4963_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4964_, lean_object* v_b_4965_, lean_object* v___y_4966_){
_start:
{
if (lean_obj_tag(v_as_x27_4964_) == 0)
{
lean_object* v___x_4968_; 
v___x_4968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4968_, 0, v_b_4965_);
return v___x_4968_;
}
else
{
lean_object* v_head_4969_; lean_object* v_tail_4970_; lean_object* v___x_4971_; lean_object* v___x_4972_; lean_object* v_env_4973_; lean_object* v_nextMacroScope_4974_; lean_object* v_ngen_4975_; lean_object* v_auxDeclNGen_4976_; lean_object* v_traceState_4977_; lean_object* v_messages_4978_; lean_object* v_infoState_4979_; lean_object* v_snapshotTasks_4980_; lean_object* v___x_4982_; uint8_t v_isShared_4983_; uint8_t v_isSharedCheck_4991_; 
v_head_4969_ = lean_ctor_get(v_as_x27_4964_, 0);
v_tail_4970_ = lean_ctor_get(v_as_x27_4964_, 1);
v___x_4971_ = lean_box(0);
v___x_4972_ = lean_st_ref_take(v___y_4966_);
v_env_4973_ = lean_ctor_get(v___x_4972_, 0);
v_nextMacroScope_4974_ = lean_ctor_get(v___x_4972_, 1);
v_ngen_4975_ = lean_ctor_get(v___x_4972_, 2);
v_auxDeclNGen_4976_ = lean_ctor_get(v___x_4972_, 3);
v_traceState_4977_ = lean_ctor_get(v___x_4972_, 4);
v_messages_4978_ = lean_ctor_get(v___x_4972_, 6);
v_infoState_4979_ = lean_ctor_get(v___x_4972_, 7);
v_snapshotTasks_4980_ = lean_ctor_get(v___x_4972_, 8);
v_isSharedCheck_4991_ = !lean_is_exclusive(v___x_4972_);
if (v_isSharedCheck_4991_ == 0)
{
lean_object* v_unused_4992_; 
v_unused_4992_ = lean_ctor_get(v___x_4972_, 5);
lean_dec(v_unused_4992_);
v___x_4982_ = v___x_4972_;
v_isShared_4983_ = v_isSharedCheck_4991_;
goto v_resetjp_4981_;
}
else
{
lean_inc(v_snapshotTasks_4980_);
lean_inc(v_infoState_4979_);
lean_inc(v_messages_4978_);
lean_inc(v_traceState_4977_);
lean_inc(v_auxDeclNGen_4976_);
lean_inc(v_ngen_4975_);
lean_inc(v_nextMacroScope_4974_);
lean_inc(v_env_4973_);
lean_dec(v___x_4972_);
v___x_4982_ = lean_box(0);
v_isShared_4983_ = v_isSharedCheck_4991_;
goto v_resetjp_4981_;
}
v_resetjp_4981_:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; lean_object* v___x_4987_; 
lean_inc(v_head_4969_);
v___x_4984_ = l_Lean_markMeta(v_env_4973_, v_head_4969_);
v___x_4985_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4983_ == 0)
{
lean_ctor_set(v___x_4982_, 5, v___x_4985_);
lean_ctor_set(v___x_4982_, 0, v___x_4984_);
v___x_4987_ = v___x_4982_;
goto v_reusejp_4986_;
}
else
{
lean_object* v_reuseFailAlloc_4990_; 
v_reuseFailAlloc_4990_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4990_, 0, v___x_4984_);
lean_ctor_set(v_reuseFailAlloc_4990_, 1, v_nextMacroScope_4974_);
lean_ctor_set(v_reuseFailAlloc_4990_, 2, v_ngen_4975_);
lean_ctor_set(v_reuseFailAlloc_4990_, 3, v_auxDeclNGen_4976_);
lean_ctor_set(v_reuseFailAlloc_4990_, 4, v_traceState_4977_);
lean_ctor_set(v_reuseFailAlloc_4990_, 5, v___x_4985_);
lean_ctor_set(v_reuseFailAlloc_4990_, 6, v_messages_4978_);
lean_ctor_set(v_reuseFailAlloc_4990_, 7, v_infoState_4979_);
lean_ctor_set(v_reuseFailAlloc_4990_, 8, v_snapshotTasks_4980_);
v___x_4987_ = v_reuseFailAlloc_4990_;
goto v_reusejp_4986_;
}
v_reusejp_4986_:
{
lean_object* v___x_4988_; 
v___x_4988_ = lean_st_ref_put(v___y_4966_, v___x_4987_);
v_as_x27_4964_ = v_tail_4970_;
v_b_4965_ = v___x_4971_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4993_, lean_object* v_b_4994_, lean_object* v___y_4995_, lean_object* v___y_4996_){
_start:
{
lean_object* v_res_4997_; 
v_res_4997_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4993_, v_b_4994_, v___y_4995_);
lean_dec(v___y_4995_);
lean_dec(v_as_x27_4993_);
return v_res_4997_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4998_, uint8_t v_logCompileErrors_4999_, uint8_t v_markMeta_5000_, lean_object* v_a_5001_, lean_object* v_a_5002_){
_start:
{
uint8_t v___x_5004_; lean_object* v___x_5005_; 
v___x_5004_ = 0;
lean_inc(v_decl_4998_);
v___x_5005_ = l_Lean_addDecl(v_decl_4998_, v___x_5004_, v_a_5001_, v_a_5002_);
if (lean_obj_tag(v___x_5005_) == 0)
{
lean_dec_ref_known(v___x_5005_, 1);
if (v_markMeta_5000_ == 0)
{
lean_object* v___x_5006_; 
v___x_5006_ = l_Lean_compileDecl(v_decl_4998_, v_logCompileErrors_4999_, v_a_5001_, v_a_5002_);
return v___x_5006_;
}
else
{
lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
lean_inc(v_decl_4998_);
v___x_5007_ = l_Lean_Declaration_getNames(v_decl_4998_);
v___x_5008_ = lean_box(0);
v___x_5009_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_5007_, v___x_5008_, v_a_5002_);
lean_dec(v___x_5007_);
lean_dec_ref(v___x_5009_);
v___x_5010_ = l_Lean_compileDecl(v_decl_4998_, v_logCompileErrors_4999_, v_a_5001_, v_a_5002_);
return v___x_5010_;
}
}
else
{
lean_dec(v_decl_4998_);
return v___x_5005_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5011_, lean_object* v_logCompileErrors_5012_, lean_object* v_markMeta_5013_, lean_object* v_a_5014_, lean_object* v_a_5015_, lean_object* v_a_5016_){
_start:
{
uint8_t v_logCompileErrors_boxed_5017_; uint8_t v_markMeta_boxed_5018_; lean_object* v_res_5019_; 
v_logCompileErrors_boxed_5017_ = lean_unbox(v_logCompileErrors_5012_);
v_markMeta_boxed_5018_ = lean_unbox(v_markMeta_5013_);
v_res_5019_ = l_Lean_addAndCompile(v_decl_5011_, v_logCompileErrors_boxed_5017_, v_markMeta_boxed_5018_, v_a_5014_, v_a_5015_);
lean_dec(v_a_5015_);
lean_dec_ref(v_a_5014_);
return v_res_5019_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5020_, lean_object* v_as_x27_5021_, lean_object* v_b_5022_, lean_object* v_a_5023_, lean_object* v___y_5024_, lean_object* v___y_5025_){
_start:
{
lean_object* v___x_5027_; 
v___x_5027_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5021_, v_b_5022_, v___y_5025_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5028_, lean_object* v_as_x27_5029_, lean_object* v_b_5030_, lean_object* v_a_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
lean_object* v_res_5035_; 
v_res_5035_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5028_, v_as_x27_5029_, v_b_5030_, v_a_5031_, v___y_5032_, v___y_5033_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v_as_x27_5029_);
lean_dec(v_as_5028_);
return v_res_5035_;
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
