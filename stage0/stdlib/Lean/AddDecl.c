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
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_114_);
v___x_118_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v___x_117_, v___y_115_);
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
v___x_123_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
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
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_192_; 
v_a_140_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_192_ == 0)
{
v___x_142_ = v___x_139_;
v_isShared_143_ = v_isSharedCheck_192_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_139_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_192_;
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
lean_object* v_a_149_; lean_object* v___x_151_; uint8_t v_isShared_152_; uint8_t v_isSharedCheck_179_; 
v_a_149_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_179_ == 0)
{
v___x_151_ = v___x_148_;
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
else
{
lean_inc(v_a_149_);
lean_dec(v___x_148_);
v___x_151_ = lean_box(0);
v_isShared_152_ = v_isSharedCheck_179_;
goto v_resetjp_150_;
}
v_resetjp_150_:
{
lean_object* v___x_153_; lean_object* v_env_154_; lean_object* v_nextMacroScope_155_; lean_object* v_ngen_156_; lean_object* v_auxDeclNGen_157_; lean_object* v_traceState_158_; lean_object* v_recordedDeps_159_; lean_object* v_messages_160_; lean_object* v_infoState_161_; lean_object* v_snapshotTasks_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_177_; 
v___x_153_ = lean_st_ref_take(v_a_130_);
v_env_154_ = lean_ctor_get(v___x_153_, 0);
v_nextMacroScope_155_ = lean_ctor_get(v___x_153_, 1);
v_ngen_156_ = lean_ctor_get(v___x_153_, 2);
v_auxDeclNGen_157_ = lean_ctor_get(v___x_153_, 3);
v_traceState_158_ = lean_ctor_get(v___x_153_, 4);
v_recordedDeps_159_ = lean_ctor_get(v___x_153_, 6);
v_messages_160_ = lean_ctor_get(v___x_153_, 7);
v_infoState_161_ = lean_ctor_get(v___x_153_, 8);
v_snapshotTasks_162_ = lean_ctor_get(v___x_153_, 9);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_153_);
if (v_isSharedCheck_177_ == 0)
{
lean_object* v_unused_178_; 
v_unused_178_ = lean_ctor_get(v___x_153_, 5);
lean_dec(v_unused_178_);
v___x_164_ = v___x_153_;
v_isShared_165_ = v_isSharedCheck_177_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_snapshotTasks_162_);
lean_inc(v_infoState_161_);
lean_inc(v_messages_160_);
lean_inc(v_recordedDeps_159_);
lean_inc(v_traceState_158_);
lean_inc(v_auxDeclNGen_157_);
lean_inc(v_ngen_156_);
lean_inc(v_nextMacroScope_155_);
lean_inc(v_env_154_);
lean_dec(v___x_153_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_177_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_171_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_168_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_167_, v_env_154_, v_declName_128_, v_a_149_);
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
v_reuseFailAlloc_176_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v___x_168_);
lean_ctor_set(v_reuseFailAlloc_176_, 1, v_nextMacroScope_155_);
lean_ctor_set(v_reuseFailAlloc_176_, 2, v_ngen_156_);
lean_ctor_set(v_reuseFailAlloc_176_, 3, v_auxDeclNGen_157_);
lean_ctor_set(v_reuseFailAlloc_176_, 4, v_traceState_158_);
lean_ctor_set(v_reuseFailAlloc_176_, 5, v___x_169_);
lean_ctor_set(v_reuseFailAlloc_176_, 6, v_recordedDeps_159_);
lean_ctor_set(v_reuseFailAlloc_176_, 7, v_messages_160_);
lean_ctor_set(v_reuseFailAlloc_176_, 8, v_infoState_161_);
lean_ctor_set(v_reuseFailAlloc_176_, 9, v_snapshotTasks_162_);
v___x_171_ = v_reuseFailAlloc_176_;
goto v_reusejp_170_;
}
v_reusejp_170_:
{
lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_172_ = lean_st_ref_put(v_a_130_, v___x_171_);
if (v_isShared_152_ == 0)
{
lean_ctor_set(v___x_151_, 0, v___x_166_);
v___x_174_ = v___x_151_;
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
lean_dec(v_declName_128_);
v_a_180_ = lean_ctor_get(v___x_148_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_148_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_148_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_148_);
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
lean_dec(v_a_138_);
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
v___x_188_ = lean_box(0);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 0, v___x_188_);
v___x_190_ = v___x_142_;
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
lean_dec(v_a_138_);
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
v_a_193_ = lean_ctor_get(v___x_139_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_139_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_139_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_139_);
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
lean_dec(v___x_133_);
lean_dec(v_declName_128_);
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
uint8_t v_suppressElabErrors_boxed_418_; uint8_t v___y_15055__boxed_419_; uint8_t v_res_420_; lean_object* v_r_421_; 
v_suppressElabErrors_boxed_418_ = lean_unbox(v_suppressElabErrors_415_);
v___y_15055__boxed_419_ = lean_unbox(v___y_416_);
v_res_420_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v_suppressElabErrors_boxed_418_, v___y_15055__boxed_419_, v_x_417_);
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
lean_object* v___y_467_; lean_object* v___y_468_; uint8_t v___y_469_; uint8_t v___y_470_; lean_object* v___y_471_; lean_object* v___y_472_; lean_object* v___y_473_; lean_object* v_toCold_474_; lean_object* v___y_475_; lean_object* v___y_504_; lean_object* v___y_505_; lean_object* v___y_506_; uint8_t v___y_507_; uint8_t v___y_508_; uint8_t v___y_509_; lean_object* v___y_510_; lean_object* v___y_511_; lean_object* v___y_531_; uint8_t v___y_532_; lean_object* v___y_533_; uint8_t v___y_534_; uint8_t v___y_535_; lean_object* v___y_536_; lean_object* v___y_537_; uint8_t v___y_541_; uint8_t v___y_542_; uint8_t v___y_543_; uint8_t v___x_554_; uint8_t v___y_556_; uint8_t v___y_557_; uint8_t v___y_558_; uint8_t v___y_560_; uint8_t v___x_568_; 
v___x_554_ = 2;
v___x_568_ = l_Lean_instBEqMessageSeverity_beq(v_severity_461_, v___x_554_);
if (v___x_568_ == 0)
{
v___y_560_ = v___x_568_;
goto v___jp_559_;
}
else
{
uint8_t v___x_569_; 
lean_inc_ref(v_msgData_460_);
v___x_569_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_460_);
v___y_560_ = v___x_569_;
goto v___jp_559_;
}
v___jp_466_:
{
lean_object* v_currNamespace_476_; lean_object* v_openDecls_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v_env_482_; lean_object* v_nextMacroScope_483_; lean_object* v_ngen_484_; lean_object* v_auxDeclNGen_485_; lean_object* v_traceState_486_; lean_object* v_cache_487_; lean_object* v_recordedDeps_488_; lean_object* v_messages_489_; lean_object* v_infoState_490_; lean_object* v_snapshotTasks_491_; lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_502_; 
v_currNamespace_476_ = lean_ctor_get(v_toCold_474_, 4);
v_openDecls_477_ = lean_ctor_get(v_toCold_474_, 5);
lean_inc(v_openDecls_477_);
lean_inc(v_currNamespace_476_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v_currNamespace_476_);
lean_ctor_set(v___x_478_, 1, v_openDecls_477_);
v___x_479_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_479_, 0, v___x_478_);
lean_ctor_set(v___x_479_, 1, v___y_467_);
lean_inc_ref(v___y_473_);
lean_inc_ref(v___y_471_);
v___x_480_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_480_, 0, v___y_471_);
lean_ctor_set(v___x_480_, 1, v___y_468_);
lean_ctor_set(v___x_480_, 2, v___y_472_);
lean_ctor_set(v___x_480_, 3, v___y_473_);
lean_ctor_set(v___x_480_, 4, v___x_479_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*5, v___y_470_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*5 + 1, v___y_469_);
lean_ctor_set_uint8(v___x_480_, sizeof(void*)*5 + 2, v_isSilent_462_);
v___x_481_ = lean_st_ref_take(v___y_475_);
v_env_482_ = lean_ctor_get(v___x_481_, 0);
v_nextMacroScope_483_ = lean_ctor_get(v___x_481_, 1);
v_ngen_484_ = lean_ctor_get(v___x_481_, 2);
v_auxDeclNGen_485_ = lean_ctor_get(v___x_481_, 3);
v_traceState_486_ = lean_ctor_get(v___x_481_, 4);
v_cache_487_ = lean_ctor_get(v___x_481_, 5);
v_recordedDeps_488_ = lean_ctor_get(v___x_481_, 6);
v_messages_489_ = lean_ctor_get(v___x_481_, 7);
v_infoState_490_ = lean_ctor_get(v___x_481_, 8);
v_snapshotTasks_491_ = lean_ctor_get(v___x_481_, 9);
v_isSharedCheck_502_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_502_ == 0)
{
v___x_493_ = v___x_481_;
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
else
{
lean_inc(v_snapshotTasks_491_);
lean_inc(v_infoState_490_);
lean_inc(v_messages_489_);
lean_inc(v_recordedDeps_488_);
lean_inc(v_cache_487_);
lean_inc(v_traceState_486_);
lean_inc(v_auxDeclNGen_485_);
lean_inc(v_ngen_484_);
lean_inc(v_nextMacroScope_483_);
lean_inc(v_env_482_);
lean_dec(v___x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_502_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v___x_495_; lean_object* v___x_496_; lean_object* v___x_498_; 
v___x_495_ = lean_box(0);
v___x_496_ = l_Lean_MessageLog_add(v___x_480_, v_messages_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 7, v___x_496_);
v___x_498_ = v___x_493_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_env_482_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_nextMacroScope_483_);
lean_ctor_set(v_reuseFailAlloc_501_, 2, v_ngen_484_);
lean_ctor_set(v_reuseFailAlloc_501_, 3, v_auxDeclNGen_485_);
lean_ctor_set(v_reuseFailAlloc_501_, 4, v_traceState_486_);
lean_ctor_set(v_reuseFailAlloc_501_, 5, v_cache_487_);
lean_ctor_set(v_reuseFailAlloc_501_, 6, v_recordedDeps_488_);
lean_ctor_set(v_reuseFailAlloc_501_, 7, v___x_496_);
lean_ctor_set(v_reuseFailAlloc_501_, 8, v_infoState_490_);
lean_ctor_set(v_reuseFailAlloc_501_, 9, v_snapshotTasks_491_);
v___x_498_ = v_reuseFailAlloc_501_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = lean_st_ref_put(v___y_475_, v___x_498_);
v___x_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_495_);
return v___x_500_;
}
}
}
v___jp_503_:
{
lean_object* v_fileName_512_; lean_object* v_fileMap_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_529_; 
v_fileName_512_ = lean_ctor_get(v___y_510_, 0);
v_fileMap_513_ = lean_ctor_get(v___y_510_, 1);
v___x_514_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_460_);
v___x_515_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_514_, v___y_463_, v___y_464_);
v_a_516_ = lean_ctor_get(v___x_515_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_515_);
if (v_isSharedCheck_529_ == 0)
{
v___x_518_ = v___x_515_;
v_isShared_519_ = v_isSharedCheck_529_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_515_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_529_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_inc_ref_n(v_fileMap_513_, 2);
v___x_520_ = l_Lean_FileMap_toPosition(v_fileMap_513_, v___y_506_);
lean_dec(v___y_506_);
v___x_521_ = l_Lean_FileMap_toPosition(v_fileMap_513_, v___y_511_);
lean_dec(v___y_511_);
v___x_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
v___x_523_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_509_ == 0)
{
lean_del_object(v___x_518_);
lean_dec_ref(v___y_504_);
v___y_467_ = v_a_516_;
v___y_468_ = v___x_520_;
v___y_469_ = v___y_508_;
v___y_470_ = v___y_507_;
v___y_471_ = v_fileName_512_;
v___y_472_ = v___x_522_;
v___y_473_ = v___x_523_;
v_toCold_474_ = v___y_505_;
v___y_475_ = v___y_464_;
goto v___jp_466_;
}
else
{
uint8_t v___x_524_; 
lean_inc(v_a_516_);
v___x_524_ = l_Lean_MessageData_hasTag(v___y_504_, v_a_516_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_527_; 
lean_dec_ref_known(v___x_522_, 1);
lean_dec_ref(v___x_520_);
lean_dec(v_a_516_);
v___x_525_ = lean_box(0);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_525_);
v___x_527_ = v___x_518_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v___x_525_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
else
{
lean_del_object(v___x_518_);
v___y_467_ = v_a_516_;
v___y_468_ = v___x_520_;
v___y_469_ = v___y_508_;
v___y_470_ = v___y_507_;
v___y_471_ = v_fileName_512_;
v___y_472_ = v___x_522_;
v___y_473_ = v___x_523_;
v_toCold_474_ = v___y_505_;
v___y_475_ = v___y_464_;
goto v___jp_466_;
}
}
}
}
v___jp_530_:
{
lean_object* v___x_538_; 
v___x_538_ = l_Lean_Syntax_getTailPos_x3f(v___y_536_, v___y_535_);
lean_dec(v___y_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_inc(v___y_537_);
v___y_504_ = v___y_531_;
v___y_505_ = v___y_533_;
v___y_506_ = v___y_537_;
v___y_507_ = v___y_535_;
v___y_508_ = v___y_534_;
v___y_509_ = v___y_532_;
v___y_510_ = v___y_533_;
v___y_511_ = v___y_537_;
goto v___jp_503_;
}
else
{
lean_object* v_val_539_; 
v_val_539_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_539_);
lean_dec_ref_known(v___x_538_, 1);
v___y_504_ = v___y_531_;
v___y_505_ = v___y_533_;
v___y_506_ = v___y_537_;
v___y_507_ = v___y_535_;
v___y_508_ = v___y_534_;
v___y_509_ = v___y_532_;
v___y_510_ = v___y_533_;
v___y_511_ = v_val_539_;
goto v___jp_503_;
}
}
v___jp_540_:
{
lean_object* v_toCold_544_; lean_object* v_ref_545_; uint8_t v_suppressElabErrors_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___f_549_; lean_object* v_ref_550_; lean_object* v___x_551_; 
v_toCold_544_ = lean_ctor_get(v___y_463_, 0);
v_ref_545_ = lean_ctor_get(v___y_463_, 2);
v_suppressElabErrors_546_ = lean_ctor_get_uint8(v___y_463_, sizeof(void*)*3 + 2);
v___x_547_ = lean_box(v_suppressElabErrors_546_);
v___x_548_ = lean_box(v___y_541_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_549_, 0, v___x_547_);
lean_closure_set(v___f_549_, 1, v___x_548_);
v_ref_550_ = l_Lean_replaceRef(v_ref_459_, v_ref_545_);
v___x_551_ = l_Lean_Syntax_getPos_x3f(v_ref_550_, v___y_542_);
if (lean_obj_tag(v___x_551_) == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(0u);
v___y_531_ = v___f_549_;
v___y_532_ = v_suppressElabErrors_546_;
v___y_533_ = v_toCold_544_;
v___y_534_ = v___y_543_;
v___y_535_ = v___y_542_;
v___y_536_ = v_ref_550_;
v___y_537_ = v___x_552_;
goto v___jp_530_;
}
else
{
lean_object* v_val_553_; 
v_val_553_ = lean_ctor_get(v___x_551_, 0);
lean_inc(v_val_553_);
lean_dec_ref_known(v___x_551_, 1);
v___y_531_ = v___f_549_;
v___y_532_ = v_suppressElabErrors_546_;
v___y_533_ = v_toCold_544_;
v___y_534_ = v___y_543_;
v___y_535_ = v___y_542_;
v___y_536_ = v_ref_550_;
v___y_537_ = v_val_553_;
goto v___jp_530_;
}
}
v___jp_555_:
{
if (v___y_558_ == 0)
{
v___y_541_ = v___y_556_;
v___y_542_ = v___y_557_;
v___y_543_ = v_severity_461_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___y_556_;
v___y_542_ = v___y_557_;
v___y_543_ = v___x_554_;
goto v___jp_540_;
}
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
uint8_t v___x_561_; uint8_t v___x_562_; 
v___x_561_ = 1;
v___x_562_ = l_Lean_instBEqMessageSeverity_beq(v_severity_461_, v___x_561_);
if (v___x_562_ == 0)
{
v___y_556_ = v___y_560_;
v___y_557_ = v___y_560_;
v___y_558_ = v___x_562_;
goto v___jp_555_;
}
else
{
lean_object* v___x_563_; lean_object* v___x_564_; uint8_t v___x_565_; 
v___x_563_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_463_);
v___x_564_ = l_Lean_warningAsError;
v___x_565_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_563_, v___x_564_);
lean_dec_ref(v___x_563_);
v___y_556_ = v___y_560_;
v___y_557_ = v___y_560_;
v___y_558_ = v___x_565_;
goto v___jp_555_;
}
}
else
{
lean_object* v___x_566_; lean_object* v___x_567_; 
lean_dec_ref(v_msgData_460_);
v___x_566_ = lean_box(0);
v___x_567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_567_, 0, v___x_566_);
return v___x_567_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_570_, lean_object* v_msgData_571_, lean_object* v_severity_572_, lean_object* v_isSilent_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_){
_start:
{
uint8_t v_severity_boxed_577_; uint8_t v_isSilent_boxed_578_; lean_object* v_res_579_; 
v_severity_boxed_577_ = lean_unbox(v_severity_572_);
v_isSilent_boxed_578_ = lean_unbox(v_isSilent_573_);
v_res_579_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_570_, v_msgData_571_, v_severity_boxed_577_, v_isSilent_boxed_578_, v___y_574_, v___y_575_);
lean_dec(v___y_575_);
lean_dec_ref(v___y_574_);
lean_dec(v_ref_570_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_580_, uint8_t v_severity_581_, uint8_t v_isSilent_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_ref_586_; lean_object* v___x_587_; 
v_ref_586_ = lean_ctor_get(v___y_583_, 2);
v___x_587_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_586_, v_msgData_580_, v_severity_581_, v_isSilent_582_, v___y_583_, v___y_584_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_588_, lean_object* v_severity_589_, lean_object* v_isSilent_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_){
_start:
{
uint8_t v_severity_boxed_594_; uint8_t v_isSilent_boxed_595_; lean_object* v_res_596_; 
v_severity_boxed_594_ = lean_unbox(v_severity_589_);
v_isSilent_boxed_595_ = lean_unbox(v_isSilent_590_);
v_res_596_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_588_, v_severity_boxed_594_, v_isSilent_boxed_595_, v___y_591_, v___y_592_);
lean_dec(v___y_592_);
lean_dec_ref(v___y_591_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
uint8_t v___x_601_; uint8_t v___x_602_; lean_object* v___x_603_; 
v___x_601_ = 1;
v___x_602_ = 0;
v___x_603_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_597_, v___x_601_, v___x_602_, v___y_598_, v___y_599_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_604_, v___y_605_, v___y_606_);
lean_dec(v___y_606_);
lean_dec_ref(v___y_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_612_, size_t v_sz_613_, size_t v_i_614_, lean_object* v_b_615_){
_start:
{
uint8_t v___x_616_; 
v___x_616_ = lean_usize_dec_lt(v_i_614_, v_sz_613_);
if (v___x_616_ == 0)
{
lean_inc_ref(v_b_615_);
return v_b_615_;
}
else
{
lean_object* v_a_617_; lean_object* v_fst_618_; lean_object* v___x_619_; uint8_t v___x_620_; 
v_a_617_ = lean_array_uget_borrowed(v_as_612_, v_i_614_);
v_fst_618_ = lean_ctor_get(v_a_617_, 0);
v___x_619_ = lean_box(0);
v___x_620_ = lean_unbox(v_fst_618_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; size_t v___x_622_; size_t v___x_623_; 
v___x_621_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_622_ = ((size_t)1ULL);
v___x_623_ = lean_usize_add(v_i_614_, v___x_622_);
v_i_614_ = v___x_623_;
v_b_615_ = v___x_621_;
goto _start;
}
else
{
lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; 
lean_inc(v_a_617_);
v___x_625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_625_, 0, v_a_617_);
v___x_626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
v___x_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_626_);
lean_ctor_set(v___x_627_, 1, v___x_619_);
return v___x_627_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_628_, lean_object* v_sz_629_, lean_object* v_i_630_, lean_object* v_b_631_){
_start:
{
size_t v_sz_boxed_632_; size_t v_i_boxed_633_; lean_object* v_res_634_; 
v_sz_boxed_632_ = lean_unbox_usize(v_sz_629_);
lean_dec(v_sz_629_);
v_i_boxed_633_ = lean_unbox_usize(v_i_630_);
lean_dec(v_i_630_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_628_, v_sz_boxed_632_, v_i_boxed_633_, v_b_631_);
lean_dec_ref(v_b_631_);
lean_dec_ref(v_as_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_635_, lean_object* v_e_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_){
_start:
{
lean_object* v___x_643_; 
v___x_643_ = l_Lean_Expr_getSorry_x3f(v_e_636_);
if (lean_obj_tag(v___x_643_) == 1)
{
lean_object* v_val_644_; lean_object* v___x_645_; 
v_val_644_ = lean_ctor_get(v___x_643_, 0);
lean_inc(v_val_644_);
lean_dec_ref_known(v___x_643_, 1);
lean_inc(v___y_641_);
lean_inc_ref(v___y_640_);
lean_inc(v___y_639_);
lean_inc_ref(v___y_638_);
lean_inc(v___y_637_);
v___x_645_ = lean_apply_7(v_fn_635_, v_val_644_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, lean_box(0));
if (lean_obj_tag(v___x_645_) == 0)
{
lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_654_; 
v_isSharedCheck_654_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_654_ == 0)
{
lean_object* v_unused_655_; 
v_unused_655_ = lean_ctor_get(v___x_645_, 0);
lean_dec(v_unused_655_);
v___x_647_ = v___x_645_;
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
else
{
lean_dec(v___x_645_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = 0;
v___x_650_ = lean_box(v___x_649_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_650_);
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
else
{
lean_object* v_a_656_; lean_object* v___x_658_; uint8_t v_isShared_659_; uint8_t v_isSharedCheck_663_; 
v_a_656_ = lean_ctor_get(v___x_645_, 0);
v_isSharedCheck_663_ = !lean_is_exclusive(v___x_645_);
if (v_isSharedCheck_663_ == 0)
{
v___x_658_ = v___x_645_;
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
else
{
lean_inc(v_a_656_);
lean_dec(v___x_645_);
v___x_658_ = lean_box(0);
v_isShared_659_ = v_isSharedCheck_663_;
goto v_resetjp_657_;
}
v_resetjp_657_:
{
lean_object* v___x_661_; 
if (v_isShared_659_ == 0)
{
v___x_661_ = v___x_658_;
goto v_reusejp_660_;
}
else
{
lean_object* v_reuseFailAlloc_662_; 
v_reuseFailAlloc_662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_662_, 0, v_a_656_);
v___x_661_ = v_reuseFailAlloc_662_;
goto v_reusejp_660_;
}
v_reusejp_660_:
{
return v___x_661_;
}
}
}
}
else
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
lean_dec(v___x_643_);
lean_dec_ref(v_fn_635_);
v___x_664_ = 1;
v___x_665_ = lean_box(v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_667_, lean_object* v_e_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_667_, v_e_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v_e_668_);
return v_res_675_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_676_, lean_object* v_x_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; lean_object* v___x_685_; 
v___x_684_ = lean_apply_1(v_x_677_, lean_box(0));
v___x_685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_685_, 0, v___x_684_);
return v___x_685_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_686_, lean_object* v_x_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_686_, v_x_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v_b_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; 
lean_inc(v___y_702_);
lean_inc_ref(v___y_701_);
lean_inc(v___y_700_);
lean_inc_ref(v___y_699_);
lean_inc(v___y_697_);
lean_inc(v___y_696_);
v___x_704_ = lean_apply_8(v_k_695_, v_b_698_, v___y_696_, v___y_697_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, lean_box(0));
return v___x_704_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v_b_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_){
_start:
{
lean_object* v_res_714_; 
v_res_714_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_705_, v___y_706_, v___y_707_, v_b_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v___y_707_);
lean_dec(v___y_706_);
return v_res_714_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_715_, lean_object* v_type_716_, lean_object* v_val_717_, lean_object* v_k_718_, uint8_t v_nondep_719_, uint8_t v_kind_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v___f_728_; lean_object* v___x_729_; 
lean_inc(v___y_722_);
lean_inc(v___y_721_);
v___f_728_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_728_, 0, v_k_718_);
lean_closure_set(v___f_728_, 1, v___y_721_);
lean_closure_set(v___f_728_, 2, v___y_722_);
v___x_729_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_715_, v_type_716_, v_val_717_, v___f_728_, v_nondep_719_, v_kind_720_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
if (lean_obj_tag(v___x_729_) == 0)
{
return v___x_729_;
}
else
{
lean_object* v_a_730_; lean_object* v___x_732_; uint8_t v_isShared_733_; uint8_t v_isSharedCheck_737_; 
v_a_730_ = lean_ctor_get(v___x_729_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_729_);
if (v_isSharedCheck_737_ == 0)
{
v___x_732_ = v___x_729_;
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
else
{
lean_inc(v_a_730_);
lean_dec(v___x_729_);
v___x_732_ = lean_box(0);
v_isShared_733_ = v_isSharedCheck_737_;
goto v_resetjp_731_;
}
v_resetjp_731_:
{
lean_object* v___x_735_; 
if (v_isShared_733_ == 0)
{
v___x_735_ = v___x_732_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_a_730_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
return v___x_735_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_738_, lean_object* v_type_739_, lean_object* v_val_740_, lean_object* v_k_741_, lean_object* v_nondep_742_, lean_object* v_kind_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_){
_start:
{
uint8_t v_nondep_boxed_751_; uint8_t v_kind_boxed_752_; lean_object* v_res_753_; 
v_nondep_boxed_751_ = lean_unbox(v_nondep_742_);
v_kind_boxed_752_ = lean_unbox(v_kind_743_);
v_res_753_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_738_, v_type_739_, v_val_740_, v_k_741_, v_nondep_boxed_751_, v_kind_boxed_752_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec_ref(v___y_746_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_754_, lean_object* v_f_755_, lean_object* v_body_756_, lean_object* v_x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
lean_object* v_res_765_; 
v_res_765_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_754_, v_f_755_, v_body_756_, v_x_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
lean_dec(v___y_759_);
lean_dec(v___y_758_);
return v_res_765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_766_, lean_object* v_fvars_767_, lean_object* v_a_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_){
_start:
{
if (lean_obj_tag(v_a_768_) == 8)
{
lean_object* v_declName_776_; lean_object* v_type_777_; lean_object* v_value_778_; lean_object* v_body_779_; lean_object* v___f_780_; lean_object* v_d_781_; lean_object* v_v_782_; lean_object* v___x_783_; 
v_declName_776_ = lean_ctor_get(v_a_768_, 0);
lean_inc(v_declName_776_);
v_type_777_ = lean_ctor_get(v_a_768_, 1);
lean_inc_ref(v_type_777_);
v_value_778_ = lean_ctor_get(v_a_768_, 2);
lean_inc_ref(v_value_778_);
v_body_779_ = lean_ctor_get(v_a_768_, 3);
lean_inc_ref(v_body_779_);
lean_dec_ref_known(v_a_768_, 4);
lean_inc_ref_n(v_f_766_, 2);
lean_inc_ref(v_fvars_767_);
v___f_780_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_780_, 0, v_fvars_767_);
lean_closure_set(v___f_780_, 1, v_f_766_);
lean_closure_set(v___f_780_, 2, v_body_779_);
v_d_781_ = lean_expr_instantiate_rev(v_type_777_, v_fvars_767_);
lean_dec_ref(v_type_777_);
v_v_782_ = lean_expr_instantiate_rev(v_value_778_, v_fvars_767_);
lean_dec_ref(v_fvars_767_);
lean_dec_ref(v_value_778_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc_ref(v___y_771_);
lean_inc(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v_d_781_);
v___x_783_ = lean_apply_8(v_f_766_, v_d_781_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, lean_box(0));
if (lean_obj_tag(v___x_783_) == 0)
{
lean_object* v___x_784_; 
lean_dec_ref_known(v___x_783_, 1);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc_ref(v___y_771_);
lean_inc(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v_v_782_);
v___x_784_ = lean_apply_8(v_f_766_, v_v_782_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, lean_box(0));
if (lean_obj_tag(v___x_784_) == 0)
{
uint8_t v___x_785_; uint8_t v___x_786_; lean_object* v___x_787_; 
lean_dec_ref_known(v___x_784_, 1);
v___x_785_ = 0;
v___x_786_ = 0;
v___x_787_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_776_, v_d_781_, v_v_782_, v___f_780_, v___x_785_, v___x_786_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
return v___x_787_;
}
else
{
lean_dec_ref(v_v_782_);
lean_dec_ref(v_d_781_);
lean_dec_ref(v___f_780_);
lean_dec(v_declName_776_);
return v___x_784_;
}
}
else
{
lean_dec_ref(v_v_782_);
lean_dec_ref(v_d_781_);
lean_dec_ref(v___f_780_);
lean_dec(v_declName_776_);
lean_dec_ref(v_f_766_);
return v___x_783_;
}
}
else
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = lean_expr_instantiate_rev(v_a_768_, v_fvars_767_);
lean_dec_ref(v_fvars_767_);
lean_dec_ref(v_a_768_);
lean_inc(v___y_774_);
lean_inc_ref(v___y_773_);
lean_inc(v___y_772_);
lean_inc_ref(v___y_771_);
lean_inc(v___y_770_);
lean_inc(v___y_769_);
v___x_789_ = lean_apply_8(v_f_766_, v___x_788_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, lean_box(0));
return v___x_789_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_790_, lean_object* v_f_791_, lean_object* v_body_792_, lean_object* v_x_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_){
_start:
{
lean_object* v___x_801_; lean_object* v___x_802_; 
v___x_801_ = lean_array_push(v_fvars_790_, v_x_793_);
v___x_802_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_791_, v___x_801_, v_body_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
return v___x_802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_803_, lean_object* v_fvars_804_, lean_object* v_a_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_803_, v_fvars_804_, v_a_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec(v___y_806_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_816_, lean_object* v_e_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_826_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_816_, v___x_825_, v_e_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_827_, lean_object* v_e_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v_res_836_; 
v_res_836_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_827_, v_e_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec(v___y_829_);
return v_res_836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_837_, uint8_t v_bi_838_, lean_object* v_type_839_, lean_object* v_k_840_, uint8_t v_kind_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
lean_object* v___f_849_; lean_object* v___x_850_; 
lean_inc(v___y_843_);
lean_inc(v___y_842_);
v___f_849_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_849_, 0, v_k_840_);
lean_closure_set(v___f_849_, 1, v___y_842_);
lean_closure_set(v___f_849_, 2, v___y_843_);
v___x_850_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_837_, v_bi_838_, v_type_839_, v___f_849_, v_kind_841_, v___y_844_, v___y_845_, v___y_846_, v___y_847_);
if (lean_obj_tag(v___x_850_) == 0)
{
return v___x_850_;
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_850_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_850_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_859_, lean_object* v_bi_860_, lean_object* v_type_861_, lean_object* v_k_862_, lean_object* v_kind_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_){
_start:
{
uint8_t v_bi_boxed_871_; uint8_t v_kind_boxed_872_; lean_object* v_res_873_; 
v_bi_boxed_871_ = lean_unbox(v_bi_860_);
v_kind_boxed_872_ = lean_unbox(v_kind_863_);
v_res_873_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_859_, v_bi_boxed_871_, v_type_861_, v_k_862_, v_kind_boxed_872_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec_ref(v___y_866_);
lean_dec(v___y_865_);
lean_dec(v___y_864_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_874_, lean_object* v_f_875_, lean_object* v_body_876_, lean_object* v_x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_874_, v_f_875_, v_body_876_, v_x_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec(v___y_878_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_886_, lean_object* v_fvars_887_, lean_object* v_a_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_, lean_object* v___y_893_, lean_object* v___y_894_){
_start:
{
if (lean_obj_tag(v_a_888_) == 7)
{
lean_object* v_binderName_896_; lean_object* v_binderType_897_; lean_object* v_body_898_; uint8_t v_binderInfo_899_; lean_object* v___f_900_; lean_object* v_d_901_; lean_object* v___x_902_; 
v_binderName_896_ = lean_ctor_get(v_a_888_, 0);
lean_inc(v_binderName_896_);
v_binderType_897_ = lean_ctor_get(v_a_888_, 1);
lean_inc_ref(v_binderType_897_);
v_body_898_ = lean_ctor_get(v_a_888_, 2);
lean_inc_ref(v_body_898_);
v_binderInfo_899_ = lean_ctor_get_uint8(v_a_888_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_888_, 3);
lean_inc_ref(v_f_886_);
lean_inc_ref(v_fvars_887_);
v___f_900_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_900_, 0, v_fvars_887_);
lean_closure_set(v___f_900_, 1, v_f_886_);
lean_closure_set(v___f_900_, 2, v_body_898_);
v_d_901_ = lean_expr_instantiate_rev(v_binderType_897_, v_fvars_887_);
lean_dec_ref(v_fvars_887_);
lean_dec_ref(v_binderType_897_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___y_892_);
lean_inc_ref(v___y_891_);
lean_inc(v___y_890_);
lean_inc(v___y_889_);
lean_inc_ref(v_d_901_);
v___x_902_ = lean_apply_8(v_f_886_, v_d_901_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, lean_box(0));
if (lean_obj_tag(v___x_902_) == 0)
{
uint8_t v___x_903_; lean_object* v___x_904_; 
lean_dec_ref_known(v___x_902_, 1);
v___x_903_ = 0;
v___x_904_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_896_, v_binderInfo_899_, v_d_901_, v___f_900_, v___x_903_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_);
return v___x_904_;
}
else
{
lean_dec_ref(v_d_901_);
lean_dec_ref(v___f_900_);
lean_dec(v_binderName_896_);
return v___x_902_;
}
}
else
{
lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_905_ = lean_expr_instantiate_rev(v_a_888_, v_fvars_887_);
lean_dec_ref(v_fvars_887_);
lean_dec_ref(v_a_888_);
lean_inc(v___y_894_);
lean_inc_ref(v___y_893_);
lean_inc(v___y_892_);
lean_inc_ref(v___y_891_);
lean_inc(v___y_890_);
lean_inc(v___y_889_);
v___x_906_ = lean_apply_8(v_f_886_, v___x_905_, v___y_889_, v___y_890_, v___y_891_, v___y_892_, v___y_893_, v___y_894_, lean_box(0));
return v___x_906_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_907_, lean_object* v_f_908_, lean_object* v_body_909_, lean_object* v_x_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_){
_start:
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_array_push(v_fvars_907_, v_x_910_);
v___x_919_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_908_, v___x_918_, v_body_909_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_920_, lean_object* v_fvars_921_, lean_object* v_a_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_){
_start:
{
lean_object* v_res_930_; 
v_res_930_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_920_, v_fvars_921_, v_a_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_, v___y_927_, v___y_928_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
lean_dec(v___y_926_);
lean_dec_ref(v___y_925_);
lean_dec(v___y_924_);
lean_dec(v___y_923_);
return v_res_930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_931_, lean_object* v_e_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_940_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_941_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_931_, v___x_940_, v_e_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
return v___x_941_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_942_, lean_object* v_e_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_942_, v_e_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_952_, lean_object* v_f_953_, lean_object* v_body_954_, lean_object* v_x_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_){
_start:
{
lean_object* v_res_963_; 
v_res_963_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_952_, v_f_953_, v_body_954_, v_x_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, v___y_961_);
lean_dec(v___y_961_);
lean_dec_ref(v___y_960_);
lean_dec(v___y_959_);
lean_dec_ref(v___y_958_);
lean_dec(v___y_957_);
lean_dec(v___y_956_);
return v_res_963_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_964_, lean_object* v_fvars_965_, lean_object* v_a_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
if (lean_obj_tag(v_a_966_) == 6)
{
lean_object* v_binderName_974_; lean_object* v_binderType_975_; lean_object* v_body_976_; uint8_t v_binderInfo_977_; lean_object* v___f_978_; lean_object* v_d_979_; lean_object* v___x_980_; 
v_binderName_974_ = lean_ctor_get(v_a_966_, 0);
lean_inc(v_binderName_974_);
v_binderType_975_ = lean_ctor_get(v_a_966_, 1);
lean_inc_ref(v_binderType_975_);
v_body_976_ = lean_ctor_get(v_a_966_, 2);
lean_inc_ref(v_body_976_);
v_binderInfo_977_ = lean_ctor_get_uint8(v_a_966_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_966_, 3);
lean_inc_ref(v_f_964_);
lean_inc_ref(v_fvars_965_);
v___f_978_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_978_, 0, v_fvars_965_);
lean_closure_set(v___f_978_, 1, v_f_964_);
lean_closure_set(v___f_978_, 2, v_body_976_);
v_d_979_ = lean_expr_instantiate_rev(v_binderType_975_, v_fvars_965_);
lean_dec_ref(v_fvars_965_);
lean_dec_ref(v_binderType_975_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc(v___y_967_);
lean_inc_ref(v_d_979_);
v___x_980_ = lean_apply_8(v_f_964_, v_d_979_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, lean_box(0));
if (lean_obj_tag(v___x_980_) == 0)
{
uint8_t v___x_981_; lean_object* v___x_982_; 
lean_dec_ref_known(v___x_980_, 1);
v___x_981_ = 0;
v___x_982_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_974_, v_binderInfo_977_, v_d_979_, v___f_978_, v___x_981_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
return v___x_982_;
}
else
{
lean_dec_ref(v_d_979_);
lean_dec_ref(v___f_978_);
lean_dec(v_binderName_974_);
return v___x_980_;
}
}
else
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = lean_expr_instantiate_rev(v_a_966_, v_fvars_965_);
lean_dec_ref(v_fvars_965_);
lean_dec_ref(v_a_966_);
lean_inc(v___y_972_);
lean_inc_ref(v___y_971_);
lean_inc(v___y_970_);
lean_inc_ref(v___y_969_);
lean_inc(v___y_968_);
lean_inc(v___y_967_);
v___x_984_ = lean_apply_8(v_f_964_, v___x_983_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, lean_box(0));
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_985_, lean_object* v_f_986_, lean_object* v_body_987_, lean_object* v_x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; lean_object* v___x_997_; 
v___x_996_ = lean_array_push(v_fvars_985_, v_x_988_);
v___x_997_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_986_, v___x_996_, v_body_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
return v___x_997_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_998_, lean_object* v_fvars_999_, lean_object* v_a_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_res_1008_; 
v_res_1008_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_998_, v_fvars_999_, v_a_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
lean_dec(v___y_1006_);
lean_dec_ref(v___y_1005_);
lean_dec(v___y_1004_);
lean_dec_ref(v___y_1003_);
lean_dec(v___y_1002_);
lean_dec(v___y_1001_);
return v_res_1008_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_1009_, lean_object* v_e_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1019_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_1009_, v___x_1018_, v_e_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_, v___y_1016_);
return v___x_1019_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1020_, lean_object* v_e_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1020_, v_e_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec(v___y_1022_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1030_, lean_object* v_x_1031_){
_start:
{
if (lean_obj_tag(v_x_1031_) == 0)
{
lean_object* v___x_1032_; 
v___x_1032_ = lean_box(0);
return v___x_1032_;
}
else
{
lean_object* v_key_1033_; lean_object* v_value_1034_; lean_object* v_tail_1035_; uint8_t v___x_1036_; 
v_key_1033_ = lean_ctor_get(v_x_1031_, 0);
v_value_1034_ = lean_ctor_get(v_x_1031_, 1);
v_tail_1035_ = lean_ctor_get(v_x_1031_, 2);
v___x_1036_ = lean_expr_eqv(v_key_1033_, v_a_1030_);
if (v___x_1036_ == 0)
{
v_x_1031_ = v_tail_1035_;
goto _start;
}
else
{
lean_object* v___x_1038_; 
lean_inc(v_value_1034_);
v___x_1038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1038_, 0, v_value_1034_);
return v___x_1038_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1039_, lean_object* v_x_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1039_, v_x_1040_);
lean_dec(v_x_1040_);
lean_dec_ref(v_a_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v_buckets_1044_; lean_object* v___x_1045_; uint64_t v___x_1046_; uint64_t v___x_1047_; uint64_t v___x_1048_; uint64_t v_fold_1049_; uint64_t v___x_1050_; uint64_t v___x_1051_; uint64_t v___x_1052_; size_t v___x_1053_; size_t v___x_1054_; size_t v___x_1055_; size_t v___x_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; 
v_buckets_1044_ = lean_ctor_get(v_m_1042_, 1);
v___x_1045_ = lean_array_get_size(v_buckets_1044_);
v___x_1046_ = l_Lean_Expr_hash(v_a_1043_);
v___x_1047_ = 32ULL;
v___x_1048_ = lean_uint64_shift_right(v___x_1046_, v___x_1047_);
v_fold_1049_ = lean_uint64_xor(v___x_1046_, v___x_1048_);
v___x_1050_ = 16ULL;
v___x_1051_ = lean_uint64_shift_right(v_fold_1049_, v___x_1050_);
v___x_1052_ = lean_uint64_xor(v_fold_1049_, v___x_1051_);
v___x_1053_ = lean_uint64_to_usize(v___x_1052_);
v___x_1054_ = lean_usize_of_nat(v___x_1045_);
v___x_1055_ = ((size_t)1ULL);
v___x_1056_ = lean_usize_sub(v___x_1054_, v___x_1055_);
v___x_1057_ = lean_usize_land(v___x_1053_, v___x_1056_);
v___x_1058_ = lean_array_uget_borrowed(v_buckets_1044_, v___x_1057_);
v___x_1059_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1043_, v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1060_, v_a_1061_);
lean_dec_ref(v_a_1061_);
lean_dec_ref(v_m_1060_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1063_, lean_object* v_x_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = lean_apply_1(v_x_1064_, lean_box(0));
v___x_1072_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1073_, lean_object* v_x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1073_, v_x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1082_, lean_object* v_x_1083_){
_start:
{
if (lean_obj_tag(v_x_1083_) == 0)
{
return v_x_1082_;
}
else
{
lean_object* v_key_1084_; lean_object* v_value_1085_; lean_object* v_tail_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1109_; 
v_key_1084_ = lean_ctor_get(v_x_1083_, 0);
v_value_1085_ = lean_ctor_get(v_x_1083_, 1);
v_tail_1086_ = lean_ctor_get(v_x_1083_, 2);
v_isSharedCheck_1109_ = !lean_is_exclusive(v_x_1083_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1088_ = v_x_1083_;
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_tail_1086_);
lean_inc(v_value_1085_);
lean_inc(v_key_1084_);
lean_dec(v_x_1083_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1109_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; uint64_t v___x_1091_; uint64_t v___x_1092_; uint64_t v___x_1093_; uint64_t v_fold_1094_; uint64_t v___x_1095_; uint64_t v___x_1096_; uint64_t v___x_1097_; size_t v___x_1098_; size_t v___x_1099_; size_t v___x_1100_; size_t v___x_1101_; size_t v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1105_; 
v___x_1090_ = lean_array_get_size(v_x_1082_);
v___x_1091_ = l_Lean_Expr_hash(v_key_1084_);
v___x_1092_ = 32ULL;
v___x_1093_ = lean_uint64_shift_right(v___x_1091_, v___x_1092_);
v_fold_1094_ = lean_uint64_xor(v___x_1091_, v___x_1093_);
v___x_1095_ = 16ULL;
v___x_1096_ = lean_uint64_shift_right(v_fold_1094_, v___x_1095_);
v___x_1097_ = lean_uint64_xor(v_fold_1094_, v___x_1096_);
v___x_1098_ = lean_uint64_to_usize(v___x_1097_);
v___x_1099_ = lean_usize_of_nat(v___x_1090_);
v___x_1100_ = ((size_t)1ULL);
v___x_1101_ = lean_usize_sub(v___x_1099_, v___x_1100_);
v___x_1102_ = lean_usize_land(v___x_1098_, v___x_1101_);
v___x_1103_ = lean_array_uget_borrowed(v_x_1082_, v___x_1102_);
lean_inc(v___x_1103_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 2, v___x_1103_);
v___x_1105_ = v___x_1088_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_key_1084_);
lean_ctor_set(v_reuseFailAlloc_1108_, 1, v_value_1085_);
lean_ctor_set(v_reuseFailAlloc_1108_, 2, v___x_1103_);
v___x_1105_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_array_uset(v_x_1082_, v___x_1102_, v___x_1105_);
v_x_1082_ = v___x_1106_;
v_x_1083_ = v_tail_1086_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1110_, lean_object* v_source_1111_, lean_object* v_target_1112_){
_start:
{
lean_object* v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = lean_array_get_size(v_source_1111_);
v___x_1114_ = lean_nat_dec_lt(v_i_1110_, v___x_1113_);
if (v___x_1114_ == 0)
{
lean_dec_ref(v_source_1111_);
lean_dec(v_i_1110_);
return v_target_1112_;
}
else
{
lean_object* v_es_1115_; lean_object* v___x_1116_; lean_object* v_source_1117_; lean_object* v_target_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v_es_1115_ = lean_array_fget(v_source_1111_, v_i_1110_);
v___x_1116_ = lean_box(0);
v_source_1117_ = lean_array_fset(v_source_1111_, v_i_1110_, v___x_1116_);
v_target_1118_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1112_, v_es_1115_);
v___x_1119_ = lean_unsigned_to_nat(1u);
v___x_1120_ = lean_nat_add(v_i_1110_, v___x_1119_);
lean_dec(v_i_1110_);
v_i_1110_ = v___x_1120_;
v_source_1111_ = v_source_1117_;
v_target_1112_ = v_target_1118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1122_){
_start:
{
lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v_nbuckets_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1123_ = lean_array_get_size(v_data_1122_);
v___x_1124_ = lean_unsigned_to_nat(2u);
v_nbuckets_1125_ = lean_nat_mul(v___x_1123_, v___x_1124_);
v___x_1126_ = lean_unsigned_to_nat(0u);
v___x_1127_ = lean_box(0);
v___x_1128_ = lean_mk_array(v_nbuckets_1125_, v___x_1127_);
v___x_1129_ = lean_array_propagate_mark(v_data_1122_, v___x_1128_);
v___x_1130_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1126_, v_data_1122_, v___x_1129_);
return v___x_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1131_, lean_object* v_b_1132_, lean_object* v_x_1133_){
_start:
{
if (lean_obj_tag(v_x_1133_) == 0)
{
lean_dec(v_b_1132_);
lean_dec_ref(v_a_1131_);
return v_x_1133_;
}
else
{
lean_object* v_key_1134_; lean_object* v_value_1135_; lean_object* v_tail_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1148_; 
v_key_1134_ = lean_ctor_get(v_x_1133_, 0);
v_value_1135_ = lean_ctor_get(v_x_1133_, 1);
v_tail_1136_ = lean_ctor_get(v_x_1133_, 2);
v_isSharedCheck_1148_ = !lean_is_exclusive(v_x_1133_);
if (v_isSharedCheck_1148_ == 0)
{
v___x_1138_ = v_x_1133_;
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_tail_1136_);
lean_inc(v_value_1135_);
lean_inc(v_key_1134_);
lean_dec(v_x_1133_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1148_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
uint8_t v___x_1140_; 
v___x_1140_ = lean_expr_eqv(v_key_1134_, v_a_1131_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1143_; 
v___x_1141_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1131_, v_b_1132_, v_tail_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 2, v___x_1141_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_key_1134_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_value_1135_);
lean_ctor_set(v_reuseFailAlloc_1144_, 2, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
else
{
lean_object* v___x_1146_; 
lean_dec(v_value_1135_);
lean_dec(v_key_1134_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v_b_1132_);
lean_ctor_set(v___x_1138_, 0, v_a_1131_);
v___x_1146_ = v___x_1138_;
goto v_reusejp_1145_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_a_1131_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_b_1132_);
lean_ctor_set(v_reuseFailAlloc_1147_, 2, v_tail_1136_);
v___x_1146_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1145_;
}
v_reusejp_1145_:
{
return v___x_1146_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1149_, lean_object* v_x_1150_){
_start:
{
if (lean_obj_tag(v_x_1150_) == 0)
{
uint8_t v___x_1151_; 
v___x_1151_ = 0;
return v___x_1151_;
}
else
{
lean_object* v_key_1152_; lean_object* v_tail_1153_; uint8_t v___x_1154_; 
v_key_1152_ = lean_ctor_get(v_x_1150_, 0);
v_tail_1153_ = lean_ctor_get(v_x_1150_, 2);
v___x_1154_ = lean_expr_eqv(v_key_1152_, v_a_1149_);
if (v___x_1154_ == 0)
{
v_x_1150_ = v_tail_1153_;
goto _start;
}
else
{
return v___x_1154_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1156_, lean_object* v_x_1157_){
_start:
{
uint8_t v_res_1158_; lean_object* v_r_1159_; 
v_res_1158_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1156_, v_x_1157_);
lean_dec(v_x_1157_);
lean_dec_ref(v_a_1156_);
v_r_1159_ = lean_box(v_res_1158_);
return v_r_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1160_, lean_object* v_a_1161_, lean_object* v_b_1162_){
_start:
{
lean_object* v_size_1163_; lean_object* v_buckets_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1207_; 
v_size_1163_ = lean_ctor_get(v_m_1160_, 0);
v_buckets_1164_ = lean_ctor_get(v_m_1160_, 1);
v_isSharedCheck_1207_ = !lean_is_exclusive(v_m_1160_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1166_ = v_m_1160_;
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_buckets_1164_);
lean_inc(v_size_1163_);
lean_dec(v_m_1160_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1207_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; uint64_t v___x_1169_; uint64_t v___x_1170_; uint64_t v___x_1171_; uint64_t v_fold_1172_; uint64_t v___x_1173_; uint64_t v___x_1174_; uint64_t v___x_1175_; size_t v___x_1176_; size_t v___x_1177_; size_t v___x_1178_; size_t v___x_1179_; size_t v___x_1180_; lean_object* v_bkt_1181_; uint8_t v___x_1182_; 
v___x_1168_ = lean_array_get_size(v_buckets_1164_);
v___x_1169_ = l_Lean_Expr_hash(v_a_1161_);
v___x_1170_ = 32ULL;
v___x_1171_ = lean_uint64_shift_right(v___x_1169_, v___x_1170_);
v_fold_1172_ = lean_uint64_xor(v___x_1169_, v___x_1171_);
v___x_1173_ = 16ULL;
v___x_1174_ = lean_uint64_shift_right(v_fold_1172_, v___x_1173_);
v___x_1175_ = lean_uint64_xor(v_fold_1172_, v___x_1174_);
v___x_1176_ = lean_uint64_to_usize(v___x_1175_);
v___x_1177_ = lean_usize_of_nat(v___x_1168_);
v___x_1178_ = ((size_t)1ULL);
v___x_1179_ = lean_usize_sub(v___x_1177_, v___x_1178_);
v___x_1180_ = lean_usize_land(v___x_1176_, v___x_1179_);
v_bkt_1181_ = lean_array_uget_borrowed(v_buckets_1164_, v___x_1180_);
v___x_1182_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1161_, v_bkt_1181_);
if (v___x_1182_ == 0)
{
lean_object* v___x_1183_; lean_object* v_size_x27_1184_; lean_object* v___x_1185_; lean_object* v_buckets_x27_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; uint8_t v___x_1192_; 
v___x_1183_ = lean_unsigned_to_nat(1u);
v_size_x27_1184_ = lean_nat_add(v_size_1163_, v___x_1183_);
lean_dec(v_size_1163_);
lean_inc(v_bkt_1181_);
v___x_1185_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1185_, 0, v_a_1161_);
lean_ctor_set(v___x_1185_, 1, v_b_1162_);
lean_ctor_set(v___x_1185_, 2, v_bkt_1181_);
v_buckets_x27_1186_ = lean_array_uset(v_buckets_1164_, v___x_1180_, v___x_1185_);
v___x_1187_ = lean_unsigned_to_nat(4u);
v___x_1188_ = lean_nat_mul(v_size_x27_1184_, v___x_1187_);
v___x_1189_ = lean_unsigned_to_nat(3u);
v___x_1190_ = lean_nat_div(v___x_1188_, v___x_1189_);
lean_dec(v___x_1188_);
v___x_1191_ = lean_array_get_size(v_buckets_x27_1186_);
v___x_1192_ = lean_nat_dec_le(v___x_1190_, v___x_1191_);
lean_dec(v___x_1190_);
if (v___x_1192_ == 0)
{
lean_object* v_val_1193_; lean_object* v___x_1195_; 
v_val_1193_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1186_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_val_1193_);
lean_ctor_set(v___x_1166_, 0, v_size_x27_1184_);
v___x_1195_ = v___x_1166_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_size_x27_1184_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v_val_1193_);
v___x_1195_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
return v___x_1195_;
}
}
else
{
lean_object* v___x_1198_; 
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v_buckets_x27_1186_);
lean_ctor_set(v___x_1166_, 0, v_size_x27_1184_);
v___x_1198_ = v___x_1166_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_size_x27_1184_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v_buckets_x27_1186_);
v___x_1198_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
return v___x_1198_;
}
}
}
else
{
lean_object* v___x_1200_; lean_object* v_buckets_x27_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
lean_inc(v_bkt_1181_);
v___x_1200_ = lean_box(0);
v_buckets_x27_1201_ = lean_array_uset(v_buckets_1164_, v___x_1180_, v___x_1200_);
v___x_1202_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1161_, v_b_1162_, v_bkt_1181_);
v___x_1203_ = lean_array_uset(v_buckets_x27_1201_, v___x_1180_, v___x_1202_);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 1, v___x_1203_);
v___x_1205_ = v___x_1166_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_size_1163_);
lean_ctor_set(v_reuseFailAlloc_1206_, 1, v___x_1203_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1208_, lean_object* v_e_1209_, lean_object* v_a_1210_){
_start:
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; 
v___x_1212_ = lean_st_ref_take(v_a_1208_);
v___x_1213_ = lean_box(0);
v___x_1214_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1212_, v_e_1209_, v_a_1210_);
v___x_1215_ = lean_st_ref_put(v_a_1208_, v___x_1214_);
return v___x_1213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1216_, lean_object* v_e_1217_, lean_object* v_a_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1216_, v_e_1217_, v_a_1218_);
lean_dec(v_a_1216_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1221_, lean_object* v_e_1222_, lean_object* v_a_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1221_, v_e_1222_, v_a_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v_a_1223_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1231_, lean_object* v_e_1232_, lean_object* v_a_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_a_1241_; lean_object* v___y_1253_; lean_object* v___x_1255_; lean_object* v___x_1256_; 
lean_inc(v_a_1233_);
v___x_1255_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1255_, 0, lean_box(0));
lean_closure_set(v___x_1255_, 1, lean_box(0));
lean_closure_set(v___x_1255_, 2, v_a_1233_);
v___x_1256_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1255_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1293_; 
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1293_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1261_; 
v___x_1261_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1257_, v_e_1232_);
lean_dec(v_a_1257_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_del_object(v___x_1259_);
lean_inc_ref(v_fn_1231_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v_e_1232_);
v___x_1262_ = lean_apply_7(v_fn_1231_, v_e_1232_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, lean_box(0));
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_object* v_a_1263_; uint8_t v___x_1264_; 
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
lean_inc(v_a_1263_);
lean_dec_ref_known(v___x_1262_, 1);
v___x_1264_ = lean_unbox(v_a_1263_);
lean_dec(v_a_1263_);
if (v___x_1264_ == 0)
{
lean_object* v___x_1265_; 
lean_dec_ref(v_fn_1231_);
v___x_1265_ = lean_box(0);
v_a_1241_ = v___x_1265_;
goto v___jp_1240_;
}
else
{
switch(lean_obj_tag(v_e_1232_))
{
case 7:
{
lean_object* v___x_1266_; lean_object* v___x_1267_; 
v___x_1266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1266_, 0, v_fn_1231_);
lean_inc_ref(v_e_1232_);
v___x_1267_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1266_, v_e_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1267_;
goto v___jp_1252_;
}
case 6:
{
lean_object* v___x_1268_; lean_object* v___x_1269_; 
v___x_1268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1268_, 0, v_fn_1231_);
lean_inc_ref(v_e_1232_);
v___x_1269_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1268_, v_e_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1269_;
goto v___jp_1252_;
}
case 8:
{
lean_object* v___x_1270_; lean_object* v___x_1271_; 
v___x_1270_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1270_, 0, v_fn_1231_);
lean_inc_ref(v_e_1232_);
v___x_1271_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1270_, v_e_1232_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1271_;
goto v___jp_1252_;
}
case 5:
{
lean_object* v_fn_1272_; lean_object* v_arg_1273_; lean_object* v___x_1274_; 
v_fn_1272_ = lean_ctor_get(v_e_1232_, 0);
v_arg_1273_ = lean_ctor_get(v_e_1232_, 1);
lean_inc_ref(v_fn_1272_);
lean_inc_ref(v_fn_1231_);
v___x_1274_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1231_, v_fn_1272_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v___x_1275_; 
lean_dec_ref_known(v___x_1274_, 1);
lean_inc_ref(v_arg_1273_);
v___x_1275_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1231_, v_arg_1273_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1275_;
goto v___jp_1252_;
}
else
{
lean_dec_ref(v_fn_1231_);
v___y_1253_ = v___x_1274_;
goto v___jp_1252_;
}
}
case 10:
{
lean_object* v_expr_1276_; lean_object* v___x_1277_; 
v_expr_1276_ = lean_ctor_get(v_e_1232_, 1);
lean_inc_ref(v_expr_1276_);
v___x_1277_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1231_, v_expr_1276_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1277_;
goto v___jp_1252_;
}
case 11:
{
lean_object* v_struct_1278_; lean_object* v___x_1279_; 
v_struct_1278_ = lean_ctor_get(v_e_1232_, 2);
lean_inc_ref(v_struct_1278_);
v___x_1279_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1231_, v_struct_1278_, v_a_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
v___y_1253_ = v___x_1279_;
goto v___jp_1252_;
}
default: 
{
lean_object* v___x_1280_; 
lean_dec_ref(v_fn_1231_);
v___x_1280_ = lean_box(0);
v_a_1241_ = v___x_1280_;
goto v___jp_1240_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_e_1232_);
lean_dec_ref(v_fn_1231_);
v_a_1281_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1262_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1262_);
v___x_1283_ = lean_box(0);
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
v_resetjp_1282_:
{
lean_object* v___x_1286_; 
if (v_isShared_1284_ == 0)
{
v___x_1286_ = v___x_1283_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1287_; 
v_reuseFailAlloc_1287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1287_, 0, v_a_1281_);
v___x_1286_ = v_reuseFailAlloc_1287_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
return v___x_1286_;
}
}
}
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1291_; 
lean_dec_ref(v_e_1232_);
lean_dec_ref(v_fn_1231_);
v_val_1289_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_val_1289_);
lean_dec_ref_known(v___x_1261_, 1);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 0, v_val_1289_);
v___x_1291_ = v___x_1259_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_val_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
else
{
lean_object* v_a_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1301_; 
lean_dec_ref(v_e_1232_);
lean_dec_ref(v_fn_1231_);
v_a_1294_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1301_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1301_ == 0)
{
v___x_1296_ = v___x_1256_;
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_a_1294_);
lean_dec(v___x_1256_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1301_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1299_; 
if (v_isShared_1297_ == 0)
{
v___x_1299_ = v___x_1296_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1300_; 
v_reuseFailAlloc_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1300_, 0, v_a_1294_);
v___x_1299_ = v_reuseFailAlloc_1300_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
return v___x_1299_;
}
}
}
v___jp_1240_:
{
lean_object* v___f_1242_; lean_object* v___x_1243_; 
lean_inc(v_a_1233_);
v___f_1242_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1242_, 0, v_a_1233_);
lean_closure_set(v___f_1242_, 1, v_e_1232_);
lean_closure_set(v___f_1242_, 2, v_a_1241_);
v___x_1243_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1242_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v___x_1245_; uint8_t v_isShared_1246_; uint8_t v_isSharedCheck_1250_; 
v_isSharedCheck_1250_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1250_ == 0)
{
lean_object* v_unused_1251_; 
v_unused_1251_ = lean_ctor_get(v___x_1243_, 0);
lean_dec(v_unused_1251_);
v___x_1245_ = v___x_1243_;
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
else
{
lean_dec(v___x_1243_);
v___x_1245_ = lean_box(0);
v_isShared_1246_ = v_isSharedCheck_1250_;
goto v_resetjp_1244_;
}
v_resetjp_1244_:
{
lean_object* v___x_1248_; 
if (v_isShared_1246_ == 0)
{
lean_ctor_set(v___x_1245_, 0, v_a_1241_);
v___x_1248_ = v___x_1245_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1249_; 
v_reuseFailAlloc_1249_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1249_, 0, v_a_1241_);
v___x_1248_ = v_reuseFailAlloc_1249_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
return v___x_1248_;
}
}
}
else
{
return v___x_1243_;
}
}
v___jp_1252_:
{
if (lean_obj_tag(v___y_1253_) == 0)
{
lean_object* v_a_1254_; 
v_a_1254_ = lean_ctor_get(v___y_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___y_1253_, 1);
v_a_1241_ = v_a_1254_;
goto v___jp_1240_;
}
else
{
lean_dec_ref(v_e_1232_);
return v___y_1253_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1302_ = lean_box(0);
v___x_1303_ = lean_unsigned_to_nat(16u);
v___x_1304_ = lean_mk_array(v___x_1303_, v___x_1302_);
return v___x_1304_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; 
v___x_1305_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1306_ = lean_unsigned_to_nat(0u);
v___x_1307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1306_);
lean_ctor_set(v___x_1307_, 1, v___x_1305_);
return v___x_1307_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1308_; lean_object* v___x_1309_; 
v___x_1308_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1309_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1309_, 0, lean_box(0));
lean_closure_set(v___x_1309_, 1, lean_box(0));
lean_closure_set(v___x_1309_, 2, v___x_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1310_, lean_object* v_fn_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v_a_1320_; lean_object* v___x_1321_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1319_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1318_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
v_a_1320_ = lean_ctor_get(v___x_1319_, 0);
lean_inc(v_a_1320_);
lean_dec_ref(v___x_1319_);
v___x_1321_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1311_, v_input_1310_, v_a_1320_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
if (lean_obj_tag(v___x_1321_) == 0)
{
lean_object* v_a_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
v_a_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc(v_a_1322_);
lean_dec_ref_known(v___x_1321_, 1);
v___x_1323_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1323_, 0, lean_box(0));
lean_closure_set(v___x_1323_, 1, lean_box(0));
lean_closure_set(v___x_1323_, 2, v_a_1320_);
v___x_1324_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1323_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1324_);
if (v_isSharedCheck_1331_ == 0)
{
lean_object* v_unused_1332_; 
v_unused_1332_ = lean_ctor_get(v___x_1324_, 0);
lean_dec(v_unused_1332_);
v___x_1326_ = v___x_1324_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_dec(v___x_1324_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
lean_ctor_set(v___x_1326_, 0, v_a_1322_);
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1322_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
else
{
lean_dec(v_a_1320_);
return v___x_1321_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1333_, lean_object* v_fn_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_, lean_object* v___y_1339_, lean_object* v___y_1340_){
_start:
{
lean_object* v_res_1341_; 
v_res_1341_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1333_, v_fn_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
return v_res_1341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1342_, lean_object* v_fn_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
lean_object* v___f_1350_; lean_object* v___x_1351_; 
v___f_1350_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1350_, 0, v_fn_1343_);
v___x_1351_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1342_, v___f_1350_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_, v___y_1348_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1352_, lean_object* v_fn_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1352_, v_fn_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1361_, lean_object* v_x_1362_, lean_object* v_x_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
if (lean_obj_tag(v_x_1363_) == 0)
{
lean_object* v___x_1370_; 
lean_dec_ref(v_fn_1361_);
v___x_1370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1370_, 0, v_x_1362_);
return v___x_1370_;
}
else
{
lean_object* v_head_1371_; lean_object* v_tail_1372_; lean_object* v_type_1373_; lean_object* v___x_1374_; 
v_head_1371_ = lean_ctor_get(v_x_1363_, 0);
lean_inc(v_head_1371_);
v_tail_1372_ = lean_ctor_get(v_x_1363_, 1);
lean_inc(v_tail_1372_);
lean_dec_ref_known(v_x_1363_, 2);
v_type_1373_ = lean_ctor_get(v_head_1371_, 1);
lean_inc_ref(v_type_1373_);
lean_dec(v_head_1371_);
lean_inc_ref(v_fn_1361_);
v___x_1374_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1373_, v_fn_1361_, v___y_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
lean_inc(v_a_1375_);
lean_dec_ref_known(v___x_1374_, 1);
v_x_1362_ = v_a_1375_;
v_x_1363_ = v_tail_1372_;
goto _start;
}
else
{
lean_dec(v_tail_1372_);
lean_dec_ref(v_fn_1361_);
return v___x_1374_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1377_, lean_object* v_x_1378_, lean_object* v_x_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_, lean_object* v___y_1384_, lean_object* v___y_1385_){
_start:
{
lean_object* v_res_1386_; 
v_res_1386_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1377_, v_x_1378_, v_x_1379_, v___y_1380_, v___y_1381_, v___y_1382_, v___y_1383_, v___y_1384_);
lean_dec(v___y_1384_);
lean_dec_ref(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1387_, lean_object* v_x_1388_, lean_object* v_x_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
if (lean_obj_tag(v_x_1389_) == 0)
{
lean_object* v___x_1396_; 
lean_dec_ref(v_fn_1387_);
v___x_1396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1396_, 0, v_x_1388_);
return v___x_1396_;
}
else
{
lean_object* v_head_1397_; lean_object* v_tail_1398_; lean_object* v___y_1400_; lean_object* v_type_1403_; lean_object* v_ctors_1404_; lean_object* v___x_1405_; 
v_head_1397_ = lean_ctor_get(v_x_1389_, 0);
lean_inc(v_head_1397_);
v_tail_1398_ = lean_ctor_get(v_x_1389_, 1);
lean_inc(v_tail_1398_);
lean_dec_ref_known(v_x_1389_, 2);
v_type_1403_ = lean_ctor_get(v_head_1397_, 1);
lean_inc_ref(v_type_1403_);
v_ctors_1404_ = lean_ctor_get(v_head_1397_, 2);
lean_inc(v_ctors_1404_);
lean_dec(v_head_1397_);
lean_inc_ref(v_fn_1387_);
v___x_1405_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1403_, v_fn_1387_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_object* v_a_1406_; lean_object* v___x_1407_; 
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc(v_a_1406_);
lean_dec_ref_known(v___x_1405_, 1);
lean_inc_ref(v_fn_1387_);
v___x_1407_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1387_, v_a_1406_, v_ctors_1404_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
v___y_1400_ = v___x_1407_;
goto v___jp_1399_;
}
else
{
lean_dec(v_ctors_1404_);
v___y_1400_ = v___x_1405_;
goto v___jp_1399_;
}
v___jp_1399_:
{
if (lean_obj_tag(v___y_1400_) == 0)
{
lean_object* v_a_1401_; 
v_a_1401_ = lean_ctor_get(v___y_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref_known(v___y_1400_, 1);
v_x_1388_ = v_a_1401_;
v_x_1389_ = v_tail_1398_;
goto _start;
}
else
{
lean_dec(v_tail_1398_);
lean_dec_ref(v_fn_1387_);
return v___y_1400_;
}
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
lean_object* v_head_1428_; lean_object* v_tail_1429_; lean_object* v___y_1431_; lean_object* v_toConstantVal_1434_; lean_object* v_value_1435_; lean_object* v_type_1436_; lean_object* v___x_1437_; 
v_head_1428_ = lean_ctor_get(v_x_1420_, 0);
lean_inc(v_head_1428_);
v_tail_1429_ = lean_ctor_get(v_x_1420_, 1);
lean_inc(v_tail_1429_);
lean_dec_ref_known(v_x_1420_, 2);
v_toConstantVal_1434_ = lean_ctor_get(v_head_1428_, 0);
lean_inc_ref(v_toConstantVal_1434_);
v_value_1435_ = lean_ctor_get(v_head_1428_, 1);
lean_inc_ref(v_value_1435_);
lean_dec(v_head_1428_);
v_type_1436_ = lean_ctor_get(v_toConstantVal_1434_, 2);
lean_inc_ref(v_type_1436_);
lean_dec_ref(v_toConstantVal_1434_);
lean_inc_ref(v_fn_1418_);
v___x_1437_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1436_, v_fn_1418_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
if (lean_obj_tag(v___x_1437_) == 0)
{
lean_object* v___x_1438_; 
lean_dec_ref_known(v___x_1437_, 1);
lean_inc_ref(v_fn_1418_);
v___x_1438_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1435_, v_fn_1418_, v___y_1421_, v___y_1422_, v___y_1423_, v___y_1424_, v___y_1425_);
v___y_1431_ = v___x_1438_;
goto v___jp_1430_;
}
else
{
lean_dec_ref(v_value_1435_);
v___y_1431_ = v___x_1437_;
goto v___jp_1430_;
}
v___jp_1430_:
{
if (lean_obj_tag(v___y_1431_) == 0)
{
lean_object* v_a_1432_; 
v_a_1432_ = lean_ctor_get(v___y_1431_, 0);
lean_inc(v_a_1432_);
lean_dec_ref_known(v___y_1431_, 1);
v_x_1419_ = v_a_1432_;
v_x_1420_ = v_tail_1429_;
goto _start;
}
else
{
lean_dec(v_tail_1429_);
lean_dec_ref(v_fn_1418_);
return v___y_1431_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1439_, lean_object* v_x_1440_, lean_object* v_x_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_, lean_object* v___y_1444_, lean_object* v___y_1445_, lean_object* v___y_1446_, lean_object* v___y_1447_){
_start:
{
lean_object* v_res_1448_; 
v_res_1448_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1439_, v_x_1440_, v_x_1441_, v___y_1442_, v___y_1443_, v___y_1444_, v___y_1445_, v___y_1446_);
lean_dec(v___y_1446_);
lean_dec_ref(v___y_1445_);
lean_dec(v___y_1444_);
lean_dec_ref(v___y_1443_);
lean_dec(v___y_1442_);
return v_res_1448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1449_, lean_object* v_d_1450_, lean_object* v_a_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_){
_start:
{
switch(lean_obj_tag(v_d_1450_))
{
case 0:
{
lean_object* v_val_1458_; lean_object* v_toConstantVal_1459_; lean_object* v_type_1460_; lean_object* v___x_1461_; 
v_val_1458_ = lean_ctor_get(v_d_1450_, 0);
lean_inc_ref(v_val_1458_);
lean_dec_ref_known(v_d_1450_, 1);
v_toConstantVal_1459_ = lean_ctor_get(v_val_1458_, 0);
lean_inc_ref(v_toConstantVal_1459_);
lean_dec_ref(v_val_1458_);
v_type_1460_ = lean_ctor_get(v_toConstantVal_1459_, 2);
lean_inc_ref(v_type_1460_);
lean_dec_ref(v_toConstantVal_1459_);
v___x_1461_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1460_, v_fn_1449_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1461_;
}
case 4:
{
lean_object* v___x_1462_; 
lean_dec_ref(v_fn_1449_);
v___x_1462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1462_, 0, v_a_1451_);
return v___x_1462_;
}
case 5:
{
lean_object* v_defns_1463_; lean_object* v___x_1464_; 
v_defns_1463_ = lean_ctor_get(v_d_1450_, 0);
lean_inc(v_defns_1463_);
lean_dec_ref_known(v_d_1450_, 1);
v___x_1464_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1449_, v_a_1451_, v_defns_1463_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1464_;
}
case 6:
{
lean_object* v_types_1465_; lean_object* v___x_1466_; 
v_types_1465_ = lean_ctor_get(v_d_1450_, 2);
lean_inc(v_types_1465_);
lean_dec_ref_known(v_d_1450_, 3);
v___x_1466_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1449_, v_a_1451_, v_types_1465_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1466_;
}
default: 
{
lean_object* v_val_1467_; lean_object* v_toConstantVal_1468_; lean_object* v_value_1469_; lean_object* v_type_1470_; lean_object* v___x_1471_; 
v_val_1467_ = lean_ctor_get(v_d_1450_, 0);
lean_inc_ref(v_val_1467_);
lean_dec(v_d_1450_);
v_toConstantVal_1468_ = lean_ctor_get(v_val_1467_, 0);
lean_inc_ref(v_toConstantVal_1468_);
v_value_1469_ = lean_ctor_get(v_val_1467_, 1);
lean_inc_ref(v_value_1469_);
lean_dec_ref(v_val_1467_);
v_type_1470_ = lean_ctor_get(v_toConstantVal_1468_, 2);
lean_inc_ref(v_type_1470_);
lean_dec_ref(v_toConstantVal_1468_);
lean_inc_ref(v_fn_1449_);
v___x_1471_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1470_, v_fn_1449_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v___x_1472_; 
lean_dec_ref_known(v___x_1471_, 1);
v___x_1472_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1469_, v_fn_1449_, v___y_1452_, v___y_1453_, v___y_1454_, v___y_1455_, v___y_1456_);
return v___x_1472_;
}
else
{
lean_dec_ref(v_value_1469_);
lean_dec_ref(v_fn_1449_);
return v___x_1471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1473_, lean_object* v_d_1474_, lean_object* v_a_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_, lean_object* v___y_1480_, lean_object* v___y_1481_){
_start:
{
lean_object* v_res_1482_; 
v_res_1482_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1473_, v_d_1474_, v_a_1475_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_, v___y_1480_);
lean_dec(v___y_1480_);
lean_dec_ref(v___y_1479_);
lean_dec(v___y_1478_);
lean_dec_ref(v___y_1477_);
lean_dec(v___y_1476_);
return v_res_1482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1483_, lean_object* v_fn_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; 
v___x_1491_ = lean_box(0);
v___x_1492_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1484_, v_decl_1483_, v___x_1491_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_, v___y_1489_);
return v___x_1492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1493_, lean_object* v_fn_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_){
_start:
{
lean_object* v_res_1501_; 
v_res_1501_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1493_, v_fn_1494_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_, v___y_1499_);
lean_dec(v___y_1499_);
lean_dec_ref(v___y_1498_);
lean_dec(v___y_1497_);
lean_dec_ref(v___y_1496_);
lean_dec(v___y_1495_);
return v_res_1501_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_1506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1506_, 0, v___x_1505_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__3(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1507_ = lean_box(1);
v___x_1508_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1509_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1507_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1511_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v___x_1512_);
lean_ctor_set(v___x_1513_, 2, v___x_1512_);
lean_ctor_set(v___x_1513_, 3, v___x_1512_);
lean_ctor_set(v___x_1513_, 4, v___x_1511_);
lean_ctor_set(v___x_1513_, 5, v___x_1511_);
lean_ctor_set(v___x_1513_, 6, v___x_1511_);
lean_ctor_set(v___x_1513_, 7, v___x_1511_);
lean_ctor_set(v___x_1513_, 8, v___x_1511_);
lean_ctor_set(v___x_1513_, 9, v___x_1511_);
lean_ctor_set(v___x_1513_, 10, v___x_1511_);
return v___x_1513_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1514_; lean_object* v___x_1515_; 
v___x_1514_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1515_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1515_, 0, v___x_1514_);
lean_ctor_set(v___x_1515_, 1, v___x_1514_);
lean_ctor_set(v___x_1515_, 2, v___x_1514_);
lean_ctor_set(v___x_1515_, 3, v___x_1514_);
lean_ctor_set(v___x_1515_, 4, v___x_1514_);
lean_ctor_set(v___x_1515_, 5, v___x_1514_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1517_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1517_, 0, v___x_1516_);
lean_ctor_set(v___x_1517_, 1, v___x_1516_);
lean_ctor_set(v___x_1517_, 2, v___x_1516_);
lean_ctor_set(v___x_1517_, 3, v___x_1516_);
lean_ctor_set(v___x_1517_, 4, v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1518_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1519_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_1520_ = lean_box(1);
v___x_1521_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1522_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1523_, 0, v___x_1522_);
lean_ctor_set(v___x_1523_, 1, v___x_1521_);
lean_ctor_set(v___x_1523_, 2, v___x_1520_);
lean_ctor_set(v___x_1523_, 3, v___x_1519_);
lean_ctor_set(v___x_1523_, 4, v___x_1518_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__11(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1528_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1529_ = l_Lean_stringToMessageData(v___x_1528_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__13(void){
_start:
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
v___x_1531_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__12));
v___x_1532_ = l_Lean_stringToMessageData(v___x_1531_);
return v___x_1532_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__15(void){
_start:
{
lean_object* v___x_1534_; lean_object* v___x_1535_; 
v___x_1534_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__14));
v___x_1535_ = l_Lean_stringToMessageData(v___x_1534_);
return v___x_1535_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; 
v___x_1536_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__15, &l_Lean_warnIfUsesSorry___closed__15_once, _init_l_Lean_warnIfUsesSorry___closed__15);
v___x_1537_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1538_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
lean_ctor_set(v___x_1538_, 1, v___x_1536_);
return v___x_1538_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1543_);
v___x_1547_ = l_Lean_warn_sorry;
v___x_1548_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_1546_, v___x_1547_);
lean_dec_ref(v___x_1546_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
lean_dec(v_decl_1542_);
v___x_1549_ = lean_box(0);
v___x_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1550_, 0, v___x_1549_);
return v___x_1550_;
}
else
{
lean_object* v___f_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v_messages_1557_; uint8_t v___x_1558_; 
v___f_1551_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__0));
v___x_1552_ = lean_box(1);
v___x_1553_ = lean_st_ref_get(v_a_1544_);
v_messages_1557_ = lean_ctor_get(v___x_1553_, 7);
lean_inc_ref(v_messages_1557_);
lean_dec(v___x_1553_);
v___x_1558_ = l_Lean_MessageLog_hasErrors(v_messages_1557_);
lean_dec_ref(v_messages_1557_);
if (v___x_1558_ == 0)
{
if (v___x_1548_ == 0)
{
lean_dec(v_decl_1542_);
goto v___jp_1554_;
}
else
{
uint8_t v___x_1559_; 
v___x_1559_ = l_Lean_Declaration_hasSorry(v_decl_1542_);
if (v___x_1559_ == 0)
{
lean_dec(v_decl_1542_);
goto v___jp_1554_;
}
else
{
lean_object* v___x_1560_; lean_object* v___x_1561_; uint8_t v___x_1562_; uint8_t v___x_1563_; uint8_t v___x_1564_; lean_object* v___x_1565_; uint64_t v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; 
v___x_1560_ = lean_unsigned_to_nat(0u);
v___x_1561_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__1));
v___x_1562_ = 1;
v___x_1563_ = 0;
v___x_1564_ = 2;
v___x_1565_ = lean_alloc_ctor(0, 0, 20);
lean_ctor_set_uint8(v___x_1565_, 0, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 2, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 3, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 4, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 5, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 6, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 7, v___x_1558_);
lean_ctor_set_uint8(v___x_1565_, 8, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 9, v___x_1562_);
lean_ctor_set_uint8(v___x_1565_, 10, v___x_1563_);
lean_ctor_set_uint8(v___x_1565_, 11, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 12, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 13, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 14, v___x_1564_);
lean_ctor_set_uint8(v___x_1565_, 15, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 16, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 17, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 18, v___x_1559_);
lean_ctor_set_uint8(v___x_1565_, 19, v___x_1558_);
v___x_1566_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1565_);
v___x_1567_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1567_, 0, v___x_1565_);
lean_ctor_set_uint64(v___x_1567_, sizeof(void*)*1, v___x_1566_);
v___x_1568_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__3, &l_Lean_warnIfUsesSorry___closed__3_once, _init_l_Lean_warnIfUsesSorry___closed__3);
v___x_1569_ = lean_box(0);
v___x_1570_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1570_, 0, v___x_1567_);
lean_ctor_set(v___x_1570_, 1, v___x_1552_);
lean_ctor_set(v___x_1570_, 2, v___x_1568_);
lean_ctor_set(v___x_1570_, 3, v___x_1561_);
lean_ctor_set(v___x_1570_, 4, v___x_1569_);
lean_ctor_set(v___x_1570_, 5, v___x_1560_);
lean_ctor_set(v___x_1570_, 6, v___x_1569_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*7, v___x_1558_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*7 + 1, v___x_1558_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*7 + 2, v___x_1558_);
lean_ctor_set_uint8(v___x_1570_, sizeof(void*)*7 + 3, v___x_1548_);
v___x_1571_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1572_ = lean_st_mk_ref(v___x_1571_);
v___x_1573_ = lean_st_mk_ref(v___x_1561_);
v___x_1574_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1542_, v___f_1551_, v___x_1573_, v___x_1570_, v___x_1572_, v_a_1543_, v_a_1544_);
lean_dec_ref_known(v___x_1570_, 7);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v_val_1578_; lean_object* v___x_1600_; size_t v_sz_1601_; size_t v___x_1602_; lean_object* v___x_1603_; lean_object* v_fst_1604_; 
lean_dec_ref_known(v___x_1574_, 1);
v___x_1575_ = lean_st_ref_get(v___x_1573_);
lean_dec(v___x_1573_);
v___x_1576_ = lean_st_ref_get(v___x_1572_);
lean_dec(v___x_1572_);
lean_dec(v___x_1576_);
v___x_1600_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__17));
v_sz_1601_ = lean_array_size(v___x_1575_);
v___x_1602_ = ((size_t)0ULL);
v___x_1603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1575_, v_sz_1601_, v___x_1602_, v___x_1600_);
v_fst_1604_ = lean_ctor_get(v___x_1603_, 0);
lean_inc(v_fst_1604_);
lean_dec_ref(v___x_1603_);
if (lean_obj_tag(v_fst_1604_) == 0)
{
goto v___jp_1594_;
}
else
{
lean_object* v_val_1605_; 
v_val_1605_ = lean_ctor_get(v_fst_1604_, 0);
lean_inc(v_val_1605_);
lean_dec_ref_known(v_fst_1604_, 1);
if (lean_obj_tag(v_val_1605_) == 0)
{
goto v___jp_1594_;
}
else
{
lean_object* v_val_1606_; 
lean_dec(v___x_1575_);
v_val_1606_ = lean_ctor_get(v_val_1605_, 0);
lean_inc(v_val_1606_);
lean_dec_ref_known(v_val_1605_, 1);
v_val_1578_ = v_val_1606_;
goto v___jp_1577_;
}
}
v___jp_1577_:
{
lean_object* v_snd_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1592_; 
v_snd_1579_ = lean_ctor_get(v_val_1578_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_val_1578_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_val_1578_, 0);
lean_dec(v_unused_1593_);
v___x_1581_ = v_val_1578_;
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_snd_1579_);
lean_dec(v_val_1578_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1592_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1586_; 
v___x_1583_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__9));
v___x_1584_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__11, &l_Lean_warnIfUsesSorry___closed__11_once, _init_l_Lean_warnIfUsesSorry___closed__11);
if (v_isShared_1582_ == 0)
{
lean_ctor_set_tag(v___x_1581_, 7);
lean_ctor_set(v___x_1581_, 0, v___x_1584_);
v___x_1586_ = v___x_1581_;
goto v_reusejp_1585_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1584_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_snd_1579_);
v___x_1586_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1585_;
}
v_reusejp_1585_:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1587_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__13, &l_Lean_warnIfUsesSorry___closed__13_once, _init_l_Lean_warnIfUsesSorry___closed__13);
v___x_1588_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1586_);
lean_ctor_set(v___x_1588_, 1, v___x_1587_);
v___x_1589_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1589_, 0, v___x_1583_);
lean_ctor_set(v___x_1589_, 1, v___x_1588_);
v___x_1590_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1589_, v_a_1543_, v_a_1544_);
return v___x_1590_;
}
}
}
v___jp_1594_:
{
lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1595_ = lean_array_get_size(v___x_1575_);
v___x_1596_ = lean_nat_dec_lt(v___x_1560_, v___x_1595_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; lean_object* v___x_1598_; 
lean_dec(v___x_1575_);
v___x_1597_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1598_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1597_, v_a_1543_, v_a_1544_);
return v___x_1598_;
}
else
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_array_fget(v___x_1575_, v___x_1560_);
lean_dec(v___x_1575_);
v_val_1578_ = v___x_1599_;
goto v___jp_1577_;
}
}
}
else
{
lean_dec(v___x_1573_);
lean_dec(v___x_1572_);
return v___x_1574_;
}
}
}
}
else
{
lean_dec(v_decl_1542_);
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
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1607_, lean_object* v_a_1608_, lean_object* v_a_1609_, lean_object* v_a_1610_){
_start:
{
lean_object* v_res_1611_; 
v_res_1611_ = l_Lean_warnIfUsesSorry(v_decl_1607_, v_a_1608_, v_a_1609_);
lean_dec(v_a_1609_);
lean_dec_ref(v_a_1608_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1612_, lean_object* v_m_1613_, lean_object* v_a_1614_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1613_, v_a_1614_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1616_, lean_object* v_m_1617_, lean_object* v_a_1618_){
_start:
{
lean_object* v_res_1619_; 
v_res_1619_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1616_, v_m_1617_, v_a_1618_);
lean_dec_ref(v_a_1618_);
lean_dec_ref(v_m_1617_);
return v_res_1619_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1620_, lean_object* v_m_1621_, lean_object* v_a_1622_, lean_object* v_b_1623_){
_start:
{
lean_object* v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1621_, v_a_1622_, v_b_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1629_, lean_object* v_a_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v_res_1632_; 
v_res_1632_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1629_, v_a_1630_, v_x_1631_);
lean_dec(v_x_1631_);
lean_dec_ref(v_a_1630_);
return v_res_1632_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_x_1635_){
_start:
{
uint8_t v___x_1636_; 
v___x_1636_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_a_1638_, lean_object* v_x_1639_){
_start:
{
uint8_t v_res_1640_; lean_object* v_r_1641_; 
v_res_1640_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1637_, v_a_1638_, v_x_1639_);
lean_dec(v_x_1639_);
lean_dec_ref(v_a_1638_);
v_r_1641_ = lean_box(v_res_1640_);
return v_r_1641_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1642_, lean_object* v_data_1643_){
_start:
{
lean_object* v___x_1644_; 
v___x_1644_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1643_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_x_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1646_, v_b_1647_, v_x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1650_, lean_object* v_name_1651_, uint8_t v_bi_1652_, lean_object* v_type_1653_, lean_object* v_k_1654_, uint8_t v_kind_1655_, lean_object* v___y_1656_, lean_object* v___y_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1651_, v_bi_1652_, v_type_1653_, v_k_1654_, v_kind_1655_, v___y_1656_, v___y_1657_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1664_, lean_object* v_name_1665_, lean_object* v_bi_1666_, lean_object* v_type_1667_, lean_object* v_k_1668_, lean_object* v_kind_1669_, lean_object* v___y_1670_, lean_object* v___y_1671_, lean_object* v___y_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_){
_start:
{
uint8_t v_bi_boxed_1677_; uint8_t v_kind_boxed_1678_; lean_object* v_res_1679_; 
v_bi_boxed_1677_ = lean_unbox(v_bi_1666_);
v_kind_boxed_1678_ = lean_unbox(v_kind_1669_);
v_res_1679_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1664_, v_name_1665_, v_bi_boxed_1677_, v_type_1667_, v_k_1668_, v_kind_boxed_1678_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_, v___y_1675_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec(v___y_1673_);
lean_dec_ref(v___y_1672_);
lean_dec(v___y_1671_);
lean_dec(v___y_1670_);
return v_res_1679_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1680_, lean_object* v_name_1681_, lean_object* v_type_1682_, lean_object* v_val_1683_, lean_object* v_k_1684_, uint8_t v_nondep_1685_, uint8_t v_kind_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
v___x_1694_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1681_, v_type_1682_, v_val_1683_, v_k_1684_, v_nondep_1685_, v_kind_1686_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
return v___x_1694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1695_, lean_object* v_name_1696_, lean_object* v_type_1697_, lean_object* v_val_1698_, lean_object* v_k_1699_, lean_object* v_nondep_1700_, lean_object* v_kind_1701_, lean_object* v___y_1702_, lean_object* v___y_1703_, lean_object* v___y_1704_, lean_object* v___y_1705_, lean_object* v___y_1706_, lean_object* v___y_1707_, lean_object* v___y_1708_){
_start:
{
uint8_t v_nondep_boxed_1709_; uint8_t v_kind_boxed_1710_; lean_object* v_res_1711_; 
v_nondep_boxed_1709_ = lean_unbox(v_nondep_1700_);
v_kind_boxed_1710_ = lean_unbox(v_kind_1701_);
v_res_1711_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1695_, v_name_1696_, v_type_1697_, v_val_1698_, v_k_1699_, v_nondep_boxed_1709_, v_kind_boxed_1710_, v___y_1702_, v___y_1703_, v___y_1704_, v___y_1705_, v___y_1706_, v___y_1707_);
lean_dec(v___y_1707_);
lean_dec_ref(v___y_1706_);
lean_dec(v___y_1705_);
lean_dec_ref(v___y_1704_);
lean_dec(v___y_1703_);
lean_dec(v___y_1702_);
return v_res_1711_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1712_, lean_object* v_i_1713_, lean_object* v_source_1714_, lean_object* v_target_1715_){
_start:
{
lean_object* v___x_1716_; 
v___x_1716_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1713_, v_source_1714_, v_target_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1717_, lean_object* v_x_1718_, lean_object* v_x_1719_){
_start:
{
lean_object* v___x_1720_; 
v___x_1720_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1718_, v_x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1770_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1771_ = 0;
v___x_1772_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1773_ = l_Lean_registerTraceClass(v___x_1770_, v___x_1771_, v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1776_, lean_object* v___y_1777_){
_start:
{
lean_object* v___x_1779_; lean_object* v_nextMacroScope_1780_; lean_object* v_ngen_1781_; lean_object* v_auxDeclNGen_1782_; lean_object* v_traceState_1783_; lean_object* v_recordedDeps_1784_; lean_object* v_messages_1785_; lean_object* v_infoState_1786_; lean_object* v_snapshotTasks_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1798_; 
v___x_1779_ = lean_st_ref_take(v___y_1777_);
v_nextMacroScope_1780_ = lean_ctor_get(v___x_1779_, 1);
v_ngen_1781_ = lean_ctor_get(v___x_1779_, 2);
v_auxDeclNGen_1782_ = lean_ctor_get(v___x_1779_, 3);
v_traceState_1783_ = lean_ctor_get(v___x_1779_, 4);
v_recordedDeps_1784_ = lean_ctor_get(v___x_1779_, 6);
v_messages_1785_ = lean_ctor_get(v___x_1779_, 7);
v_infoState_1786_ = lean_ctor_get(v___x_1779_, 8);
v_snapshotTasks_1787_ = lean_ctor_get(v___x_1779_, 9);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1798_ == 0)
{
lean_object* v_unused_1799_; lean_object* v_unused_1800_; 
v_unused_1799_ = lean_ctor_get(v___x_1779_, 5);
lean_dec(v_unused_1799_);
v_unused_1800_ = lean_ctor_get(v___x_1779_, 0);
lean_dec(v_unused_1800_);
v___x_1789_ = v___x_1779_;
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_snapshotTasks_1787_);
lean_inc(v_infoState_1786_);
lean_inc(v_messages_1785_);
lean_inc(v_recordedDeps_1784_);
lean_inc(v_traceState_1783_);
lean_inc(v_auxDeclNGen_1782_);
lean_inc(v_ngen_1781_);
lean_inc(v_nextMacroScope_1780_);
lean_dec(v___x_1779_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1798_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1794_; 
v___x_1791_ = lean_box(0);
v___x_1792_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1790_ == 0)
{
lean_ctor_set(v___x_1789_, 5, v___x_1792_);
lean_ctor_set(v___x_1789_, 0, v_env_1776_);
v___x_1794_ = v___x_1789_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_env_1776_);
lean_ctor_set(v_reuseFailAlloc_1797_, 1, v_nextMacroScope_1780_);
lean_ctor_set(v_reuseFailAlloc_1797_, 2, v_ngen_1781_);
lean_ctor_set(v_reuseFailAlloc_1797_, 3, v_auxDeclNGen_1782_);
lean_ctor_set(v_reuseFailAlloc_1797_, 4, v_traceState_1783_);
lean_ctor_set(v_reuseFailAlloc_1797_, 5, v___x_1792_);
lean_ctor_set(v_reuseFailAlloc_1797_, 6, v_recordedDeps_1784_);
lean_ctor_set(v_reuseFailAlloc_1797_, 7, v_messages_1785_);
lean_ctor_set(v_reuseFailAlloc_1797_, 8, v_infoState_1786_);
lean_ctor_set(v_reuseFailAlloc_1797_, 9, v_snapshotTasks_1787_);
v___x_1794_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
lean_object* v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = lean_st_ref_put(v___y_1777_, v___x_1794_);
v___x_1796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1796_, 0, v___x_1791_);
return v___x_1796_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_){
_start:
{
lean_object* v_res_1804_; 
v_res_1804_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1801_, v___y_1802_);
lean_dec(v___y_1802_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1805_, lean_object* v___y_1806_, lean_object* v___y_1807_){
_start:
{
lean_object* v___x_1809_; 
v___x_1809_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1805_, v___y_1807_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
lean_object* v_res_1814_; 
v_res_1814_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1810_, v___y_1811_, v___y_1812_);
lean_dec(v___y_1812_);
lean_dec_ref(v___y_1811_);
return v_res_1814_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_box(0);
v___x_1816_ = l_Lean_interruptExceptionId;
v___x_1817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1817_, 0, v___x_1816_);
lean_ctor_set(v___x_1817_, 1, v___x_1815_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; 
v___x_1819_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
return v___x_1820_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1821_){
_start:
{
lean_object* v_res_1822_; 
v_res_1822_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_){
_start:
{
lean_object* v_ref_1827_; lean_object* v___x_1828_; lean_object* v_a_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1837_; 
v_ref_1827_ = lean_ctor_get(v___y_1824_, 2);
v___x_1828_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1823_, v___y_1824_, v___y_1825_);
v_a_1829_ = lean_ctor_get(v___x_1828_, 0);
v_isSharedCheck_1837_ = !lean_is_exclusive(v___x_1828_);
if (v_isSharedCheck_1837_ == 0)
{
v___x_1831_ = v___x_1828_;
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_a_1829_);
lean_dec(v___x_1828_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1837_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v___x_1833_; lean_object* v___x_1835_; 
lean_inc(v_ref_1827_);
v___x_1833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1833_, 0, v_ref_1827_);
lean_ctor_set(v___x_1833_, 1, v_a_1829_);
if (v_isShared_1832_ == 0)
{
lean_ctor_set_tag(v___x_1831_, 1);
lean_ctor_set(v___x_1831_, 0, v___x_1833_);
v___x_1835_ = v___x_1831_;
goto v_reusejp_1834_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1833_);
v___x_1835_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1834_;
}
v_reusejp_1834_:
{
return v___x_1835_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_res_1842_; 
v_res_1842_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1838_, v___y_1839_, v___y_1840_);
lean_dec(v___y_1840_);
lean_dec_ref(v___y_1839_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
lean_object* v___y_1848_; lean_object* v___y_1849_; 
if (lean_obj_tag(v_ex_1843_) == 16)
{
lean_object* v___x_1853_; lean_object* v_a_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1861_; 
v___x_1853_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1861_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1861_ == 0)
{
v___x_1856_ = v___x_1853_;
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_a_1854_);
lean_dec(v___x_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1861_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
lean_object* v___x_1859_; 
if (v_isShared_1857_ == 0)
{
v___x_1859_ = v___x_1856_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v_a_1854_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
return v___x_1859_;
}
}
}
else
{
v___y_1848_ = v___y_1844_;
v___y_1849_ = v___y_1845_;
goto v___jp_1847_;
}
v___jp_1847_:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1848_);
v___x_1851_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1843_, v___x_1850_);
v___x_1852_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1851_, v___y_1848_, v___y_1849_);
return v___x_1852_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_){
_start:
{
lean_object* v_res_1866_; 
v_res_1866_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1862_, v___y_1863_, v___y_1864_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1866_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1867_, lean_object* v___y_1868_, lean_object* v___y_1869_){
_start:
{
if (lean_obj_tag(v_x_1867_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v_x_1867_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v_x_1867_, 1);
v___x_1872_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1871_, v___y_1868_, v___y_1869_);
return v___x_1872_;
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
v_a_1873_ = lean_ctor_get(v_x_1867_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v_x_1867_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v_x_1867_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v_x_1867_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
lean_ctor_set_tag(v___x_1875_, 0);
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1881_, lean_object* v___y_1882_, lean_object* v___y_1883_, lean_object* v___y_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1881_, v___y_1882_, v___y_1883_);
lean_dec(v___y_1883_);
lean_dec_ref(v___y_1882_);
return v_res_1885_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1892_ = lean_unsigned_to_nat(1u);
v___x_1893_ = l_Lean_Level_ofNat(v___x_1892_);
return v___x_1893_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4(void){
_start:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v___x_1894_ = lean_box(0);
v___x_1895_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__3);
v___x_1896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1895_);
lean_ctor_set(v___x_1896_, 1, v___x_1894_);
return v___x_1896_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1897_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4);
v___x_1898_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1899_ = l_Lean_mkConst(v___x_1898_, v___x_1897_);
return v___x_1899_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1900_; lean_object* v___x_1901_; 
v___x_1900_ = lean_unsigned_to_nat(0u);
v___x_1901_ = l_Lean_Level_ofNat(v___x_1900_);
return v___x_1901_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1902_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1903_ = l_Lean_mkSort(v___x_1902_);
return v___x_1903_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_box(0);
v___x_1910_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1911_ = l_Lean_mkConst(v___x_1910_, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1913_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1914_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1915_ = l_Lean_mkAppB(v___x_1914_, v___x_1913_, v___x_1912_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1921_, lean_object* v_b_1922_, lean_object* v___y_1923_, lean_object* v___y_1924_){
_start:
{
if (lean_obj_tag(v_as_x27_1921_) == 0)
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1926_, 0, v_b_1922_);
return v___x_1926_;
}
else
{
lean_object* v_head_1927_; lean_object* v_tail_1928_; lean_object* v___x_1929_; lean_object* v___y_1931_; uint8_t v___y_1932_; lean_object* v_a_1936_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; uint8_t v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v_toCold_1946_; lean_object* v_env_1947_; lean_object* v_cancelTk_x3f_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec_ref(v_b_1922_);
v_head_1927_ = lean_ctor_get(v_as_x27_1921_, 0);
v_tail_1928_ = lean_ctor_get(v_as_x27_1921_, 1);
v___x_1929_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1939_ = lean_box(0);
v___x_1940_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1927_);
v___x_1941_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1941_, 0, v_head_1927_);
lean_ctor_set(v___x_1941_, 1, v___x_1939_);
lean_ctor_set(v___x_1941_, 2, v___x_1940_);
v___x_1942_ = 0;
v___x_1943_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1943_, 0, v___x_1941_);
lean_ctor_set_uint8(v___x_1943_, sizeof(void*)*1, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
v___x_1945_ = lean_st_ref_get(v___y_1924_);
v_toCold_1946_ = lean_ctor_get(v___y_1923_, 0);
v_env_1947_ = lean_ctor_get(v___x_1945_, 0);
lean_inc_ref(v_env_1947_);
lean_dec(v___x_1945_);
v_cancelTk_x3f_1948_ = lean_ctor_get(v_toCold_1946_, 10);
v___x_1949_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_1923_);
v___x_1950_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1947_, v___x_1949_, v___x_1944_, v_cancelTk_x3f_1948_);
lean_dec_ref_known(v___x_1944_, 1);
lean_dec_ref(v___x_1949_);
v___x_1951_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1950_, v___y_1923_, v___y_1924_);
if (lean_obj_tag(v___x_1951_) == 0)
{
lean_object* v_a_1952_; lean_object* v___x_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1961_; 
v_a_1952_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1952_);
lean_dec_ref_known(v___x_1951_, 1);
v___x_1953_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1952_, v___y_1924_);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1953_);
if (v_isSharedCheck_1961_ == 0)
{
lean_object* v_unused_1962_; 
v_unused_1962_ = lean_ctor_get(v___x_1953_, 0);
lean_dec(v_unused_1962_);
v___x_1955_ = v___x_1953_;
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
else
{
lean_dec(v___x_1953_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1961_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1957_; lean_object* v___x_1959_; 
v___x_1957_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1956_ == 0)
{
lean_ctor_set(v___x_1955_, 0, v___x_1957_);
v___x_1959_ = v___x_1955_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v___x_1957_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
else
{
lean_object* v_a_1963_; 
v_a_1963_ = lean_ctor_get(v___x_1951_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1951_, 1);
v_a_1936_ = v_a_1963_;
goto v___jp_1935_;
}
v___jp_1930_:
{
if (v___y_1932_ == 0)
{
lean_dec_ref(v___y_1931_);
v_as_x27_1921_ = v_tail_1928_;
v_b_1922_ = v___x_1929_;
goto _start;
}
else
{
lean_object* v___x_1934_; 
v___x_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1934_, 0, v___y_1931_);
return v___x_1934_;
}
}
v___jp_1935_:
{
uint8_t v___x_1937_; 
v___x_1937_ = l_Lean_Exception_isInterrupt(v_a_1936_);
if (v___x_1937_ == 0)
{
uint8_t v___x_1938_; 
lean_inc_ref(v_a_1936_);
v___x_1938_ = l_Lean_Exception_isRuntime(v_a_1936_);
v___y_1931_ = v_a_1936_;
v___y_1932_ = v___x_1938_;
goto v___jp_1930_;
}
else
{
v___y_1931_ = v_a_1936_;
v___y_1932_ = v___x_1937_;
goto v___jp_1930_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1964_, v_b_1965_, v___y_1966_, v___y_1967_);
lean_dec(v___y_1967_);
lean_dec_ref(v___y_1966_);
lean_dec(v_as_x27_1964_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_){
_start:
{
lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_2003_; uint8_t v___y_2004_; lean_object* v_a_2007_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v_a_2015_; 
switch(lean_obj_tag(v_decl_1970_))
{
case 1:
{
lean_object* v_val_2018_; lean_object* v_toConstantVal_2019_; uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v_fallbackDecl_2022_; lean_object* v___x_2023_; lean_object* v_toCold_2024_; lean_object* v_env_2025_; lean_object* v_cancelTk_x3f_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; 
v_val_2018_ = lean_ctor_get(v_decl_1970_, 0);
v_toConstantVal_2019_ = lean_ctor_get(v_val_2018_, 0);
v___x_2020_ = 0;
lean_inc_ref(v_toConstantVal_2019_);
v___x_2021_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2021_, 0, v_toConstantVal_2019_);
lean_ctor_set_uint8(v___x_2021_, sizeof(void*)*1, v___x_2020_);
v_fallbackDecl_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2022_, 0, v___x_2021_);
v___x_2023_ = lean_st_ref_get(v_a_1972_);
v_toCold_2024_ = lean_ctor_get(v_a_1971_, 0);
v_env_2025_ = lean_ctor_get(v___x_2023_, 0);
lean_inc_ref(v_env_2025_);
lean_dec(v___x_2023_);
v_cancelTk_x3f_2026_ = lean_ctor_get(v_toCold_2024_, 10);
v___x_2027_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1971_);
v___x_2028_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2025_, v___x_2027_, v_fallbackDecl_2022_, v_cancelTk_x3f_2026_);
lean_dec_ref_known(v_fallbackDecl_2022_, 1);
lean_dec_ref(v___x_2027_);
v___x_2029_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2028_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; lean_object* v___x_2031_; lean_object* v___x_2033_; uint8_t v_isShared_2034_; uint8_t v_isSharedCheck_2039_; 
lean_dec_ref_known(v_decl_1970_, 1);
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2030_, v_a_1972_);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2039_ == 0)
{
lean_object* v_unused_2040_; 
v_unused_2040_ = lean_ctor_get(v___x_2031_, 0);
lean_dec(v_unused_2040_);
v___x_2033_ = v___x_2031_;
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
else
{
lean_dec(v___x_2031_);
v___x_2033_ = lean_box(0);
v_isShared_2034_ = v_isSharedCheck_2039_;
goto v_resetjp_2032_;
}
v_resetjp_2032_:
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2035_ = lean_box(0);
if (v_isShared_2034_ == 0)
{
lean_ctor_set(v___x_2033_, 0, v___x_2035_);
v___x_2037_ = v___x_2033_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
else
{
lean_object* v_a_2041_; 
v_a_2041_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2029_, 1);
v_a_2007_ = v_a_2041_;
goto v___jp_2006_;
}
}
case 2:
{
lean_object* v_val_2042_; lean_object* v_toConstantVal_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; lean_object* v_fallbackDecl_2046_; lean_object* v___x_2047_; lean_object* v_toCold_2048_; lean_object* v_env_2049_; lean_object* v_cancelTk_x3f_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; lean_object* v___x_2053_; 
v_val_2042_ = lean_ctor_get(v_decl_1970_, 0);
v_toConstantVal_2043_ = lean_ctor_get(v_val_2042_, 0);
v___x_2044_ = 0;
lean_inc_ref(v_toConstantVal_2043_);
v___x_2045_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2045_, 0, v_toConstantVal_2043_);
lean_ctor_set_uint8(v___x_2045_, sizeof(void*)*1, v___x_2044_);
v_fallbackDecl_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2046_, 0, v___x_2045_);
v___x_2047_ = lean_st_ref_get(v_a_1972_);
v_toCold_2048_ = lean_ctor_get(v_a_1971_, 0);
v_env_2049_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_ref(v_env_2049_);
lean_dec(v___x_2047_);
v_cancelTk_x3f_2050_ = lean_ctor_get(v_toCold_2048_, 10);
v___x_2051_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_1971_);
v___x_2052_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2049_, v___x_2051_, v_fallbackDecl_2046_, v_cancelTk_x3f_2050_);
lean_dec_ref_known(v_fallbackDecl_2046_, 1);
lean_dec_ref(v___x_2051_);
v___x_2053_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2052_, v_a_1971_, v_a_1972_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_object* v_a_2054_; lean_object* v___x_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2063_; 
lean_dec_ref_known(v_decl_1970_, 1);
v_a_2054_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2054_);
lean_dec_ref_known(v___x_2053_, 1);
v___x_2055_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2054_, v_a_1972_);
v_isSharedCheck_2063_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2063_ == 0)
{
lean_object* v_unused_2064_; 
v_unused_2064_ = lean_ctor_get(v___x_2055_, 0);
lean_dec(v_unused_2064_);
v___x_2057_ = v___x_2055_;
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
else
{
lean_dec(v___x_2055_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2063_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2059_; lean_object* v___x_2061_; 
v___x_2059_ = lean_box(0);
if (v_isShared_2058_ == 0)
{
lean_ctor_set(v___x_2057_, 0, v___x_2059_);
v___x_2061_ = v___x_2057_;
goto v_reusejp_2060_;
}
else
{
lean_object* v_reuseFailAlloc_2062_; 
v_reuseFailAlloc_2062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2062_, 0, v___x_2059_);
v___x_2061_ = v_reuseFailAlloc_2062_;
goto v_reusejp_2060_;
}
v_reusejp_2060_:
{
return v___x_2061_;
}
}
}
else
{
lean_object* v_a_2065_; 
v_a_2065_ = lean_ctor_get(v___x_2053_, 0);
lean_inc(v_a_2065_);
lean_dec_ref_known(v___x_2053_, 1);
v_a_2015_ = v_a_2065_;
goto v___jp_2014_;
}
}
default: 
{
v___y_1975_ = v_a_1971_;
v___y_1976_ = v_a_1972_;
goto v___jp_1974_;
}
}
v___jp_1974_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1977_ = l_Lean_Declaration_getNames(v_decl_1970_);
v___x_1978_ = lean_box(0);
v___x_1979_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0));
v___x_1980_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1977_, v___x_1979_, v___y_1975_, v___y_1976_);
lean_dec(v___x_1977_);
if (lean_obj_tag(v___x_1980_) == 0)
{
lean_object* v_a_1981_; lean_object* v___x_1983_; uint8_t v_isShared_1984_; uint8_t v_isSharedCheck_1993_; 
v_a_1981_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_1993_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_1993_ == 0)
{
v___x_1983_ = v___x_1980_;
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
else
{
lean_inc(v_a_1981_);
lean_dec(v___x_1980_);
v___x_1983_ = lean_box(0);
v_isShared_1984_ = v_isSharedCheck_1993_;
goto v_resetjp_1982_;
}
v_resetjp_1982_:
{
lean_object* v_fst_1985_; 
v_fst_1985_ = lean_ctor_get(v_a_1981_, 0);
lean_inc(v_fst_1985_);
lean_dec(v_a_1981_);
if (lean_obj_tag(v_fst_1985_) == 0)
{
lean_object* v___x_1987_; 
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v___x_1978_);
v___x_1987_ = v___x_1983_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1978_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
return v___x_1987_;
}
}
else
{
lean_object* v_val_1989_; lean_object* v___x_1991_; 
v_val_1989_ = lean_ctor_get(v_fst_1985_, 0);
lean_inc(v_val_1989_);
lean_dec_ref_known(v_fst_1985_, 1);
if (v_isShared_1984_ == 0)
{
lean_ctor_set(v___x_1983_, 0, v_val_1989_);
v___x_1991_ = v___x_1983_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v_val_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
return v___x_1991_;
}
}
}
}
else
{
lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
v_a_1994_ = lean_ctor_get(v___x_1980_, 0);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1980_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1980_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_dec(v___x_1980_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
v___jp_2002_:
{
if (v___y_2004_ == 0)
{
lean_dec_ref(v___y_2003_);
v___y_1975_ = v_a_1971_;
v___y_1976_ = v_a_1972_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2005_; 
lean_dec(v_decl_1970_);
v___x_2005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___y_2003_);
return v___x_2005_;
}
}
v___jp_2006_:
{
uint8_t v___x_2008_; 
v___x_2008_ = l_Lean_Exception_isInterrupt(v_a_2007_);
if (v___x_2008_ == 0)
{
uint8_t v___x_2009_; 
lean_inc_ref(v_a_2007_);
v___x_2009_ = l_Lean_Exception_isRuntime(v_a_2007_);
v___y_2003_ = v_a_2007_;
v___y_2004_ = v___x_2009_;
goto v___jp_2002_;
}
else
{
v___y_2003_ = v_a_2007_;
v___y_2004_ = v___x_2008_;
goto v___jp_2002_;
}
}
v___jp_2010_:
{
if (v___y_2012_ == 0)
{
lean_dec_ref(v___y_2011_);
v___y_1975_ = v_a_1971_;
v___y_1976_ = v_a_1972_;
goto v___jp_1974_;
}
else
{
lean_object* v___x_2013_; 
lean_dec(v_decl_1970_);
v___x_2013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2013_, 0, v___y_2011_);
return v___x_2013_;
}
}
v___jp_2014_:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Exception_isInterrupt(v_a_2015_);
if (v___x_2016_ == 0)
{
uint8_t v___x_2017_; 
lean_inc_ref(v_a_2015_);
v___x_2017_ = l_Lean_Exception_isRuntime(v_a_2015_);
v___y_2011_ = v_a_2015_;
v___y_2012_ = v___x_2017_;
goto v___jp_2010_;
}
else
{
v___y_2011_ = v_a_2015_;
v___y_2012_ = v___x_2016_;
goto v___jp_2010_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2066_, lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_){
_start:
{
lean_object* v_res_2070_; 
v_res_2070_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2066_, v_a_2067_, v_a_2068_);
lean_dec(v_a_2068_);
lean_dec_ref(v_a_2067_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2071_, lean_object* v_x_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_){
_start:
{
lean_object* v___x_2076_; 
v___x_2076_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2072_, v___y_2073_, v___y_2074_);
return v___x_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2077_, v_x_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2083_, lean_object* v_as_x27_2084_, lean_object* v_b_2085_, lean_object* v_a_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
lean_object* v___x_2090_; 
v___x_2090_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2084_, v_b_2085_, v___y_2087_, v___y_2088_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2091_, lean_object* v_as_x27_2092_, lean_object* v_b_2093_, lean_object* v_a_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_, lean_object* v___y_2097_){
_start:
{
lean_object* v_res_2098_; 
v_res_2098_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2091_, v_as_x27_2092_, v_b_2093_, v_a_2094_, v___y_2095_, v___y_2096_);
lean_dec(v___y_2096_);
lean_dec_ref(v___y_2095_);
lean_dec(v_as_x27_2092_);
lean_dec(v_as_2091_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v_res_2108_; 
v_res_2108_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2104_, v___y_2105_, v___y_2106_);
lean_dec(v___y_2106_);
lean_dec_ref(v___y_2105_);
return v_res_2108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2109_, lean_object* v_ex_2110_, lean_object* v___y_2111_, lean_object* v___y_2112_){
_start:
{
lean_object* v___x_2114_; 
v___x_2114_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2110_, v___y_2111_, v___y_2112_);
return v___x_2114_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2115_, lean_object* v_ex_2116_, lean_object* v___y_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_){
_start:
{
lean_object* v_res_2120_; 
v_res_2120_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2115_, v_ex_2116_, v___y_2117_, v___y_2118_);
lean_dec(v___y_2118_);
lean_dec_ref(v___y_2117_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2121_, lean_object* v_msg_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_){
_start:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2122_, v___y_2123_, v___y_2124_);
return v___x_2126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2127_, lean_object* v_msg_2128_, lean_object* v___y_2129_, lean_object* v___y_2130_, lean_object* v___y_2131_){
_start:
{
lean_object* v_res_2132_; 
v_res_2132_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2127_, v_msg_2128_, v___y_2129_, v___y_2130_);
lean_dec(v___y_2130_);
lean_dec_ref(v___y_2129_);
return v_res_2132_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_unsigned_to_nat(32u);
v___x_2134_ = lean_mk_empty_array_with_capacity(v___x_2133_);
v___x_2135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; 
v___x_2136_ = ((size_t)5ULL);
v___x_2137_ = lean_unsigned_to_nat(0u);
v___x_2138_ = lean_unsigned_to_nat(32u);
v___x_2139_ = lean_mk_empty_array_with_capacity(v___x_2138_);
v___x_2140_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2141_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
lean_ctor_set(v___x_2141_, 1, v___x_2139_);
lean_ctor_set(v___x_2141_, 2, v___x_2137_);
lean_ctor_set(v___x_2141_, 3, v___x_2137_);
lean_ctor_set_usize(v___x_2141_, 4, v___x_2136_);
return v___x_2141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2142_){
_start:
{
lean_object* v___x_2144_; lean_object* v_traceState_2145_; lean_object* v_traces_2146_; lean_object* v___x_2147_; lean_object* v_traceState_2148_; lean_object* v_env_2149_; lean_object* v_nextMacroScope_2150_; lean_object* v_ngen_2151_; lean_object* v_auxDeclNGen_2152_; lean_object* v_cache_2153_; lean_object* v_recordedDeps_2154_; lean_object* v_messages_2155_; lean_object* v_infoState_2156_; lean_object* v_snapshotTasks_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2176_; 
v___x_2144_ = lean_st_ref_get(v___y_2142_);
v_traceState_2145_ = lean_ctor_get(v___x_2144_, 4);
lean_inc_ref(v_traceState_2145_);
lean_dec(v___x_2144_);
v_traces_2146_ = lean_ctor_get(v_traceState_2145_, 0);
lean_inc_ref(v_traces_2146_);
lean_dec_ref(v_traceState_2145_);
v___x_2147_ = lean_st_ref_take(v___y_2142_);
v_traceState_2148_ = lean_ctor_get(v___x_2147_, 4);
v_env_2149_ = lean_ctor_get(v___x_2147_, 0);
v_nextMacroScope_2150_ = lean_ctor_get(v___x_2147_, 1);
v_ngen_2151_ = lean_ctor_get(v___x_2147_, 2);
v_auxDeclNGen_2152_ = lean_ctor_get(v___x_2147_, 3);
v_cache_2153_ = lean_ctor_get(v___x_2147_, 5);
v_recordedDeps_2154_ = lean_ctor_get(v___x_2147_, 6);
v_messages_2155_ = lean_ctor_get(v___x_2147_, 7);
v_infoState_2156_ = lean_ctor_get(v___x_2147_, 8);
v_snapshotTasks_2157_ = lean_ctor_get(v___x_2147_, 9);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2159_ = v___x_2147_;
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_snapshotTasks_2157_);
lean_inc(v_infoState_2156_);
lean_inc(v_messages_2155_);
lean_inc(v_recordedDeps_2154_);
lean_inc(v_cache_2153_);
lean_inc(v_traceState_2148_);
lean_inc(v_auxDeclNGen_2152_);
lean_inc(v_ngen_2151_);
lean_inc(v_nextMacroScope_2150_);
lean_inc(v_env_2149_);
lean_dec(v___x_2147_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2176_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
uint64_t v_tid_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2174_; 
v_tid_2161_ = lean_ctor_get_uint64(v_traceState_2148_, sizeof(void*)*1);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_traceState_2148_);
if (v_isSharedCheck_2174_ == 0)
{
lean_object* v_unused_2175_; 
v_unused_2175_ = lean_ctor_get(v_traceState_2148_, 0);
lean_dec(v_unused_2175_);
v___x_2163_ = v_traceState_2148_;
v_isShared_2164_ = v_isSharedCheck_2174_;
goto v_resetjp_2162_;
}
else
{
lean_dec(v_traceState_2148_);
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
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_env_2149_);
lean_ctor_set(v_reuseFailAlloc_2172_, 1, v_nextMacroScope_2150_);
lean_ctor_set(v_reuseFailAlloc_2172_, 2, v_ngen_2151_);
lean_ctor_set(v_reuseFailAlloc_2172_, 3, v_auxDeclNGen_2152_);
lean_ctor_set(v_reuseFailAlloc_2172_, 4, v___x_2167_);
lean_ctor_set(v_reuseFailAlloc_2172_, 5, v_cache_2153_);
lean_ctor_set(v_reuseFailAlloc_2172_, 6, v_recordedDeps_2154_);
lean_ctor_set(v_reuseFailAlloc_2172_, 7, v_messages_2155_);
lean_ctor_set(v_reuseFailAlloc_2172_, 8, v_infoState_2156_);
lean_ctor_set(v_reuseFailAlloc_2172_, 9, v_snapshotTasks_2157_);
v___x_2169_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; 
v___x_2170_ = lean_st_ref_put(v___y_2142_, v___x_2169_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_traces_2146_);
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
lean_object* v_toCold_2283_; lean_object* v_currRecDepth_2284_; lean_object* v_ref_2285_; uint16_t v_optionFlags_2286_; uint8_t v_suppressElabErrors_2287_; uint8_t v_isRecordingDeps_2288_; lean_object* v_ref_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v_traceState_2292_; lean_object* v_traces_2293_; lean_object* v___x_2294_; size_t v_sz_2295_; size_t v___x_2296_; lean_object* v___x_2297_; lean_object* v_msg_2298_; lean_object* v___x_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2338_; 
v_toCold_2283_ = lean_ctor_get(v___y_2280_, 0);
v_currRecDepth_2284_ = lean_ctor_get(v___y_2280_, 1);
v_ref_2285_ = lean_ctor_get(v___y_2280_, 2);
v_optionFlags_2286_ = lean_ctor_get_uint16(v___y_2280_, sizeof(void*)*3);
v_suppressElabErrors_2287_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*3 + 2);
v_isRecordingDeps_2288_ = lean_ctor_get_uint8(v___y_2280_, sizeof(void*)*3 + 3);
v_ref_2289_ = l_Lean_replaceRef(v_ref_2278_, v_ref_2285_);
lean_inc(v_currRecDepth_2284_);
lean_inc_ref(v_toCold_2283_);
v___x_2290_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_2290_, 0, v_toCold_2283_);
lean_ctor_set(v___x_2290_, 1, v_currRecDepth_2284_);
lean_ctor_set(v___x_2290_, 2, v_ref_2289_);
lean_ctor_set_uint16(v___x_2290_, sizeof(void*)*3, v_optionFlags_2286_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*3 + 2, v_suppressElabErrors_2287_);
lean_ctor_set_uint8(v___x_2290_, sizeof(void*)*3 + 3, v_isRecordingDeps_2288_);
v___x_2291_ = lean_st_ref_get(v___y_2281_);
v_traceState_2292_ = lean_ctor_get(v___x_2291_, 4);
lean_inc_ref(v_traceState_2292_);
lean_dec(v___x_2291_);
v_traces_2293_ = lean_ctor_get(v_traceState_2292_, 0);
lean_inc_ref(v_traces_2293_);
lean_dec_ref(v_traceState_2292_);
v___x_2294_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2293_);
lean_dec_ref(v_traces_2293_);
v_sz_2295_ = lean_array_size(v___x_2294_);
v___x_2296_ = ((size_t)0ULL);
v___x_2297_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2295_, v___x_2296_, v___x_2294_);
v_msg_2298_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2298_, 0, v_data_2277_);
lean_ctor_set(v_msg_2298_, 1, v_msg_2279_);
lean_ctor_set(v_msg_2298_, 2, v___x_2297_);
v___x_2299_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2298_, v___x_2290_, v___y_2281_);
lean_dec_ref_known(v___x_2290_, 3);
v_a_2300_ = lean_ctor_get(v___x_2299_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2299_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2302_ = v___x_2299_;
v_isShared_2303_ = v_isSharedCheck_2338_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2299_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2338_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2304_; lean_object* v_traceState_2305_; lean_object* v_env_2306_; lean_object* v_nextMacroScope_2307_; lean_object* v_ngen_2308_; lean_object* v_auxDeclNGen_2309_; lean_object* v_cache_2310_; lean_object* v_recordedDeps_2311_; lean_object* v_messages_2312_; lean_object* v_infoState_2313_; lean_object* v_snapshotTasks_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2337_; 
v___x_2304_ = lean_st_ref_take(v___y_2281_);
v_traceState_2305_ = lean_ctor_get(v___x_2304_, 4);
v_env_2306_ = lean_ctor_get(v___x_2304_, 0);
v_nextMacroScope_2307_ = lean_ctor_get(v___x_2304_, 1);
v_ngen_2308_ = lean_ctor_get(v___x_2304_, 2);
v_auxDeclNGen_2309_ = lean_ctor_get(v___x_2304_, 3);
v_cache_2310_ = lean_ctor_get(v___x_2304_, 5);
v_recordedDeps_2311_ = lean_ctor_get(v___x_2304_, 6);
v_messages_2312_ = lean_ctor_get(v___x_2304_, 7);
v_infoState_2313_ = lean_ctor_get(v___x_2304_, 8);
v_snapshotTasks_2314_ = lean_ctor_get(v___x_2304_, 9);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2304_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2316_ = v___x_2304_;
v_isShared_2317_ = v_isSharedCheck_2337_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_snapshotTasks_2314_);
lean_inc(v_infoState_2313_);
lean_inc(v_messages_2312_);
lean_inc(v_recordedDeps_2311_);
lean_inc(v_cache_2310_);
lean_inc(v_traceState_2305_);
lean_inc(v_auxDeclNGen_2309_);
lean_inc(v_ngen_2308_);
lean_inc(v_nextMacroScope_2307_);
lean_inc(v_env_2306_);
lean_dec(v___x_2304_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2337_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
uint64_t v_tid_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2335_; 
v_tid_2318_ = lean_ctor_get_uint64(v_traceState_2305_, sizeof(void*)*1);
v_isSharedCheck_2335_ = !lean_is_exclusive(v_traceState_2305_);
if (v_isSharedCheck_2335_ == 0)
{
lean_object* v_unused_2336_; 
v_unused_2336_ = lean_ctor_get(v_traceState_2305_, 0);
lean_dec(v_unused_2336_);
v___x_2320_ = v_traceState_2305_;
v_isShared_2321_ = v_isSharedCheck_2335_;
goto v_resetjp_2319_;
}
else
{
lean_dec(v_traceState_2305_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2335_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2326_; 
v___x_2322_ = lean_box(0);
v___x_2323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2323_, 0, v_ref_2278_);
lean_ctor_set(v___x_2323_, 1, v_a_2300_);
v___x_2324_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2276_, v___x_2323_);
if (v_isShared_2321_ == 0)
{
lean_ctor_set(v___x_2320_, 0, v___x_2324_);
v___x_2326_ = v___x_2320_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2324_);
lean_ctor_set_uint64(v_reuseFailAlloc_2334_, sizeof(void*)*1, v_tid_2318_);
v___x_2326_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2317_ == 0)
{
lean_ctor_set(v___x_2316_, 4, v___x_2326_);
v___x_2328_ = v___x_2316_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_env_2306_);
lean_ctor_set(v_reuseFailAlloc_2333_, 1, v_nextMacroScope_2307_);
lean_ctor_set(v_reuseFailAlloc_2333_, 2, v_ngen_2308_);
lean_ctor_set(v_reuseFailAlloc_2333_, 3, v_auxDeclNGen_2309_);
lean_ctor_set(v_reuseFailAlloc_2333_, 4, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2333_, 5, v_cache_2310_);
lean_ctor_set(v_reuseFailAlloc_2333_, 6, v_recordedDeps_2311_);
lean_ctor_set(v_reuseFailAlloc_2333_, 7, v_messages_2312_);
lean_ctor_set(v_reuseFailAlloc_2333_, 8, v_infoState_2313_);
lean_ctor_set(v_reuseFailAlloc_2333_, 9, v_snapshotTasks_2314_);
v___x_2328_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2329_; lean_object* v___x_2331_; 
v___x_2329_ = lean_st_ref_put(v___y_2281_, v___x_2328_);
if (v_isShared_2303_ == 0)
{
lean_ctor_set(v___x_2302_, 0, v___x_2322_);
v___x_2331_ = v___x_2302_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2322_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2339_, lean_object* v_data_2340_, lean_object* v_ref_2341_, lean_object* v_msg_2342_, lean_object* v___y_2343_, lean_object* v___y_2344_, lean_object* v___y_2345_){
_start:
{
lean_object* v_res_2346_; 
v_res_2346_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2339_, v_data_2340_, v_ref_2341_, v_msg_2342_, v___y_2343_, v___y_2344_);
lean_dec(v___y_2344_);
lean_dec_ref(v___y_2343_);
return v_res_2346_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2347_){
_start:
{
if (lean_obj_tag(v_x_2347_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v_x_2347_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v_x_2347_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 1);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
v_a_2357_ = lean_ctor_get(v_x_2347_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v_x_2347_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v_x_2347_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v_x_2347_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
lean_ctor_set_tag(v___x_2359_, 0);
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2365_, lean_object* v___y_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2365_);
return v_res_2367_;
}
}
LEAN_EXPORT uint8_t l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2368_){
_start:
{
if (lean_obj_tag(v_e_2368_) == 0)
{
uint8_t v___x_2369_; 
v___x_2369_ = 2;
return v___x_2369_;
}
else
{
uint8_t v___x_2370_; 
v___x_2370_ = 0;
return v___x_2370_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2371_){
_start:
{
uint8_t v_res_2372_; lean_object* v_r_2373_; 
v_res_2372_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2371_);
lean_dec_ref(v_e_2371_);
v_r_2373_ = lean_box(v_res_2372_);
return v_r_2373_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2374_; double v___x_2375_; 
v___x_2374_ = lean_unsigned_to_nat(0u);
v___x_2375_ = lean_float_of_nat(v___x_2374_);
return v___x_2375_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2379_; double v___x_2380_; 
v___x_2379_ = lean_unsigned_to_nat(1000u);
v___x_2380_ = lean_float_of_nat(v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2381_, uint8_t v_collapsed_2382_, lean_object* v_tag_2383_, lean_object* v_opts_2384_, uint8_t v_clsEnabled_2385_, lean_object* v_oldTraces_2386_, lean_object* v_msg_2387_, lean_object* v_resStartStop_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v_fst_2392_; lean_object* v_snd_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v_data_2397_; lean_object* v_fst_2400_; lean_object* v_snd_2401_; lean_object* v___x_2402_; uint8_t v___x_2403_; lean_object* v___y_2405_; lean_object* v_a_2406_; uint8_t v___y_2421_; double v___y_2453_; 
v_fst_2392_ = lean_ctor_get(v_resStartStop_2388_, 0);
lean_inc(v_fst_2392_);
v_snd_2393_ = lean_ctor_get(v_resStartStop_2388_, 1);
lean_inc(v_snd_2393_);
lean_dec_ref(v_resStartStop_2388_);
v_fst_2400_ = lean_ctor_get(v_snd_2393_, 0);
lean_inc(v_fst_2400_);
v_snd_2401_ = lean_ctor_get(v_snd_2393_, 1);
lean_inc(v_snd_2401_);
lean_dec(v_snd_2393_);
v___x_2402_ = l_Lean_trace_profiler;
v___x_2403_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2384_, v___x_2402_);
if (v___x_2403_ == 0)
{
v___y_2421_ = v___x_2403_;
goto v___jp_2420_;
}
else
{
lean_object* v___x_2458_; uint8_t v___x_2459_; 
v___x_2458_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2459_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2384_, v___x_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; lean_object* v___x_2461_; double v___x_2462_; double v___x_2463_; double v___x_2464_; 
v___x_2460_ = l_Lean_trace_profiler_threshold;
v___x_2461_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2384_, v___x_2460_);
v___x_2462_ = lean_float_of_nat(v___x_2461_);
v___x_2463_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2464_ = lean_float_div(v___x_2462_, v___x_2463_);
v___y_2453_ = v___x_2464_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2466_; double v___x_2467_; 
v___x_2465_ = l_Lean_trace_profiler_threshold;
v___x_2466_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__1(v_opts_2384_, v___x_2465_);
v___x_2467_ = lean_float_of_nat(v___x_2466_);
v___y_2453_ = v___x_2467_;
goto v___jp_2452_;
}
}
v___jp_2394_:
{
lean_object* v___x_2398_; 
lean_inc(v___y_2395_);
v___x_2398_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2386_, v_data_2397_, v___y_2395_, v___y_2396_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v___x_2399_; 
lean_dec_ref_known(v___x_2398_, 1);
v___x_2399_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2392_);
return v___x_2399_;
}
else
{
lean_dec(v_fst_2392_);
return v___x_2398_;
}
}
v___jp_2404_:
{
uint8_t v_result_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; double v___x_2410_; lean_object* v_data_2411_; 
v_result_2407_ = l_Lean_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2392_);
v___x_2408_ = lean_box(v_result_2407_);
v___x_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
v___x_2410_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2383_);
lean_inc_ref(v___x_2409_);
lean_inc(v_cls_2381_);
v_data_2411_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2411_, 0, v_cls_2381_);
lean_ctor_set(v_data_2411_, 1, v___x_2409_);
lean_ctor_set(v_data_2411_, 2, v_tag_2383_);
lean_ctor_set_float(v_data_2411_, sizeof(void*)*3, v___x_2410_);
lean_ctor_set_float(v_data_2411_, sizeof(void*)*3 + 8, v___x_2410_);
lean_ctor_set_uint8(v_data_2411_, sizeof(void*)*3 + 16, v_collapsed_2382_);
if (v___x_2403_ == 0)
{
lean_dec_ref_known(v___x_2409_, 1);
lean_dec(v_snd_2401_);
lean_dec(v_fst_2400_);
lean_dec_ref(v_tag_2383_);
lean_dec(v_cls_2381_);
v___y_2395_ = v___y_2405_;
v___y_2396_ = v_a_2406_;
v_data_2397_ = v_data_2411_;
goto v___jp_2394_;
}
else
{
lean_object* v_data_2412_; double v___x_2413_; double v___x_2414_; 
lean_dec_ref_known(v_data_2411_, 3);
v_data_2412_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2412_, 0, v_cls_2381_);
lean_ctor_set(v_data_2412_, 1, v___x_2409_);
lean_ctor_set(v_data_2412_, 2, v_tag_2383_);
v___x_2413_ = lean_unbox_float(v_fst_2400_);
lean_dec(v_fst_2400_);
lean_ctor_set_float(v_data_2412_, sizeof(void*)*3, v___x_2413_);
v___x_2414_ = lean_unbox_float(v_snd_2401_);
lean_dec(v_snd_2401_);
lean_ctor_set_float(v_data_2412_, sizeof(void*)*3 + 8, v___x_2414_);
lean_ctor_set_uint8(v_data_2412_, sizeof(void*)*3 + 16, v_collapsed_2382_);
v___y_2395_ = v___y_2405_;
v___y_2396_ = v_a_2406_;
v_data_2397_ = v_data_2412_;
goto v___jp_2394_;
}
}
v___jp_2415_:
{
lean_object* v_ref_2416_; lean_object* v___x_2417_; 
v_ref_2416_ = lean_ctor_get(v___y_2389_, 2);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v_fst_2392_);
v___x_2417_ = lean_apply_4(v_msg_2387_, v_fst_2392_, v___y_2389_, v___y_2390_, lean_box(0));
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___y_2405_ = v_ref_2416_;
v_a_2406_ = v_a_2418_;
goto v___jp_2404_;
}
else
{
lean_object* v___x_2419_; 
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2405_ = v_ref_2416_;
v_a_2406_ = v___x_2419_;
goto v___jp_2404_;
}
}
v___jp_2420_:
{
if (v_clsEnabled_2385_ == 0)
{
if (v___y_2421_ == 0)
{
lean_object* v___x_2422_; lean_object* v_traceState_2423_; lean_object* v_env_2424_; lean_object* v_nextMacroScope_2425_; lean_object* v_ngen_2426_; lean_object* v_auxDeclNGen_2427_; lean_object* v_cache_2428_; lean_object* v_recordedDeps_2429_; lean_object* v_messages_2430_; lean_object* v_infoState_2431_; lean_object* v_snapshotTasks_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v_snd_2401_);
lean_dec(v_fst_2400_);
lean_dec_ref(v_msg_2387_);
lean_dec_ref(v_tag_2383_);
lean_dec(v_cls_2381_);
v___x_2422_ = lean_st_ref_take(v___y_2390_);
v_traceState_2423_ = lean_ctor_get(v___x_2422_, 4);
v_env_2424_ = lean_ctor_get(v___x_2422_, 0);
v_nextMacroScope_2425_ = lean_ctor_get(v___x_2422_, 1);
v_ngen_2426_ = lean_ctor_get(v___x_2422_, 2);
v_auxDeclNGen_2427_ = lean_ctor_get(v___x_2422_, 3);
v_cache_2428_ = lean_ctor_get(v___x_2422_, 5);
v_recordedDeps_2429_ = lean_ctor_get(v___x_2422_, 6);
v_messages_2430_ = lean_ctor_get(v___x_2422_, 7);
v_infoState_2431_ = lean_ctor_get(v___x_2422_, 8);
v_snapshotTasks_2432_ = lean_ctor_get(v___x_2422_, 9);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2422_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2434_ = v___x_2422_;
v_isShared_2435_ = v_isSharedCheck_2451_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_snapshotTasks_2432_);
lean_inc(v_infoState_2431_);
lean_inc(v_messages_2430_);
lean_inc(v_recordedDeps_2429_);
lean_inc(v_cache_2428_);
lean_inc(v_traceState_2423_);
lean_inc(v_auxDeclNGen_2427_);
lean_inc(v_ngen_2426_);
lean_inc(v_nextMacroScope_2425_);
lean_inc(v_env_2424_);
lean_dec(v___x_2422_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2451_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
uint64_t v_tid_2436_; lean_object* v_traces_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2450_; 
v_tid_2436_ = lean_ctor_get_uint64(v_traceState_2423_, sizeof(void*)*1);
v_traces_2437_ = lean_ctor_get(v_traceState_2423_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v_traceState_2423_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2439_ = v_traceState_2423_;
v_isShared_2440_ = v_isSharedCheck_2450_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_traces_2437_);
lean_dec(v_traceState_2423_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2450_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
v___x_2441_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2386_, v_traces_2437_);
lean_dec_ref(v_traces_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2441_);
lean_ctor_set_uint64(v_reuseFailAlloc_2449_, sizeof(void*)*1, v_tid_2436_);
v___x_2443_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
lean_object* v___x_2445_; 
if (v_isShared_2435_ == 0)
{
lean_ctor_set(v___x_2434_, 4, v___x_2443_);
v___x_2445_ = v___x_2434_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_env_2424_);
lean_ctor_set(v_reuseFailAlloc_2448_, 1, v_nextMacroScope_2425_);
lean_ctor_set(v_reuseFailAlloc_2448_, 2, v_ngen_2426_);
lean_ctor_set(v_reuseFailAlloc_2448_, 3, v_auxDeclNGen_2427_);
lean_ctor_set(v_reuseFailAlloc_2448_, 4, v___x_2443_);
lean_ctor_set(v_reuseFailAlloc_2448_, 5, v_cache_2428_);
lean_ctor_set(v_reuseFailAlloc_2448_, 6, v_recordedDeps_2429_);
lean_ctor_set(v_reuseFailAlloc_2448_, 7, v_messages_2430_);
lean_ctor_set(v_reuseFailAlloc_2448_, 8, v_infoState_2431_);
lean_ctor_set(v_reuseFailAlloc_2448_, 9, v_snapshotTasks_2432_);
v___x_2445_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = lean_st_ref_put(v___y_2390_, v___x_2445_);
v___x_2447_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2392_);
return v___x_2447_;
}
}
}
}
}
else
{
goto v___jp_2415_;
}
}
else
{
goto v___jp_2415_;
}
}
v___jp_2452_:
{
double v___x_2454_; double v___x_2455_; double v___x_2456_; uint8_t v___x_2457_; 
v___x_2454_ = lean_unbox_float(v_snd_2401_);
v___x_2455_ = lean_unbox_float(v_fst_2400_);
v___x_2456_ = lean_float_sub(v___x_2454_, v___x_2455_);
v___x_2457_ = lean_float_decLt(v___y_2453_, v___x_2456_);
v___y_2421_ = v___x_2457_;
goto v___jp_2420_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2468_, lean_object* v_collapsed_2469_, lean_object* v_tag_2470_, lean_object* v_opts_2471_, lean_object* v_clsEnabled_2472_, lean_object* v_oldTraces_2473_, lean_object* v_msg_2474_, lean_object* v_resStartStop_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
uint8_t v_collapsed_boxed_2479_; uint8_t v_clsEnabled_boxed_2480_; lean_object* v_res_2481_; 
v_collapsed_boxed_2479_ = lean_unbox(v_collapsed_2469_);
v_clsEnabled_boxed_2480_ = lean_unbox(v_clsEnabled_2472_);
v_res_2481_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2468_, v_collapsed_boxed_2479_, v_tag_2470_, v_opts_2471_, v_clsEnabled_boxed_2480_, v_oldTraces_2473_, v_msg_2474_, v_resStartStop_2475_, v___y_2476_, v___y_2477_);
lean_dec(v___y_2477_);
lean_dec_ref(v___y_2476_);
lean_dec_ref(v_opts_2471_);
return v_res_2481_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2484_; double v___x_2485_; 
v___x_2484_ = lean_unsigned_to_nat(1000000000u);
v___x_2485_ = lean_float_of_nat(v___x_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2486_, lean_object* v___x_2487_, uint8_t v___x_2488_, lean_object* v___x_2489_, lean_object* v___f_2490_, lean_object* v___y_2491_, lean_object* v___y_2492_){
_start:
{
lean_object* v___y_2495_; lean_object* v___y_2496_; uint8_t v___y_2497_; lean_object* v___y_2508_; lean_object* v_a_2509_; lean_object* v___y_2513_; lean_object* v___y_2514_; uint8_t v___y_2515_; lean_object* v___y_2526_; lean_object* v_a_2527_; lean_object* v_toCold_2530_; lean_object* v_options_2531_; uint8_t v_hasTrace_2532_; 
v_toCold_2530_ = lean_ctor_get(v___y_2491_, 0);
v_options_2531_ = lean_ctor_get(v_toCold_2530_, 2);
v_hasTrace_2532_ = lean_ctor_get_uint8(v_options_2531_, sizeof(void*)*1);
if (v_hasTrace_2532_ == 0)
{
lean_object* v_cancelTk_x3f_2533_; lean_object* v___x_2534_; 
lean_dec_ref(v___f_2490_);
lean_dec_ref(v___x_2489_);
lean_dec(v___x_2487_);
v_cancelTk_x3f_2533_ = lean_ctor_get(v_toCold_2530_, 10);
lean_inc(v_decl_2486_);
v___x_2534_ = l_Lean_warnIfUsesSorry(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2534_) == 0)
{
lean_object* v___x_2535_; lean_object* v_env_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2534_, 1);
v___x_2535_ = lean_st_ref_get(v___y_2492_);
v_env_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc_ref(v_env_2536_);
lean_dec(v___x_2535_);
v___x_2537_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2491_);
v___x_2538_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2536_, v___x_2537_, v_decl_2486_, v_cancelTk_x3f_2533_);
lean_dec_ref(v___x_2537_);
v___x_2539_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2538_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
lean_dec(v_decl_2486_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2541_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2540_, v___y_2492_);
return v___x_2541_;
}
else
{
lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2549_; 
v_a_2542_ = lean_ctor_get(v___x_2539_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2539_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2544_ = v___x_2539_;
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2539_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2549_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2547_; 
lean_inc(v_a_2542_);
if (v_isShared_2545_ == 0)
{
v___x_2547_ = v___x_2544_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_a_2542_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
v___y_2526_ = v___x_2547_;
v_a_2527_ = v_a_2542_;
goto v___jp_2525_;
}
}
}
}
else
{
lean_dec(v_decl_2486_);
return v___x_2534_;
}
}
else
{
lean_object* v_cancelTk_x3f_2550_; lean_object* v_inheritedTraceOptions_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v_a_2558_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v_a_2573_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v_a_2578_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v_a_2595_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v_a_2613_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v_a_2618_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v_a_2635_; 
v_cancelTk_x3f_2550_ = lean_ctor_get(v_toCold_2530_, 10);
v_inheritedTraceOptions_2551_ = lean_ctor_get(v_toCold_2530_, 11);
v___x_2552_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2487_);
v___x_2553_ = l_Lean_Name_append(v___x_2552_, v___x_2487_);
v___x_2554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2551_, v_options_2531_, v___x_2553_);
lean_dec(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2665_; uint8_t v___x_2666_; 
v___x_2665_ = l_Lean_trace_profiler;
v___x_2666_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2531_, v___x_2665_);
if (v___x_2666_ == 0)
{
lean_object* v___x_2667_; 
lean_dec_ref(v___f_2490_);
lean_dec_ref(v___x_2489_);
lean_dec(v___x_2487_);
lean_inc(v_decl_2486_);
v___x_2667_ = l_Lean_warnIfUsesSorry(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2667_) == 0)
{
lean_object* v___x_2668_; lean_object* v_env_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
lean_dec_ref_known(v___x_2667_, 1);
v___x_2668_ = lean_st_ref_get(v___y_2492_);
v_env_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc_ref(v_env_2669_);
lean_dec(v___x_2668_);
v___x_2670_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2491_);
v___x_2671_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2669_, v___x_2670_, v_decl_2486_, v_cancelTk_x3f_2550_);
lean_dec_ref(v___x_2670_);
v___x_2672_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2671_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
lean_dec(v_decl_2486_);
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2673_, v___y_2492_);
return v___x_2674_;
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
v_a_2675_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2672_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2672_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
lean_inc(v_a_2675_);
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v___y_2508_ = v___x_2680_;
v_a_2509_ = v_a_2675_;
goto v___jp_2507_;
}
}
}
}
else
{
lean_dec(v_decl_2486_);
return v___x_2667_;
}
}
else
{
goto v___jp_2638_;
}
}
else
{
goto v___jp_2638_;
}
v___jp_2555_:
{
lean_object* v___x_2559_; double v___x_2560_; double v___x_2561_; double v___x_2562_; double v___x_2563_; double v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v___x_2559_ = lean_io_mono_nanos_now();
v___x_2560_ = lean_float_of_nat(v___y_2557_);
v___x_2561_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_2562_ = lean_float_div(v___x_2560_, v___x_2561_);
v___x_2563_ = lean_float_of_nat(v___x_2559_);
v___x_2564_ = lean_float_div(v___x_2563_, v___x_2561_);
v___x_2565_ = lean_box_float(v___x_2562_);
v___x_2566_ = lean_box_float(v___x_2564_);
v___x_2567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2565_);
lean_ctor_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2568_, 0, v_a_2558_);
lean_ctor_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2487_, v___x_2488_, v___x_2489_, v_options_2531_, v___x_2554_, v___y_2556_, v___f_2490_, v___x_2568_, v___y_2491_, v___y_2492_);
return v___x_2569_;
}
v___jp_2570_:
{
lean_object* v___x_2574_; 
v___x_2574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2574_, 0, v_a_2573_);
v___y_2556_ = v___y_2571_;
v___y_2557_ = v___y_2572_;
v_a_2558_ = v___x_2574_;
goto v___jp_2555_;
}
v___jp_2575_:
{
lean_object* v___x_2579_; 
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v_a_2578_);
v___y_2556_ = v___y_2576_;
v___y_2557_ = v___y_2577_;
v_a_2558_ = v___x_2579_;
goto v___jp_2555_;
}
v___jp_2580_:
{
if (lean_obj_tag(v___y_2583_) == 0)
{
lean_object* v_a_2584_; 
v_a_2584_ = lean_ctor_get(v___y_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___y_2583_, 1);
v___y_2576_ = v___y_2581_;
v___y_2577_ = v___y_2582_;
v_a_2578_ = v_a_2584_;
goto v___jp_2575_;
}
else
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___y_2583_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___y_2583_, 1);
v___y_2571_ = v___y_2581_;
v___y_2572_ = v___y_2582_;
v_a_2573_ = v_a_2585_;
goto v___jp_2570_;
}
}
v___jp_2586_:
{
if (v___y_2590_ == 0)
{
lean_object* v___x_2591_; 
v___x_2591_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_dec_ref_known(v___x_2591_, 1);
v___y_2571_ = v___y_2588_;
v___y_2572_ = v___y_2589_;
v_a_2573_ = v___y_2587_;
goto v___jp_2570_;
}
else
{
lean_dec_ref(v___y_2587_);
v___y_2581_ = v___y_2588_;
v___y_2582_ = v___y_2589_;
v___y_2583_ = v___x_2591_;
goto v___jp_2580_;
}
}
else
{
lean_dec(v_decl_2486_);
v___y_2571_ = v___y_2588_;
v___y_2572_ = v___y_2589_;
v_a_2573_ = v___y_2587_;
goto v___jp_2570_;
}
}
v___jp_2592_:
{
uint8_t v___x_2596_; 
v___x_2596_ = l_Lean_Exception_isInterrupt(v_a_2595_);
if (v___x_2596_ == 0)
{
uint8_t v___x_2597_; 
lean_inc_ref(v_a_2595_);
v___x_2597_ = l_Lean_Exception_isRuntime(v_a_2595_);
v___y_2587_ = v_a_2595_;
v___y_2588_ = v___y_2593_;
v___y_2589_ = v___y_2594_;
v___y_2590_ = v___x_2597_;
goto v___jp_2586_;
}
else
{
v___y_2587_ = v_a_2595_;
v___y_2588_ = v___y_2593_;
v___y_2589_ = v___y_2594_;
v___y_2590_ = v___x_2596_;
goto v___jp_2586_;
}
}
v___jp_2598_:
{
lean_object* v___x_2602_; double v___x_2603_; double v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2602_ = lean_io_get_num_heartbeats();
v___x_2603_ = lean_float_of_nat(v___y_2599_);
v___x_2604_ = lean_float_of_nat(v___x_2602_);
v___x_2605_ = lean_box_float(v___x_2603_);
v___x_2606_ = lean_box_float(v___x_2604_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2601_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2487_, v___x_2488_, v___x_2489_, v_options_2531_, v___x_2554_, v___y_2600_, v___f_2490_, v___x_2608_, v___y_2491_, v___y_2492_);
return v___x_2609_;
}
v___jp_2610_:
{
lean_object* v___x_2614_; 
v___x_2614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2614_, 0, v_a_2613_);
v___y_2599_ = v___y_2611_;
v___y_2600_ = v___y_2612_;
v_a_2601_ = v___x_2614_;
goto v___jp_2598_;
}
v___jp_2615_:
{
lean_object* v___x_2619_; 
v___x_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2619_, 0, v_a_2618_);
v___y_2599_ = v___y_2616_;
v___y_2600_ = v___y_2617_;
v_a_2601_ = v___x_2619_;
goto v___jp_2598_;
}
v___jp_2620_:
{
if (lean_obj_tag(v___y_2623_) == 0)
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___y_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___y_2623_, 1);
v___y_2616_ = v___y_2621_;
v___y_2617_ = v___y_2622_;
v_a_2618_ = v_a_2624_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2625_; 
v_a_2625_ = lean_ctor_get(v___y_2623_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___y_2623_, 1);
v___y_2611_ = v___y_2621_;
v___y_2612_ = v___y_2622_;
v_a_2613_ = v_a_2625_;
goto v___jp_2610_;
}
}
v___jp_2626_:
{
if (v___y_2630_ == 0)
{
lean_object* v___x_2631_; 
v___x_2631_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref_known(v___x_2631_, 1);
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2628_;
v_a_2613_ = v___y_2629_;
goto v___jp_2610_;
}
else
{
lean_dec_ref(v___y_2629_);
v___y_2621_ = v___y_2627_;
v___y_2622_ = v___y_2628_;
v___y_2623_ = v___x_2631_;
goto v___jp_2620_;
}
}
else
{
lean_dec(v_decl_2486_);
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2628_;
v_a_2613_ = v___y_2629_;
goto v___jp_2610_;
}
}
v___jp_2632_:
{
uint8_t v___x_2636_; 
v___x_2636_ = l_Lean_Exception_isInterrupt(v_a_2635_);
if (v___x_2636_ == 0)
{
uint8_t v___x_2637_; 
lean_inc_ref(v_a_2635_);
v___x_2637_ = l_Lean_Exception_isRuntime(v_a_2635_);
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2634_;
v___y_2629_ = v_a_2635_;
v___y_2630_ = v___x_2637_;
goto v___jp_2626_;
}
else
{
v___y_2627_ = v___y_2633_;
v___y_2628_ = v___y_2634_;
v___y_2629_ = v_a_2635_;
v___y_2630_ = v___x_2636_;
goto v___jp_2626_;
}
}
v___jp_2638_:
{
lean_object* v___x_2639_; lean_object* v_a_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2492_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2642_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2531_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2486_);
v___x_2644_ = l_Lean_warnIfUsesSorry(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; lean_object* v_env_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = lean_st_ref_get(v___y_2492_);
v_env_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_ref(v_env_2646_);
lean_dec(v___x_2645_);
v___x_2647_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2491_);
v___x_2648_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2646_, v___x_2647_, v_decl_2486_, v_cancelTk_x3f_2550_);
lean_dec_ref(v___x_2647_);
v___x_2649_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2648_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2649_) == 0)
{
lean_object* v_a_2650_; lean_object* v___x_2651_; lean_object* v_a_2652_; 
lean_dec(v_decl_2486_);
v_a_2650_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2650_);
lean_dec_ref_known(v___x_2649_, 1);
v___x_2651_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2650_, v___y_2492_);
v_a_2652_ = lean_ctor_get(v___x_2651_, 0);
lean_inc(v_a_2652_);
lean_dec_ref(v___x_2651_);
v___y_2576_ = v_a_2640_;
v___y_2577_ = v___x_2643_;
v_a_2578_ = v_a_2652_;
goto v___jp_2575_;
}
else
{
lean_object* v_a_2653_; 
v_a_2653_ = lean_ctor_get(v___x_2649_, 0);
lean_inc(v_a_2653_);
lean_dec_ref_known(v___x_2649_, 1);
v___y_2593_ = v_a_2640_;
v___y_2594_ = v___x_2643_;
v_a_2595_ = v_a_2653_;
goto v___jp_2592_;
}
}
else
{
lean_dec(v_decl_2486_);
v___y_2581_ = v_a_2640_;
v___y_2582_ = v___x_2643_;
v___y_2583_ = v___x_2644_;
goto v___jp_2580_;
}
}
else
{
lean_object* v___x_2654_; lean_object* v___x_2655_; 
v___x_2654_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2486_);
v___x_2655_ = l_Lean_warnIfUsesSorry(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v___x_2656_; lean_object* v_env_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
lean_dec_ref_known(v___x_2655_, 1);
v___x_2656_ = lean_st_ref_get(v___y_2492_);
v_env_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_ref(v_env_2657_);
lean_dec(v___x_2656_);
v___x_2658_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2491_);
v___x_2659_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2657_, v___x_2658_, v_decl_2486_, v_cancelTk_x3f_2550_);
lean_dec_ref(v___x_2658_);
v___x_2660_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2659_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; lean_object* v_a_2663_; 
lean_dec(v_decl_2486_);
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref_known(v___x_2660_, 1);
v___x_2662_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2661_, v___y_2492_);
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
lean_dec_ref(v___x_2662_);
v___y_2616_ = v___x_2654_;
v___y_2617_ = v_a_2640_;
v_a_2618_ = v_a_2663_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2664_; 
v_a_2664_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v___x_2660_, 1);
v___y_2633_ = v___x_2654_;
v___y_2634_ = v_a_2640_;
v_a_2635_ = v_a_2664_;
goto v___jp_2632_;
}
}
else
{
lean_dec(v_decl_2486_);
v___y_2621_ = v___x_2654_;
v___y_2622_ = v_a_2640_;
v___y_2623_ = v___x_2655_;
goto v___jp_2620_;
}
}
}
}
v___jp_2494_:
{
if (v___y_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v___y_2495_);
v___x_2498_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2505_ == 0)
{
lean_object* v_unused_2506_; 
v_unused_2506_ = lean_ctor_get(v___x_2498_, 0);
lean_dec(v_unused_2506_);
v___x_2500_ = v___x_2498_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_dec(v___x_2498_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
lean_ctor_set_tag(v___x_2500_, 1);
lean_ctor_set(v___x_2500_, 0, v___y_2496_);
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v___y_2496_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
else
{
lean_dec_ref(v___y_2496_);
return v___x_2498_;
}
}
else
{
lean_dec_ref(v___y_2496_);
lean_dec(v_decl_2486_);
return v___y_2495_;
}
}
v___jp_2507_:
{
uint8_t v___x_2510_; 
v___x_2510_ = l_Lean_Exception_isInterrupt(v_a_2509_);
if (v___x_2510_ == 0)
{
uint8_t v___x_2511_; 
lean_inc_ref(v_a_2509_);
v___x_2511_ = l_Lean_Exception_isRuntime(v_a_2509_);
v___y_2495_ = v___y_2508_;
v___y_2496_ = v_a_2509_;
v___y_2497_ = v___x_2511_;
goto v___jp_2494_;
}
else
{
v___y_2495_ = v___y_2508_;
v___y_2496_ = v_a_2509_;
v___y_2497_ = v___x_2510_;
goto v___jp_2494_;
}
}
v___jp_2512_:
{
if (v___y_2515_ == 0)
{
lean_object* v___x_2516_; 
lean_dec_ref(v___y_2514_);
v___x_2516_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2486_, v___y_2491_, v___y_2492_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2523_ == 0)
{
lean_object* v_unused_2524_; 
v_unused_2524_ = lean_ctor_get(v___x_2516_, 0);
lean_dec(v_unused_2524_);
v___x_2518_ = v___x_2516_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_dec(v___x_2516_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
lean_ctor_set_tag(v___x_2518_, 1);
lean_ctor_set(v___x_2518_, 0, v___y_2513_);
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___y_2513_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
else
{
lean_dec_ref(v___y_2513_);
return v___x_2516_;
}
}
else
{
lean_dec_ref(v___y_2513_);
lean_dec(v_decl_2486_);
return v___y_2514_;
}
}
v___jp_2525_:
{
uint8_t v___x_2528_; 
v___x_2528_ = l_Lean_Exception_isInterrupt(v_a_2527_);
if (v___x_2528_ == 0)
{
uint8_t v___x_2529_; 
lean_inc_ref(v_a_2527_);
v___x_2529_ = l_Lean_Exception_isRuntime(v_a_2527_);
v___y_2513_ = v_a_2527_;
v___y_2514_ = v___y_2526_;
v___y_2515_ = v___x_2529_;
goto v___jp_2512_;
}
else
{
v___y_2513_ = v_a_2527_;
v___y_2514_ = v___y_2526_;
v___y_2515_ = v___x_2528_;
goto v___jp_2512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2683_, lean_object* v___x_2684_, lean_object* v___x_2685_, lean_object* v___x_2686_, lean_object* v___f_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
uint8_t v___x_7949__boxed_2691_; lean_object* v_res_2692_; 
v___x_7949__boxed_2691_ = lean_unbox(v___x_2685_);
v_res_2692_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2683_, v___x_2684_, v___x_7949__boxed_2691_, v___x_2686_, v___f_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___f_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; uint8_t v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___f_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
lean_inc(v_decl_2697_);
v___f_2701_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2701_, 0, v_decl_2697_);
v___x_2702_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v_a_2698_);
v___x_2703_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2704_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2705_ = 1;
v___x_2706_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2707_ = lean_box(v___x_2705_);
v___f_2708_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2708_, 0, v_decl_2697_);
lean_closure_set(v___f_2708_, 1, v___x_2704_);
lean_closure_set(v___f_2708_, 2, v___x_2707_);
lean_closure_set(v___f_2708_, 3, v___x_2706_);
lean_closure_set(v___f_2708_, 4, v___f_2701_);
v___x_2709_ = lean_box(0);
v___x_2710_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2703_, v___x_2702_, v___f_2708_, v___x_2709_, v_a_2698_, v_a_2699_);
lean_dec_ref(v___x_2702_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2711_, v_a_2712_, v_a_2713_);
lean_dec(v_a_2713_);
lean_dec_ref(v_a_2712_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_){
_start:
{
lean_object* v___x_2721_; 
v___x_2721_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2717_);
return v___x_2721_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2722_, lean_object* v_x_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2722_, v_x_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2728_, lean_object* v_a_2729_, lean_object* v_ref_2730_, lean_object* v_a_x3f_2731_){
_start:
{
lean_object* v___x_2733_; lean_object* v_env_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_st_ref_get(v___y_2728_);
v_env_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc_ref(v_env_2734_);
lean_dec(v___x_2733_);
v___x_2735_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2729_, v_env_2734_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2743_; 
lean_dec(v_ref_2730_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2743_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2743_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2743_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2741_; 
if (v_isShared_2739_ == 0)
{
v___x_2741_ = v___x_2738_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2742_; 
v_reuseFailAlloc_2742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_a_2736_);
v___x_2741_ = v_reuseFailAlloc_2742_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
return v___x_2741_;
}
}
}
else
{
lean_object* v_a_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2755_; 
v_a_2744_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2755_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2755_ == 0)
{
v___x_2746_ = v___x_2735_;
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
else
{
lean_inc(v_a_2744_);
lean_dec(v___x_2735_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2755_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2753_; 
v___x_2748_ = lean_io_error_to_string(v_a_2744_);
v___x_2749_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2749_, 0, v___x_2748_);
v___x_2750_ = l_Lean_MessageData_ofFormat(v___x_2749_);
v___x_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2751_, 0, v_ref_2730_);
lean_ctor_set(v___x_2751_, 1, v___x_2750_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 0, v___x_2751_);
v___x_2753_ = v___x_2746_;
goto v_reusejp_2752_;
}
else
{
lean_object* v_reuseFailAlloc_2754_; 
v_reuseFailAlloc_2754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2754_, 0, v___x_2751_);
v___x_2753_ = v_reuseFailAlloc_2754_;
goto v_reusejp_2752_;
}
v_reusejp_2752_:
{
return v___x_2753_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2756_, lean_object* v_a_2757_, lean_object* v_ref_2758_, lean_object* v_a_x3f_2759_, lean_object* v___y_2760_){
_start:
{
lean_object* v_res_2761_; 
v_res_2761_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2756_, v_a_2757_, v_ref_2758_, v_a_x3f_2759_);
lean_dec(v_a_x3f_2759_);
lean_dec(v___y_2756_);
return v_res_2761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v_a_2764_, lean_object* v_a_x3f_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v_env_2768_; lean_object* v_ref_2769_; lean_object* v___x_2770_; 
v___x_2767_ = lean_st_ref_get(v___y_2762_);
v_env_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc_ref(v_env_2768_);
lean_dec(v___x_2767_);
v_ref_2769_ = lean_ctor_get(v___y_2763_, 2);
v___x_2770_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2764_, v_env_2768_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
else
{
lean_object* v_a_2779_; lean_object* v___x_2781_; uint8_t v_isShared_2782_; uint8_t v_isSharedCheck_2790_; 
v_a_2779_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2781_ = v___x_2770_;
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
else
{
lean_inc(v_a_2779_);
lean_dec(v___x_2770_);
v___x_2781_ = lean_box(0);
v_isShared_2782_ = v_isSharedCheck_2790_;
goto v_resetjp_2780_;
}
v_resetjp_2780_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2783_ = lean_io_error_to_string(v_a_2779_);
v___x_2784_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v___x_2785_ = l_Lean_MessageData_ofFormat(v___x_2784_);
lean_inc(v_ref_2769_);
v___x_2786_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2786_, 0, v_ref_2769_);
lean_ctor_set(v___x_2786_, 1, v___x_2785_);
if (v_isShared_2782_ == 0)
{
lean_ctor_set(v___x_2781_, 0, v___x_2786_);
v___x_2788_ = v___x_2781_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v___x_2786_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v_a_2793_, lean_object* v_a_x3f_2794_, lean_object* v___y_2795_){
_start:
{
lean_object* v_res_2796_; 
v_res_2796_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2791_, v___y_2792_, v_a_2793_, v_a_x3f_2794_);
lean_dec(v_a_x3f_2794_);
lean_dec_ref(v___y_2792_);
lean_dec(v___y_2791_);
return v_res_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_a_2797_, lean_object* v_asyncEnv_2798_, lean_object* v_decl_2799_, lean_object* v_x_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_){
_start:
{
lean_object* v___x_2804_; lean_object* v_r_2805_; 
v___x_2804_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2798_, v___y_2802_);
lean_dec_ref(v___x_2804_);
v_r_2805_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2799_, v___y_2801_, v___y_2802_);
if (lean_obj_tag(v_r_2805_) == 0)
{
lean_object* v_a_2806_; lean_object* v___x_2808_; uint8_t v_isShared_2809_; uint8_t v_isSharedCheck_2822_; 
v_a_2806_ = lean_ctor_get(v_r_2805_, 0);
v_isSharedCheck_2822_ = !lean_is_exclusive(v_r_2805_);
if (v_isSharedCheck_2822_ == 0)
{
v___x_2808_ = v_r_2805_;
v_isShared_2809_ = v_isSharedCheck_2822_;
goto v_resetjp_2807_;
}
else
{
lean_inc(v_a_2806_);
lean_dec(v_r_2805_);
v___x_2808_ = lean_box(0);
v_isShared_2809_ = v_isSharedCheck_2822_;
goto v_resetjp_2807_;
}
v_resetjp_2807_:
{
lean_object* v___x_2811_; 
lean_inc(v_a_2806_);
if (v_isShared_2809_ == 0)
{
lean_ctor_set_tag(v___x_2808_, 1);
v___x_2811_ = v___x_2808_;
goto v_reusejp_2810_;
}
else
{
lean_object* v_reuseFailAlloc_2821_; 
v_reuseFailAlloc_2821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_a_2806_);
v___x_2811_ = v_reuseFailAlloc_2821_;
goto v_reusejp_2810_;
}
v_reusejp_2810_:
{
lean_object* v___x_2812_; 
v___x_2812_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2802_, v___y_2801_, v_a_2797_, v___x_2811_);
lean_dec_ref(v___x_2811_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; 
v_unused_2820_ = lean_ctor_get(v___x_2812_, 0);
lean_dec(v_unused_2820_);
v___x_2814_ = v___x_2812_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v___x_2812_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 0, v_a_2806_);
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2806_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
else
{
lean_dec(v_a_2806_);
return v___x_2812_;
}
}
}
}
else
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; 
v_a_2823_ = lean_ctor_get(v_r_2805_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v_r_2805_, 1);
v___x_2824_ = lean_box(0);
v___x_2825_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v___y_2802_, v___y_2801_, v_a_2797_, v___x_2824_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2832_; 
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2825_, 0);
lean_dec(v_unused_2833_);
v___x_2827_ = v___x_2825_;
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v___x_2825_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2832_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2830_; 
if (v_isShared_2828_ == 0)
{
lean_ctor_set_tag(v___x_2827_, 1);
lean_ctor_set(v___x_2827_, 0, v_a_2823_);
v___x_2830_ = v___x_2827_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v_a_2823_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_dec(v_a_2823_);
return v___x_2825_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_a_2834_, lean_object* v_asyncEnv_2835_, lean_object* v_decl_2836_, lean_object* v_x_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_a_2834_, v_asyncEnv_2835_, v_decl_2836_, v_x_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec_ref(v_x_2837_);
return v_res_2841_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2844_ = l_Lean_stringToMessageData(v___x_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2845_, lean_object* v_x_2846_, lean_object* v___y_2847_, lean_object* v___y_2848_){
_start:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; 
v___x_2850_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2851_ = l_Lean_Declaration_getNames(v_decl_2845_);
v___x_2852_ = lean_box(0);
v___x_2853_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2851_, v___x_2852_);
v___x_2854_ = l_Lean_MessageData_ofList(v___x_2853_);
v___x_2855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2855_, 0, v___x_2850_);
lean_ctor_set(v___x_2855_, 1, v___x_2854_);
v___x_2856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2857_, lean_object* v_x_2858_, lean_object* v___y_2859_, lean_object* v___y_2860_, lean_object* v___y_2861_){
_start:
{
lean_object* v_res_2862_; 
v_res_2862_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2857_, v_x_2858_, v___y_2859_, v___y_2860_);
lean_dec(v___y_2860_);
lean_dec_ref(v___y_2859_);
lean_dec_ref(v_x_2858_);
return v_res_2862_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2865_, lean_object* v_msg_2866_, lean_object* v___y_2867_, lean_object* v___y_2868_){
_start:
{
lean_object* v_ref_2870_; lean_object* v___x_2871_; lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2917_; 
v_ref_2870_ = lean_ctor_get(v___y_2867_, 2);
v___x_2871_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2866_, v___y_2867_, v___y_2868_);
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2874_ = v___x_2871_;
v_isShared_2875_ = v_isSharedCheck_2917_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2871_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2917_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v_traceState_2877_; lean_object* v_env_2878_; lean_object* v_nextMacroScope_2879_; lean_object* v_ngen_2880_; lean_object* v_auxDeclNGen_2881_; lean_object* v_cache_2882_; lean_object* v_recordedDeps_2883_; lean_object* v_messages_2884_; lean_object* v_infoState_2885_; lean_object* v_snapshotTasks_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2916_; 
v___x_2876_ = lean_st_ref_take(v___y_2868_);
v_traceState_2877_ = lean_ctor_get(v___x_2876_, 4);
v_env_2878_ = lean_ctor_get(v___x_2876_, 0);
v_nextMacroScope_2879_ = lean_ctor_get(v___x_2876_, 1);
v_ngen_2880_ = lean_ctor_get(v___x_2876_, 2);
v_auxDeclNGen_2881_ = lean_ctor_get(v___x_2876_, 3);
v_cache_2882_ = lean_ctor_get(v___x_2876_, 5);
v_recordedDeps_2883_ = lean_ctor_get(v___x_2876_, 6);
v_messages_2884_ = lean_ctor_get(v___x_2876_, 7);
v_infoState_2885_ = lean_ctor_get(v___x_2876_, 8);
v_snapshotTasks_2886_ = lean_ctor_get(v___x_2876_, 9);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2888_ = v___x_2876_;
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_snapshotTasks_2886_);
lean_inc(v_infoState_2885_);
lean_inc(v_messages_2884_);
lean_inc(v_recordedDeps_2883_);
lean_inc(v_cache_2882_);
lean_inc(v_traceState_2877_);
lean_inc(v_auxDeclNGen_2881_);
lean_inc(v_ngen_2880_);
lean_inc(v_nextMacroScope_2879_);
lean_inc(v_env_2878_);
lean_dec(v___x_2876_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2916_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
uint64_t v_tid_2890_; lean_object* v_traces_2891_; lean_object* v___x_2893_; uint8_t v_isShared_2894_; uint8_t v_isSharedCheck_2915_; 
v_tid_2890_ = lean_ctor_get_uint64(v_traceState_2877_, sizeof(void*)*1);
v_traces_2891_ = lean_ctor_get(v_traceState_2877_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v_traceState_2877_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2893_ = v_traceState_2877_;
v_isShared_2894_ = v_isSharedCheck_2915_;
goto v_resetjp_2892_;
}
else
{
lean_inc(v_traces_2891_);
lean_dec(v_traceState_2877_);
v___x_2893_ = lean_box(0);
v_isShared_2894_ = v_isSharedCheck_2915_;
goto v_resetjp_2892_;
}
v_resetjp_2892_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; double v___x_2897_; uint8_t v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2906_; 
v___x_2895_ = lean_box(0);
v___x_2896_ = lean_box(0);
v___x_2897_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2898_ = 0;
v___x_2899_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2900_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2900_, 0, v_cls_2865_);
lean_ctor_set(v___x_2900_, 1, v___x_2896_);
lean_ctor_set(v___x_2900_, 2, v___x_2899_);
lean_ctor_set_float(v___x_2900_, sizeof(void*)*3, v___x_2897_);
lean_ctor_set_float(v___x_2900_, sizeof(void*)*3 + 8, v___x_2897_);
lean_ctor_set_uint8(v___x_2900_, sizeof(void*)*3 + 16, v___x_2898_);
v___x_2901_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2902_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v_a_2872_);
lean_ctor_set(v___x_2902_, 2, v___x_2901_);
lean_inc(v_ref_2870_);
v___x_2903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2903_, 0, v_ref_2870_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
v___x_2904_ = l_Lean_PersistentArray_push___redArg(v_traces_2891_, v___x_2903_);
if (v_isShared_2894_ == 0)
{
lean_ctor_set(v___x_2893_, 0, v___x_2904_);
v___x_2906_ = v___x_2893_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v___x_2904_);
lean_ctor_set_uint64(v_reuseFailAlloc_2914_, sizeof(void*)*1, v_tid_2890_);
v___x_2906_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
lean_object* v___x_2908_; 
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 4, v___x_2906_);
v___x_2908_ = v___x_2888_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_env_2878_);
lean_ctor_set(v_reuseFailAlloc_2913_, 1, v_nextMacroScope_2879_);
lean_ctor_set(v_reuseFailAlloc_2913_, 2, v_ngen_2880_);
lean_ctor_set(v_reuseFailAlloc_2913_, 3, v_auxDeclNGen_2881_);
lean_ctor_set(v_reuseFailAlloc_2913_, 4, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2913_, 5, v_cache_2882_);
lean_ctor_set(v_reuseFailAlloc_2913_, 6, v_recordedDeps_2883_);
lean_ctor_set(v_reuseFailAlloc_2913_, 7, v_messages_2884_);
lean_ctor_set(v_reuseFailAlloc_2913_, 8, v_infoState_2885_);
lean_ctor_set(v_reuseFailAlloc_2913_, 9, v_snapshotTasks_2886_);
v___x_2908_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
lean_object* v___x_2909_; lean_object* v___x_2911_; 
v___x_2909_ = lean_st_ref_put(v___y_2868_, v___x_2908_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2895_);
v___x_2911_ = v___x_2874_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v___x_2895_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2918_, lean_object* v_msg_2919_, lean_object* v___y_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2918_, v_msg_2919_, v___y_2920_, v___y_2921_);
lean_dec(v___y_2921_);
lean_dec_ref(v___y_2920_);
return v_res_2923_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2925_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_2926_ = l_Lean_stringToMessageData(v___x_2925_);
return v___x_2926_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v_decl_2927_, lean_object* v_cls_2928_, lean_object* v_x_2929_, lean_object* v___y_2930_, lean_object* v___y_2931_){
_start:
{
lean_object* v_toCold_2933_; lean_object* v_options_2934_; uint8_t v_hasTrace_2935_; 
v_toCold_2933_ = lean_ctor_get(v___y_2930_, 0);
v_options_2934_ = lean_ctor_get(v_toCold_2933_, 2);
v_hasTrace_2935_ = lean_ctor_get_uint8(v_options_2934_, sizeof(void*)*1);
if (v_hasTrace_2935_ == 0)
{
lean_object* v___x_2936_; 
lean_dec(v_cls_2928_);
v___x_2936_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2927_, v___y_2930_, v___y_2931_);
return v___x_2936_;
}
else
{
lean_object* v_inheritedTraceOptions_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_inheritedTraceOptions_2937_ = lean_ctor_get(v_toCold_2933_, 11);
v___x_2938_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2928_);
v___x_2939_ = l_Lean_Name_append(v___x_2938_, v_cls_2928_);
v___x_2940_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2937_, v_options_2934_, v___x_2939_);
lean_dec(v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; 
lean_dec(v_cls_2928_);
v___x_2941_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2927_, v___y_2930_, v___y_2931_);
return v___x_2941_;
}
else
{
lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2942_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_2943_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2928_, v___x_2942_, v___y_2930_, v___y_2931_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2944_; 
lean_dec_ref_known(v___x_2943_, 1);
v___x_2944_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2927_, v___y_2930_, v___y_2931_);
return v___x_2944_;
}
else
{
lean_dec(v_decl_2927_);
return v___x_2943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v_decl_2945_, lean_object* v_cls_2946_, lean_object* v_x_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_2945_, v_cls_2946_, v_x_2947_, v___y_2948_, v___y_2949_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
lean_dec(v_x_2947_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2952_, lean_object* v___y_2953_){
_start:
{
lean_object* v___x_2955_; uint8_t v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v___x_2955_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2953_);
v___x_2956_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_2955_, v_opt_2952_);
lean_dec_ref(v___x_2955_);
v___x_2957_ = lean_box(v___x_2956_);
v___x_2958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2958_, 0, v___x_2957_);
return v___x_2958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2959_, lean_object* v___y_2960_, lean_object* v___y_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2959_, v___y_2960_);
lean_dec_ref(v___y_2960_);
lean_dec_ref(v_opt_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2963_){
_start:
{
if (lean_obj_tag(v_x_2963_) == 0)
{
uint8_t v___x_2964_; 
v___x_2964_ = 1;
return v___x_2964_;
}
else
{
lean_object* v_head_2965_; lean_object* v_tail_2966_; uint8_t v___x_2967_; 
v_head_2965_ = lean_ctor_get(v_x_2963_, 0);
v_tail_2966_ = lean_ctor_get(v_x_2963_, 1);
v___x_2967_ = l_Lean_isPrivateName(v_head_2965_);
if (v___x_2967_ == 0)
{
return v___x_2967_;
}
else
{
v_x_2963_ = v_tail_2966_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2969_){
_start:
{
uint8_t v_res_2970_; lean_object* v_r_2971_; 
v_res_2970_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2969_);
lean_dec(v_x_2969_);
v_r_2971_ = lean_box(v_res_2970_);
return v_r_2971_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3(void){
_start:
{
lean_object* v___x_2977_; lean_object* v___x_2978_; 
v___x_2977_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__2));
v___x_2978_ = l_Lean_stringToMessageData(v___x_2977_);
return v___x_2978_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5(void){
_start:
{
lean_object* v___x_2980_; lean_object* v___x_2981_; 
v___x_2980_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__4));
v___x_2981_ = l_Lean_stringToMessageData(v___x_2980_);
return v___x_2981_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7(void){
_start:
{
lean_object* v___x_2983_; lean_object* v___x_2984_; 
v___x_2983_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__6));
v___x_2984_ = l_Lean_stringToMessageData(v___x_2983_);
return v___x_2984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_decl_2985_, uint8_t v_hasTrace_2986_, uint8_t v___x_2987_, lean_object* v___x_2988_, lean_object* v_cls_2989_, lean_object* v___x_2990_, lean_object* v_____x_2991_, lean_object* v_exportedInfo_x3f_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_){
_start:
{
lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v_a_2999_; lean_object* v___y_3010_; lean_object* v___y_3011_; lean_object* v_a_3012_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___y_3028_; lean_object* v___y_3029_; lean_object* v___y_3030_; lean_object* v___y_3031_; lean_object* v___y_3032_; lean_object* v___y_3033_; lean_object* v_snd_3095_; lean_object* v_fst_3096_; lean_object* v___x_3098_; uint8_t v_isShared_3099_; uint8_t v_isSharedCheck_3225_; 
v_snd_3095_ = lean_ctor_get(v_____x_2991_, 1);
v_fst_3096_ = lean_ctor_get(v_____x_2991_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v_____x_2991_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3098_ = v_____x_2991_;
v_isShared_3099_ = v_isSharedCheck_3225_;
goto v_resetjp_3097_;
}
else
{
lean_inc(v_snd_3095_);
lean_inc(v_fst_3096_);
lean_dec(v_____x_2991_);
v___x_3098_ = lean_box(0);
v_isShared_3099_ = v_isSharedCheck_3225_;
goto v_resetjp_3097_;
}
v___jp_2996_:
{
lean_object* v___x_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
v___x_3000_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2997_, v___y_2998_);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3007_ == 0)
{
lean_object* v_unused_3008_; 
v_unused_3008_ = lean_ctor_get(v___x_3000_, 0);
lean_dec(v_unused_3008_);
v___x_3002_ = v___x_3000_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_dec(v___x_3000_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
lean_ctor_set_tag(v___x_3002_, 1);
lean_ctor_set(v___x_3002_, 0, v_a_2999_);
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_2999_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
v___jp_3009_:
{
lean_object* v___x_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
v___x_3013_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3010_, v___y_3011_);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3020_ == 0)
{
lean_object* v_unused_3021_; 
v_unused_3021_ = lean_ctor_get(v___x_3013_, 0);
lean_dec(v_unused_3021_);
v___x_3015_ = v___x_3013_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_dec(v___x_3013_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
lean_ctor_set(v___x_3015_, 0, v_a_3012_);
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3012_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
v___jp_3022_:
{
lean_object* v___x_3034_; 
lean_inc_ref(v___y_3029_);
v___x_3034_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3030_, v___y_3029_, v___y_3028_, v___y_3033_);
if (lean_obj_tag(v___x_3034_) == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref_known(v___x_3034_, 1);
lean_dec(v___y_3027_);
lean_inc_ref(v___y_3031_);
v___x_3035_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3031_, v___y_3032_);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3035_);
if (v_isSharedCheck_3081_ == 0)
{
lean_object* v_unused_3082_; 
v_unused_3082_ = lean_ctor_get(v___x_3035_, 0);
lean_dec(v_unused_3082_);
v___x_3037_ = v___x_3035_;
v_isShared_3038_ = v_isSharedCheck_3081_;
goto v_resetjp_3036_;
}
else
{
lean_dec(v___x_3035_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3081_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; uint8_t v___x_3041_; 
v___x_3039_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3025_);
v___x_3040_ = l_Lean_Elab_async;
v___x_3041_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3039_, v___x_3040_);
lean_dec_ref(v___x_3039_);
if (v___x_3041_ == 0)
{
lean_object* v___x_3042_; lean_object* v_r_3043_; 
lean_del_object(v___x_3037_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3023_);
v___x_3042_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3029_, v___y_3032_);
lean_dec_ref(v___x_3042_);
v_r_3043_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2985_, v___y_3025_, v___y_3032_);
if (lean_obj_tag(v_r_3043_) == 0)
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3053_; 
v_a_3044_ = lean_ctor_get(v_r_3043_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v_r_3043_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3046_ = v_r_3043_;
v_isShared_3047_ = v_isSharedCheck_3053_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v_r_3043_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3053_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
lean_inc(v_a_3044_);
if (v_isShared_3047_ == 0)
{
lean_ctor_set_tag(v___x_3046_, 1);
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_apply_2(v___y_3024_, v___x_3049_, lean_box(0));
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_dec_ref_known(v___x_3050_, 1);
v___y_3010_ = v___y_3031_;
v___y_3011_ = v___y_3032_;
v_a_3012_ = v_a_3044_;
goto v___jp_3009_;
}
else
{
lean_object* v_a_3051_; 
lean_dec(v_a_3044_);
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref_known(v___x_3050_, 1);
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v_a_2999_ = v_a_3051_;
goto v___jp_2996_;
}
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
v_a_3054_ = lean_ctor_get(v_r_3043_, 0);
lean_inc(v_a_3054_);
lean_dec_ref_known(v_r_3043_, 1);
v___x_3055_ = lean_box(0);
v___x_3056_ = lean_apply_2(v___y_3024_, v___x_3055_, lean_box(0));
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_dec_ref_known(v___x_3056_, 1);
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v_a_2999_ = v_a_3054_;
goto v___jp_2996_;
}
else
{
lean_object* v_a_3057_; 
lean_dec(v_a_3054_);
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
v___y_2997_ = v___y_3031_;
v___y_2998_ = v___y_3032_;
v_a_2999_ = v_a_3057_;
goto v___jp_2996_;
}
}
}
else
{
lean_object* v___x_3058_; lean_object* v___x_3060_; 
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3024_);
lean_dec(v_decl_2985_);
v___x_3058_ = l_IO_CancelToken_new();
if (v_isShared_3038_ == 0)
{
lean_ctor_set_tag(v___x_3037_, 1);
lean_ctor_set(v___x_3037_, 0, v___x_3058_);
v___x_3060_ = v___x_3037_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3058_);
v___x_3060_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; 
v___x_3061_ = lean_unsigned_to_nat(0u);
v___x_3062_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3063_ = l_Lean_Name_toString(v___x_3062_, v_hasTrace_2986_);
lean_inc_ref(v___x_3060_);
v___x_3064_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3023_, v___x_3060_, v___x_3063_, v___y_3025_, v___y_3032_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v_checked_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v_checked_3066_ = lean_ctor_get(v___y_3026_, 2);
lean_inc_ref(v_checked_3066_);
lean_dec_ref(v___y_3026_);
v___x_3067_ = lean_io_map_task(v_a_3065_, v_checked_3066_, v___x_3061_, v___x_2987_);
v___x_3068_ = lean_box(0);
v___x_3069_ = lean_box(2);
v___x_3070_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3070_, 0, v___x_3068_);
lean_ctor_set(v___x_3070_, 1, v___x_3069_);
lean_ctor_set(v___x_3070_, 2, v___x_3060_);
lean_ctor_set(v___x_3070_, 3, v___x_3067_);
v___x_3071_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3070_, v___y_3032_);
return v___x_3071_;
}
else
{
lean_object* v_a_3072_; lean_object* v___x_3074_; uint8_t v_isShared_3075_; uint8_t v_isSharedCheck_3079_; 
lean_dec_ref(v___x_3060_);
lean_dec_ref(v___y_3026_);
v_a_3072_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3074_ = v___x_3064_;
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
else
{
lean_inc(v_a_3072_);
lean_dec(v___x_3064_);
v___x_3074_ = lean_box(0);
v_isShared_3075_ = v_isSharedCheck_3079_;
goto v_resetjp_3073_;
}
v_resetjp_3073_:
{
lean_object* v___x_3077_; 
if (v_isShared_3075_ == 0)
{
v___x_3077_ = v___x_3074_;
goto v_reusejp_3076_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v_a_3072_);
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
}
}
}
else
{
lean_object* v_a_3083_; lean_object* v___x_3085_; uint8_t v_isShared_3086_; uint8_t v_isSharedCheck_3094_; 
lean_dec_ref(v___y_3031_);
lean_dec_ref(v___y_3029_);
lean_dec_ref(v___y_3026_);
lean_dec_ref(v___y_3024_);
lean_dec_ref(v___y_3023_);
lean_dec(v_decl_2985_);
v_a_3083_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3085_ = v___x_3034_;
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
else
{
lean_inc(v_a_3083_);
lean_dec(v___x_3034_);
v___x_3085_ = lean_box(0);
v_isShared_3086_ = v_isSharedCheck_3094_;
goto v_resetjp_3084_;
}
v_resetjp_3084_:
{
lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3092_; 
v___x_3087_ = lean_io_error_to_string(v_a_3083_);
v___x_3088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = l_Lean_MessageData_ofFormat(v___x_3088_);
v___x_3090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3090_, 0, v___y_3027_);
lean_ctor_set(v___x_3090_, 1, v___x_3089_);
if (v_isShared_3086_ == 0)
{
lean_ctor_set(v___x_3085_, 0, v___x_3090_);
v___x_3092_ = v___x_3085_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3090_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
v_resetjp_3097_:
{
lean_object* v_fst_3100_; lean_object* v_snd_3101_; lean_object* v___x_3103_; uint8_t v_isShared_3104_; uint8_t v_isSharedCheck_3224_; 
v_fst_3100_ = lean_ctor_get(v_snd_3095_, 0);
v_snd_3101_ = lean_ctor_get(v_snd_3095_, 1);
v_isSharedCheck_3224_ = !lean_is_exclusive(v_snd_3095_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3103_ = v_snd_3095_;
v_isShared_3104_ = v_isSharedCheck_3224_;
goto v_resetjp_3102_;
}
else
{
lean_inc(v_snd_3101_);
lean_inc(v_fst_3100_);
lean_dec(v_snd_3095_);
v___x_3103_ = lean_box(0);
v_isShared_3104_ = v_isSharedCheck_3224_;
goto v_resetjp_3102_;
}
v_resetjp_3102_:
{
lean_object* v___y_3106_; lean_object* v___y_3107_; lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v_exportedInfo_x3f_3135_; lean_object* v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3147_; lean_object* v___y_3148_; lean_object* v___y_3151_; lean_object* v___y_3152_; lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___x_3214_; lean_object* v_env_3215_; uint8_t v___x_3216_; 
v___x_3214_ = lean_st_ref_get(v___y_2994_);
v_env_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc_ref(v_env_3215_);
lean_dec(v___x_3214_);
v___x_3216_ = l_Lean_Environment_containsOnBranch(v_env_3215_, v_fst_3096_);
lean_dec_ref(v_env_3215_);
if (v___x_3216_ == 0)
{
lean_del_object(v___x_3098_);
v___y_3179_ = v___y_2993_;
v___y_3180_ = v___y_2994_;
goto v___jp_3178_;
}
else
{
lean_object* v___x_3217_; lean_object* v_env_3218_; lean_object* v___x_3219_; lean_object* v___x_3221_; 
lean_del_object(v___x_3103_);
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec(v_exportedInfo_x3f_2992_);
lean_dec(v___x_2990_);
lean_dec(v_cls_2989_);
lean_dec_ref(v___x_2988_);
lean_dec(v_decl_2985_);
v___x_3217_ = lean_st_ref_get(v___y_2994_);
v_env_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc_ref(v_env_3218_);
lean_dec(v___x_3217_);
v___x_3219_ = lean_elab_environment_to_kernel_env(v_env_3218_);
if (v_isShared_3099_ == 0)
{
lean_ctor_set_tag(v___x_3098_, 1);
lean_ctor_set(v___x_3098_, 1, v_fst_3096_);
lean_ctor_set(v___x_3098_, 0, v___x_3219_);
v___x_3221_ = v___x_3098_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v___x_3219_);
lean_ctor_set(v_reuseFailAlloc_3223_, 1, v_fst_3096_);
v___x_3221_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
lean_object* v___x_3222_; 
v___x_3222_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3221_, v___y_2993_, v___y_2994_);
return v___x_3222_;
}
}
v___jp_3105_:
{
lean_object* v_ref_3111_; uint8_t v___x_3112_; lean_object* v___x_3113_; 
v_ref_3111_ = lean_ctor_get(v___y_3106_, 2);
v___x_3112_ = lean_unbox(v_snd_3101_);
lean_dec(v_snd_3101_);
lean_inc_ref(v___y_3109_);
v___x_3113_ = l_Lean_Environment_addConstAsync(v___y_3109_, v_fst_3096_, v___x_3112_, v___y_3110_, v___x_2987_, v_hasTrace_2986_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v_mainEnv_3115_; lean_object* v_asyncEnv_3116_; lean_object* v___f_3117_; lean_object* v___f_3118_; lean_object* v___x_3119_; 
lean_del_object(v___x_3103_);
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc_n(v_a_3114_, 3);
lean_dec_ref_known(v___x_3113_, 1);
v_mainEnv_3115_ = lean_ctor_get(v_a_3114_, 0);
lean_inc_ref(v_mainEnv_3115_);
v_asyncEnv_3116_ = lean_ctor_get(v_a_3114_, 1);
lean_inc_ref_n(v_asyncEnv_3116_, 2);
lean_inc(v_ref_3111_);
lean_inc(v___y_3107_);
v___f_3117_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3117_, 0, v___y_3107_);
lean_closure_set(v___f_3117_, 1, v_a_3114_);
lean_closure_set(v___f_3117_, 2, v_ref_3111_);
lean_inc(v_decl_2985_);
v___f_3118_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3118_, 0, v_a_3114_);
lean_closure_set(v___f_3118_, 1, v_asyncEnv_3116_);
lean_closure_set(v___f_3118_, 2, v_decl_2985_);
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v_fst_3100_);
if (lean_obj_tag(v___y_3108_) == 0)
{
lean_inc_ref(v___x_3119_);
lean_inc(v_ref_3111_);
v___y_3023_ = v___f_3118_;
v___y_3024_ = v___f_3117_;
v___y_3025_ = v___y_3106_;
v___y_3026_ = v___y_3109_;
v___y_3027_ = v_ref_3111_;
v___y_3028_ = v___x_3119_;
v___y_3029_ = v_asyncEnv_3116_;
v___y_3030_ = v_a_3114_;
v___y_3031_ = v_mainEnv_3115_;
v___y_3032_ = v___y_3107_;
v___y_3033_ = v___x_3119_;
goto v___jp_3022_;
}
else
{
lean_inc(v_ref_3111_);
v___y_3023_ = v___f_3118_;
v___y_3024_ = v___f_3117_;
v___y_3025_ = v___y_3106_;
v___y_3026_ = v___y_3109_;
v___y_3027_ = v_ref_3111_;
v___y_3028_ = v___x_3119_;
v___y_3029_ = v_asyncEnv_3116_;
v___y_3030_ = v_a_3114_;
v___y_3031_ = v_mainEnv_3115_;
v___y_3032_ = v___y_3107_;
v___y_3033_ = v___y_3108_;
goto v___jp_3022_;
}
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3133_; 
lean_dec_ref(v___y_3109_);
lean_dec(v___y_3108_);
lean_dec(v_fst_3100_);
lean_dec(v_decl_2985_);
v_a_3120_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3122_ = v___x_3113_;
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3113_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3133_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3124_ = lean_io_error_to_string(v_a_3120_);
v___x_3125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3125_, 0, v___x_3124_);
v___x_3126_ = l_Lean_MessageData_ofFormat(v___x_3125_);
lean_inc(v_ref_3111_);
if (v_isShared_3104_ == 0)
{
lean_ctor_set(v___x_3103_, 1, v___x_3126_);
lean_ctor_set(v___x_3103_, 0, v_ref_3111_);
v___x_3128_ = v___x_3103_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_ref_3111_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
lean_object* v___x_3130_; 
if (v_isShared_3123_ == 0)
{
lean_ctor_set(v___x_3122_, 0, v___x_3128_);
v___x_3130_ = v___x_3122_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
}
}
v___jp_3134_:
{
lean_object* v___x_3138_; 
v___x_3138_ = lean_st_ref_get(v___y_3137_);
if (lean_obj_tag(v_exportedInfo_x3f_3135_) == 0)
{
lean_object* v_env_3139_; lean_object* v___x_3140_; 
v_env_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3139_);
lean_dec(v___x_3138_);
v___x_3140_ = lean_box(0);
v___y_3106_ = v___y_3136_;
v___y_3107_ = v___y_3137_;
v___y_3108_ = v_exportedInfo_x3f_3135_;
v___y_3109_ = v_env_3139_;
v___y_3110_ = v___x_3140_;
goto v___jp_3105_;
}
else
{
lean_object* v_env_3141_; lean_object* v_val_3142_; uint8_t v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
v_env_3141_ = lean_ctor_get(v___x_3138_, 0);
lean_inc_ref(v_env_3141_);
lean_dec(v___x_3138_);
v_val_3142_ = lean_ctor_get(v_exportedInfo_x3f_3135_, 0);
v___x_3143_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3142_);
v___x_3144_ = lean_box(v___x_3143_);
v___x_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
v___y_3106_ = v___y_3136_;
v___y_3107_ = v___y_3137_;
v___y_3108_ = v_exportedInfo_x3f_3135_;
v___y_3109_ = v_env_3141_;
v___y_3110_ = v___x_3145_;
goto v___jp_3105_;
}
}
v___jp_3146_:
{
lean_object* v___x_3149_; 
lean_inc(v_fst_3100_);
v___x_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3149_, 0, v_fst_3100_);
v_exportedInfo_x3f_3135_ = v___x_3149_;
v___y_3136_ = v___y_3147_;
v___y_3137_ = v___y_3148_;
goto v___jp_3134_;
}
v___jp_3150_:
{
lean_object* v___x_3153_; 
lean_inc(v_fst_3100_);
v___x_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3153_, 0, v_fst_3100_);
v_exportedInfo_x3f_3135_ = v___x_3153_;
v___y_3136_ = v___y_3151_;
v___y_3137_ = v___y_3152_;
goto v___jp_3134_;
}
v___jp_3154_:
{
lean_object* v___x_3157_; lean_object* v_env_3158_; lean_object* v_nextMacroScope_3159_; lean_object* v_ngen_3160_; lean_object* v_auxDeclNGen_3161_; lean_object* v_traceState_3162_; lean_object* v_recordedDeps_3163_; lean_object* v_messages_3164_; lean_object* v_infoState_3165_; lean_object* v_snapshotTasks_3166_; lean_object* v___x_3168_; uint8_t v_isShared_3169_; uint8_t v_isSharedCheck_3176_; 
v___x_3157_ = lean_st_ref_take(v___y_3155_);
v_env_3158_ = lean_ctor_get(v___x_3157_, 0);
v_nextMacroScope_3159_ = lean_ctor_get(v___x_3157_, 1);
v_ngen_3160_ = lean_ctor_get(v___x_3157_, 2);
v_auxDeclNGen_3161_ = lean_ctor_get(v___x_3157_, 3);
v_traceState_3162_ = lean_ctor_get(v___x_3157_, 4);
v_recordedDeps_3163_ = lean_ctor_get(v___x_3157_, 6);
v_messages_3164_ = lean_ctor_get(v___x_3157_, 7);
v_infoState_3165_ = lean_ctor_get(v___x_3157_, 8);
v_snapshotTasks_3166_ = lean_ctor_get(v___x_3157_, 9);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3176_ == 0)
{
lean_object* v_unused_3177_; 
v_unused_3177_ = lean_ctor_get(v___x_3157_, 5);
lean_dec(v_unused_3177_);
v___x_3168_ = v___x_3157_;
v_isShared_3169_ = v_isSharedCheck_3176_;
goto v_resetjp_3167_;
}
else
{
lean_inc(v_snapshotTasks_3166_);
lean_inc(v_infoState_3165_);
lean_inc(v_messages_3164_);
lean_inc(v_recordedDeps_3163_);
lean_inc(v_traceState_3162_);
lean_inc(v_auxDeclNGen_3161_);
lean_inc(v_ngen_3160_);
lean_inc(v_nextMacroScope_3159_);
lean_inc(v_env_3158_);
lean_dec(v___x_3157_);
v___x_3168_ = lean_box(0);
v_isShared_3169_ = v_isSharedCheck_3176_;
goto v_resetjp_3167_;
}
v_resetjp_3167_:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3173_; 
v___x_3170_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3101_);
lean_inc(v_fst_3096_);
v___x_3171_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3170_, v_env_3158_, v_fst_3096_, v_snd_3101_);
if (v_isShared_3169_ == 0)
{
lean_ctor_set(v___x_3168_, 5, v___x_2988_);
lean_ctor_set(v___x_3168_, 0, v___x_3171_);
v___x_3173_ = v___x_3168_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3175_; 
v_reuseFailAlloc_3175_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3175_, 0, v___x_3171_);
lean_ctor_set(v_reuseFailAlloc_3175_, 1, v_nextMacroScope_3159_);
lean_ctor_set(v_reuseFailAlloc_3175_, 2, v_ngen_3160_);
lean_ctor_set(v_reuseFailAlloc_3175_, 3, v_auxDeclNGen_3161_);
lean_ctor_set(v_reuseFailAlloc_3175_, 4, v_traceState_3162_);
lean_ctor_set(v_reuseFailAlloc_3175_, 5, v___x_2988_);
lean_ctor_set(v_reuseFailAlloc_3175_, 6, v_recordedDeps_3163_);
lean_ctor_set(v_reuseFailAlloc_3175_, 7, v_messages_3164_);
lean_ctor_set(v_reuseFailAlloc_3175_, 8, v_infoState_3165_);
lean_ctor_set(v_reuseFailAlloc_3175_, 9, v_snapshotTasks_3166_);
v___x_3173_ = v_reuseFailAlloc_3175_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
lean_object* v___x_3174_; 
v___x_3174_ = lean_st_ref_put(v___y_3155_, v___x_3173_);
v_exportedInfo_x3f_3135_ = v_exportedInfo_x3f_2992_;
v___y_3136_ = v___y_3156_;
v___y_3137_ = v___y_3155_;
goto v___jp_3134_;
}
}
}
v___jp_3178_:
{
lean_object* v___x_3181_; uint8_t v___x_3182_; 
lean_inc(v_decl_2985_);
v___x_3181_ = l_Lean_Declaration_getTopLevelNames(v_decl_2985_);
v___x_3182_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3181_);
lean_dec(v___x_3181_);
if (v___x_3182_ == 0)
{
lean_dec(v___x_2990_);
if (lean_obj_tag(v_exportedInfo_x3f_2992_) == 0)
{
if (v___x_3182_ == 0)
{
lean_object* v_toCold_3183_; lean_object* v_options_3184_; uint8_t v_hasTrace_3185_; 
lean_dec_ref(v___x_2988_);
v_toCold_3183_ = lean_ctor_get(v___y_3179_, 0);
v_options_3184_ = lean_ctor_get(v_toCold_3183_, 2);
v_hasTrace_3185_ = lean_ctor_get_uint8(v_options_3184_, sizeof(void*)*1);
if (v_hasTrace_3185_ == 0)
{
lean_dec(v_cls_2989_);
v___y_3147_ = v___y_3179_;
v___y_3148_ = v___y_3180_;
goto v___jp_3146_;
}
else
{
lean_object* v_inheritedTraceOptions_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; uint8_t v___x_3189_; 
v_inheritedTraceOptions_3186_ = lean_ctor_get(v_toCold_3183_, 11);
v___x_3187_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2989_);
v___x_3188_ = l_Lean_Name_append(v___x_3187_, v_cls_2989_);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3186_, v_options_3184_, v___x_3188_);
lean_dec(v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec(v_cls_2989_);
v___y_3147_ = v___y_3179_;
v___y_3148_ = v___y_3180_;
goto v___jp_3146_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3191_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2989_, v___x_3190_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_dec_ref_known(v___x_3191_, 1);
v___y_3147_ = v___y_3179_;
v___y_3148_ = v___y_3180_;
goto v___jp_3146_;
}
else
{
lean_del_object(v___x_3103_);
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec(v_fst_3096_);
lean_dec(v_decl_2985_);
return v___x_3191_;
}
}
}
}
else
{
lean_dec(v_cls_2989_);
v___y_3155_ = v___y_3180_;
v___y_3156_ = v___y_3179_;
goto v___jp_3154_;
}
}
else
{
lean_dec(v_cls_2989_);
v___y_3155_ = v___y_3180_;
v___y_3156_ = v___y_3179_;
goto v___jp_3154_;
}
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v_a_3194_; uint8_t v___x_3195_; 
lean_dec(v_exportedInfo_x3f_2992_);
lean_dec_ref(v___x_2988_);
v___x_3192_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3193_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3192_, v___y_3179_);
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
v___x_3195_ = lean_unbox(v_a_3194_);
lean_dec(v_a_3194_);
if (v___x_3195_ == 0)
{
lean_object* v_toCold_3196_; lean_object* v_options_3197_; uint8_t v_hasTrace_3198_; 
v_toCold_3196_ = lean_ctor_get(v___y_3179_, 0);
v_options_3197_ = lean_ctor_get(v_toCold_3196_, 2);
v_hasTrace_3198_ = lean_ctor_get_uint8(v_options_3197_, sizeof(void*)*1);
if (v_hasTrace_3198_ == 0)
{
lean_dec(v_cls_2989_);
v_exportedInfo_x3f_3135_ = v___x_2990_;
v___y_3136_ = v___y_3179_;
v___y_3137_ = v___y_3180_;
goto v___jp_3134_;
}
else
{
lean_object* v_inheritedTraceOptions_3199_; lean_object* v___x_3200_; lean_object* v___x_3201_; uint8_t v___x_3202_; 
v_inheritedTraceOptions_3199_ = lean_ctor_get(v_toCold_3196_, 11);
v___x_3200_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2989_);
v___x_3201_ = l_Lean_Name_append(v___x_3200_, v_cls_2989_);
v___x_3202_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3199_, v_options_3197_, v___x_3201_);
lean_dec(v___x_3201_);
if (v___x_3202_ == 0)
{
lean_dec(v_cls_2989_);
v_exportedInfo_x3f_3135_ = v___x_2990_;
v___y_3136_ = v___y_3179_;
v___y_3137_ = v___y_3180_;
goto v___jp_3134_;
}
else
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3204_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2989_, v___x_3203_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_dec_ref_known(v___x_3204_, 1);
v_exportedInfo_x3f_3135_ = v___x_2990_;
v___y_3136_ = v___y_3179_;
v___y_3137_ = v___y_3180_;
goto v___jp_3134_;
}
else
{
lean_del_object(v___x_3103_);
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec(v_fst_3096_);
lean_dec(v___x_2990_);
lean_dec(v_decl_2985_);
return v___x_3204_;
}
}
}
}
else
{
lean_object* v_toCold_3205_; lean_object* v_options_3206_; uint8_t v_hasTrace_3207_; 
lean_dec(v___x_2990_);
v_toCold_3205_ = lean_ctor_get(v___y_3179_, 0);
v_options_3206_ = lean_ctor_get(v_toCold_3205_, 2);
v_hasTrace_3207_ = lean_ctor_get_uint8(v_options_3206_, sizeof(void*)*1);
if (v_hasTrace_3207_ == 0)
{
lean_dec(v_cls_2989_);
v___y_3151_ = v___y_3179_;
v___y_3152_ = v___y_3180_;
goto v___jp_3150_;
}
else
{
lean_object* v_inheritedTraceOptions_3208_; lean_object* v___x_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; 
v_inheritedTraceOptions_3208_ = lean_ctor_get(v_toCold_3205_, 11);
v___x_3209_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2989_);
v___x_3210_ = l_Lean_Name_append(v___x_3209_, v_cls_2989_);
v___x_3211_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3208_, v_options_3206_, v___x_3210_);
lean_dec(v___x_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v_cls_2989_);
v___y_3151_ = v___y_3179_;
v___y_3152_ = v___y_3180_;
goto v___jp_3150_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3213_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2989_, v___x_3212_, v___y_3179_, v___y_3180_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec_ref_known(v___x_3213_, 1);
v___y_3151_ = v___y_3179_;
v___y_3152_ = v___y_3180_;
goto v___jp_3150_;
}
else
{
lean_del_object(v___x_3103_);
lean_dec(v_snd_3101_);
lean_dec(v_fst_3100_);
lean_dec(v_fst_3096_);
lean_dec(v_decl_2985_);
return v___x_3213_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_decl_3226_, lean_object* v_hasTrace_3227_, lean_object* v___x_3228_, lean_object* v___x_3229_, lean_object* v_cls_3230_, lean_object* v___x_3231_, lean_object* v_____x_3232_, lean_object* v_exportedInfo_x3f_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
uint8_t v_hasTrace_boxed_3237_; uint8_t v___x_53257__boxed_3238_; lean_object* v_res_3239_; 
v_hasTrace_boxed_3237_ = lean_unbox(v_hasTrace_3227_);
v___x_53257__boxed_3238_ = lean_unbox(v___x_3228_);
v_res_3239_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3226_, v_hasTrace_boxed_3237_, v___x_53257__boxed_3238_, v___x_3229_, v_cls_3230_, v___x_3231_, v_____x_3232_, v_exportedInfo_x3f_3233_, v___y_3234_, v___y_3235_);
lean_dec(v___y_3235_);
lean_dec_ref(v___y_3234_);
return v_res_3239_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1(void){
_start:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__0));
v___x_3242_ = l_Lean_stringToMessageData(v___x_3241_);
return v___x_3242_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3(void){
_start:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__2));
v___x_3245_ = l_Lean_stringToMessageData(v___x_3244_);
return v___x_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v___f_3246_, uint8_t v___x_3247_, lean_object* v_cls_3248_, lean_object* v___x_3249_, uint8_t v_forceExpose_3250_, lean_object* v_defn_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_){
_start:
{
lean_object* v_exportedInfo_x3f_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3268_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; uint8_t v___y_3276_; lean_object* v___x_3281_; lean_object* v_env_3282_; lean_object* v___x_3283_; uint8_t v___y_3285_; lean_object* v_env_3301_; 
v___x_3281_ = lean_st_ref_get(v___y_3253_);
v_env_3282_ = lean_ctor_get(v___x_3281_, 0);
lean_inc_ref(v_env_3282_);
lean_dec(v___x_3281_);
v___x_3283_ = lean_st_ref_get(v___y_3253_);
v_env_3301_ = lean_ctor_get(v___x_3283_, 0);
lean_inc_ref(v_env_3301_);
lean_dec(v___x_3283_);
if (v_forceExpose_3250_ == 0)
{
goto v___jp_3302_;
}
else
{
if (v___x_3247_ == 0)
{
lean_dec_ref(v_env_3301_);
lean_dec_ref(v_env_3282_);
lean_dec(v_cls_3248_);
v_exportedInfo_x3f_3256_ = v___x_3249_;
v___y_3257_ = v___y_3252_;
v___y_3258_ = v___y_3253_;
goto v___jp_3255_;
}
else
{
goto v___jp_3302_;
}
}
v___jp_3255_:
{
lean_object* v_toConstantVal_3259_; lean_object* v_name_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_toConstantVal_3259_ = lean_ctor_get(v_defn_3251_, 0);
v_name_3260_ = lean_ctor_get(v_toConstantVal_3259_, 0);
lean_inc(v_name_3260_);
v___x_3261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3261_, 0, v_defn_3251_);
v___x_3262_ = 0;
v___x_3263_ = lean_box(v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3261_);
lean_ctor_set(v___x_3264_, 1, v___x_3263_);
v___x_3265_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3265_, 0, v_name_3260_);
lean_ctor_set(v___x_3265_, 1, v___x_3264_);
lean_inc(v___y_3258_);
lean_inc_ref(v___y_3257_);
v___x_3266_ = lean_apply_5(v___f_3246_, v___x_3265_, v_exportedInfo_x3f_3256_, v___y_3257_, v___y_3258_, lean_box(0));
return v___x_3266_;
}
v___jp_3267_:
{
lean_object* v___x_3272_; lean_object* v___x_3273_; lean_object* v___x_3274_; 
v___x_3272_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3272_, 0, v___y_3270_);
lean_ctor_set_uint8(v___x_3272_, sizeof(void*)*1, v___y_3271_);
v___x_3273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3273_, 0, v___x_3272_);
v___x_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3274_, 0, v___x_3273_);
v_exportedInfo_x3f_3256_ = v___x_3274_;
v___y_3257_ = v___y_3269_;
v___y_3258_ = v___y_3268_;
goto v___jp_3255_;
}
v___jp_3275_:
{
lean_object* v_toConstantVal_3277_; uint8_t v_safety_3278_; uint8_t v___x_3279_; uint8_t v___x_3280_; 
v_toConstantVal_3277_ = lean_ctor_get(v_defn_3251_, 0);
v_safety_3278_ = lean_ctor_get_uint8(v_defn_3251_, sizeof(void*)*4);
v___x_3279_ = 1;
v___x_3280_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3278_, v___x_3279_);
if (v___x_3280_ == 0)
{
lean_inc_ref(v_toConstantVal_3277_);
v___y_3268_ = v___y_3253_;
v___y_3269_ = v___y_3252_;
v___y_3270_ = v_toConstantVal_3277_;
v___y_3271_ = v___y_3276_;
goto v___jp_3267_;
}
else
{
lean_inc_ref(v_toConstantVal_3277_);
v___y_3268_ = v___y_3253_;
v___y_3269_ = v___y_3252_;
v___y_3270_ = v_toConstantVal_3277_;
v___y_3271_ = v___x_3247_;
goto v___jp_3267_;
}
}
v___jp_3284_:
{
lean_object* v_toCold_3286_; lean_object* v_options_3287_; uint8_t v_hasTrace_3288_; 
v_toCold_3286_ = lean_ctor_get(v___y_3252_, 0);
v_options_3287_ = lean_ctor_get(v_toCold_3286_, 2);
v_hasTrace_3288_ = lean_ctor_get_uint8(v_options_3287_, sizeof(void*)*1);
if (v_hasTrace_3288_ == 0)
{
lean_dec(v_cls_3248_);
v___y_3276_ = v___y_3285_;
goto v___jp_3275_;
}
else
{
lean_object* v_inheritedTraceOptions_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; uint8_t v___x_3292_; 
v_inheritedTraceOptions_3289_ = lean_ctor_get(v_toCold_3286_, 11);
v___x_3290_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3248_);
v___x_3291_ = l_Lean_Name_append(v___x_3290_, v_cls_3248_);
v___x_3292_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3289_, v_options_3287_, v___x_3291_);
lean_dec(v___x_3291_);
if (v___x_3292_ == 0)
{
lean_dec(v_cls_3248_);
v___y_3276_ = v___y_3285_;
goto v___jp_3275_;
}
else
{
lean_object* v_toConstantVal_3293_; lean_object* v_name_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; 
v_toConstantVal_3293_ = lean_ctor_get(v_defn_3251_, 0);
v_name_3294_ = lean_ctor_get(v_toConstantVal_3293_, 0);
v___x_3295_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3294_);
v___x_3296_ = l_Lean_MessageData_ofName(v_name_3294_);
v___x_3297_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3295_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3299_, 0, v___x_3297_);
lean_ctor_set(v___x_3299_, 1, v___x_3298_);
v___x_3300_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3248_, v___x_3299_, v___y_3252_, v___y_3253_);
if (lean_obj_tag(v___x_3300_) == 0)
{
lean_dec_ref_known(v___x_3300_, 1);
v___y_3276_ = v___y_3285_;
goto v___jp_3275_;
}
else
{
lean_dec_ref(v_defn_3251_);
lean_dec_ref(v___f_3246_);
return v___x_3300_;
}
}
}
}
v___jp_3302_:
{
lean_object* v___x_3303_; uint8_t v_isModule_3304_; 
v___x_3303_ = l_Lean_Environment_header(v_env_3282_);
lean_dec_ref(v_env_3282_);
v_isModule_3304_ = lean_ctor_get_uint8(v___x_3303_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3303_);
if (v_isModule_3304_ == 0)
{
lean_dec_ref(v_env_3301_);
lean_dec(v_cls_3248_);
v_exportedInfo_x3f_3256_ = v___x_3249_;
v___y_3257_ = v___y_3252_;
v___y_3258_ = v___y_3253_;
goto v___jp_3255_;
}
else
{
uint8_t v_isExporting_3305_; 
v_isExporting_3305_ = lean_ctor_get_uint8(v_env_3301_, sizeof(void*)*8);
lean_dec_ref(v_env_3301_);
if (v_isExporting_3305_ == 0)
{
lean_dec(v___x_3249_);
v___y_3285_ = v_isModule_3304_;
goto v___jp_3284_;
}
else
{
if (v___x_3247_ == 0)
{
lean_dec(v_cls_3248_);
v_exportedInfo_x3f_3256_ = v___x_3249_;
v___y_3257_ = v___y_3252_;
v___y_3258_ = v___y_3253_;
goto v___jp_3255_;
}
else
{
lean_dec(v___x_3249_);
v___y_3285_ = v___x_3247_;
goto v___jp_3284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v___f_3306_, lean_object* v___x_3307_, lean_object* v_cls_3308_, lean_object* v___x_3309_, lean_object* v_forceExpose_3310_, lean_object* v_defn_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_){
_start:
{
uint8_t v___x_53730__boxed_3315_; uint8_t v_forceExpose_boxed_3316_; lean_object* v_res_3317_; 
v___x_53730__boxed_3315_ = lean_unbox(v___x_3307_);
v_forceExpose_boxed_3316_ = lean_unbox(v_forceExpose_3310_);
v_res_3317_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_3306_, v___x_53730__boxed_3315_, v_cls_3308_, v___x_3309_, v_forceExpose_boxed_3316_, v_defn_3311_, v___y_3312_, v___y_3313_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3318_, lean_object* v___f_3319_, lean_object* v_____r_3320_, lean_object* v_exportedInfo_x3f_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_toConstantVal_3325_; lean_object* v_name_3326_; lean_object* v___x_3327_; uint8_t v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; 
v_toConstantVal_3325_ = lean_ctor_get(v_val_3318_, 0);
v_name_3326_ = lean_ctor_get(v_toConstantVal_3325_, 0);
lean_inc(v_name_3326_);
v___x_3327_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3327_, 0, v_val_3318_);
v___x_3328_ = 1;
v___x_3329_ = lean_box(v___x_3328_);
v___x_3330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3327_);
lean_ctor_set(v___x_3330_, 1, v___x_3329_);
v___x_3331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3331_, 0, v_name_3326_);
lean_ctor_set(v___x_3331_, 1, v___x_3330_);
lean_inc(v___y_3323_);
lean_inc_ref(v___y_3322_);
v___x_3332_ = lean_apply_5(v___f_3319_, v___x_3331_, v_exportedInfo_x3f_3321_, v___y_3322_, v___y_3323_, lean_box(0));
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3333_, lean_object* v___f_3334_, lean_object* v_____r_3335_, lean_object* v_exportedInfo_x3f_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_res_3340_; 
v_res_3340_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3333_, v___f_3334_, v_____r_3335_, v_exportedInfo_x3f_3336_, v___y_3337_, v___y_3338_);
lean_dec(v___y_3338_);
lean_dec_ref(v___y_3337_);
return v_res_3340_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3341_, uint8_t v___x_3342_, lean_object* v___f_3343_, lean_object* v_____r_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_){
_start:
{
lean_object* v_toConstantVal_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v___x_3353_; 
v_toConstantVal_3348_ = lean_ctor_get(v_val_3341_, 0);
lean_inc_ref(v_toConstantVal_3348_);
v___x_3349_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3349_, 0, v_toConstantVal_3348_);
lean_ctor_set_uint8(v___x_3349_, sizeof(void*)*1, v___x_3342_);
v___x_3350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3349_);
v___x_3351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3351_, 0, v___x_3350_);
v___x_3352_ = lean_box(0);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
v___x_3353_ = lean_apply_5(v___f_3343_, v___x_3352_, v___x_3351_, v___y_3345_, v___y_3346_, lean_box(0));
return v___x_3353_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3354_, lean_object* v___x_3355_, lean_object* v___f_3356_, lean_object* v_____r_3357_, lean_object* v___y_3358_, lean_object* v___y_3359_, lean_object* v___y_3360_){
_start:
{
uint8_t v___x_53861__boxed_3361_; lean_object* v_res_3362_; 
v___x_53861__boxed_3361_ = lean_unbox(v___x_3355_);
v_res_3362_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3354_, v___x_53861__boxed_3361_, v___f_3356_, v_____r_3357_, v___y_3358_, v___y_3359_);
lean_dec(v___y_3359_);
lean_dec_ref(v___y_3358_);
lean_dec_ref(v_val_3354_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_val_3363_, lean_object* v___f_3364_, lean_object* v_____r_3365_, lean_object* v_exportedInfo_x3f_3366_, lean_object* v___y_3367_, lean_object* v___y_3368_){
_start:
{
lean_object* v_toConstantVal_3370_; lean_object* v_name_3371_; lean_object* v___x_3372_; uint8_t v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_toConstantVal_3370_ = lean_ctor_get(v_val_3363_, 0);
v_name_3371_ = lean_ctor_get(v_toConstantVal_3370_, 0);
lean_inc(v_name_3371_);
v___x_3372_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3372_, 0, v_val_3363_);
v___x_3373_ = 3;
v___x_3374_ = lean_box(v___x_3373_);
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3372_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3376_, 0, v_name_3371_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
lean_inc(v___y_3368_);
lean_inc_ref(v___y_3367_);
v___x_3377_ = lean_apply_5(v___f_3364_, v___x_3376_, v_exportedInfo_x3f_3366_, v___y_3367_, v___y_3368_, lean_box(0));
return v___x_3377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_val_3378_, lean_object* v___f_3379_, lean_object* v_____r_3380_, lean_object* v_exportedInfo_x3f_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_val_3378_, v___f_3379_, v_____r_3380_, v_exportedInfo_x3f_3381_, v___y_3382_, v___y_3383_);
lean_dec(v___y_3383_);
lean_dec_ref(v___y_3382_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v_val_3386_, lean_object* v___f_3387_, lean_object* v_____r_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_){
_start:
{
lean_object* v_toConstantVal_3392_; uint8_t v_isUnsafe_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v___x_3398_; 
v_toConstantVal_3392_ = lean_ctor_get(v_val_3386_, 0);
v_isUnsafe_3393_ = lean_ctor_get_uint8(v_val_3386_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3392_);
v___x_3394_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3394_, 0, v_toConstantVal_3392_);
lean_ctor_set_uint8(v___x_3394_, sizeof(void*)*1, v_isUnsafe_3393_);
v___x_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
v___x_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3396_, 0, v___x_3395_);
v___x_3397_ = lean_box(0);
lean_inc(v___y_3390_);
lean_inc_ref(v___y_3389_);
v___x_3398_ = lean_apply_5(v___f_3387_, v___x_3397_, v___x_3396_, v___y_3389_, v___y_3390_, lean_box(0));
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v_val_3399_, lean_object* v___f_3400_, lean_object* v_____r_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_3399_, v___f_3400_, v_____r_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v_val_3399_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(lean_object* v_decl_3406_, uint8_t v___x_3407_, lean_object* v_cls_3408_, lean_object* v___x_3409_, lean_object* v___x_3410_, lean_object* v_____x_3411_, lean_object* v_exportedInfo_x3f_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___y_3417_; lean_object* v___y_3418_; lean_object* v_a_3419_; lean_object* v___y_3430_; lean_object* v___y_3431_; lean_object* v_a_3432_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___y_3451_; uint8_t v___y_3452_; lean_object* v___y_3453_; lean_object* v___y_3454_; lean_object* v_snd_3516_; lean_object* v_fst_3517_; lean_object* v___x_3519_; uint8_t v_isShared_3520_; uint8_t v_isSharedCheck_3648_; 
v_snd_3516_ = lean_ctor_get(v_____x_3411_, 1);
v_fst_3517_ = lean_ctor_get(v_____x_3411_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_____x_3411_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3519_ = v_____x_3411_;
v_isShared_3520_ = v_isSharedCheck_3648_;
goto v_resetjp_3518_;
}
else
{
lean_inc(v_snd_3516_);
lean_inc(v_fst_3517_);
lean_dec(v_____x_3411_);
v___x_3519_ = lean_box(0);
v_isShared_3520_ = v_isSharedCheck_3648_;
goto v_resetjp_3518_;
}
v___jp_3416_:
{
lean_object* v___x_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
v___x_3420_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3418_, v___y_3417_);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3420_);
if (v_isSharedCheck_3427_ == 0)
{
lean_object* v_unused_3428_; 
v_unused_3428_ = lean_ctor_get(v___x_3420_, 0);
lean_dec(v_unused_3428_);
v___x_3422_ = v___x_3420_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_dec(v___x_3420_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
lean_ctor_set_tag(v___x_3422_, 1);
lean_ctor_set(v___x_3422_, 0, v_a_3419_);
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3419_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
v___jp_3429_:
{
lean_object* v___x_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3440_; 
v___x_3433_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3431_, v___y_3430_);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3433_);
if (v_isSharedCheck_3440_ == 0)
{
lean_object* v_unused_3441_; 
v_unused_3441_ = lean_ctor_get(v___x_3433_, 0);
lean_dec(v_unused_3441_);
v___x_3435_ = v___x_3433_;
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
else
{
lean_dec(v___x_3433_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3440_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
lean_object* v___x_3438_; 
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v_a_3432_);
v___x_3438_ = v___x_3435_;
goto v_reusejp_3437_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_a_3432_);
v___x_3438_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3437_;
}
v_reusejp_3437_:
{
return v___x_3438_;
}
}
}
v___jp_3442_:
{
lean_object* v___x_3455_; 
lean_inc_ref(v___y_3451_);
v___x_3455_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3447_, v___y_3451_, v___y_3448_, v___y_3454_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v___x_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3502_; 
lean_dec_ref_known(v___x_3455_, 1);
lean_dec(v___y_3444_);
lean_inc_ref(v___y_3453_);
v___x_3456_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3453_, v___y_3449_);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3502_ == 0)
{
lean_object* v_unused_3503_; 
v_unused_3503_ = lean_ctor_get(v___x_3456_, 0);
lean_dec(v_unused_3503_);
v___x_3458_ = v___x_3456_;
v_isShared_3459_ = v_isSharedCheck_3502_;
goto v_resetjp_3457_;
}
else
{
lean_dec(v___x_3456_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3502_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; uint8_t v___x_3462_; 
v___x_3460_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3445_);
v___x_3461_ = l_Lean_Elab_async;
v___x_3462_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3460_, v___x_3461_);
lean_dec_ref(v___x_3460_);
if (v___x_3462_ == 0)
{
lean_object* v___x_3463_; lean_object* v_r_3464_; 
lean_del_object(v___x_3458_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3446_);
v___x_3463_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3451_, v___y_3449_);
lean_dec_ref(v___x_3463_);
v_r_3464_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3406_, v___y_3445_, v___y_3449_);
if (lean_obj_tag(v_r_3464_) == 0)
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
v_a_3465_ = lean_ctor_get(v_r_3464_, 0);
v_isSharedCheck_3474_ = !lean_is_exclusive(v_r_3464_);
if (v_isSharedCheck_3474_ == 0)
{
v___x_3467_ = v_r_3464_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v_r_3464_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
lean_inc(v_a_3465_);
if (v_isShared_3468_ == 0)
{
lean_ctor_set_tag(v___x_3467_, 1);
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
lean_object* v___x_3471_; 
v___x_3471_ = lean_apply_2(v___y_3443_, v___x_3470_, lean_box(0));
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_dec_ref_known(v___x_3471_, 1);
v___y_3430_ = v___y_3449_;
v___y_3431_ = v___y_3453_;
v_a_3432_ = v_a_3465_;
goto v___jp_3429_;
}
else
{
lean_object* v_a_3472_; 
lean_dec(v_a_3465_);
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
lean_inc(v_a_3472_);
lean_dec_ref_known(v___x_3471_, 1);
v___y_3417_ = v___y_3449_;
v___y_3418_ = v___y_3453_;
v_a_3419_ = v_a_3472_;
goto v___jp_3416_;
}
}
}
}
else
{
lean_object* v_a_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v_a_3475_ = lean_ctor_get(v_r_3464_, 0);
lean_inc(v_a_3475_);
lean_dec_ref_known(v_r_3464_, 1);
v___x_3476_ = lean_box(0);
v___x_3477_ = lean_apply_2(v___y_3443_, v___x_3476_, lean_box(0));
if (lean_obj_tag(v___x_3477_) == 0)
{
lean_dec_ref_known(v___x_3477_, 1);
v___y_3417_ = v___y_3449_;
v___y_3418_ = v___y_3453_;
v_a_3419_ = v_a_3475_;
goto v___jp_3416_;
}
else
{
lean_object* v_a_3478_; 
lean_dec(v_a_3475_);
v_a_3478_ = lean_ctor_get(v___x_3477_, 0);
lean_inc(v_a_3478_);
lean_dec_ref_known(v___x_3477_, 1);
v___y_3417_ = v___y_3449_;
v___y_3418_ = v___y_3453_;
v_a_3419_ = v_a_3478_;
goto v___jp_3416_;
}
}
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3481_; 
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v___y_3443_);
lean_dec(v_decl_3406_);
v___x_3479_ = l_IO_CancelToken_new();
if (v_isShared_3459_ == 0)
{
lean_ctor_set_tag(v___x_3458_, 1);
lean_ctor_set(v___x_3458_, 0, v___x_3479_);
v___x_3481_ = v___x_3458_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v___x_3479_);
v___x_3481_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; 
v___x_3482_ = lean_unsigned_to_nat(0u);
v___x_3483_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3484_ = l_Lean_Name_toString(v___x_3483_, v___x_3407_);
lean_inc_ref(v___x_3481_);
v___x_3485_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3450_, v___x_3481_, v___x_3484_, v___y_3445_, v___y_3449_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v_checked_3487_; lean_object* v___x_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref_known(v___x_3485_, 1);
v_checked_3487_ = lean_ctor_get(v___y_3446_, 2);
lean_inc_ref(v_checked_3487_);
lean_dec_ref(v___y_3446_);
v___x_3488_ = lean_io_map_task(v_a_3486_, v_checked_3487_, v___x_3482_, v___y_3452_);
v___x_3489_ = lean_box(0);
v___x_3490_ = lean_box(2);
v___x_3491_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3489_);
lean_ctor_set(v___x_3491_, 1, v___x_3490_);
lean_ctor_set(v___x_3491_, 2, v___x_3481_);
lean_ctor_set(v___x_3491_, 3, v___x_3488_);
v___x_3492_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3491_, v___y_3449_);
return v___x_3492_;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v___x_3481_);
lean_dec_ref(v___y_3446_);
v_a_3493_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3485_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3485_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v___x_3506_; uint8_t v_isShared_3507_; uint8_t v_isSharedCheck_3515_; 
lean_dec_ref(v___y_3453_);
lean_dec_ref(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec_ref(v___y_3446_);
lean_dec_ref(v___y_3443_);
lean_dec(v_decl_3406_);
v_a_3504_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3515_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3515_ == 0)
{
v___x_3506_ = v___x_3455_;
v_isShared_3507_ = v_isSharedCheck_3515_;
goto v_resetjp_3505_;
}
else
{
lean_inc(v_a_3504_);
lean_dec(v___x_3455_);
v___x_3506_ = lean_box(0);
v_isShared_3507_ = v_isSharedCheck_3515_;
goto v_resetjp_3505_;
}
v_resetjp_3505_:
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3513_; 
v___x_3508_ = lean_io_error_to_string(v_a_3504_);
v___x_3509_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___x_3510_ = l_Lean_MessageData_ofFormat(v___x_3509_);
v___x_3511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___y_3444_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
if (v_isShared_3507_ == 0)
{
lean_ctor_set(v___x_3506_, 0, v___x_3511_);
v___x_3513_ = v___x_3506_;
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
v_resetjp_3518_:
{
lean_object* v_fst_3521_; lean_object* v_snd_3522_; lean_object* v___x_3524_; uint8_t v_isShared_3525_; uint8_t v_isSharedCheck_3647_; 
v_fst_3521_ = lean_ctor_get(v_snd_3516_, 0);
v_snd_3522_ = lean_ctor_get(v_snd_3516_, 1);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_snd_3516_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3524_ = v_snd_3516_;
v_isShared_3525_ = v_isSharedCheck_3647_;
goto v_resetjp_3523_;
}
else
{
lean_inc(v_snd_3522_);
lean_inc(v_fst_3521_);
lean_dec(v_snd_3516_);
v___x_3524_ = lean_box(0);
v_isShared_3525_ = v_isSharedCheck_3647_;
goto v_resetjp_3523_;
}
v_resetjp_3523_:
{
lean_object* v___y_3527_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3530_; lean_object* v___y_3531_; lean_object* v_exportedInfo_x3f_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3569_; lean_object* v___y_3570_; lean_object* v___y_3573_; lean_object* v___y_3574_; lean_object* v___y_3577_; lean_object* v___y_3578_; uint8_t v___y_3579_; lean_object* v___y_3611_; lean_object* v___y_3612_; lean_object* v___x_3637_; lean_object* v_env_3638_; uint8_t v___x_3639_; 
v___x_3637_ = lean_st_ref_get(v___y_3414_);
v_env_3638_ = lean_ctor_get(v___x_3637_, 0);
lean_inc_ref(v_env_3638_);
lean_dec(v___x_3637_);
v___x_3639_ = l_Lean_Environment_containsOnBranch(v_env_3638_, v_fst_3517_);
lean_dec_ref(v_env_3638_);
if (v___x_3639_ == 0)
{
lean_del_object(v___x_3519_);
v___y_3611_ = v___y_3413_;
v___y_3612_ = v___y_3414_;
goto v___jp_3610_;
}
else
{
lean_object* v___x_3640_; lean_object* v_env_3641_; lean_object* v___x_3642_; lean_object* v___x_3644_; 
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec(v_exportedInfo_x3f_3412_);
lean_dec(v___x_3410_);
lean_dec_ref(v___x_3409_);
lean_dec(v_cls_3408_);
lean_dec(v_decl_3406_);
v___x_3640_ = lean_st_ref_get(v___y_3414_);
v_env_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc_ref(v_env_3641_);
lean_dec(v___x_3640_);
v___x_3642_ = lean_elab_environment_to_kernel_env(v_env_3641_);
if (v_isShared_3520_ == 0)
{
lean_ctor_set_tag(v___x_3519_, 1);
lean_ctor_set(v___x_3519_, 1, v_fst_3517_);
lean_ctor_set(v___x_3519_, 0, v___x_3642_);
v___x_3644_ = v___x_3519_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3646_, 1, v_fst_3517_);
v___x_3644_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
lean_object* v___x_3645_; 
v___x_3645_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3644_, v___y_3413_, v___y_3414_);
return v___x_3645_;
}
}
v___jp_3526_:
{
lean_object* v_ref_3532_; uint8_t v___x_3533_; uint8_t v___x_3534_; lean_object* v___x_3535_; 
v_ref_3532_ = lean_ctor_get(v___y_3527_, 2);
v___x_3533_ = 0;
v___x_3534_ = lean_unbox(v_snd_3522_);
lean_dec(v_snd_3522_);
lean_inc_ref(v___y_3530_);
v___x_3535_ = l_Lean_Environment_addConstAsync(v___y_3530_, v_fst_3517_, v___x_3534_, v___y_3531_, v___x_3533_, v___x_3407_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_object* v_a_3536_; lean_object* v_mainEnv_3537_; lean_object* v_asyncEnv_3538_; lean_object* v___f_3539_; lean_object* v___f_3540_; lean_object* v___x_3541_; 
lean_del_object(v___x_3524_);
v_a_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc_n(v_a_3536_, 3);
lean_dec_ref_known(v___x_3535_, 1);
v_mainEnv_3537_ = lean_ctor_get(v_a_3536_, 0);
lean_inc_ref(v_mainEnv_3537_);
v_asyncEnv_3538_ = lean_ctor_get(v_a_3536_, 1);
lean_inc_ref_n(v_asyncEnv_3538_, 2);
lean_inc(v_ref_3532_);
lean_inc(v___y_3528_);
v___f_3539_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3539_, 0, v___y_3528_);
lean_closure_set(v___f_3539_, 1, v_a_3536_);
lean_closure_set(v___f_3539_, 2, v_ref_3532_);
lean_inc(v_decl_3406_);
v___f_3540_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3540_, 0, v_a_3536_);
lean_closure_set(v___f_3540_, 1, v_asyncEnv_3538_);
lean_closure_set(v___f_3540_, 2, v_decl_3406_);
v___x_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3541_, 0, v_fst_3521_);
if (lean_obj_tag(v___y_3529_) == 0)
{
lean_inc_ref(v___x_3541_);
lean_inc(v_ref_3532_);
v___y_3443_ = v___f_3539_;
v___y_3444_ = v_ref_3532_;
v___y_3445_ = v___y_3527_;
v___y_3446_ = v___y_3530_;
v___y_3447_ = v_a_3536_;
v___y_3448_ = v___x_3541_;
v___y_3449_ = v___y_3528_;
v___y_3450_ = v___f_3540_;
v___y_3451_ = v_asyncEnv_3538_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_mainEnv_3537_;
v___y_3454_ = v___x_3541_;
goto v___jp_3442_;
}
else
{
lean_inc(v_ref_3532_);
v___y_3443_ = v___f_3539_;
v___y_3444_ = v_ref_3532_;
v___y_3445_ = v___y_3527_;
v___y_3446_ = v___y_3530_;
v___y_3447_ = v_a_3536_;
v___y_3448_ = v___x_3541_;
v___y_3449_ = v___y_3528_;
v___y_3450_ = v___f_3540_;
v___y_3451_ = v_asyncEnv_3538_;
v___y_3452_ = v___x_3533_;
v___y_3453_ = v_mainEnv_3537_;
v___y_3454_ = v___y_3529_;
goto v___jp_3442_;
}
}
else
{
lean_object* v_a_3542_; lean_object* v___x_3544_; uint8_t v_isShared_3545_; uint8_t v_isSharedCheck_3555_; 
lean_dec_ref(v___y_3530_);
lean_dec(v___y_3529_);
lean_dec(v_fst_3521_);
lean_dec(v_decl_3406_);
v_a_3542_ = lean_ctor_get(v___x_3535_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3535_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3544_ = v___x_3535_;
v_isShared_3545_ = v_isSharedCheck_3555_;
goto v_resetjp_3543_;
}
else
{
lean_inc(v_a_3542_);
lean_dec(v___x_3535_);
v___x_3544_ = lean_box(0);
v_isShared_3545_ = v_isSharedCheck_3555_;
goto v_resetjp_3543_;
}
v_resetjp_3543_:
{
lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3550_; 
v___x_3546_ = lean_io_error_to_string(v_a_3542_);
v___x_3547_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3547_, 0, v___x_3546_);
v___x_3548_ = l_Lean_MessageData_ofFormat(v___x_3547_);
lean_inc(v_ref_3532_);
if (v_isShared_3525_ == 0)
{
lean_ctor_set(v___x_3524_, 1, v___x_3548_);
lean_ctor_set(v___x_3524_, 0, v_ref_3532_);
v___x_3550_ = v___x_3524_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_ref_3532_);
lean_ctor_set(v_reuseFailAlloc_3554_, 1, v___x_3548_);
v___x_3550_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
lean_object* v___x_3552_; 
if (v_isShared_3545_ == 0)
{
lean_ctor_set(v___x_3544_, 0, v___x_3550_);
v___x_3552_ = v___x_3544_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
v___jp_3556_:
{
lean_object* v___x_3560_; 
v___x_3560_ = lean_st_ref_get(v___y_3559_);
if (lean_obj_tag(v_exportedInfo_x3f_3557_) == 0)
{
lean_object* v_env_3561_; lean_object* v___x_3562_; 
v_env_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref(v_env_3561_);
lean_dec(v___x_3560_);
v___x_3562_ = lean_box(0);
v___y_3527_ = v___y_3558_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v_exportedInfo_x3f_3557_;
v___y_3530_ = v_env_3561_;
v___y_3531_ = v___x_3562_;
goto v___jp_3526_;
}
else
{
lean_object* v_env_3563_; lean_object* v_val_3564_; uint8_t v___x_3565_; lean_object* v___x_3566_; lean_object* v___x_3567_; 
v_env_3563_ = lean_ctor_get(v___x_3560_, 0);
lean_inc_ref(v_env_3563_);
lean_dec(v___x_3560_);
v_val_3564_ = lean_ctor_get(v_exportedInfo_x3f_3557_, 0);
v___x_3565_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3564_);
v___x_3566_ = lean_box(v___x_3565_);
v___x_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3567_, 0, v___x_3566_);
v___y_3527_ = v___y_3558_;
v___y_3528_ = v___y_3559_;
v___y_3529_ = v_exportedInfo_x3f_3557_;
v___y_3530_ = v_env_3563_;
v___y_3531_ = v___x_3567_;
goto v___jp_3526_;
}
}
v___jp_3568_:
{
lean_object* v___x_3571_; 
lean_inc(v_fst_3521_);
v___x_3571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_fst_3521_);
v_exportedInfo_x3f_3557_ = v___x_3571_;
v___y_3558_ = v___y_3569_;
v___y_3559_ = v___y_3570_;
goto v___jp_3556_;
}
v___jp_3572_:
{
lean_object* v___x_3575_; 
lean_inc(v_fst_3521_);
v___x_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_fst_3521_);
v_exportedInfo_x3f_3557_ = v___x_3575_;
v___y_3558_ = v___y_3573_;
v___y_3559_ = v___y_3574_;
goto v___jp_3556_;
}
v___jp_3576_:
{
if (v___y_3579_ == 0)
{
lean_object* v_toCold_3580_; lean_object* v_options_3581_; uint8_t v_hasTrace_3582_; 
lean_dec(v_exportedInfo_x3f_3412_);
lean_dec_ref(v___x_3409_);
v_toCold_3580_ = lean_ctor_get(v___y_3577_, 0);
v_options_3581_ = lean_ctor_get(v_toCold_3580_, 2);
v_hasTrace_3582_ = lean_ctor_get_uint8(v_options_3581_, sizeof(void*)*1);
if (v_hasTrace_3582_ == 0)
{
lean_dec(v_cls_3408_);
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___y_3578_;
goto v___jp_3568_;
}
else
{
lean_object* v_inheritedTraceOptions_3583_; lean_object* v___x_3584_; lean_object* v___x_3585_; uint8_t v___x_3586_; 
v_inheritedTraceOptions_3583_ = lean_ctor_get(v_toCold_3580_, 11);
v___x_3584_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3408_);
v___x_3585_ = l_Lean_Name_append(v___x_3584_, v_cls_3408_);
v___x_3586_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3583_, v_options_3581_, v___x_3585_);
lean_dec(v___x_3585_);
if (v___x_3586_ == 0)
{
lean_dec(v_cls_3408_);
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___y_3578_;
goto v___jp_3568_;
}
else
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_3588_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3408_, v___x_3587_, v___y_3577_, v___y_3578_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_dec_ref_known(v___x_3588_, 1);
v___y_3569_ = v___y_3577_;
v___y_3570_ = v___y_3578_;
goto v___jp_3568_;
}
else
{
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec(v_fst_3517_);
lean_dec(v_decl_3406_);
return v___x_3588_;
}
}
}
}
else
{
lean_object* v___x_3589_; lean_object* v_env_3590_; lean_object* v_nextMacroScope_3591_; lean_object* v_ngen_3592_; lean_object* v_auxDeclNGen_3593_; lean_object* v_traceState_3594_; lean_object* v_recordedDeps_3595_; lean_object* v_messages_3596_; lean_object* v_infoState_3597_; lean_object* v_snapshotTasks_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3608_; 
lean_dec(v_cls_3408_);
v___x_3589_ = lean_st_ref_take(v___y_3578_);
v_env_3590_ = lean_ctor_get(v___x_3589_, 0);
v_nextMacroScope_3591_ = lean_ctor_get(v___x_3589_, 1);
v_ngen_3592_ = lean_ctor_get(v___x_3589_, 2);
v_auxDeclNGen_3593_ = lean_ctor_get(v___x_3589_, 3);
v_traceState_3594_ = lean_ctor_get(v___x_3589_, 4);
v_recordedDeps_3595_ = lean_ctor_get(v___x_3589_, 6);
v_messages_3596_ = lean_ctor_get(v___x_3589_, 7);
v_infoState_3597_ = lean_ctor_get(v___x_3589_, 8);
v_snapshotTasks_3598_ = lean_ctor_get(v___x_3589_, 9);
v_isSharedCheck_3608_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3608_ == 0)
{
lean_object* v_unused_3609_; 
v_unused_3609_ = lean_ctor_get(v___x_3589_, 5);
lean_dec(v_unused_3609_);
v___x_3600_ = v___x_3589_;
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_snapshotTasks_3598_);
lean_inc(v_infoState_3597_);
lean_inc(v_messages_3596_);
lean_inc(v_recordedDeps_3595_);
lean_inc(v_traceState_3594_);
lean_inc(v_auxDeclNGen_3593_);
lean_inc(v_ngen_3592_);
lean_inc(v_nextMacroScope_3591_);
lean_inc(v_env_3590_);
lean_dec(v___x_3589_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3608_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3602_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3522_);
lean_inc(v_fst_3517_);
v___x_3603_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3602_, v_env_3590_, v_fst_3517_, v_snd_3522_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 5, v___x_3409_);
lean_ctor_set(v___x_3600_, 0, v___x_3603_);
v___x_3605_ = v___x_3600_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3603_);
lean_ctor_set(v_reuseFailAlloc_3607_, 1, v_nextMacroScope_3591_);
lean_ctor_set(v_reuseFailAlloc_3607_, 2, v_ngen_3592_);
lean_ctor_set(v_reuseFailAlloc_3607_, 3, v_auxDeclNGen_3593_);
lean_ctor_set(v_reuseFailAlloc_3607_, 4, v_traceState_3594_);
lean_ctor_set(v_reuseFailAlloc_3607_, 5, v___x_3409_);
lean_ctor_set(v_reuseFailAlloc_3607_, 6, v_recordedDeps_3595_);
lean_ctor_set(v_reuseFailAlloc_3607_, 7, v_messages_3596_);
lean_ctor_set(v_reuseFailAlloc_3607_, 8, v_infoState_3597_);
lean_ctor_set(v_reuseFailAlloc_3607_, 9, v_snapshotTasks_3598_);
v___x_3605_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; 
v___x_3606_ = lean_st_ref_put(v___y_3578_, v___x_3605_);
v_exportedInfo_x3f_3557_ = v_exportedInfo_x3f_3412_;
v___y_3558_ = v___y_3577_;
v___y_3559_ = v___y_3578_;
goto v___jp_3556_;
}
}
}
}
v___jp_3610_:
{
lean_object* v___x_3613_; uint8_t v___x_3614_; 
lean_inc(v_decl_3406_);
v___x_3613_ = l_Lean_Declaration_getTopLevelNames(v_decl_3406_);
v___x_3614_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3613_);
lean_dec(v___x_3613_);
if (v___x_3614_ == 0)
{
lean_dec(v___x_3410_);
if (lean_obj_tag(v_exportedInfo_x3f_3412_) == 0)
{
v___y_3577_ = v___y_3611_;
v___y_3578_ = v___y_3612_;
v___y_3579_ = v___x_3614_;
goto v___jp_3576_;
}
else
{
v___y_3577_ = v___y_3611_;
v___y_3578_ = v___y_3612_;
v___y_3579_ = v___x_3407_;
goto v___jp_3576_;
}
}
else
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v_a_3617_; uint8_t v___x_3618_; 
lean_dec(v_exportedInfo_x3f_3412_);
lean_dec_ref(v___x_3409_);
v___x_3615_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3616_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3615_, v___y_3611_);
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref(v___x_3616_);
v___x_3618_ = lean_unbox(v_a_3617_);
lean_dec(v_a_3617_);
if (v___x_3618_ == 0)
{
lean_object* v_toCold_3619_; lean_object* v_options_3620_; uint8_t v_hasTrace_3621_; 
v_toCold_3619_ = lean_ctor_get(v___y_3611_, 0);
v_options_3620_ = lean_ctor_get(v_toCold_3619_, 2);
v_hasTrace_3621_ = lean_ctor_get_uint8(v_options_3620_, sizeof(void*)*1);
if (v_hasTrace_3621_ == 0)
{
lean_dec(v_cls_3408_);
v_exportedInfo_x3f_3557_ = v___x_3410_;
v___y_3558_ = v___y_3611_;
v___y_3559_ = v___y_3612_;
goto v___jp_3556_;
}
else
{
lean_object* v_inheritedTraceOptions_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; uint8_t v___x_3625_; 
v_inheritedTraceOptions_3622_ = lean_ctor_get(v_toCold_3619_, 11);
v___x_3623_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3408_);
v___x_3624_ = l_Lean_Name_append(v___x_3623_, v_cls_3408_);
v___x_3625_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3622_, v_options_3620_, v___x_3624_);
lean_dec(v___x_3624_);
if (v___x_3625_ == 0)
{
lean_dec(v_cls_3408_);
v_exportedInfo_x3f_3557_ = v___x_3410_;
v___y_3558_ = v___y_3611_;
v___y_3559_ = v___y_3612_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_3627_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3408_, v___x_3626_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3627_) == 0)
{
lean_dec_ref_known(v___x_3627_, 1);
v_exportedInfo_x3f_3557_ = v___x_3410_;
v___y_3558_ = v___y_3611_;
v___y_3559_ = v___y_3612_;
goto v___jp_3556_;
}
else
{
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec(v_fst_3517_);
lean_dec(v___x_3410_);
lean_dec(v_decl_3406_);
return v___x_3627_;
}
}
}
}
else
{
lean_object* v_toCold_3628_; lean_object* v_options_3629_; uint8_t v_hasTrace_3630_; 
lean_dec(v___x_3410_);
v_toCold_3628_ = lean_ctor_get(v___y_3611_, 0);
v_options_3629_ = lean_ctor_get(v_toCold_3628_, 2);
v_hasTrace_3630_ = lean_ctor_get_uint8(v_options_3629_, sizeof(void*)*1);
if (v_hasTrace_3630_ == 0)
{
lean_dec(v_cls_3408_);
v___y_3573_ = v___y_3611_;
v___y_3574_ = v___y_3612_;
goto v___jp_3572_;
}
else
{
lean_object* v_inheritedTraceOptions_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; uint8_t v___x_3634_; 
v_inheritedTraceOptions_3631_ = lean_ctor_get(v_toCold_3628_, 11);
v___x_3632_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3408_);
v___x_3633_ = l_Lean_Name_append(v___x_3632_, v_cls_3408_);
v___x_3634_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3631_, v_options_3629_, v___x_3633_);
lean_dec(v___x_3633_);
if (v___x_3634_ == 0)
{
lean_dec(v_cls_3408_);
v___y_3573_ = v___y_3611_;
v___y_3574_ = v___y_3612_;
goto v___jp_3572_;
}
else
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_3636_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3408_, v___x_3635_, v___y_3611_, v___y_3612_);
if (lean_obj_tag(v___x_3636_) == 0)
{
lean_dec_ref_known(v___x_3636_, 1);
v___y_3573_ = v___y_3611_;
v___y_3574_ = v___y_3612_;
goto v___jp_3572_;
}
else
{
lean_del_object(v___x_3524_);
lean_dec(v_snd_3522_);
lean_dec(v_fst_3521_);
lean_dec(v_fst_3517_);
lean_dec(v_decl_3406_);
return v___x_3636_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed(lean_object* v_decl_3649_, lean_object* v___x_3650_, lean_object* v_cls_3651_, lean_object* v___x_3652_, lean_object* v___x_3653_, lean_object* v_____x_3654_, lean_object* v_exportedInfo_x3f_3655_, lean_object* v___y_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_){
_start:
{
uint8_t v___x_53992__boxed_3659_; lean_object* v_res_3660_; 
v___x_53992__boxed_3659_ = lean_unbox(v___x_3650_);
v_res_3660_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3649_, v___x_53992__boxed_3659_, v_cls_3651_, v___x_3652_, v___x_3653_, v_____x_3654_, v_exportedInfo_x3f_3655_, v___y_3656_, v___y_3657_);
lean_dec(v___y_3657_);
lean_dec_ref(v___y_3656_);
return v_res_3660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(lean_object* v___f_3661_, uint8_t v_forceExpose_3662_, uint8_t v___x_3663_, lean_object* v___x_3664_, lean_object* v_cls_3665_, lean_object* v_defn_3666_, lean_object* v___y_3667_, lean_object* v___y_3668_){
_start:
{
lean_object* v_exportedInfo_x3f_3671_; lean_object* v___y_3672_; lean_object* v___y_3673_; lean_object* v___y_3683_; lean_object* v___y_3684_; lean_object* v___y_3685_; uint8_t v___y_3686_; lean_object* v___x_3690_; lean_object* v_env_3691_; lean_object* v___x_3692_; 
v___x_3690_ = lean_st_ref_get(v___y_3668_);
v_env_3691_ = lean_ctor_get(v___x_3690_, 0);
lean_inc_ref(v_env_3691_);
lean_dec(v___x_3690_);
v___x_3692_ = lean_st_ref_get(v___y_3668_);
if (v_forceExpose_3662_ == 0)
{
if (v___x_3663_ == 0)
{
lean_dec(v___x_3692_);
lean_dec_ref(v_env_3691_);
lean_dec(v_cls_3665_);
v_exportedInfo_x3f_3671_ = v___x_3664_;
v___y_3672_ = v___y_3667_;
v___y_3673_ = v___y_3668_;
goto v___jp_3670_;
}
else
{
lean_object* v_env_3693_; lean_object* v___x_3694_; uint8_t v_isModule_3695_; 
v_env_3693_ = lean_ctor_get(v___x_3692_, 0);
lean_inc_ref(v_env_3693_);
lean_dec(v___x_3692_);
v___x_3694_ = l_Lean_Environment_header(v_env_3691_);
lean_dec_ref(v_env_3691_);
v_isModule_3695_ = lean_ctor_get_uint8(v___x_3694_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3694_);
if (v_isModule_3695_ == 0)
{
lean_dec_ref(v_env_3693_);
lean_dec(v_cls_3665_);
v_exportedInfo_x3f_3671_ = v___x_3664_;
v___y_3672_ = v___y_3667_;
v___y_3673_ = v___y_3668_;
goto v___jp_3670_;
}
else
{
uint8_t v_isExporting_3696_; lean_object* v___y_3698_; lean_object* v___y_3699_; 
v_isExporting_3696_ = lean_ctor_get_uint8(v_env_3693_, sizeof(void*)*8);
lean_dec_ref(v_env_3693_);
if (v_isExporting_3696_ == 0)
{
lean_object* v_toCold_3704_; lean_object* v_options_3705_; uint8_t v_hasTrace_3706_; 
lean_dec(v___x_3664_);
v_toCold_3704_ = lean_ctor_get(v___y_3667_, 0);
v_options_3705_ = lean_ctor_get(v_toCold_3704_, 2);
v_hasTrace_3706_ = lean_ctor_get_uint8(v_options_3705_, sizeof(void*)*1);
if (v_hasTrace_3706_ == 0)
{
lean_dec(v_cls_3665_);
v___y_3698_ = v___y_3667_;
v___y_3699_ = v___y_3668_;
goto v___jp_3697_;
}
else
{
lean_object* v_inheritedTraceOptions_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v_inheritedTraceOptions_3707_ = lean_ctor_get(v_toCold_3704_, 11);
v___x_3708_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3665_);
v___x_3709_ = l_Lean_Name_append(v___x_3708_, v_cls_3665_);
v___x_3710_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3707_, v_options_3705_, v___x_3709_);
lean_dec(v___x_3709_);
if (v___x_3710_ == 0)
{
lean_dec(v_cls_3665_);
v___y_3698_ = v___y_3667_;
v___y_3699_ = v___y_3668_;
goto v___jp_3697_;
}
else
{
lean_object* v_toConstantVal_3711_; lean_object* v_name_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_toConstantVal_3711_ = lean_ctor_get(v_defn_3666_, 0);
v_name_3712_ = lean_ctor_get(v_toConstantVal_3711_, 0);
v___x_3713_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_3712_);
v___x_3714_ = l_Lean_MessageData_ofName(v_name_3712_);
v___x_3715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3715_, 0, v___x_3713_);
lean_ctor_set(v___x_3715_, 1, v___x_3714_);
v___x_3716_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_3717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3715_);
lean_ctor_set(v___x_3717_, 1, v___x_3716_);
v___x_3718_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3665_, v___x_3717_, v___y_3667_, v___y_3668_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_dec_ref_known(v___x_3718_, 1);
v___y_3698_ = v___y_3667_;
v___y_3699_ = v___y_3668_;
goto v___jp_3697_;
}
else
{
lean_dec_ref(v_defn_3666_);
lean_dec_ref(v___f_3661_);
return v___x_3718_;
}
}
}
}
else
{
lean_dec(v_cls_3665_);
v_exportedInfo_x3f_3671_ = v___x_3664_;
v___y_3672_ = v___y_3667_;
v___y_3673_ = v___y_3668_;
goto v___jp_3670_;
}
v___jp_3697_:
{
lean_object* v_toConstantVal_3700_; uint8_t v_safety_3701_; uint8_t v___x_3702_; uint8_t v___x_3703_; 
v_toConstantVal_3700_ = lean_ctor_get(v_defn_3666_, 0);
v_safety_3701_ = lean_ctor_get_uint8(v_defn_3666_, sizeof(void*)*4);
v___x_3702_ = 1;
v___x_3703_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3701_, v___x_3702_);
if (v___x_3703_ == 0)
{
lean_inc_ref(v_toConstantVal_3700_);
v___y_3683_ = v___y_3698_;
v___y_3684_ = v_toConstantVal_3700_;
v___y_3685_ = v___y_3699_;
v___y_3686_ = v_isModule_3695_;
goto v___jp_3682_;
}
else
{
lean_inc_ref(v_toConstantVal_3700_);
v___y_3683_ = v___y_3698_;
v___y_3684_ = v_toConstantVal_3700_;
v___y_3685_ = v___y_3699_;
v___y_3686_ = v_isExporting_3696_;
goto v___jp_3682_;
}
}
}
}
}
else
{
lean_dec(v___x_3692_);
lean_dec_ref(v_env_3691_);
lean_dec(v_cls_3665_);
v_exportedInfo_x3f_3671_ = v___x_3664_;
v___y_3672_ = v___y_3667_;
v___y_3673_ = v___y_3668_;
goto v___jp_3670_;
}
v___jp_3670_:
{
lean_object* v_toConstantVal_3674_; lean_object* v_name_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; 
v_toConstantVal_3674_ = lean_ctor_get(v_defn_3666_, 0);
v_name_3675_ = lean_ctor_get(v_toConstantVal_3674_, 0);
lean_inc(v_name_3675_);
v___x_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3676_, 0, v_defn_3666_);
v___x_3677_ = 0;
v___x_3678_ = lean_box(v___x_3677_);
v___x_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3679_, 0, v___x_3676_);
lean_ctor_set(v___x_3679_, 1, v___x_3678_);
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v_name_3675_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
lean_inc(v___y_3673_);
lean_inc_ref(v___y_3672_);
v___x_3681_ = lean_apply_5(v___f_3661_, v___x_3680_, v_exportedInfo_x3f_3671_, v___y_3672_, v___y_3673_, lean_box(0));
return v___x_3681_;
}
v___jp_3682_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3689_; 
v___x_3687_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3687_, 0, v___y_3684_);
lean_ctor_set_uint8(v___x_3687_, sizeof(void*)*1, v___y_3686_);
v___x_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
v_exportedInfo_x3f_3671_ = v___x_3689_;
v___y_3672_ = v___y_3683_;
v___y_3673_ = v___y_3685_;
goto v___jp_3670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11___boxed(lean_object* v___f_3719_, lean_object* v_forceExpose_3720_, lean_object* v___x_3721_, lean_object* v___x_3722_, lean_object* v_cls_3723_, lean_object* v_defn_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
uint8_t v_forceExpose_boxed_3728_; uint8_t v___x_54468__boxed_3729_; lean_object* v_res_3730_; 
v_forceExpose_boxed_3728_ = lean_unbox(v_forceExpose_3720_);
v___x_54468__boxed_3729_ = lean_unbox(v___x_3721_);
v_res_3730_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_3719_, v_forceExpose_boxed_3728_, v___x_54468__boxed_3729_, v___x_3722_, v_cls_3723_, v_defn_3724_, v___y_3725_, v___y_3726_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3730_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_val_3731_, lean_object* v___f_3732_, lean_object* v_____r_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_){
_start:
{
lean_object* v_toConstantVal_3737_; uint8_t v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; 
v_toConstantVal_3737_ = lean_ctor_get(v_val_3731_, 0);
v___x_3738_ = 0;
lean_inc_ref(v_toConstantVal_3737_);
v___x_3739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3739_, 0, v_toConstantVal_3737_);
lean_ctor_set_uint8(v___x_3739_, sizeof(void*)*1, v___x_3738_);
v___x_3740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3739_);
v___x_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3740_);
v___x_3742_ = lean_box(0);
lean_inc(v___y_3735_);
lean_inc_ref(v___y_3734_);
v___x_3743_ = lean_apply_5(v___f_3732_, v___x_3742_, v___x_3741_, v___y_3734_, v___y_3735_, lean_box(0));
return v___x_3743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_val_3744_, lean_object* v___f_3745_, lean_object* v_____r_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_){
_start:
{
lean_object* v_res_3750_; 
v_res_3750_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_3744_, v___f_3745_, v_____r_3746_, v___y_3747_, v___y_3748_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_val_3744_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3751_, lean_object* v_x_3752_){
_start:
{
if (lean_obj_tag(v_x_3752_) == 0)
{
return v_x_3751_;
}
else
{
lean_object* v_head_3753_; lean_object* v_tail_3754_; lean_object* v___x_3755_; 
v_head_3753_ = lean_ctor_get(v_x_3752_, 0);
lean_inc(v_head_3753_);
v_tail_3754_ = lean_ctor_get(v_x_3752_, 1);
lean_inc(v_tail_3754_);
lean_dec_ref_known(v_x_3752_, 2);
v___x_3755_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3751_, v_head_3753_);
v_x_3751_ = v___x_3755_;
v_x_3752_ = v_tail_3754_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; 
v_cls_3757_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3758_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3759_ = l_Lean_Name_append(v___x_3758_, v_cls_3757_);
return v___x_3759_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3761_; lean_object* v___x_3762_; 
v___x_3761_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3762_ = l_Lean_stringToMessageData(v___x_3761_);
return v___x_3762_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3765_ = l_Lean_stringToMessageData(v___x_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3766_, uint8_t v_forceExpose_3767_, lean_object* v_a_3768_, lean_object* v_a_3769_){
_start:
{
lean_object* v___y_3772_; lean_object* v___y_3773_; lean_object* v_a_3774_; lean_object* v___y_3785_; lean_object* v___y_3786_; lean_object* v_a_3787_; lean_object* v___y_3798_; lean_object* v___y_3799_; lean_object* v_a_3800_; lean_object* v___y_3811_; lean_object* v___y_3812_; lean_object* v_a_3813_; lean_object* v_toCold_3823_; lean_object* v_options_3824_; lean_object* v_inheritedTraceOptions_3825_; uint8_t v_hasTrace_3826_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; lean_object* v___y_3831_; lean_object* v___y_3832_; lean_object* v___y_3833_; lean_object* v___y_3834_; lean_object* v___y_3835_; uint8_t v___y_3836_; lean_object* v___y_3837_; lean_object* v___y_3838_; lean_object* v___y_3839_; lean_object* v___y_3902_; lean_object* v___y_3903_; uint8_t v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3932_; uint8_t v___y_3933_; lean_object* v___y_3934_; lean_object* v_exportedInfo_x3f_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3947_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3954_; uint8_t v___y_3955_; lean_object* v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v_cls_3960_; lean_object* v___y_3962_; lean_object* v_options_3963_; lean_object* v_inheritedTraceOptions_3964_; lean_object* v___y_3965_; 
v_toCold_3823_ = lean_ctor_get(v_a_3768_, 0);
v_options_3824_ = lean_ctor_get(v_toCold_3823_, 2);
v_inheritedTraceOptions_3825_ = lean_ctor_get(v_toCold_3823_, 11);
v_hasTrace_3826_ = lean_ctor_get_uint8(v_options_3824_, sizeof(void*)*1);
v_cls_3960_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3826_ == 0)
{
lean_object* v___x_3972_; lean_object* v_env_3973_; lean_object* v_nextMacroScope_3974_; lean_object* v_ngen_3975_; lean_object* v_auxDeclNGen_3976_; lean_object* v_traceState_3977_; lean_object* v_recordedDeps_3978_; lean_object* v_messages_3979_; lean_object* v_infoState_3980_; lean_object* v_snapshotTasks_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4184_; 
v___x_3972_ = lean_st_ref_take(v_a_3769_);
v_env_3973_ = lean_ctor_get(v___x_3972_, 0);
v_nextMacroScope_3974_ = lean_ctor_get(v___x_3972_, 1);
v_ngen_3975_ = lean_ctor_get(v___x_3972_, 2);
v_auxDeclNGen_3976_ = lean_ctor_get(v___x_3972_, 3);
v_traceState_3977_ = lean_ctor_get(v___x_3972_, 4);
v_recordedDeps_3978_ = lean_ctor_get(v___x_3972_, 6);
v_messages_3979_ = lean_ctor_get(v___x_3972_, 7);
v_infoState_3980_ = lean_ctor_get(v___x_3972_, 8);
v_snapshotTasks_3981_ = lean_ctor_get(v___x_3972_, 9);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___x_3972_);
if (v_isSharedCheck_4184_ == 0)
{
lean_object* v_unused_4185_; 
v_unused_4185_ = lean_ctor_get(v___x_3972_, 5);
lean_dec(v_unused_4185_);
v___x_3983_ = v___x_3972_;
v_isShared_3984_ = v_isSharedCheck_4184_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_snapshotTasks_3981_);
lean_inc(v_infoState_3980_);
lean_inc(v_messages_3979_);
lean_inc(v_recordedDeps_3978_);
lean_inc(v_traceState_3977_);
lean_inc(v_auxDeclNGen_3976_);
lean_inc(v_ngen_3975_);
lean_inc(v_nextMacroScope_3974_);
lean_inc(v_env_3973_);
lean_dec(v___x_3972_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4184_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3985_; lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; uint8_t v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___x_4018_; 
lean_inc(v_decl_3766_);
v___x_3985_ = l_Lean_Declaration_getNames(v_decl_3766_);
v___x_3986_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3973_, v___x_3985_);
v___x_3987_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 5, v___x_3987_);
lean_ctor_set(v___x_3983_, 0, v___x_3986_);
v___x_4018_ = v___x_3983_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v___x_3986_);
lean_ctor_set(v_reuseFailAlloc_4183_, 1, v_nextMacroScope_3974_);
lean_ctor_set(v_reuseFailAlloc_4183_, 2, v_ngen_3975_);
lean_ctor_set(v_reuseFailAlloc_4183_, 3, v_auxDeclNGen_3976_);
lean_ctor_set(v_reuseFailAlloc_4183_, 4, v_traceState_3977_);
lean_ctor_set(v_reuseFailAlloc_4183_, 5, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_4183_, 6, v_recordedDeps_3978_);
lean_ctor_set(v_reuseFailAlloc_4183_, 7, v_messages_3979_);
lean_ctor_set(v_reuseFailAlloc_4183_, 8, v_infoState_3980_);
lean_ctor_set(v_reuseFailAlloc_4183_, 9, v_snapshotTasks_3981_);
v___x_4018_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4017_;
}
v___jp_3988_:
{
lean_object* v___x_3995_; lean_object* v_env_3996_; lean_object* v_nextMacroScope_3997_; lean_object* v_ngen_3998_; lean_object* v_auxDeclNGen_3999_; lean_object* v_traceState_4000_; lean_object* v_recordedDeps_4001_; lean_object* v_messages_4002_; lean_object* v_infoState_4003_; lean_object* v_snapshotTasks_4004_; lean_object* v___x_4006_; uint8_t v_isShared_4007_; uint8_t v_isSharedCheck_4015_; 
v___x_3995_ = lean_st_ref_take(v___y_3989_);
v_env_3996_ = lean_ctor_get(v___x_3995_, 0);
v_nextMacroScope_3997_ = lean_ctor_get(v___x_3995_, 1);
v_ngen_3998_ = lean_ctor_get(v___x_3995_, 2);
v_auxDeclNGen_3999_ = lean_ctor_get(v___x_3995_, 3);
v_traceState_4000_ = lean_ctor_get(v___x_3995_, 4);
v_recordedDeps_4001_ = lean_ctor_get(v___x_3995_, 6);
v_messages_4002_ = lean_ctor_get(v___x_3995_, 7);
v_infoState_4003_ = lean_ctor_get(v___x_3995_, 8);
v_snapshotTasks_4004_ = lean_ctor_get(v___x_3995_, 9);
v_isSharedCheck_4015_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4015_ == 0)
{
lean_object* v_unused_4016_; 
v_unused_4016_ = lean_ctor_get(v___x_3995_, 5);
lean_dec(v_unused_4016_);
v___x_4006_ = v___x_3995_;
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
else
{
lean_inc(v_snapshotTasks_4004_);
lean_inc(v_infoState_4003_);
lean_inc(v_messages_4002_);
lean_inc(v_recordedDeps_4001_);
lean_inc(v_traceState_4000_);
lean_inc(v_auxDeclNGen_3999_);
lean_inc(v_ngen_3998_);
lean_inc(v_nextMacroScope_3997_);
lean_inc(v_env_3996_);
lean_dec(v___x_3995_);
v___x_4006_ = lean_box(0);
v_isShared_4007_ = v_isSharedCheck_4015_;
goto v_resetjp_4005_;
}
v_resetjp_4005_:
{
lean_object* v___x_4008_; lean_object* v___x_4009_; lean_object* v___x_4010_; lean_object* v___x_4012_; 
v___x_4008_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4009_ = lean_box(v___y_3992_);
lean_inc(v___y_3990_);
v___x_4010_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4008_, v_env_3996_, v___y_3990_, v___x_4009_);
if (v_isShared_4007_ == 0)
{
lean_ctor_set(v___x_4006_, 5, v___x_3987_);
lean_ctor_set(v___x_4006_, 0, v___x_4010_);
v___x_4012_ = v___x_4006_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4014_; 
v_reuseFailAlloc_4014_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4014_, 0, v___x_4010_);
lean_ctor_set(v_reuseFailAlloc_4014_, 1, v_nextMacroScope_3997_);
lean_ctor_set(v_reuseFailAlloc_4014_, 2, v_ngen_3998_);
lean_ctor_set(v_reuseFailAlloc_4014_, 3, v_auxDeclNGen_3999_);
lean_ctor_set(v_reuseFailAlloc_4014_, 4, v_traceState_4000_);
lean_ctor_set(v_reuseFailAlloc_4014_, 5, v___x_3987_);
lean_ctor_set(v_reuseFailAlloc_4014_, 6, v_recordedDeps_4001_);
lean_ctor_set(v_reuseFailAlloc_4014_, 7, v_messages_4002_);
lean_ctor_set(v_reuseFailAlloc_4014_, 8, v_infoState_4003_);
lean_ctor_set(v_reuseFailAlloc_4014_, 9, v_snapshotTasks_4004_);
v___x_4012_ = v_reuseFailAlloc_4014_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
lean_object* v___x_4013_; 
v___x_4013_ = lean_st_ref_put(v___y_3989_, v___x_4012_);
v___y_3932_ = v___y_3990_;
v___y_3933_ = v___y_3992_;
v___y_3934_ = v___y_3993_;
v_exportedInfo_x3f_3935_ = v___y_3991_;
v___y_3936_ = v___y_3994_;
v___y_3937_ = v___y_3989_;
goto v___jp_3931_;
}
}
}
v_reusejp_4017_:
{
lean_object* v___x_4019_; lean_object* v___x_4020_; lean_object* v___y_4022_; uint8_t v___y_4023_; lean_object* v___y_4024_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v_fst_4059_; lean_object* v_fst_4060_; uint8_t v_snd_4061_; lean_object* v_exportedInfo_x3f_4062_; lean_object* v___y_4063_; lean_object* v___y_4064_; lean_object* v___y_4074_; lean_object* v_exportedInfo_x3f_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4083_; lean_object* v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; uint8_t v___y_4087_; lean_object* v___y_4092_; lean_object* v_toConstantVal_4093_; uint8_t v_safety_4094_; uint8_t v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4101_; uint8_t v___y_4102_; lean_object* v___y_4103_; lean_object* v___y_4104_; lean_object* v_defn_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; 
v___x_4019_ = lean_st_ref_put(v_a_3769_, v___x_4018_);
v___x_4020_ = lean_box(0);
switch(lean_obj_tag(v_decl_3766_))
{
case 2:
{
lean_object* v_val_4133_; lean_object* v_exportedInfo_x3f_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___x_4142_; 
v_val_4133_ = lean_ctor_get(v_decl_3766_, 0);
v___x_4142_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4143_; lean_object* v___x_4144_; uint8_t v_isModule_4145_; 
v_env_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc_ref(v_env_4143_);
lean_dec(v___x_4142_);
v___x_4144_ = l_Lean_Environment_header(v_env_4143_);
lean_dec_ref(v_env_4143_);
v_isModule_4145_ = lean_ctor_get_uint8(v___x_4144_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4144_);
if (v_isModule_4145_ == 0)
{
v_exportedInfo_x3f_4135_ = v___x_4020_;
v___y_4136_ = v_a_3768_;
v___y_4137_ = v_a_3769_;
goto v___jp_4134_;
}
else
{
lean_object* v_toConstantVal_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
v_toConstantVal_4146_ = lean_ctor_get(v_val_4133_, 0);
lean_inc_ref(v_toConstantVal_4146_);
v___x_4147_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4147_, 0, v_toConstantVal_4146_);
lean_ctor_set_uint8(v___x_4147_, sizeof(void*)*1, v_hasTrace_3826_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
v_exportedInfo_x3f_4135_ = v___x_4149_;
v___y_4136_ = v_a_3768_;
v___y_4137_ = v_a_3769_;
goto v___jp_4134_;
}
}
else
{
lean_dec(v___x_4142_);
v_exportedInfo_x3f_4135_ = v___x_4020_;
v___y_4136_ = v_a_3768_;
v___y_4137_ = v_a_3769_;
goto v___jp_4134_;
}
v___jp_4134_:
{
lean_object* v_toConstantVal_4138_; lean_object* v_name_4139_; lean_object* v___x_4140_; uint8_t v___x_4141_; 
v_toConstantVal_4138_ = lean_ctor_get(v_val_4133_, 0);
v_name_4139_ = lean_ctor_get(v_toConstantVal_4138_, 0);
lean_inc_ref(v_val_4133_);
v___x_4140_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4140_, 0, v_val_4133_);
v___x_4141_ = 1;
lean_inc(v_name_4139_);
v_fst_4059_ = v_name_4139_;
v_fst_4060_ = v___x_4140_;
v_snd_4061_ = v___x_4141_;
v_exportedInfo_x3f_4062_ = v_exportedInfo_x3f_4135_;
v___y_4063_ = v___y_4136_;
v___y_4064_ = v___y_4137_;
goto v___jp_4058_;
}
}
case 1:
{
lean_object* v_val_4150_; 
v_val_4150_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref(v_val_4150_);
v_defn_4108_ = v_val_4150_;
v___y_4109_ = v_a_3768_;
v___y_4110_ = v_a_3769_;
goto v___jp_4107_;
}
case 5:
{
lean_object* v_defns_4151_; 
v_defns_4151_ = lean_ctor_get(v_decl_3766_, 0);
if (lean_obj_tag(v_defns_4151_) == 1)
{
lean_object* v_tail_4152_; 
v_tail_4152_ = lean_ctor_get(v_defns_4151_, 1);
if (lean_obj_tag(v_tail_4152_) == 0)
{
lean_object* v_head_4153_; 
v_head_4153_ = lean_ctor_get(v_defns_4151_, 0);
lean_inc(v_head_4153_);
v_defn_4108_ = v_head_4153_;
v___y_4109_ = v_a_3768_;
v___y_4110_ = v_a_3769_;
goto v___jp_4107_;
}
else
{
lean_object* v___x_4154_; 
v___x_4154_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v_a_3768_, v_a_3769_);
return v___x_4154_;
}
}
else
{
lean_object* v___x_4155_; 
v___x_4155_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v_a_3768_, v_a_3769_);
return v___x_4155_;
}
}
case 3:
{
lean_object* v_val_4156_; lean_object* v_exportedInfo_x3f_4158_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v___x_4165_; lean_object* v_env_4166_; lean_object* v___x_4167_; 
v_val_4156_ = lean_ctor_get(v_decl_3766_, 0);
v___x_4165_ = lean_st_ref_get(v_a_3769_);
v_env_4166_ = lean_ctor_get(v___x_4165_, 0);
lean_inc_ref(v_env_4166_);
lean_dec(v___x_4165_);
v___x_4167_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4168_; lean_object* v___x_4169_; uint8_t v_isModule_4170_; 
v_env_4168_ = lean_ctor_get(v___x_4167_, 0);
lean_inc_ref(v_env_4168_);
lean_dec(v___x_4167_);
v___x_4169_ = l_Lean_Environment_header(v_env_4166_);
lean_dec_ref(v_env_4166_);
v_isModule_4170_ = lean_ctor_get_uint8(v___x_4169_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4169_);
if (v_isModule_4170_ == 0)
{
lean_dec_ref(v_env_4168_);
v_exportedInfo_x3f_4158_ = v___x_4020_;
v___y_4159_ = v_a_3768_;
v___y_4160_ = v_a_3769_;
goto v___jp_4157_;
}
else
{
uint8_t v_isExporting_4171_; 
v_isExporting_4171_ = lean_ctor_get_uint8(v_env_4168_, sizeof(void*)*8);
lean_dec_ref(v_env_4168_);
if (v_isExporting_4171_ == 0)
{
lean_object* v_toConstantVal_4172_; uint8_t v_isUnsafe_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v_toConstantVal_4172_ = lean_ctor_get(v_val_4156_, 0);
v_isUnsafe_4173_ = lean_ctor_get_uint8(v_val_4156_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4172_);
v___x_4174_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4174_, 0, v_toConstantVal_4172_);
lean_ctor_set_uint8(v___x_4174_, sizeof(void*)*1, v_isUnsafe_4173_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
v___x_4176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
v_exportedInfo_x3f_4158_ = v___x_4176_;
v___y_4159_ = v_a_3768_;
v___y_4160_ = v_a_3769_;
goto v___jp_4157_;
}
else
{
v_exportedInfo_x3f_4158_ = v___x_4020_;
v___y_4159_ = v_a_3768_;
v___y_4160_ = v_a_3769_;
goto v___jp_4157_;
}
}
}
else
{
lean_dec(v___x_4167_);
lean_dec_ref(v_env_4166_);
v_exportedInfo_x3f_4158_ = v___x_4020_;
v___y_4159_ = v_a_3768_;
v___y_4160_ = v_a_3769_;
goto v___jp_4157_;
}
v___jp_4157_:
{
lean_object* v_toConstantVal_4161_; lean_object* v_name_4162_; lean_object* v___x_4163_; uint8_t v___x_4164_; 
v_toConstantVal_4161_ = lean_ctor_get(v_val_4156_, 0);
v_name_4162_ = lean_ctor_get(v_toConstantVal_4161_, 0);
lean_inc_ref(v_val_4156_);
v___x_4163_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4163_, 0, v_val_4156_);
v___x_4164_ = 3;
lean_inc(v_name_4162_);
v_fst_4059_ = v_name_4162_;
v_fst_4060_ = v___x_4163_;
v_snd_4061_ = v___x_4164_;
v_exportedInfo_x3f_4062_ = v_exportedInfo_x3f_4158_;
v___y_4063_ = v___y_4159_;
v___y_4064_ = v___y_4160_;
goto v___jp_4058_;
}
}
case 0:
{
lean_object* v_val_4177_; lean_object* v_toConstantVal_4178_; lean_object* v_name_4179_; lean_object* v___x_4180_; uint8_t v___x_4181_; 
v_val_4177_ = lean_ctor_get(v_decl_3766_, 0);
v_toConstantVal_4178_ = lean_ctor_get(v_val_4177_, 0);
v_name_4179_ = lean_ctor_get(v_toConstantVal_4178_, 0);
lean_inc_ref(v_val_4177_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v_val_4177_);
v___x_4181_ = 2;
lean_inc(v_name_4179_);
v_fst_4059_ = v_name_4179_;
v_fst_4060_ = v___x_4180_;
v_snd_4061_ = v___x_4181_;
v_exportedInfo_x3f_4062_ = v___x_4020_;
v___y_4063_ = v_a_3768_;
v___y_4064_ = v_a_3769_;
goto v___jp_4058_;
}
default: 
{
lean_object* v___x_4182_; 
v___x_4182_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v_a_3768_, v_a_3769_);
return v___x_4182_;
}
}
v___jp_4021_:
{
lean_object* v___x_4028_; uint8_t v___x_4029_; 
lean_inc(v_decl_3766_);
v___x_4028_ = l_Lean_Declaration_getTopLevelNames(v_decl_3766_);
v___x_4029_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4028_);
lean_dec(v___x_4028_);
if (v___x_4029_ == 0)
{
if (lean_obj_tag(v___y_4024_) == 0)
{
if (v___x_4029_ == 0)
{
lean_object* v_toCold_4030_; lean_object* v_options_4031_; uint8_t v_hasTrace_4032_; 
v_toCold_4030_ = lean_ctor_get(v___y_4026_, 0);
v_options_4031_ = lean_ctor_get(v_toCold_4030_, 2);
v_hasTrace_4032_ = lean_ctor_get_uint8(v_options_4031_, sizeof(void*)*1);
if (v_hasTrace_4032_ == 0)
{
v___y_3954_ = v___y_4022_;
v___y_3955_ = v___y_4023_;
v___y_3956_ = v___y_4025_;
v___y_3957_ = v___y_4026_;
v___y_3958_ = v___y_4027_;
goto v___jp_3953_;
}
else
{
lean_object* v_inheritedTraceOptions_4033_; lean_object* v___x_4034_; uint8_t v___x_4035_; 
v_inheritedTraceOptions_4033_ = lean_ctor_get(v_toCold_4030_, 11);
v___x_4034_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4035_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4033_, v_options_4031_, v___x_4034_);
if (v___x_4035_ == 0)
{
v___y_3954_ = v___y_4022_;
v___y_3955_ = v___y_4023_;
v___y_3956_ = v___y_4025_;
v___y_3957_ = v___y_4026_;
v___y_3958_ = v___y_4027_;
goto v___jp_3953_;
}
else
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4037_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4036_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_dec_ref_known(v___x_4037_, 1);
v___y_3954_ = v___y_4022_;
v___y_3955_ = v___y_4023_;
v___y_3956_ = v___y_4025_;
v___y_3957_ = v___y_4026_;
v___y_3958_ = v___y_4027_;
goto v___jp_3953_;
}
else
{
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4022_);
lean_dec(v_decl_3766_);
return v___x_4037_;
}
}
}
}
else
{
v___y_3989_ = v___y_4027_;
v___y_3990_ = v___y_4022_;
v___y_3991_ = v___y_4024_;
v___y_3992_ = v___y_4023_;
v___y_3993_ = v___y_4025_;
v___y_3994_ = v___y_4026_;
goto v___jp_3988_;
}
}
else
{
v___y_3989_ = v___y_4027_;
v___y_3990_ = v___y_4022_;
v___y_3991_ = v___y_4024_;
v___y_3992_ = v___y_4023_;
v___y_3993_ = v___y_4025_;
v___y_3994_ = v___y_4026_;
goto v___jp_3988_;
}
}
else
{
lean_object* v___x_4038_; lean_object* v___x_4039_; lean_object* v_a_4040_; uint8_t v___x_4041_; 
lean_dec(v___y_4024_);
v___x_4038_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4039_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4038_, v___y_4026_);
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
v___x_4041_ = lean_unbox(v_a_4040_);
lean_dec(v_a_4040_);
if (v___x_4041_ == 0)
{
lean_object* v_toCold_4042_; lean_object* v_options_4043_; uint8_t v_hasTrace_4044_; 
v_toCold_4042_ = lean_ctor_get(v___y_4026_, 0);
v_options_4043_ = lean_ctor_get(v_toCold_4042_, 2);
v_hasTrace_4044_ = lean_ctor_get_uint8(v_options_4043_, sizeof(void*)*1);
if (v_hasTrace_4044_ == 0)
{
v___y_3932_ = v___y_4022_;
v___y_3933_ = v___y_4023_;
v___y_3934_ = v___y_4025_;
v_exportedInfo_x3f_3935_ = v___x_4020_;
v___y_3936_ = v___y_4026_;
v___y_3937_ = v___y_4027_;
goto v___jp_3931_;
}
else
{
lean_object* v_inheritedTraceOptions_4045_; lean_object* v___x_4046_; uint8_t v___x_4047_; 
v_inheritedTraceOptions_4045_ = lean_ctor_get(v_toCold_4042_, 11);
v___x_4046_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4047_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4045_, v_options_4043_, v___x_4046_);
if (v___x_4047_ == 0)
{
v___y_3932_ = v___y_4022_;
v___y_3933_ = v___y_4023_;
v___y_3934_ = v___y_4025_;
v_exportedInfo_x3f_3935_ = v___x_4020_;
v___y_3936_ = v___y_4026_;
v___y_3937_ = v___y_4027_;
goto v___jp_3931_;
}
else
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4049_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4048_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_dec_ref_known(v___x_4049_, 1);
v___y_3932_ = v___y_4022_;
v___y_3933_ = v___y_4023_;
v___y_3934_ = v___y_4025_;
v_exportedInfo_x3f_3935_ = v___x_4020_;
v___y_3936_ = v___y_4026_;
v___y_3937_ = v___y_4027_;
goto v___jp_3931_;
}
else
{
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4022_);
lean_dec(v_decl_3766_);
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_toCold_4050_; lean_object* v_options_4051_; uint8_t v_hasTrace_4052_; 
v_toCold_4050_ = lean_ctor_get(v___y_4026_, 0);
v_options_4051_ = lean_ctor_get(v_toCold_4050_, 2);
v_hasTrace_4052_ = lean_ctor_get_uint8(v_options_4051_, sizeof(void*)*1);
if (v_hasTrace_4052_ == 0)
{
v___y_3947_ = v___y_4022_;
v___y_3948_ = v___y_4023_;
v___y_3949_ = v___y_4025_;
v___y_3950_ = v___y_4026_;
v___y_3951_ = v___y_4027_;
goto v___jp_3946_;
}
else
{
lean_object* v_inheritedTraceOptions_4053_; lean_object* v___x_4054_; uint8_t v___x_4055_; 
v_inheritedTraceOptions_4053_ = lean_ctor_get(v_toCold_4050_, 11);
v___x_4054_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4055_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4053_, v_options_4051_, v___x_4054_);
if (v___x_4055_ == 0)
{
v___y_3947_ = v___y_4022_;
v___y_3948_ = v___y_4023_;
v___y_3949_ = v___y_4025_;
v___y_3950_ = v___y_4026_;
v___y_3951_ = v___y_4027_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4056_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4057_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4056_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4057_) == 0)
{
lean_dec_ref_known(v___x_4057_, 1);
v___y_3947_ = v___y_4022_;
v___y_3948_ = v___y_4023_;
v___y_3949_ = v___y_4025_;
v___y_3950_ = v___y_4026_;
v___y_3951_ = v___y_4027_;
goto v___jp_3946_;
}
else
{
lean_dec_ref(v___y_4025_);
lean_dec(v___y_4022_);
lean_dec(v_decl_3766_);
return v___x_4057_;
}
}
}
}
}
}
v___jp_4058_:
{
lean_object* v___x_4065_; lean_object* v_env_4066_; uint8_t v___x_4067_; 
v___x_4065_ = lean_st_ref_get(v___y_4064_);
v_env_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc_ref(v_env_4066_);
lean_dec(v___x_4065_);
v___x_4067_ = l_Lean_Environment_containsOnBranch(v_env_4066_, v_fst_4059_);
lean_dec_ref(v_env_4066_);
if (v___x_4067_ == 0)
{
v___y_4022_ = v_fst_4059_;
v___y_4023_ = v_snd_4061_;
v___y_4024_ = v_exportedInfo_x3f_4062_;
v___y_4025_ = v_fst_4060_;
v___y_4026_ = v___y_4063_;
v___y_4027_ = v___y_4064_;
goto v___jp_4021_;
}
else
{
lean_object* v___x_4068_; lean_object* v_env_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; 
lean_dec(v_exportedInfo_x3f_4062_);
lean_dec_ref(v_fst_4060_);
lean_dec(v_decl_3766_);
v___x_4068_ = lean_st_ref_get(v___y_4064_);
v_env_4069_ = lean_ctor_get(v___x_4068_, 0);
lean_inc_ref(v_env_4069_);
lean_dec(v___x_4068_);
v___x_4070_ = lean_elab_environment_to_kernel_env(v_env_4069_);
v___x_4071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
lean_ctor_set(v___x_4071_, 1, v_fst_4059_);
v___x_4072_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4071_, v___y_4063_, v___y_4064_);
return v___x_4072_;
}
}
v___jp_4073_:
{
lean_object* v_toConstantVal_4078_; lean_object* v_name_4079_; lean_object* v___x_4080_; uint8_t v___x_4081_; 
v_toConstantVal_4078_ = lean_ctor_get(v___y_4074_, 0);
v_name_4079_ = lean_ctor_get(v_toConstantVal_4078_, 0);
lean_inc(v_name_4079_);
v___x_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4080_, 0, v___y_4074_);
v___x_4081_ = 0;
v_fst_4059_ = v_name_4079_;
v_fst_4060_ = v___x_4080_;
v_snd_4061_ = v___x_4081_;
v_exportedInfo_x3f_4062_ = v_exportedInfo_x3f_4075_;
v___y_4063_ = v___y_4076_;
v___y_4064_ = v___y_4077_;
goto v___jp_4058_;
}
v___jp_4082_:
{
lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4088_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4088_, 0, v___y_4084_);
lean_ctor_set_uint8(v___x_4088_, sizeof(void*)*1, v___y_4087_);
v___x_4089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4089_, 0, v___x_4088_);
v___x_4090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
v___y_4074_ = v___y_4086_;
v_exportedInfo_x3f_4075_ = v___x_4090_;
v___y_4076_ = v___y_4083_;
v___y_4077_ = v___y_4085_;
goto v___jp_4073_;
}
v___jp_4091_:
{
uint8_t v___x_4098_; uint8_t v___x_4099_; 
v___x_4098_ = 1;
v___x_4099_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4094_, v___x_4098_);
if (v___x_4099_ == 0)
{
v___y_4083_ = v___y_4096_;
v___y_4084_ = v_toConstantVal_4093_;
v___y_4085_ = v___y_4097_;
v___y_4086_ = v___y_4092_;
v___y_4087_ = v___y_4095_;
goto v___jp_4082_;
}
else
{
v___y_4083_ = v___y_4096_;
v___y_4084_ = v_toConstantVal_4093_;
v___y_4085_ = v___y_4097_;
v___y_4086_ = v___y_4092_;
v___y_4087_ = v_hasTrace_3826_;
goto v___jp_4082_;
}
}
v___jp_4100_:
{
lean_object* v_toConstantVal_4105_; uint8_t v_safety_4106_; 
v_toConstantVal_4105_ = lean_ctor_get(v___y_4101_, 0);
lean_inc_ref(v_toConstantVal_4105_);
v_safety_4106_ = lean_ctor_get_uint8(v___y_4101_, sizeof(void*)*4);
v___y_4092_ = v___y_4101_;
v_toConstantVal_4093_ = v_toConstantVal_4105_;
v_safety_4094_ = v_safety_4106_;
v___y_4095_ = v___y_4102_;
v___y_4096_ = v___y_4103_;
v___y_4097_ = v___y_4104_;
goto v___jp_4091_;
}
v___jp_4107_:
{
lean_object* v___x_4111_; lean_object* v_env_4112_; lean_object* v___x_4113_; 
v___x_4111_ = lean_st_ref_get(v___y_4110_);
v_env_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc_ref(v_env_4112_);
lean_dec(v___x_4111_);
v___x_4113_ = lean_st_ref_get(v___y_4110_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4114_; lean_object* v___x_4115_; uint8_t v_isModule_4116_; 
v_env_4114_ = lean_ctor_get(v___x_4113_, 0);
lean_inc_ref(v_env_4114_);
lean_dec(v___x_4113_);
v___x_4115_ = l_Lean_Environment_header(v_env_4112_);
lean_dec_ref(v_env_4112_);
v_isModule_4116_ = lean_ctor_get_uint8(v___x_4115_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4115_);
if (v_isModule_4116_ == 0)
{
lean_dec_ref(v_env_4114_);
v___y_4074_ = v_defn_4108_;
v_exportedInfo_x3f_4075_ = v___x_4020_;
v___y_4076_ = v___y_4109_;
v___y_4077_ = v___y_4110_;
goto v___jp_4073_;
}
else
{
uint8_t v_isExporting_4117_; 
v_isExporting_4117_ = lean_ctor_get_uint8(v_env_4114_, sizeof(void*)*8);
lean_dec_ref(v_env_4114_);
if (v_isExporting_4117_ == 0)
{
lean_object* v_toCold_4118_; lean_object* v_options_4119_; uint8_t v_hasTrace_4120_; 
v_toCold_4118_ = lean_ctor_get(v___y_4109_, 0);
v_options_4119_ = lean_ctor_get(v_toCold_4118_, 2);
v_hasTrace_4120_ = lean_ctor_get_uint8(v_options_4119_, sizeof(void*)*1);
if (v_hasTrace_4120_ == 0)
{
v___y_4101_ = v_defn_4108_;
v___y_4102_ = v_isModule_4116_;
v___y_4103_ = v___y_4109_;
v___y_4104_ = v___y_4110_;
goto v___jp_4100_;
}
else
{
lean_object* v_inheritedTraceOptions_4121_; lean_object* v___x_4122_; uint8_t v___x_4123_; 
v_inheritedTraceOptions_4121_ = lean_ctor_get(v_toCold_4118_, 11);
v___x_4122_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4123_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4121_, v_options_4119_, v___x_4122_);
if (v___x_4123_ == 0)
{
v___y_4101_ = v_defn_4108_;
v___y_4102_ = v_isModule_4116_;
v___y_4103_ = v___y_4109_;
v___y_4104_ = v___y_4110_;
goto v___jp_4100_;
}
else
{
lean_object* v_toConstantVal_4124_; uint8_t v_safety_4125_; lean_object* v_name_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; 
v_toConstantVal_4124_ = lean_ctor_get(v_defn_4108_, 0);
lean_inc_ref(v_toConstantVal_4124_);
v_safety_4125_ = lean_ctor_get_uint8(v_defn_4108_, sizeof(void*)*4);
v_name_4126_ = lean_ctor_get(v_toConstantVal_4124_, 0);
v___x_4127_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4126_);
v___x_4128_ = l_Lean_MessageData_ofName(v_name_4126_);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4129_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4131_, v___y_4109_, v___y_4110_);
if (lean_obj_tag(v___x_4132_) == 0)
{
lean_dec_ref_known(v___x_4132_, 1);
v___y_4092_ = v_defn_4108_;
v_toConstantVal_4093_ = v_toConstantVal_4124_;
v_safety_4094_ = v_safety_4125_;
v___y_4095_ = v_isModule_4116_;
v___y_4096_ = v___y_4109_;
v___y_4097_ = v___y_4110_;
goto v___jp_4091_;
}
else
{
lean_dec_ref(v_toConstantVal_4124_);
lean_dec_ref(v_defn_4108_);
lean_dec(v_decl_3766_);
return v___x_4132_;
}
}
}
}
else
{
v___y_4074_ = v_defn_4108_;
v_exportedInfo_x3f_4075_ = v___x_4020_;
v___y_4076_ = v___y_4109_;
v___y_4077_ = v___y_4110_;
goto v___jp_4073_;
}
}
}
else
{
lean_dec(v___x_4113_);
lean_dec_ref(v_env_4112_);
v___y_4074_ = v_defn_4108_;
v_exportedInfo_x3f_4075_ = v___x_4020_;
v___y_4076_ = v___y_4109_;
v___y_4077_ = v___y_4110_;
goto v___jp_4073_;
}
}
}
}
}
else
{
lean_object* v___f_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; uint8_t v___x_4189_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v_a_4193_; lean_object* v___y_4206_; lean_object* v___y_4207_; lean_object* v___y_4208_; lean_object* v___y_4226_; lean_object* v___y_4227_; lean_object* v___y_4228_; lean_object* v___y_4229_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4235_; lean_object* v___y_4236_; lean_object* v___y_4237_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4257_; lean_object* v___y_4258_; lean_object* v___y_4272_; lean_object* v___y_4273_; lean_object* v___y_4274_; lean_object* v___y_4275_; lean_object* v___y_4279_; uint8_t v___y_4280_; lean_object* v___y_4281_; lean_object* v___y_4282_; lean_object* v___y_4283_; lean_object* v___y_4284_; lean_object* v___y_4285_; lean_object* v___y_4286_; lean_object* v___y_4287_; lean_object* v___y_4292_; lean_object* v___y_4293_; lean_object* v_a_4294_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4306_; lean_object* v___y_4324_; lean_object* v___y_4325_; lean_object* v___y_4326_; lean_object* v___y_4327_; lean_object* v___y_4331_; lean_object* v___y_4332_; lean_object* v___y_4333_; lean_object* v___y_4334_; 
lean_inc(v_decl_3766_);
v___f_4186_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed), 5, 1);
lean_closure_set(v___f_4186_, 0, v_decl_3766_);
v___x_4187_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4188_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3825_, v_options_3824_, v___x_4188_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4493_; uint8_t v___x_4494_; lean_object* v___y_4496_; lean_object* v___y_4497_; lean_object* v___y_4498_; lean_object* v___y_4499_; lean_object* v___y_4500_; lean_object* v___y_4501_; lean_object* v___y_4502_; lean_object* v___y_4503_; lean_object* v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4569_; lean_object* v___y_4570_; lean_object* v___y_4571_; lean_object* v___y_4572_; uint8_t v___y_4573_; lean_object* v___y_4574_; lean_object* v___y_4575_; lean_object* v___y_4576_; uint8_t v___y_4598_; lean_object* v___y_4599_; lean_object* v___y_4600_; lean_object* v_exportedInfo_x3f_4601_; lean_object* v___y_4602_; lean_object* v___y_4603_; uint8_t v___y_4613_; lean_object* v___y_4614_; lean_object* v___y_4615_; lean_object* v___y_4616_; lean_object* v___y_4617_; uint8_t v___y_4620_; lean_object* v___y_4621_; lean_object* v___y_4622_; lean_object* v___y_4623_; lean_object* v___y_4624_; 
v___x_4493_ = l_Lean_trace_profiler;
v___x_4494_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3824_, v___x_4493_);
if (v___x_4494_ == 0)
{
lean_object* v___x_4626_; lean_object* v_env_4627_; lean_object* v_nextMacroScope_4628_; lean_object* v_ngen_4629_; lean_object* v_auxDeclNGen_4630_; lean_object* v_traceState_4631_; lean_object* v_recordedDeps_4632_; lean_object* v_messages_4633_; lean_object* v_infoState_4634_; lean_object* v_snapshotTasks_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4868_; 
lean_dec_ref(v___f_4186_);
v___x_4626_ = lean_st_ref_take(v_a_3769_);
v_env_4627_ = lean_ctor_get(v___x_4626_, 0);
v_nextMacroScope_4628_ = lean_ctor_get(v___x_4626_, 1);
v_ngen_4629_ = lean_ctor_get(v___x_4626_, 2);
v_auxDeclNGen_4630_ = lean_ctor_get(v___x_4626_, 3);
v_traceState_4631_ = lean_ctor_get(v___x_4626_, 4);
v_recordedDeps_4632_ = lean_ctor_get(v___x_4626_, 6);
v_messages_4633_ = lean_ctor_get(v___x_4626_, 7);
v_infoState_4634_ = lean_ctor_get(v___x_4626_, 8);
v_snapshotTasks_4635_ = lean_ctor_get(v___x_4626_, 9);
v_isSharedCheck_4868_ = !lean_is_exclusive(v___x_4626_);
if (v_isSharedCheck_4868_ == 0)
{
lean_object* v_unused_4869_; 
v_unused_4869_ = lean_ctor_get(v___x_4626_, 5);
lean_dec(v_unused_4869_);
v___x_4637_ = v___x_4626_;
v_isShared_4638_ = v_isSharedCheck_4868_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_snapshotTasks_4635_);
lean_inc(v_infoState_4634_);
lean_inc(v_messages_4633_);
lean_inc(v_recordedDeps_4632_);
lean_inc(v_traceState_4631_);
lean_inc(v_auxDeclNGen_4630_);
lean_inc(v_ngen_4629_);
lean_inc(v_nextMacroScope_4628_);
lean_inc(v_env_4627_);
lean_dec(v___x_4626_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4868_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4639_; lean_object* v___x_4640_; lean_object* v___x_4641_; uint8_t v___y_4643_; lean_object* v___y_4644_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___x_4672_; 
lean_inc(v_decl_3766_);
v___x_4639_ = l_Lean_Declaration_getNames(v_decl_3766_);
v___x_4640_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4627_, v___x_4639_);
v___x_4641_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4638_ == 0)
{
lean_ctor_set(v___x_4637_, 5, v___x_4641_);
lean_ctor_set(v___x_4637_, 0, v___x_4640_);
v___x_4672_ = v___x_4637_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4867_; 
v_reuseFailAlloc_4867_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4867_, 0, v___x_4640_);
lean_ctor_set(v_reuseFailAlloc_4867_, 1, v_nextMacroScope_4628_);
lean_ctor_set(v_reuseFailAlloc_4867_, 2, v_ngen_4629_);
lean_ctor_set(v_reuseFailAlloc_4867_, 3, v_auxDeclNGen_4630_);
lean_ctor_set(v_reuseFailAlloc_4867_, 4, v_traceState_4631_);
lean_ctor_set(v_reuseFailAlloc_4867_, 5, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4867_, 6, v_recordedDeps_4632_);
lean_ctor_set(v_reuseFailAlloc_4867_, 7, v_messages_4633_);
lean_ctor_set(v_reuseFailAlloc_4867_, 8, v_infoState_4634_);
lean_ctor_set(v_reuseFailAlloc_4867_, 9, v_snapshotTasks_4635_);
v___x_4672_ = v_reuseFailAlloc_4867_;
goto v_reusejp_4671_;
}
v___jp_4642_:
{
lean_object* v___x_4649_; lean_object* v_env_4650_; lean_object* v_nextMacroScope_4651_; lean_object* v_ngen_4652_; lean_object* v_auxDeclNGen_4653_; lean_object* v_traceState_4654_; lean_object* v_recordedDeps_4655_; lean_object* v_messages_4656_; lean_object* v_infoState_4657_; lean_object* v_snapshotTasks_4658_; lean_object* v___x_4660_; uint8_t v_isShared_4661_; uint8_t v_isSharedCheck_4669_; 
v___x_4649_ = lean_st_ref_take(v___y_4648_);
v_env_4650_ = lean_ctor_get(v___x_4649_, 0);
v_nextMacroScope_4651_ = lean_ctor_get(v___x_4649_, 1);
v_ngen_4652_ = lean_ctor_get(v___x_4649_, 2);
v_auxDeclNGen_4653_ = lean_ctor_get(v___x_4649_, 3);
v_traceState_4654_ = lean_ctor_get(v___x_4649_, 4);
v_recordedDeps_4655_ = lean_ctor_get(v___x_4649_, 6);
v_messages_4656_ = lean_ctor_get(v___x_4649_, 7);
v_infoState_4657_ = lean_ctor_get(v___x_4649_, 8);
v_snapshotTasks_4658_ = lean_ctor_get(v___x_4649_, 9);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4649_);
if (v_isSharedCheck_4669_ == 0)
{
lean_object* v_unused_4670_; 
v_unused_4670_ = lean_ctor_get(v___x_4649_, 5);
lean_dec(v_unused_4670_);
v___x_4660_ = v___x_4649_;
v_isShared_4661_ = v_isSharedCheck_4669_;
goto v_resetjp_4659_;
}
else
{
lean_inc(v_snapshotTasks_4658_);
lean_inc(v_infoState_4657_);
lean_inc(v_messages_4656_);
lean_inc(v_recordedDeps_4655_);
lean_inc(v_traceState_4654_);
lean_inc(v_auxDeclNGen_4653_);
lean_inc(v_ngen_4652_);
lean_inc(v_nextMacroScope_4651_);
lean_inc(v_env_4650_);
lean_dec(v___x_4649_);
v___x_4660_ = lean_box(0);
v_isShared_4661_ = v_isSharedCheck_4669_;
goto v_resetjp_4659_;
}
v_resetjp_4659_:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4666_; 
v___x_4662_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4663_ = lean_box(v___y_4643_);
lean_inc(v___y_4647_);
v___x_4664_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4662_, v_env_4650_, v___y_4647_, v___x_4663_);
if (v_isShared_4661_ == 0)
{
lean_ctor_set(v___x_4660_, 5, v___x_4641_);
lean_ctor_set(v___x_4660_, 0, v___x_4664_);
v___x_4666_ = v___x_4660_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4668_, 1, v_nextMacroScope_4651_);
lean_ctor_set(v_reuseFailAlloc_4668_, 2, v_ngen_4652_);
lean_ctor_set(v_reuseFailAlloc_4668_, 3, v_auxDeclNGen_4653_);
lean_ctor_set(v_reuseFailAlloc_4668_, 4, v_traceState_4654_);
lean_ctor_set(v_reuseFailAlloc_4668_, 5, v___x_4641_);
lean_ctor_set(v_reuseFailAlloc_4668_, 6, v_recordedDeps_4655_);
lean_ctor_set(v_reuseFailAlloc_4668_, 7, v_messages_4656_);
lean_ctor_set(v_reuseFailAlloc_4668_, 8, v_infoState_4657_);
lean_ctor_set(v_reuseFailAlloc_4668_, 9, v_snapshotTasks_4658_);
v___x_4666_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4667_; 
v___x_4667_ = lean_st_ref_put(v___y_4648_, v___x_4666_);
v___y_4598_ = v___y_4643_;
v___y_4599_ = v___y_4644_;
v___y_4600_ = v___y_4647_;
v_exportedInfo_x3f_4601_ = v___y_4645_;
v___y_4602_ = v___y_4646_;
v___y_4603_ = v___y_4648_;
goto v___jp_4597_;
}
}
}
v_reusejp_4671_:
{
lean_object* v___x_4673_; lean_object* v___x_4674_; uint8_t v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4679_; lean_object* v___y_4680_; lean_object* v___y_4681_; lean_object* v_fst_4710_; lean_object* v_fst_4711_; uint8_t v_snd_4712_; lean_object* v_exportedInfo_x3f_4713_; lean_object* v___y_4714_; lean_object* v___y_4715_; lean_object* v___y_4725_; lean_object* v_exportedInfo_x3f_4726_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___y_4734_; lean_object* v___y_4735_; lean_object* v___y_4736_; lean_object* v___y_4737_; uint8_t v___y_4738_; uint8_t v___y_4743_; lean_object* v___y_4744_; lean_object* v_toConstantVal_4745_; uint8_t v_safety_4746_; lean_object* v___y_4747_; lean_object* v___y_4748_; uint8_t v___y_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4755_; lean_object* v___y_4759_; lean_object* v___y_4760_; lean_object* v___y_4761_; uint8_t v___y_4762_; lean_object* v___y_4778_; lean_object* v___y_4779_; lean_object* v___y_4780_; lean_object* v___y_4781_; lean_object* v___y_4782_; lean_object* v_defn_4787_; lean_object* v___y_4788_; lean_object* v___y_4789_; 
v___x_4673_ = lean_st_ref_put(v_a_3769_, v___x_4672_);
v___x_4674_ = lean_box(0);
switch(lean_obj_tag(v_decl_3766_))
{
case 2:
{
lean_object* v_val_4795_; lean_object* v_exportedInfo_x3f_4797_; lean_object* v___y_4798_; lean_object* v___y_4799_; lean_object* v___y_4805_; lean_object* v___y_4806_; lean_object* v___x_4811_; lean_object* v_env_4812_; 
v_val_4795_ = lean_ctor_get(v_decl_3766_, 0);
v___x_4811_ = lean_st_ref_get(v_a_3769_);
v_env_4812_ = lean_ctor_get(v___x_4811_, 0);
lean_inc_ref(v_env_4812_);
lean_dec(v___x_4811_);
if (v_forceExpose_3767_ == 0)
{
goto v___jp_4813_;
}
else
{
if (v___x_4494_ == 0)
{
lean_dec_ref(v_env_4812_);
v_exportedInfo_x3f_4797_ = v___x_4674_;
v___y_4798_ = v_a_3768_;
v___y_4799_ = v_a_3769_;
goto v___jp_4796_;
}
else
{
goto v___jp_4813_;
}
}
v___jp_4796_:
{
lean_object* v_toConstantVal_4800_; lean_object* v_name_4801_; lean_object* v___x_4802_; uint8_t v___x_4803_; 
v_toConstantVal_4800_ = lean_ctor_get(v_val_4795_, 0);
v_name_4801_ = lean_ctor_get(v_toConstantVal_4800_, 0);
lean_inc_ref(v_val_4795_);
v___x_4802_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4802_, 0, v_val_4795_);
v___x_4803_ = 1;
lean_inc(v_name_4801_);
v_fst_4710_ = v_name_4801_;
v_fst_4711_ = v___x_4802_;
v_snd_4712_ = v___x_4803_;
v_exportedInfo_x3f_4713_ = v_exportedInfo_x3f_4797_;
v___y_4714_ = v___y_4798_;
v___y_4715_ = v___y_4799_;
goto v___jp_4709_;
}
v___jp_4804_:
{
lean_object* v_toConstantVal_4807_; lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4810_; 
v_toConstantVal_4807_ = lean_ctor_get(v_val_4795_, 0);
lean_inc_ref(v_toConstantVal_4807_);
v___x_4808_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4808_, 0, v_toConstantVal_4807_);
lean_ctor_set_uint8(v___x_4808_, sizeof(void*)*1, v___x_4494_);
v___x_4809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4809_, 0, v___x_4808_);
v___x_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4810_, 0, v___x_4809_);
v_exportedInfo_x3f_4797_ = v___x_4810_;
v___y_4798_ = v___y_4805_;
v___y_4799_ = v___y_4806_;
goto v___jp_4796_;
}
v___jp_4813_:
{
lean_object* v___x_4814_; uint8_t v_isModule_4815_; 
v___x_4814_ = l_Lean_Environment_header(v_env_4812_);
lean_dec_ref(v_env_4812_);
v_isModule_4815_ = lean_ctor_get_uint8(v___x_4814_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4814_);
if (v_isModule_4815_ == 0)
{
v_exportedInfo_x3f_4797_ = v___x_4674_;
v___y_4798_ = v_a_3768_;
v___y_4799_ = v_a_3769_;
goto v___jp_4796_;
}
else
{
if (v___x_4189_ == 0)
{
v___y_4805_ = v_a_3768_;
v___y_4806_ = v_a_3769_;
goto v___jp_4804_;
}
else
{
lean_object* v_toConstantVal_4816_; lean_object* v_name_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; lean_object* v___x_4820_; lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v___x_4823_; 
v_toConstantVal_4816_ = lean_ctor_get(v_val_4795_, 0);
v_name_4817_ = lean_ctor_get(v_toConstantVal_4816_, 0);
v___x_4818_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4817_);
v___x_4819_ = l_Lean_MessageData_ofName(v_name_4817_);
v___x_4820_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4820_, 0, v___x_4818_);
lean_ctor_set(v___x_4820_, 1, v___x_4819_);
v___x_4821_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4822_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4822_, 0, v___x_4820_);
lean_ctor_set(v___x_4822_, 1, v___x_4821_);
v___x_4823_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4822_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4823_) == 0)
{
lean_dec_ref_known(v___x_4823_, 1);
v___y_4805_ = v_a_3768_;
v___y_4806_ = v_a_3769_;
goto v___jp_4804_;
}
else
{
lean_dec_ref_known(v_decl_3766_, 1);
return v___x_4823_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4824_; 
v_val_4824_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref(v_val_4824_);
v_defn_4787_ = v_val_4824_;
v___y_4788_ = v_a_3768_;
v___y_4789_ = v_a_3769_;
goto v___jp_4786_;
}
case 5:
{
lean_object* v_defns_4825_; 
v_defns_4825_ = lean_ctor_get(v_decl_3766_, 0);
if (lean_obj_tag(v_defns_4825_) == 1)
{
lean_object* v_tail_4826_; 
v_tail_4826_ = lean_ctor_get(v_defns_4825_, 1);
if (lean_obj_tag(v_tail_4826_) == 0)
{
lean_object* v_head_4827_; 
v_head_4827_ = lean_ctor_get(v_defns_4825_, 0);
lean_inc(v_head_4827_);
v_defn_4787_ = v_head_4827_;
v___y_4788_ = v_a_3768_;
v___y_4789_ = v_a_3769_;
goto v___jp_4786_;
}
else
{
v___y_3962_ = v_a_3768_;
v_options_3963_ = v_options_3824_;
v_inheritedTraceOptions_3964_ = v_inheritedTraceOptions_3825_;
v___y_3965_ = v_a_3769_;
goto v___jp_3961_;
}
}
else
{
v___y_3962_ = v_a_3768_;
v_options_3963_ = v_options_3824_;
v_inheritedTraceOptions_3964_ = v_inheritedTraceOptions_3825_;
v___y_3965_ = v_a_3769_;
goto v___jp_3961_;
}
}
case 3:
{
lean_object* v_val_4828_; lean_object* v_exportedInfo_x3f_4830_; lean_object* v___y_4831_; lean_object* v___y_4832_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___x_4845_; lean_object* v_env_4846_; lean_object* v___x_4847_; lean_object* v_env_4857_; 
v_val_4828_ = lean_ctor_get(v_decl_3766_, 0);
v___x_4845_ = lean_st_ref_get(v_a_3769_);
v_env_4846_ = lean_ctor_get(v___x_4845_, 0);
lean_inc_ref(v_env_4846_);
lean_dec(v___x_4845_);
v___x_4847_ = lean_st_ref_get(v_a_3769_);
v_env_4857_ = lean_ctor_get(v___x_4847_, 0);
lean_inc_ref(v_env_4857_);
lean_dec(v___x_4847_);
if (v_forceExpose_3767_ == 0)
{
goto v___jp_4858_;
}
else
{
if (v___x_4494_ == 0)
{
lean_dec_ref(v_env_4857_);
lean_dec_ref(v_env_4846_);
v_exportedInfo_x3f_4830_ = v___x_4674_;
v___y_4831_ = v_a_3768_;
v___y_4832_ = v_a_3769_;
goto v___jp_4829_;
}
else
{
goto v___jp_4858_;
}
}
v___jp_4829_:
{
lean_object* v_toConstantVal_4833_; lean_object* v_name_4834_; lean_object* v___x_4835_; uint8_t v___x_4836_; 
v_toConstantVal_4833_ = lean_ctor_get(v_val_4828_, 0);
v_name_4834_ = lean_ctor_get(v_toConstantVal_4833_, 0);
lean_inc_ref(v_val_4828_);
v___x_4835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4835_, 0, v_val_4828_);
v___x_4836_ = 3;
lean_inc(v_name_4834_);
v_fst_4710_ = v_name_4834_;
v_fst_4711_ = v___x_4835_;
v_snd_4712_ = v___x_4836_;
v_exportedInfo_x3f_4713_ = v_exportedInfo_x3f_4830_;
v___y_4714_ = v___y_4831_;
v___y_4715_ = v___y_4832_;
goto v___jp_4709_;
}
v___jp_4837_:
{
lean_object* v_toConstantVal_4840_; uint8_t v_isUnsafe_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v_toConstantVal_4840_ = lean_ctor_get(v_val_4828_, 0);
v_isUnsafe_4841_ = lean_ctor_get_uint8(v_val_4828_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4840_);
v___x_4842_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4842_, 0, v_toConstantVal_4840_);
lean_ctor_set_uint8(v___x_4842_, sizeof(void*)*1, v_isUnsafe_4841_);
v___x_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
v___x_4844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
v_exportedInfo_x3f_4830_ = v___x_4844_;
v___y_4831_ = v___y_4838_;
v___y_4832_ = v___y_4839_;
goto v___jp_4829_;
}
v___jp_4848_:
{
if (v___x_4189_ == 0)
{
v___y_4838_ = v_a_3768_;
v___y_4839_ = v_a_3769_;
goto v___jp_4837_;
}
else
{
lean_object* v_toConstantVal_4849_; lean_object* v_name_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4853_; lean_object* v___x_4854_; lean_object* v___x_4855_; lean_object* v___x_4856_; 
v_toConstantVal_4849_ = lean_ctor_get(v_val_4828_, 0);
v_name_4850_ = lean_ctor_get(v_toConstantVal_4849_, 0);
v___x_4851_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4850_);
v___x_4852_ = l_Lean_MessageData_ofName(v_name_4850_);
v___x_4853_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4853_, 0, v___x_4851_);
lean_ctor_set(v___x_4853_, 1, v___x_4852_);
v___x_4854_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4855_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4855_, 0, v___x_4853_);
lean_ctor_set(v___x_4855_, 1, v___x_4854_);
v___x_4856_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4855_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4856_) == 0)
{
lean_dec_ref_known(v___x_4856_, 1);
v___y_4838_ = v_a_3768_;
v___y_4839_ = v_a_3769_;
goto v___jp_4837_;
}
else
{
lean_dec_ref_known(v_decl_3766_, 1);
return v___x_4856_;
}
}
}
v___jp_4858_:
{
lean_object* v___x_4859_; uint8_t v_isModule_4860_; 
v___x_4859_ = l_Lean_Environment_header(v_env_4846_);
lean_dec_ref(v_env_4846_);
v_isModule_4860_ = lean_ctor_get_uint8(v___x_4859_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4859_);
if (v_isModule_4860_ == 0)
{
lean_dec_ref(v_env_4857_);
v_exportedInfo_x3f_4830_ = v___x_4674_;
v___y_4831_ = v_a_3768_;
v___y_4832_ = v_a_3769_;
goto v___jp_4829_;
}
else
{
uint8_t v_isExporting_4861_; 
v_isExporting_4861_ = lean_ctor_get_uint8(v_env_4857_, sizeof(void*)*8);
lean_dec_ref(v_env_4857_);
if (v_isExporting_4861_ == 0)
{
goto v___jp_4848_;
}
else
{
if (v___x_4494_ == 0)
{
v_exportedInfo_x3f_4830_ = v___x_4674_;
v___y_4831_ = v_a_3768_;
v___y_4832_ = v_a_3769_;
goto v___jp_4829_;
}
else
{
goto v___jp_4848_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4862_; lean_object* v_toConstantVal_4863_; lean_object* v_name_4864_; lean_object* v___x_4865_; uint8_t v___x_4866_; 
v_val_4862_ = lean_ctor_get(v_decl_3766_, 0);
v_toConstantVal_4863_ = lean_ctor_get(v_val_4862_, 0);
v_name_4864_ = lean_ctor_get(v_toConstantVal_4863_, 0);
lean_inc_ref(v_val_4862_);
v___x_4865_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4865_, 0, v_val_4862_);
v___x_4866_ = 2;
lean_inc(v_name_4864_);
v_fst_4710_ = v_name_4864_;
v_fst_4711_ = v___x_4865_;
v_snd_4712_ = v___x_4866_;
v_exportedInfo_x3f_4713_ = v___x_4674_;
v___y_4714_ = v_a_3768_;
v___y_4715_ = v_a_3769_;
goto v___jp_4709_;
}
default: 
{
v___y_3962_ = v_a_3768_;
v_options_3963_ = v_options_3824_;
v_inheritedTraceOptions_3964_ = v_inheritedTraceOptions_3825_;
v___y_3965_ = v_a_3769_;
goto v___jp_3961_;
}
}
v___jp_4675_:
{
lean_object* v___x_4682_; uint8_t v___x_4683_; 
lean_inc(v_decl_3766_);
v___x_4682_ = l_Lean_Declaration_getTopLevelNames(v_decl_3766_);
v___x_4683_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4682_);
lean_dec(v___x_4682_);
if (v___x_4683_ == 0)
{
if (lean_obj_tag(v___y_4678_) == 0)
{
if (v___x_4683_ == 0)
{
lean_object* v_toCold_4684_; lean_object* v_options_4685_; uint8_t v_hasTrace_4686_; 
v_toCold_4684_ = lean_ctor_get(v___y_4680_, 0);
v_options_4685_ = lean_ctor_get(v_toCold_4684_, 2);
v_hasTrace_4686_ = lean_ctor_get_uint8(v_options_4685_, sizeof(void*)*1);
if (v_hasTrace_4686_ == 0)
{
v___y_4620_ = v___y_4676_;
v___y_4621_ = v___y_4677_;
v___y_4622_ = v___y_4679_;
v___y_4623_ = v___y_4680_;
v___y_4624_ = v___y_4681_;
goto v___jp_4619_;
}
else
{
lean_object* v_inheritedTraceOptions_4687_; uint8_t v___x_4688_; 
v_inheritedTraceOptions_4687_ = lean_ctor_get(v_toCold_4684_, 11);
v___x_4688_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4687_, v_options_4685_, v___x_4188_);
if (v___x_4688_ == 0)
{
v___y_4620_ = v___y_4676_;
v___y_4621_ = v___y_4677_;
v___y_4622_ = v___y_4679_;
v___y_4623_ = v___y_4680_;
v___y_4624_ = v___y_4681_;
goto v___jp_4619_;
}
else
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
v___x_4689_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__3);
v___x_4690_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4689_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_dec_ref_known(v___x_4690_, 1);
v___y_4620_ = v___y_4676_;
v___y_4621_ = v___y_4677_;
v___y_4622_ = v___y_4679_;
v___y_4623_ = v___y_4680_;
v___y_4624_ = v___y_4681_;
goto v___jp_4619_;
}
else
{
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4677_);
lean_dec(v_decl_3766_);
return v___x_4690_;
}
}
}
}
else
{
v___y_4643_ = v___y_4676_;
v___y_4644_ = v___y_4677_;
v___y_4645_ = v___y_4678_;
v___y_4646_ = v___y_4680_;
v___y_4647_ = v___y_4679_;
v___y_4648_ = v___y_4681_;
goto v___jp_4642_;
}
}
else
{
v___y_4643_ = v___y_4676_;
v___y_4644_ = v___y_4677_;
v___y_4645_ = v___y_4678_;
v___y_4646_ = v___y_4680_;
v___y_4647_ = v___y_4679_;
v___y_4648_ = v___y_4681_;
goto v___jp_4642_;
}
}
else
{
lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v_a_4693_; uint8_t v___x_4694_; 
lean_dec(v___y_4678_);
v___x_4691_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4692_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4691_, v___y_4680_);
v_a_4693_ = lean_ctor_get(v___x_4692_, 0);
lean_inc(v_a_4693_);
lean_dec_ref(v___x_4692_);
v___x_4694_ = lean_unbox(v_a_4693_);
lean_dec(v_a_4693_);
if (v___x_4694_ == 0)
{
lean_object* v_toCold_4695_; lean_object* v_options_4696_; uint8_t v_hasTrace_4697_; 
v_toCold_4695_ = lean_ctor_get(v___y_4680_, 0);
v_options_4696_ = lean_ctor_get(v_toCold_4695_, 2);
v_hasTrace_4697_ = lean_ctor_get_uint8(v_options_4696_, sizeof(void*)*1);
if (v_hasTrace_4697_ == 0)
{
v___y_4598_ = v___y_4676_;
v___y_4599_ = v___y_4677_;
v___y_4600_ = v___y_4679_;
v_exportedInfo_x3f_4601_ = v___x_4674_;
v___y_4602_ = v___y_4680_;
v___y_4603_ = v___y_4681_;
goto v___jp_4597_;
}
else
{
lean_object* v_inheritedTraceOptions_4698_; uint8_t v___x_4699_; 
v_inheritedTraceOptions_4698_ = lean_ctor_get(v_toCold_4695_, 11);
v___x_4699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4698_, v_options_4696_, v___x_4188_);
if (v___x_4699_ == 0)
{
v___y_4598_ = v___y_4676_;
v___y_4599_ = v___y_4677_;
v___y_4600_ = v___y_4679_;
v_exportedInfo_x3f_4601_ = v___x_4674_;
v___y_4602_ = v___y_4680_;
v___y_4603_ = v___y_4681_;
goto v___jp_4597_;
}
else
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__5);
v___x_4701_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4700_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4701_) == 0)
{
lean_dec_ref_known(v___x_4701_, 1);
v___y_4598_ = v___y_4676_;
v___y_4599_ = v___y_4677_;
v___y_4600_ = v___y_4679_;
v_exportedInfo_x3f_4601_ = v___x_4674_;
v___y_4602_ = v___y_4680_;
v___y_4603_ = v___y_4681_;
goto v___jp_4597_;
}
else
{
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4677_);
lean_dec(v_decl_3766_);
return v___x_4701_;
}
}
}
}
else
{
lean_object* v_toCold_4702_; lean_object* v_options_4703_; uint8_t v_hasTrace_4704_; 
v_toCold_4702_ = lean_ctor_get(v___y_4680_, 0);
v_options_4703_ = lean_ctor_get(v_toCold_4702_, 2);
v_hasTrace_4704_ = lean_ctor_get_uint8(v_options_4703_, sizeof(void*)*1);
if (v_hasTrace_4704_ == 0)
{
v___y_4613_ = v___y_4676_;
v___y_4614_ = v___y_4677_;
v___y_4615_ = v___y_4679_;
v___y_4616_ = v___y_4680_;
v___y_4617_ = v___y_4681_;
goto v___jp_4612_;
}
else
{
lean_object* v_inheritedTraceOptions_4705_; uint8_t v___x_4706_; 
v_inheritedTraceOptions_4705_ = lean_ctor_get(v_toCold_4702_, 11);
v___x_4706_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4705_, v_options_4703_, v___x_4188_);
if (v___x_4706_ == 0)
{
v___y_4613_ = v___y_4676_;
v___y_4614_ = v___y_4677_;
v___y_4615_ = v___y_4679_;
v___y_4616_ = v___y_4680_;
v___y_4617_ = v___y_4681_;
goto v___jp_4612_;
}
else
{
lean_object* v___x_4707_; lean_object* v___x_4708_; 
v___x_4707_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__7);
v___x_4708_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4707_, v___y_4680_, v___y_4681_);
if (lean_obj_tag(v___x_4708_) == 0)
{
lean_dec_ref_known(v___x_4708_, 1);
v___y_4613_ = v___y_4676_;
v___y_4614_ = v___y_4677_;
v___y_4615_ = v___y_4679_;
v___y_4616_ = v___y_4680_;
v___y_4617_ = v___y_4681_;
goto v___jp_4612_;
}
else
{
lean_dec(v___y_4679_);
lean_dec_ref(v___y_4677_);
lean_dec(v_decl_3766_);
return v___x_4708_;
}
}
}
}
}
}
v___jp_4709_:
{
lean_object* v___x_4716_; lean_object* v_env_4717_; uint8_t v___x_4718_; 
v___x_4716_ = lean_st_ref_get(v___y_4715_);
v_env_4717_ = lean_ctor_get(v___x_4716_, 0);
lean_inc_ref(v_env_4717_);
lean_dec(v___x_4716_);
v___x_4718_ = l_Lean_Environment_containsOnBranch(v_env_4717_, v_fst_4710_);
lean_dec_ref(v_env_4717_);
if (v___x_4718_ == 0)
{
v___y_4676_ = v_snd_4712_;
v___y_4677_ = v_fst_4711_;
v___y_4678_ = v_exportedInfo_x3f_4713_;
v___y_4679_ = v_fst_4710_;
v___y_4680_ = v___y_4714_;
v___y_4681_ = v___y_4715_;
goto v___jp_4675_;
}
else
{
lean_object* v___x_4719_; lean_object* v_env_4720_; lean_object* v___x_4721_; lean_object* v___x_4722_; lean_object* v___x_4723_; 
lean_dec(v_exportedInfo_x3f_4713_);
lean_dec_ref(v_fst_4711_);
lean_dec(v_decl_3766_);
v___x_4719_ = lean_st_ref_get(v___y_4715_);
v_env_4720_ = lean_ctor_get(v___x_4719_, 0);
lean_inc_ref(v_env_4720_);
lean_dec(v___x_4719_);
v___x_4721_ = lean_elab_environment_to_kernel_env(v_env_4720_);
v___x_4722_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4722_, 0, v___x_4721_);
lean_ctor_set(v___x_4722_, 1, v_fst_4710_);
v___x_4723_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4722_, v___y_4714_, v___y_4715_);
return v___x_4723_;
}
}
v___jp_4724_:
{
lean_object* v_toConstantVal_4729_; lean_object* v_name_4730_; lean_object* v___x_4731_; uint8_t v___x_4732_; 
v_toConstantVal_4729_ = lean_ctor_get(v___y_4725_, 0);
v_name_4730_ = lean_ctor_get(v_toConstantVal_4729_, 0);
lean_inc(v_name_4730_);
v___x_4731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___y_4725_);
v___x_4732_ = 0;
v_fst_4710_ = v_name_4730_;
v_fst_4711_ = v___x_4731_;
v_snd_4712_ = v___x_4732_;
v_exportedInfo_x3f_4713_ = v_exportedInfo_x3f_4726_;
v___y_4714_ = v___y_4727_;
v___y_4715_ = v___y_4728_;
goto v___jp_4709_;
}
v___jp_4733_:
{
lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
v___x_4739_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4739_, 0, v___y_4737_);
lean_ctor_set_uint8(v___x_4739_, sizeof(void*)*1, v___y_4738_);
v___x_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4740_, 0, v___x_4739_);
v___x_4741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4740_);
v___y_4725_ = v___y_4736_;
v_exportedInfo_x3f_4726_ = v___x_4741_;
v___y_4727_ = v___y_4735_;
v___y_4728_ = v___y_4734_;
goto v___jp_4724_;
}
v___jp_4742_:
{
uint8_t v___x_4749_; uint8_t v___x_4750_; 
v___x_4749_ = 1;
v___x_4750_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4746_, v___x_4749_);
if (v___x_4750_ == 0)
{
v___y_4734_ = v___y_4748_;
v___y_4735_ = v___y_4747_;
v___y_4736_ = v___y_4744_;
v___y_4737_ = v_toConstantVal_4745_;
v___y_4738_ = v___y_4743_;
goto v___jp_4733_;
}
else
{
v___y_4734_ = v___y_4748_;
v___y_4735_ = v___y_4747_;
v___y_4736_ = v___y_4744_;
v___y_4737_ = v_toConstantVal_4745_;
v___y_4738_ = v___x_4494_;
goto v___jp_4733_;
}
}
v___jp_4751_:
{
lean_object* v_toConstantVal_4756_; uint8_t v_safety_4757_; 
v_toConstantVal_4756_ = lean_ctor_get(v___y_4753_, 0);
lean_inc_ref(v_toConstantVal_4756_);
v_safety_4757_ = lean_ctor_get_uint8(v___y_4753_, sizeof(void*)*4);
v___y_4743_ = v___y_4752_;
v___y_4744_ = v___y_4753_;
v_toConstantVal_4745_ = v_toConstantVal_4756_;
v_safety_4746_ = v_safety_4757_;
v___y_4747_ = v___y_4754_;
v___y_4748_ = v___y_4755_;
goto v___jp_4742_;
}
v___jp_4758_:
{
lean_object* v_toCold_4763_; lean_object* v_options_4764_; uint8_t v_hasTrace_4765_; 
v_toCold_4763_ = lean_ctor_get(v___y_4760_, 0);
v_options_4764_ = lean_ctor_get(v_toCold_4763_, 2);
v_hasTrace_4765_ = lean_ctor_get_uint8(v_options_4764_, sizeof(void*)*1);
if (v_hasTrace_4765_ == 0)
{
v___y_4752_ = v___y_4762_;
v___y_4753_ = v___y_4761_;
v___y_4754_ = v___y_4760_;
v___y_4755_ = v___y_4759_;
goto v___jp_4751_;
}
else
{
lean_object* v_inheritedTraceOptions_4766_; uint8_t v___x_4767_; 
v_inheritedTraceOptions_4766_ = lean_ctor_get(v_toCold_4763_, 11);
v___x_4767_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4766_, v_options_4764_, v___x_4188_);
if (v___x_4767_ == 0)
{
v___y_4752_ = v___y_4762_;
v___y_4753_ = v___y_4761_;
v___y_4754_ = v___y_4760_;
v___y_4755_ = v___y_4759_;
goto v___jp_4751_;
}
else
{
lean_object* v_toConstantVal_4768_; uint8_t v_safety_4769_; lean_object* v_name_4770_; lean_object* v___x_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; 
v_toConstantVal_4768_ = lean_ctor_get(v___y_4761_, 0);
lean_inc_ref(v_toConstantVal_4768_);
v_safety_4769_ = lean_ctor_get_uint8(v___y_4761_, sizeof(void*)*4);
v_name_4770_ = lean_ctor_get(v_toConstantVal_4768_, 0);
v___x_4771_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__1);
lean_inc(v_name_4770_);
v___x_4772_ = l_Lean_MessageData_ofName(v_name_4770_);
v___x_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4773_, 0, v___x_4771_);
lean_ctor_set(v___x_4773_, 1, v___x_4772_);
v___x_4774_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4775_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4775_, 0, v___x_4773_);
lean_ctor_set(v___x_4775_, 1, v___x_4774_);
v___x_4776_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4775_, v___y_4760_, v___y_4759_);
if (lean_obj_tag(v___x_4776_) == 0)
{
lean_dec_ref_known(v___x_4776_, 1);
v___y_4743_ = v___y_4762_;
v___y_4744_ = v___y_4761_;
v_toConstantVal_4745_ = v_toConstantVal_4768_;
v_safety_4746_ = v_safety_4769_;
v___y_4747_ = v___y_4760_;
v___y_4748_ = v___y_4759_;
goto v___jp_4742_;
}
else
{
lean_dec_ref(v_toConstantVal_4768_);
lean_dec_ref(v___y_4761_);
lean_dec(v_decl_3766_);
return v___x_4776_;
}
}
}
}
v___jp_4777_:
{
lean_object* v___x_4783_; uint8_t v_isModule_4784_; 
v___x_4783_ = l_Lean_Environment_header(v___y_4779_);
lean_dec_ref(v___y_4779_);
v_isModule_4784_ = lean_ctor_get_uint8(v___x_4783_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4783_);
if (v_isModule_4784_ == 0)
{
lean_dec_ref(v___y_4781_);
v___y_4725_ = v___y_4782_;
v_exportedInfo_x3f_4726_ = v___x_4674_;
v___y_4727_ = v___y_4780_;
v___y_4728_ = v___y_4778_;
goto v___jp_4724_;
}
else
{
uint8_t v_isExporting_4785_; 
v_isExporting_4785_ = lean_ctor_get_uint8(v___y_4781_, sizeof(void*)*8);
lean_dec_ref(v___y_4781_);
if (v_isExporting_4785_ == 0)
{
v___y_4759_ = v___y_4778_;
v___y_4760_ = v___y_4780_;
v___y_4761_ = v___y_4782_;
v___y_4762_ = v_isModule_4784_;
goto v___jp_4758_;
}
else
{
if (v___x_4494_ == 0)
{
v___y_4725_ = v___y_4782_;
v_exportedInfo_x3f_4726_ = v___x_4674_;
v___y_4727_ = v___y_4780_;
v___y_4728_ = v___y_4778_;
goto v___jp_4724_;
}
else
{
v___y_4759_ = v___y_4778_;
v___y_4760_ = v___y_4780_;
v___y_4761_ = v___y_4782_;
v___y_4762_ = v___x_4494_;
goto v___jp_4758_;
}
}
}
}
v___jp_4786_:
{
lean_object* v___x_4790_; lean_object* v_env_4791_; lean_object* v___x_4792_; 
v___x_4790_ = lean_st_ref_get(v___y_4789_);
v_env_4791_ = lean_ctor_get(v___x_4790_, 0);
lean_inc_ref(v_env_4791_);
lean_dec(v___x_4790_);
v___x_4792_ = lean_st_ref_get(v___y_4789_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4793_; 
v_env_4793_ = lean_ctor_get(v___x_4792_, 0);
lean_inc_ref(v_env_4793_);
lean_dec(v___x_4792_);
v___y_4778_ = v___y_4789_;
v___y_4779_ = v_env_4791_;
v___y_4780_ = v___y_4788_;
v___y_4781_ = v_env_4793_;
v___y_4782_ = v_defn_4787_;
goto v___jp_4777_;
}
else
{
if (v___x_4494_ == 0)
{
lean_dec(v___x_4792_);
lean_dec_ref(v_env_4791_);
v___y_4725_ = v_defn_4787_;
v_exportedInfo_x3f_4726_ = v___x_4674_;
v___y_4727_ = v___y_4788_;
v___y_4728_ = v___y_4789_;
goto v___jp_4724_;
}
else
{
lean_object* v_env_4794_; 
v_env_4794_ = lean_ctor_get(v___x_4792_, 0);
lean_inc_ref(v_env_4794_);
lean_dec(v___x_4792_);
v___y_4778_ = v___y_4789_;
v___y_4779_ = v_env_4791_;
v___y_4780_ = v___y_4788_;
v___y_4781_ = v_env_4794_;
v___y_4782_ = v_defn_4787_;
goto v___jp_4777_;
}
}
}
}
}
}
else
{
goto v___jp_4337_;
}
v___jp_4495_:
{
lean_object* v___x_4507_; 
lean_inc_ref(v___y_4497_);
v___x_4507_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4499_, v___y_4497_, v___y_4504_, v___y_4506_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v___x_4508_; lean_object* v___x_4510_; uint8_t v_isShared_4511_; uint8_t v_isSharedCheck_4554_; 
lean_dec_ref_known(v___x_4507_, 1);
lean_dec(v___y_4505_);
lean_inc_ref(v___y_4501_);
v___x_4508_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4501_, v___y_4500_);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4508_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v___x_4508_, 0);
lean_dec(v_unused_4555_);
v___x_4510_ = v___x_4508_;
v_isShared_4511_ = v_isSharedCheck_4554_;
goto v_resetjp_4509_;
}
else
{
lean_dec(v___x_4508_);
v___x_4510_ = lean_box(0);
v_isShared_4511_ = v_isSharedCheck_4554_;
goto v_resetjp_4509_;
}
v_resetjp_4509_:
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4498_);
v___x_4513_ = l_Lean_Elab_async;
v___x_4514_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_4512_, v___x_4513_);
lean_dec_ref(v___x_4512_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v_r_4516_; 
lean_del_object(v___x_4510_);
lean_dec_ref(v___y_4502_);
lean_dec_ref(v___y_4496_);
v___x_4515_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4497_, v___y_4500_);
lean_dec_ref(v___x_4515_);
v_r_4516_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v___y_4498_, v___y_4500_);
if (lean_obj_tag(v_r_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4519_; uint8_t v_isShared_4520_; uint8_t v_isSharedCheck_4526_; 
v_a_4517_ = lean_ctor_get(v_r_4516_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v_r_4516_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4519_ = v_r_4516_;
v_isShared_4520_ = v_isSharedCheck_4526_;
goto v_resetjp_4518_;
}
else
{
lean_inc(v_a_4517_);
lean_dec(v_r_4516_);
v___x_4519_ = lean_box(0);
v_isShared_4520_ = v_isSharedCheck_4526_;
goto v_resetjp_4518_;
}
v_resetjp_4518_:
{
lean_object* v___x_4522_; 
lean_inc(v_a_4517_);
if (v_isShared_4520_ == 0)
{
lean_ctor_set_tag(v___x_4519_, 1);
v___x_4522_ = v___x_4519_;
goto v_reusejp_4521_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4517_);
v___x_4522_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4521_;
}
v_reusejp_4521_:
{
lean_object* v___x_4523_; 
v___x_4523_ = lean_apply_2(v___y_4503_, v___x_4522_, lean_box(0));
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_dec_ref_known(v___x_4523_, 1);
v___y_3772_ = v___y_4500_;
v___y_3773_ = v___y_4501_;
v_a_3774_ = v_a_4517_;
goto v___jp_3771_;
}
else
{
lean_object* v_a_4524_; 
lean_dec(v_a_4517_);
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v___x_4523_, 1);
v___y_3785_ = v___y_4500_;
v___y_3786_ = v___y_4501_;
v_a_3787_ = v_a_4524_;
goto v___jp_3784_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4528_; lean_object* v___x_4529_; 
v_a_4527_ = lean_ctor_get(v_r_4516_, 0);
lean_inc(v_a_4527_);
lean_dec_ref_known(v_r_4516_, 1);
v___x_4528_ = lean_box(0);
v___x_4529_ = lean_apply_2(v___y_4503_, v___x_4528_, lean_box(0));
if (lean_obj_tag(v___x_4529_) == 0)
{
lean_dec_ref_known(v___x_4529_, 1);
v___y_3785_ = v___y_4500_;
v___y_3786_ = v___y_4501_;
v_a_3787_ = v_a_4527_;
goto v___jp_3784_;
}
else
{
lean_object* v_a_4530_; 
lean_dec(v_a_4527_);
v_a_4530_ = lean_ctor_get(v___x_4529_, 0);
lean_inc(v_a_4530_);
lean_dec_ref_known(v___x_4529_, 1);
v___y_3785_ = v___y_4500_;
v___y_3786_ = v___y_4501_;
v_a_3787_ = v_a_4530_;
goto v___jp_3784_;
}
}
}
else
{
lean_object* v___x_4531_; lean_object* v___x_4533_; 
lean_dec_ref(v___y_4503_);
lean_dec_ref(v___y_4501_);
lean_dec_ref(v___y_4497_);
lean_dec(v_decl_3766_);
v___x_4531_ = l_IO_CancelToken_new();
if (v_isShared_4511_ == 0)
{
lean_ctor_set_tag(v___x_4510_, 1);
lean_ctor_set(v___x_4510_, 0, v___x_4531_);
v___x_4533_ = v___x_4510_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4531_);
v___x_4533_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; 
v___x_4534_ = lean_unsigned_to_nat(0u);
v___x_4535_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_4536_ = l_Lean_Name_toString(v___x_4535_, v_hasTrace_3826_);
lean_inc_ref(v___x_4533_);
v___x_4537_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4502_, v___x_4533_, v___x_4536_, v___y_4498_, v___y_4500_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v_checked_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; lean_object* v___x_4544_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v_checked_4539_ = lean_ctor_get(v___y_4496_, 2);
lean_inc_ref(v_checked_4539_);
lean_dec_ref(v___y_4496_);
v___x_4540_ = lean_io_map_task(v_a_4538_, v_checked_4539_, v___x_4534_, v___x_4494_);
v___x_4541_ = lean_box(0);
v___x_4542_ = lean_box(2);
v___x_4543_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4543_, 0, v___x_4541_);
lean_ctor_set(v___x_4543_, 1, v___x_4542_);
lean_ctor_set(v___x_4543_, 2, v___x_4533_);
lean_ctor_set(v___x_4543_, 3, v___x_4540_);
v___x_4544_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4543_, v___y_4500_);
return v___x_4544_;
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v___x_4533_);
lean_dec_ref(v___y_4496_);
v_a_4545_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4537_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4537_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4567_; 
lean_dec_ref(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec_ref(v___y_4497_);
lean_dec_ref(v___y_4496_);
lean_dec(v_decl_3766_);
v_a_4556_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4567_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4567_ == 0)
{
v___x_4558_ = v___x_4507_;
v_isShared_4559_ = v_isSharedCheck_4567_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4507_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4567_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; lean_object* v___x_4563_; lean_object* v___x_4565_; 
v___x_4560_ = lean_io_error_to_string(v_a_4556_);
v___x_4561_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4561_, 0, v___x_4560_);
v___x_4562_ = l_Lean_MessageData_ofFormat(v___x_4561_);
v___x_4563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4563_, 0, v___y_4505_);
lean_ctor_set(v___x_4563_, 1, v___x_4562_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___x_4563_);
v___x_4565_ = v___x_4558_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
}
}
v___jp_4568_:
{
lean_object* v_ref_4577_; lean_object* v___x_4578_; 
v_ref_4577_ = lean_ctor_get(v___y_4571_, 2);
lean_inc_ref(v___y_4575_);
v___x_4578_ = l_Lean_Environment_addConstAsync(v___y_4575_, v___y_4569_, v___y_4573_, v___y_4576_, v___x_4494_, v_hasTrace_3826_);
if (lean_obj_tag(v___x_4578_) == 0)
{
lean_object* v_a_4579_; lean_object* v_mainEnv_4580_; lean_object* v_asyncEnv_4581_; lean_object* v___f_4582_; lean_object* v___f_4583_; lean_object* v___x_4584_; 
v_a_4579_ = lean_ctor_get(v___x_4578_, 0);
lean_inc_n(v_a_4579_, 3);
lean_dec_ref_known(v___x_4578_, 1);
v_mainEnv_4580_ = lean_ctor_get(v_a_4579_, 0);
lean_inc_ref(v_mainEnv_4580_);
v_asyncEnv_4581_ = lean_ctor_get(v_a_4579_, 1);
lean_inc_ref_n(v_asyncEnv_4581_, 2);
lean_inc(v_ref_4577_);
lean_inc(v___y_4572_);
v___f_4582_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4582_, 0, v___y_4572_);
lean_closure_set(v___f_4582_, 1, v_a_4579_);
lean_closure_set(v___f_4582_, 2, v_ref_4577_);
lean_inc(v_decl_3766_);
v___f_4583_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4583_, 0, v_a_4579_);
lean_closure_set(v___f_4583_, 1, v_asyncEnv_4581_);
lean_closure_set(v___f_4583_, 2, v_decl_3766_);
v___x_4584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4584_, 0, v___y_4570_);
if (lean_obj_tag(v___y_4574_) == 0)
{
lean_inc(v_ref_4577_);
lean_inc_ref(v___x_4584_);
v___y_4496_ = v___y_4575_;
v___y_4497_ = v_asyncEnv_4581_;
v___y_4498_ = v___y_4571_;
v___y_4499_ = v_a_4579_;
v___y_4500_ = v___y_4572_;
v___y_4501_ = v_mainEnv_4580_;
v___y_4502_ = v___f_4583_;
v___y_4503_ = v___f_4582_;
v___y_4504_ = v___x_4584_;
v___y_4505_ = v_ref_4577_;
v___y_4506_ = v___x_4584_;
goto v___jp_4495_;
}
else
{
lean_inc(v_ref_4577_);
v___y_4496_ = v___y_4575_;
v___y_4497_ = v_asyncEnv_4581_;
v___y_4498_ = v___y_4571_;
v___y_4499_ = v_a_4579_;
v___y_4500_ = v___y_4572_;
v___y_4501_ = v_mainEnv_4580_;
v___y_4502_ = v___f_4583_;
v___y_4503_ = v___f_4582_;
v___y_4504_ = v___x_4584_;
v___y_4505_ = v_ref_4577_;
v___y_4506_ = v___y_4574_;
goto v___jp_4495_;
}
}
else
{
lean_object* v_a_4585_; lean_object* v___x_4587_; uint8_t v_isShared_4588_; uint8_t v_isSharedCheck_4596_; 
lean_dec_ref(v___y_4575_);
lean_dec(v___y_4574_);
lean_dec_ref(v___y_4570_);
lean_dec(v_decl_3766_);
v_a_4585_ = lean_ctor_get(v___x_4578_, 0);
v_isSharedCheck_4596_ = !lean_is_exclusive(v___x_4578_);
if (v_isSharedCheck_4596_ == 0)
{
v___x_4587_ = v___x_4578_;
v_isShared_4588_ = v_isSharedCheck_4596_;
goto v_resetjp_4586_;
}
else
{
lean_inc(v_a_4585_);
lean_dec(v___x_4578_);
v___x_4587_ = lean_box(0);
v_isShared_4588_ = v_isSharedCheck_4596_;
goto v_resetjp_4586_;
}
v_resetjp_4586_:
{
lean_object* v___x_4589_; lean_object* v___x_4590_; lean_object* v___x_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4589_ = lean_io_error_to_string(v_a_4585_);
v___x_4590_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4590_, 0, v___x_4589_);
v___x_4591_ = l_Lean_MessageData_ofFormat(v___x_4590_);
lean_inc(v_ref_4577_);
v___x_4592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4592_, 0, v_ref_4577_);
lean_ctor_set(v___x_4592_, 1, v___x_4591_);
if (v_isShared_4588_ == 0)
{
lean_ctor_set(v___x_4587_, 0, v___x_4592_);
v___x_4594_ = v___x_4587_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
}
}
v___jp_4597_:
{
lean_object* v___x_4604_; 
v___x_4604_ = lean_st_ref_get(v___y_4603_);
if (lean_obj_tag(v_exportedInfo_x3f_4601_) == 0)
{
lean_object* v_env_4605_; lean_object* v___x_4606_; 
v_env_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc_ref(v_env_4605_);
lean_dec(v___x_4604_);
v___x_4606_ = lean_box(0);
v___y_4569_ = v___y_4600_;
v___y_4570_ = v___y_4599_;
v___y_4571_ = v___y_4602_;
v___y_4572_ = v___y_4603_;
v___y_4573_ = v___y_4598_;
v___y_4574_ = v_exportedInfo_x3f_4601_;
v___y_4575_ = v_env_4605_;
v___y_4576_ = v___x_4606_;
goto v___jp_4568_;
}
else
{
lean_object* v_env_4607_; lean_object* v_val_4608_; uint8_t v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; 
v_env_4607_ = lean_ctor_get(v___x_4604_, 0);
lean_inc_ref(v_env_4607_);
lean_dec(v___x_4604_);
v_val_4608_ = lean_ctor_get(v_exportedInfo_x3f_4601_, 0);
v___x_4609_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4608_);
v___x_4610_ = lean_box(v___x_4609_);
v___x_4611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
v___y_4569_ = v___y_4600_;
v___y_4570_ = v___y_4599_;
v___y_4571_ = v___y_4602_;
v___y_4572_ = v___y_4603_;
v___y_4573_ = v___y_4598_;
v___y_4574_ = v_exportedInfo_x3f_4601_;
v___y_4575_ = v_env_4607_;
v___y_4576_ = v___x_4611_;
goto v___jp_4568_;
}
}
v___jp_4612_:
{
lean_object* v___x_4618_; 
lean_inc_ref(v___y_4614_);
v___x_4618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4618_, 0, v___y_4614_);
v___y_4598_ = v___y_4613_;
v___y_4599_ = v___y_4614_;
v___y_4600_ = v___y_4615_;
v_exportedInfo_x3f_4601_ = v___x_4618_;
v___y_4602_ = v___y_4616_;
v___y_4603_ = v___y_4617_;
goto v___jp_4597_;
}
v___jp_4619_:
{
lean_object* v___x_4625_; 
lean_inc_ref(v___y_4621_);
v___x_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4625_, 0, v___y_4621_);
v___y_4598_ = v___y_4620_;
v___y_4599_ = v___y_4621_;
v___y_4600_ = v___y_4622_;
v_exportedInfo_x3f_4601_ = v___x_4625_;
v___y_4602_ = v___y_4623_;
v___y_4603_ = v___y_4624_;
goto v___jp_4597_;
}
}
else
{
goto v___jp_4337_;
}
v___jp_4190_:
{
lean_object* v___x_4194_; double v___x_4195_; double v___x_4196_; double v___x_4197_; double v___x_4198_; double v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4194_ = lean_io_mono_nanos_now();
v___x_4195_ = lean_float_of_nat(v___y_4191_);
v___x_4196_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4197_ = lean_float_div(v___x_4195_, v___x_4196_);
v___x_4198_ = lean_float_of_nat(v___x_4194_);
v___x_4199_ = lean_float_div(v___x_4198_, v___x_4196_);
v___x_4200_ = lean_box_float(v___x_4197_);
v___x_4201_ = lean_box_float(v___x_4199_);
v___x_4202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4203_, 0, v_a_4193_);
lean_ctor_set(v___x_4203_, 1, v___x_4202_);
v___x_4204_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3960_, v_hasTrace_3826_, v___x_4187_, v_options_3824_, v___x_4189_, v___y_4192_, v___f_4186_, v___x_4203_, v_a_3768_, v_a_3769_);
return v___x_4204_;
}
v___jp_4205_:
{
if (lean_obj_tag(v___y_4208_) == 0)
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
v_a_4209_ = lean_ctor_get(v___y_4208_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___y_4208_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___y_4208_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___y_4208_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
lean_ctor_set_tag(v___x_4211_, 1);
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
v___y_4191_ = v___y_4206_;
v___y_4192_ = v___y_4207_;
v_a_4193_ = v___x_4214_;
goto v___jp_4190_;
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
v_a_4217_ = lean_ctor_get(v___y_4208_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___y_4208_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___y_4208_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___y_4208_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
lean_ctor_set_tag(v___x_4219_, 0);
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
v___y_4191_ = v___y_4206_;
v___y_4192_ = v___y_4207_;
v_a_4193_ = v___x_4222_;
goto v___jp_4190_;
}
}
}
}
v___jp_4225_:
{
lean_object* v___x_4230_; lean_object* v___x_4231_; 
v___x_4230_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4231_ = lean_apply_5(v___y_4229_, v___x_4230_, v___y_4228_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4226_;
v___y_4207_ = v___y_4227_;
v___y_4208_ = v___x_4231_;
goto v___jp_4205_;
}
v___jp_4232_:
{
lean_object* v___x_4240_; uint8_t v_isModule_4241_; 
v___x_4240_ = l_Lean_Environment_header(v___y_4235_);
lean_dec_ref(v___y_4235_);
v_isModule_4241_ = lean_ctor_get_uint8(v___x_4240_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4240_);
if (v_isModule_4241_ == 0)
{
lean_dec_ref(v___y_4238_);
lean_dec_ref(v___y_4234_);
v___y_4226_ = v___y_4233_;
v___y_4227_ = v___y_4236_;
v___y_4228_ = v___y_4237_;
v___y_4229_ = v___y_4239_;
goto v___jp_4225_;
}
else
{
lean_dec_ref(v___y_4239_);
lean_dec(v___y_4237_);
if (v___x_4189_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; 
lean_dec_ref(v___y_4234_);
v___x_4242_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4243_ = lean_apply_4(v___y_4238_, v___x_4242_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4236_;
v___y_4208_ = v___x_4243_;
goto v___jp_4205_;
}
else
{
lean_object* v_toConstantVal_4244_; lean_object* v_name_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; 
v_toConstantVal_4244_ = lean_ctor_get(v___y_4234_, 0);
lean_inc_ref(v_toConstantVal_4244_);
lean_dec_ref(v___y_4234_);
v_name_4245_ = lean_ctor_get(v_toConstantVal_4244_, 0);
lean_inc(v_name_4245_);
lean_dec_ref(v_toConstantVal_4244_);
v___x_4246_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4247_ = l_Lean_MessageData_ofName(v_name_4245_);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4246_);
lean_ctor_set(v___x_4248_, 1, v___x_4247_);
v___x_4249_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4250_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; lean_object* v___x_4253_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4253_ = lean_apply_4(v___y_4238_, v_a_4252_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4236_;
v___y_4208_ = v___x_4253_;
goto v___jp_4205_;
}
else
{
lean_dec_ref(v___y_4238_);
v___y_4206_ = v___y_4233_;
v___y_4207_ = v___y_4236_;
v___y_4208_ = v___x_4251_;
goto v___jp_4205_;
}
}
}
}
v___jp_4254_:
{
if (v___x_4189_ == 0)
{
lean_object* v___x_4259_; lean_object* v___x_4260_; 
lean_dec_ref(v___y_4258_);
v___x_4259_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4260_ = lean_apply_4(v___y_4257_, v___x_4259_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4255_;
v___y_4207_ = v___y_4256_;
v___y_4208_ = v___x_4260_;
goto v___jp_4205_;
}
else
{
lean_object* v_toConstantVal_4261_; lean_object* v_name_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v_toConstantVal_4261_ = lean_ctor_get(v___y_4258_, 0);
lean_inc_ref(v_toConstantVal_4261_);
lean_dec_ref(v___y_4258_);
v_name_4262_ = lean_ctor_get(v_toConstantVal_4261_, 0);
lean_inc(v_name_4262_);
lean_dec_ref(v_toConstantVal_4261_);
v___x_4263_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4264_ = l_Lean_MessageData_ofName(v_name_4262_);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4267_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; lean_object* v___x_4270_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4270_ = lean_apply_4(v___y_4257_, v_a_4269_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4255_;
v___y_4207_ = v___y_4256_;
v___y_4208_ = v___x_4270_;
goto v___jp_4205_;
}
else
{
lean_dec_ref(v___y_4257_);
v___y_4206_ = v___y_4255_;
v___y_4207_ = v___y_4256_;
v___y_4208_ = v___x_4268_;
goto v___jp_4205_;
}
}
}
v___jp_4271_:
{
lean_object* v___x_4276_; lean_object* v___x_4277_; 
v___x_4276_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4277_ = lean_apply_5(v___y_4274_, v___x_4276_, v___y_4275_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4206_ = v___y_4272_;
v___y_4207_ = v___y_4273_;
v___y_4208_ = v___x_4277_;
goto v___jp_4205_;
}
v___jp_4278_:
{
lean_object* v___x_4288_; uint8_t v_isModule_4289_; 
v___x_4288_ = l_Lean_Environment_header(v___y_4285_);
lean_dec_ref(v___y_4285_);
v_isModule_4289_ = lean_ctor_get_uint8(v___x_4288_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4288_);
if (v_isModule_4289_ == 0)
{
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4286_);
lean_dec_ref(v___y_4281_);
v___y_4272_ = v___y_4279_;
v___y_4273_ = v___y_4283_;
v___y_4274_ = v___y_4282_;
v___y_4275_ = v___y_4284_;
goto v___jp_4271_;
}
else
{
uint8_t v_isExporting_4290_; 
v_isExporting_4290_ = lean_ctor_get_uint8(v___y_4281_, sizeof(void*)*8);
lean_dec_ref(v___y_4281_);
if (v_isExporting_4290_ == 0)
{
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4282_);
v___y_4255_ = v___y_4279_;
v___y_4256_ = v___y_4283_;
v___y_4257_ = v___y_4286_;
v___y_4258_ = v___y_4287_;
goto v___jp_4254_;
}
else
{
if (v___y_4280_ == 0)
{
lean_dec_ref(v___y_4287_);
lean_dec_ref(v___y_4286_);
v___y_4272_ = v___y_4279_;
v___y_4273_ = v___y_4283_;
v___y_4274_ = v___y_4282_;
v___y_4275_ = v___y_4284_;
goto v___jp_4271_;
}
else
{
lean_dec(v___y_4284_);
lean_dec_ref(v___y_4282_);
v___y_4255_ = v___y_4279_;
v___y_4256_ = v___y_4283_;
v___y_4257_ = v___y_4286_;
v___y_4258_ = v___y_4287_;
goto v___jp_4254_;
}
}
}
}
v___jp_4291_:
{
lean_object* v___x_4295_; double v___x_4296_; double v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v___x_4295_ = lean_io_get_num_heartbeats();
v___x_4296_ = lean_float_of_nat(v___y_4293_);
v___x_4297_ = lean_float_of_nat(v___x_4295_);
v___x_4298_ = lean_box_float(v___x_4296_);
v___x_4299_ = lean_box_float(v___x_4297_);
v___x_4300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4301_, 0, v_a_4294_);
lean_ctor_set(v___x_4301_, 1, v___x_4300_);
v___x_4302_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3960_, v_hasTrace_3826_, v___x_4187_, v_options_3824_, v___x_4189_, v___y_4292_, v___f_4186_, v___x_4301_, v_a_3768_, v_a_3769_);
return v___x_4302_;
}
v___jp_4303_:
{
if (lean_obj_tag(v___y_4306_) == 0)
{
lean_object* v_a_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
v_a_4307_ = lean_ctor_get(v___y_4306_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___y_4306_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___y_4306_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_a_4307_);
lean_dec(v___y_4306_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 1);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_a_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
v___y_4292_ = v___y_4304_;
v___y_4293_ = v___y_4305_;
v_a_4294_ = v___x_4312_;
goto v___jp_4291_;
}
}
}
else
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4322_; 
v_a_4315_ = lean_ctor_get(v___y_4306_, 0);
v_isSharedCheck_4322_ = !lean_is_exclusive(v___y_4306_);
if (v_isSharedCheck_4322_ == 0)
{
v___x_4317_ = v___y_4306_;
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___y_4306_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4322_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v___x_4320_; 
if (v_isShared_4318_ == 0)
{
lean_ctor_set_tag(v___x_4317_, 0);
v___x_4320_ = v___x_4317_;
goto v_reusejp_4319_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_a_4315_);
v___x_4320_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4319_;
}
v_reusejp_4319_:
{
v___y_4292_ = v___y_4304_;
v___y_4293_ = v___y_4305_;
v_a_4294_ = v___x_4320_;
goto v___jp_4291_;
}
}
}
}
v___jp_4323_:
{
lean_object* v___x_4328_; lean_object* v___x_4329_; 
v___x_4328_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4329_ = lean_apply_5(v___y_4327_, v___x_4328_, v___y_4324_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4304_ = v___y_4325_;
v___y_4305_ = v___y_4326_;
v___y_4306_ = v___x_4329_;
goto v___jp_4303_;
}
v___jp_4330_:
{
lean_object* v___x_4335_; lean_object* v___x_4336_; 
v___x_4335_ = lean_box(0);
lean_inc(v_a_3769_);
lean_inc_ref(v_a_3768_);
v___x_4336_ = lean_apply_5(v___y_4334_, v___x_4335_, v___y_4331_, v_a_3768_, v_a_3769_, lean_box(0));
v___y_4304_ = v___y_4332_;
v___y_4305_ = v___y_4333_;
v___y_4306_ = v___x_4336_;
goto v___jp_4303_;
}
v___jp_4337_:
{
lean_object* v___x_4338_; lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4492_; 
v___x_4338_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3769_);
v_a_4339_ = lean_ctor_get(v___x_4338_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4338_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4341_ = v___x_4338_;
v_isShared_4342_ = v_isSharedCheck_4492_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4338_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4492_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; uint8_t v___x_4344_; 
v___x_4343_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4344_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3824_, v___x_4343_);
if (v___x_4344_ == 0)
{
lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v_env_4347_; lean_object* v_nextMacroScope_4348_; lean_object* v_ngen_4349_; lean_object* v_auxDeclNGen_4350_; lean_object* v_traceState_4351_; lean_object* v_recordedDeps_4352_; lean_object* v_messages_4353_; lean_object* v_infoState_4354_; lean_object* v_snapshotTasks_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4405_; 
v___x_4345_ = lean_io_mono_nanos_now();
v___x_4346_ = lean_st_ref_take(v_a_3769_);
v_env_4347_ = lean_ctor_get(v___x_4346_, 0);
v_nextMacroScope_4348_ = lean_ctor_get(v___x_4346_, 1);
v_ngen_4349_ = lean_ctor_get(v___x_4346_, 2);
v_auxDeclNGen_4350_ = lean_ctor_get(v___x_4346_, 3);
v_traceState_4351_ = lean_ctor_get(v___x_4346_, 4);
v_recordedDeps_4352_ = lean_ctor_get(v___x_4346_, 6);
v_messages_4353_ = lean_ctor_get(v___x_4346_, 7);
v_infoState_4354_ = lean_ctor_get(v___x_4346_, 8);
v_snapshotTasks_4355_ = lean_ctor_get(v___x_4346_, 9);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4405_ == 0)
{
lean_object* v_unused_4406_; 
v_unused_4406_ = lean_ctor_get(v___x_4346_, 5);
lean_dec(v_unused_4406_);
v___x_4357_ = v___x_4346_;
v_isShared_4358_ = v_isSharedCheck_4405_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_snapshotTasks_4355_);
lean_inc(v_infoState_4354_);
lean_inc(v_messages_4353_);
lean_inc(v_recordedDeps_4352_);
lean_inc(v_traceState_4351_);
lean_inc(v_auxDeclNGen_4350_);
lean_inc(v_ngen_4349_);
lean_inc(v_nextMacroScope_4348_);
lean_inc(v_env_4347_);
lean_dec(v___x_4346_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4405_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4363_; 
lean_inc(v_decl_3766_);
v___x_4359_ = l_Lean_Declaration_getNames(v_decl_3766_);
v___x_4360_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4347_, v___x_4359_);
v___x_4361_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4358_ == 0)
{
lean_ctor_set(v___x_4357_, 5, v___x_4361_);
lean_ctor_set(v___x_4357_, 0, v___x_4360_);
v___x_4363_ = v___x_4357_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4404_, 1, v_nextMacroScope_4348_);
lean_ctor_set(v_reuseFailAlloc_4404_, 2, v_ngen_4349_);
lean_ctor_set(v_reuseFailAlloc_4404_, 3, v_auxDeclNGen_4350_);
lean_ctor_set(v_reuseFailAlloc_4404_, 4, v_traceState_4351_);
lean_ctor_set(v_reuseFailAlloc_4404_, 5, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4404_, 6, v_recordedDeps_4352_);
lean_ctor_set(v_reuseFailAlloc_4404_, 7, v_messages_4353_);
lean_ctor_set(v_reuseFailAlloc_4404_, 8, v_infoState_4354_);
lean_ctor_set(v_reuseFailAlloc_4404_, 9, v_snapshotTasks_4355_);
v___x_4363_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; lean_object* v___x_4365_; lean_object* v___x_4366_; lean_object* v___x_4367_; lean_object* v___f_4368_; 
v___x_4364_ = lean_st_ref_put(v_a_3769_, v___x_4363_);
v___x_4365_ = lean_box(0);
v___x_4366_ = lean_box(v_hasTrace_3826_);
v___x_4367_ = lean_box(v___x_4344_);
lean_inc(v_decl_3766_);
v___f_4368_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 11, 6);
lean_closure_set(v___f_4368_, 0, v_decl_3766_);
lean_closure_set(v___f_4368_, 1, v___x_4366_);
lean_closure_set(v___f_4368_, 2, v___x_4367_);
lean_closure_set(v___f_4368_, 3, v___x_4361_);
lean_closure_set(v___f_4368_, 4, v_cls_3960_);
lean_closure_set(v___f_4368_, 5, v___x_4365_);
switch(lean_obj_tag(v_decl_3766_))
{
case 2:
{
lean_object* v_val_4369_; lean_object* v___f_4370_; lean_object* v___x_4371_; lean_object* v___f_4372_; lean_object* v___x_4373_; 
lean_del_object(v___x_4341_);
v_val_4369_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref_n(v_val_4369_, 3);
lean_dec_ref_known(v_decl_3766_, 1);
v___f_4370_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4370_, 0, v_val_4369_);
lean_closure_set(v___f_4370_, 1, v___f_4368_);
v___x_4371_ = lean_box(v___x_4344_);
lean_inc_ref(v___f_4370_);
v___f_4372_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 3);
lean_closure_set(v___f_4372_, 0, v_val_4369_);
lean_closure_set(v___f_4372_, 1, v___x_4371_);
lean_closure_set(v___f_4372_, 2, v___f_4370_);
v___x_4373_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4374_; 
v_env_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc_ref(v_env_4374_);
lean_dec(v___x_4373_);
v___y_4233_ = v___x_4345_;
v___y_4234_ = v_val_4369_;
v___y_4235_ = v_env_4374_;
v___y_4236_ = v_a_4339_;
v___y_4237_ = v___x_4365_;
v___y_4238_ = v___f_4372_;
v___y_4239_ = v___f_4370_;
goto v___jp_4232_;
}
else
{
if (v___x_4344_ == 0)
{
lean_dec(v___x_4373_);
lean_dec_ref(v___f_4372_);
lean_dec_ref(v_val_4369_);
v___y_4226_ = v___x_4345_;
v___y_4227_ = v_a_4339_;
v___y_4228_ = v___x_4365_;
v___y_4229_ = v___f_4370_;
goto v___jp_4225_;
}
else
{
lean_object* v_env_4375_; 
v_env_4375_ = lean_ctor_get(v___x_4373_, 0);
lean_inc_ref(v_env_4375_);
lean_dec(v___x_4373_);
v___y_4233_ = v___x_4345_;
v___y_4234_ = v_val_4369_;
v___y_4235_ = v_env_4375_;
v___y_4236_ = v_a_4339_;
v___y_4237_ = v___x_4365_;
v___y_4238_ = v___f_4372_;
v___y_4239_ = v___f_4370_;
goto v___jp_4232_;
}
}
}
case 1:
{
lean_object* v_val_4376_; lean_object* v___x_4377_; 
lean_del_object(v___x_4341_);
v_val_4376_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref(v_val_4376_);
lean_dec_ref_known(v_decl_3766_, 1);
v___x_4377_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4368_, v___x_4344_, v_cls_3960_, v___x_4365_, v_forceExpose_3767_, v_val_4376_, v_a_3768_, v_a_3769_);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4377_;
goto v___jp_4205_;
}
case 5:
{
lean_object* v_defns_4378_; 
lean_del_object(v___x_4341_);
v_defns_4378_ = lean_ctor_get(v_decl_3766_, 0);
if (lean_obj_tag(v_defns_4378_) == 1)
{
lean_object* v_tail_4379_; 
v_tail_4379_ = lean_ctor_get(v_defns_4378_, 1);
if (lean_obj_tag(v_tail_4379_) == 0)
{
lean_object* v_head_4380_; lean_object* v___x_4381_; 
lean_inc_ref(v_defns_4378_);
lean_dec_ref_known(v_decl_3766_, 1);
v_head_4380_ = lean_ctor_get(v_defns_4378_, 0);
lean_inc(v_head_4380_);
lean_dec_ref_known(v_defns_4378_, 2);
v___x_4381_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v___f_4368_, v___x_4344_, v_cls_3960_, v___x_4365_, v_forceExpose_3767_, v_head_4380_, v_a_3768_, v_a_3769_);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4381_;
goto v___jp_4205_;
}
else
{
lean_object* v___x_4382_; 
lean_dec_ref(v___f_4368_);
lean_inc_ref(v_decl_3766_);
v___x_4382_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec_ref_known(v_decl_3766_, 1);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4382_;
goto v___jp_4205_;
}
}
else
{
lean_object* v___x_4383_; 
lean_dec_ref(v___f_4368_);
lean_inc_ref(v_decl_3766_);
v___x_4383_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec_ref_known(v_decl_3766_, 1);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4383_;
goto v___jp_4205_;
}
}
case 3:
{
lean_object* v_val_4384_; lean_object* v___f_4385_; lean_object* v___f_4386_; lean_object* v___x_4387_; lean_object* v_env_4388_; lean_object* v___x_4389_; 
lean_del_object(v___x_4341_);
v_val_4384_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref_n(v_val_4384_, 3);
lean_dec_ref_known(v_decl_3766_, 1);
v___f_4385_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4385_, 0, v_val_4384_);
lean_closure_set(v___f_4385_, 1, v___f_4368_);
lean_inc_ref(v___f_4385_);
v___f_4386_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed), 6, 2);
lean_closure_set(v___f_4386_, 0, v_val_4384_);
lean_closure_set(v___f_4386_, 1, v___f_4385_);
v___x_4387_ = lean_st_ref_get(v_a_3769_);
v_env_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc_ref(v_env_4388_);
lean_dec(v___x_4387_);
v___x_4389_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
lean_object* v_env_4390_; 
v_env_4390_ = lean_ctor_get(v___x_4389_, 0);
lean_inc_ref(v_env_4390_);
lean_dec(v___x_4389_);
v___y_4279_ = v___x_4345_;
v___y_4280_ = v___x_4344_;
v___y_4281_ = v_env_4390_;
v___y_4282_ = v___f_4385_;
v___y_4283_ = v_a_4339_;
v___y_4284_ = v___x_4365_;
v___y_4285_ = v_env_4388_;
v___y_4286_ = v___f_4386_;
v___y_4287_ = v_val_4384_;
goto v___jp_4278_;
}
else
{
if (v___x_4344_ == 0)
{
lean_dec(v___x_4389_);
lean_dec_ref(v_env_4388_);
lean_dec_ref(v___f_4386_);
lean_dec_ref(v_val_4384_);
v___y_4272_ = v___x_4345_;
v___y_4273_ = v_a_4339_;
v___y_4274_ = v___f_4385_;
v___y_4275_ = v___x_4365_;
goto v___jp_4271_;
}
else
{
lean_object* v_env_4391_; 
v_env_4391_ = lean_ctor_get(v___x_4389_, 0);
lean_inc_ref(v_env_4391_);
lean_dec(v___x_4389_);
v___y_4279_ = v___x_4345_;
v___y_4280_ = v___x_4344_;
v___y_4281_ = v_env_4391_;
v___y_4282_ = v___f_4385_;
v___y_4283_ = v_a_4339_;
v___y_4284_ = v___x_4365_;
v___y_4285_ = v_env_4388_;
v___y_4286_ = v___f_4386_;
v___y_4287_ = v_val_4384_;
goto v___jp_4278_;
}
}
}
case 0:
{
lean_object* v_val_4392_; lean_object* v_toConstantVal_4393_; lean_object* v_name_4394_; lean_object* v___x_4396_; 
lean_dec_ref(v___f_4368_);
v_val_4392_ = lean_ctor_get(v_decl_3766_, 0);
v_toConstantVal_4393_ = lean_ctor_get(v_val_4392_, 0);
v_name_4394_ = lean_ctor_get(v_toConstantVal_4393_, 0);
lean_inc_ref(v_val_4392_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v_val_4392_);
v___x_4396_ = v___x_4341_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v_val_4392_);
v___x_4396_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
uint8_t v___x_4397_; lean_object* v___x_4398_; lean_object* v___x_4399_; lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4397_ = 2;
v___x_4398_ = lean_box(v___x_4397_);
v___x_4399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4399_, 0, v___x_4396_);
lean_ctor_set(v___x_4399_, 1, v___x_4398_);
lean_inc(v_name_4394_);
v___x_4400_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4400_, 0, v_name_4394_);
lean_ctor_set(v___x_4400_, 1, v___x_4399_);
v___x_4401_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_decl_3766_, v_hasTrace_3826_, v___x_4344_, v___x_4361_, v_cls_3960_, v___x_4365_, v___x_4400_, v___x_4365_, v_a_3768_, v_a_3769_);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4401_;
goto v___jp_4205_;
}
}
default: 
{
lean_object* v___x_4403_; 
lean_dec_ref(v___f_4368_);
lean_del_object(v___x_4341_);
lean_inc(v_decl_3766_);
v___x_4403_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec(v_decl_3766_);
v___y_4206_ = v___x_4345_;
v___y_4207_ = v_a_4339_;
v___y_4208_ = v___x_4403_;
goto v___jp_4205_;
}
}
}
}
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v_env_4409_; lean_object* v_nextMacroScope_4410_; lean_object* v_ngen_4411_; lean_object* v_auxDeclNGen_4412_; lean_object* v_traceState_4413_; lean_object* v_recordedDeps_4414_; lean_object* v_messages_4415_; lean_object* v_infoState_4416_; lean_object* v_snapshotTasks_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4490_; 
v___x_4407_ = lean_io_get_num_heartbeats();
v___x_4408_ = lean_st_ref_take(v_a_3769_);
v_env_4409_ = lean_ctor_get(v___x_4408_, 0);
v_nextMacroScope_4410_ = lean_ctor_get(v___x_4408_, 1);
v_ngen_4411_ = lean_ctor_get(v___x_4408_, 2);
v_auxDeclNGen_4412_ = lean_ctor_get(v___x_4408_, 3);
v_traceState_4413_ = lean_ctor_get(v___x_4408_, 4);
v_recordedDeps_4414_ = lean_ctor_get(v___x_4408_, 6);
v_messages_4415_ = lean_ctor_get(v___x_4408_, 7);
v_infoState_4416_ = lean_ctor_get(v___x_4408_, 8);
v_snapshotTasks_4417_ = lean_ctor_get(v___x_4408_, 9);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4408_);
if (v_isSharedCheck_4490_ == 0)
{
lean_object* v_unused_4491_; 
v_unused_4491_ = lean_ctor_get(v___x_4408_, 5);
lean_dec(v_unused_4491_);
v___x_4419_ = v___x_4408_;
v_isShared_4420_ = v_isSharedCheck_4490_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_snapshotTasks_4417_);
lean_inc(v_infoState_4416_);
lean_inc(v_messages_4415_);
lean_inc(v_recordedDeps_4414_);
lean_inc(v_traceState_4413_);
lean_inc(v_auxDeclNGen_4412_);
lean_inc(v_ngen_4411_);
lean_inc(v_nextMacroScope_4410_);
lean_inc(v_env_4409_);
lean_dec(v___x_4408_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4490_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4425_; 
lean_inc(v_decl_3766_);
v___x_4421_ = l_Lean_Declaration_getNames(v_decl_3766_);
v___x_4422_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4409_, v___x_4421_);
v___x_4423_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 5, v___x_4423_);
lean_ctor_set(v___x_4419_, 0, v___x_4422_);
v___x_4425_ = v___x_4419_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v___x_4422_);
lean_ctor_set(v_reuseFailAlloc_4489_, 1, v_nextMacroScope_4410_);
lean_ctor_set(v_reuseFailAlloc_4489_, 2, v_ngen_4411_);
lean_ctor_set(v_reuseFailAlloc_4489_, 3, v_auxDeclNGen_4412_);
lean_ctor_set(v_reuseFailAlloc_4489_, 4, v_traceState_4413_);
lean_ctor_set(v_reuseFailAlloc_4489_, 5, v___x_4423_);
lean_ctor_set(v_reuseFailAlloc_4489_, 6, v_recordedDeps_4414_);
lean_ctor_set(v_reuseFailAlloc_4489_, 7, v_messages_4415_);
lean_ctor_set(v_reuseFailAlloc_4489_, 8, v_infoState_4416_);
lean_ctor_set(v_reuseFailAlloc_4489_, 9, v_snapshotTasks_4417_);
v___x_4425_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
lean_object* v___x_4426_; lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___f_4429_; 
v___x_4426_ = lean_st_ref_put(v_a_3769_, v___x_4425_);
v___x_4427_ = lean_box(0);
v___x_4428_ = lean_box(v___x_4344_);
lean_inc(v_decl_3766_);
v___f_4429_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14___boxed), 10, 5);
lean_closure_set(v___f_4429_, 0, v_decl_3766_);
lean_closure_set(v___f_4429_, 1, v___x_4428_);
lean_closure_set(v___f_4429_, 2, v_cls_3960_);
lean_closure_set(v___f_4429_, 3, v___x_4423_);
lean_closure_set(v___f_4429_, 4, v___x_4427_);
switch(lean_obj_tag(v_decl_3766_))
{
case 2:
{
lean_object* v_val_4430_; lean_object* v___f_4431_; lean_object* v___x_4432_; 
lean_del_object(v___x_4341_);
v_val_4430_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref_n(v_val_4430_, 2);
lean_dec_ref_known(v_decl_3766_, 1);
v___f_4431_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 2);
lean_closure_set(v___f_4431_, 0, v_val_4430_);
lean_closure_set(v___f_4431_, 1, v___f_4429_);
v___x_4432_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
if (v___x_4344_ == 0)
{
lean_dec(v___x_4432_);
lean_dec_ref(v_val_4430_);
v___y_4331_ = v___x_4427_;
v___y_4332_ = v_a_4339_;
v___y_4333_ = v___x_4407_;
v___y_4334_ = v___f_4431_;
goto v___jp_4330_;
}
else
{
lean_object* v_env_4433_; lean_object* v___x_4434_; uint8_t v_isModule_4435_; 
v_env_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc_ref(v_env_4433_);
lean_dec(v___x_4432_);
v___x_4434_ = l_Lean_Environment_header(v_env_4433_);
lean_dec_ref(v_env_4433_);
v_isModule_4435_ = lean_ctor_get_uint8(v___x_4434_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4434_);
if (v_isModule_4435_ == 0)
{
lean_dec_ref(v_val_4430_);
v___y_4331_ = v___x_4427_;
v___y_4332_ = v_a_4339_;
v___y_4333_ = v___x_4407_;
v___y_4334_ = v___f_4431_;
goto v___jp_4330_;
}
else
{
if (v___x_4189_ == 0)
{
lean_object* v___x_4436_; lean_object* v___x_4437_; 
v___x_4436_ = lean_box(0);
v___x_4437_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4430_, v___f_4431_, v___x_4436_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_val_4430_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4437_;
goto v___jp_4303_;
}
else
{
lean_object* v_toConstantVal_4438_; lean_object* v_name_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; 
v_toConstantVal_4438_ = lean_ctor_get(v_val_4430_, 0);
v_name_4439_ = lean_ctor_get(v_toConstantVal_4438_, 0);
v___x_4440_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4439_);
v___x_4441_ = l_Lean_MessageData_ofName(v_name_4439_);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4440_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4444_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4444_, 0, v___x_4442_);
lean_ctor_set(v___x_4444_, 1, v___x_4443_);
v___x_4445_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4444_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4447_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc(v_a_4446_);
lean_dec_ref_known(v___x_4445_, 1);
v___x_4447_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_val_4430_, v___f_4431_, v_a_4446_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_val_4430_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4447_;
goto v___jp_4303_;
}
else
{
lean_dec_ref(v___f_4431_);
lean_dec_ref(v_val_4430_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4445_;
goto v___jp_4303_;
}
}
}
}
}
else
{
lean_dec(v___x_4432_);
lean_dec_ref(v_val_4430_);
v___y_4331_ = v___x_4427_;
v___y_4332_ = v_a_4339_;
v___y_4333_ = v___x_4407_;
v___y_4334_ = v___f_4431_;
goto v___jp_4330_;
}
}
case 1:
{
lean_object* v_val_4448_; lean_object* v___x_4449_; 
lean_del_object(v___x_4341_);
v_val_4448_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref(v_val_4448_);
lean_dec_ref_known(v_decl_3766_, 1);
v___x_4449_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4429_, v_forceExpose_3767_, v___x_4344_, v___x_4427_, v_cls_3960_, v_val_4448_, v_a_3768_, v_a_3769_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4449_;
goto v___jp_4303_;
}
case 5:
{
lean_object* v_defns_4450_; 
lean_del_object(v___x_4341_);
v_defns_4450_ = lean_ctor_get(v_decl_3766_, 0);
if (lean_obj_tag(v_defns_4450_) == 1)
{
lean_object* v_tail_4451_; 
v_tail_4451_ = lean_ctor_get(v_defns_4450_, 1);
if (lean_obj_tag(v_tail_4451_) == 0)
{
lean_object* v_head_4452_; lean_object* v___x_4453_; 
lean_inc_ref(v_defns_4450_);
lean_dec_ref_known(v_decl_3766_, 1);
v_head_4452_ = lean_ctor_get(v_defns_4450_, 0);
lean_inc(v_head_4452_);
lean_dec_ref_known(v_defns_4450_, 2);
v___x_4453_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__11(v___f_4429_, v_forceExpose_3767_, v___x_4344_, v___x_4427_, v_cls_3960_, v_head_4452_, v_a_3768_, v_a_3769_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4453_;
goto v___jp_4303_;
}
else
{
lean_object* v___x_4454_; 
lean_dec_ref(v___f_4429_);
lean_inc_ref(v_decl_3766_);
v___x_4454_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec_ref_known(v_decl_3766_, 1);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4454_;
goto v___jp_4303_;
}
}
else
{
lean_object* v___x_4455_; 
lean_dec_ref(v___f_4429_);
lean_inc_ref(v_decl_3766_);
v___x_4455_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec_ref_known(v_decl_3766_, 1);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4455_;
goto v___jp_4303_;
}
}
case 3:
{
lean_object* v_val_4456_; lean_object* v___f_4457_; lean_object* v___x_4458_; lean_object* v_env_4459_; lean_object* v___x_4460_; 
lean_del_object(v___x_4341_);
v_val_4456_ = lean_ctor_get(v_decl_3766_, 0);
lean_inc_ref_n(v_val_4456_, 2);
lean_dec_ref_known(v_decl_3766_, 1);
v___f_4457_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 7, 2);
lean_closure_set(v___f_4457_, 0, v_val_4456_);
lean_closure_set(v___f_4457_, 1, v___f_4429_);
v___x_4458_ = lean_st_ref_get(v_a_3769_);
v_env_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc_ref(v_env_4459_);
lean_dec(v___x_4458_);
v___x_4460_ = lean_st_ref_get(v_a_3769_);
if (v_forceExpose_3767_ == 0)
{
if (v___x_4344_ == 0)
{
lean_dec(v___x_4460_);
lean_dec_ref(v_env_4459_);
lean_dec_ref(v_val_4456_);
v___y_4324_ = v___x_4427_;
v___y_4325_ = v_a_4339_;
v___y_4326_ = v___x_4407_;
v___y_4327_ = v___f_4457_;
goto v___jp_4323_;
}
else
{
lean_object* v_env_4461_; lean_object* v___x_4462_; uint8_t v_isModule_4463_; 
v_env_4461_ = lean_ctor_get(v___x_4460_, 0);
lean_inc_ref(v_env_4461_);
lean_dec(v___x_4460_);
v___x_4462_ = l_Lean_Environment_header(v_env_4459_);
lean_dec_ref(v_env_4459_);
v_isModule_4463_ = lean_ctor_get_uint8(v___x_4462_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4462_);
if (v_isModule_4463_ == 0)
{
lean_dec_ref(v_env_4461_);
lean_dec_ref(v_val_4456_);
v___y_4324_ = v___x_4427_;
v___y_4325_ = v_a_4339_;
v___y_4326_ = v___x_4407_;
v___y_4327_ = v___f_4457_;
goto v___jp_4323_;
}
else
{
uint8_t v_isExporting_4464_; 
v_isExporting_4464_ = lean_ctor_get_uint8(v_env_4461_, sizeof(void*)*8);
lean_dec_ref(v_env_4461_);
if (v_isExporting_4464_ == 0)
{
if (v___x_4189_ == 0)
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = lean_box(0);
v___x_4466_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4456_, v___f_4457_, v___x_4465_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_val_4456_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4466_;
goto v___jp_4303_;
}
else
{
lean_object* v_toConstantVal_4467_; lean_object* v_name_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_toConstantVal_4467_ = lean_ctor_get(v_val_4456_, 0);
v_name_4468_ = lean_ctor_get(v_toConstantVal_4467_, 0);
v___x_4469_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4468_);
v___x_4470_ = l_Lean_MessageData_ofName(v_name_4468_);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
v___x_4472_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___closed__3);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_4473_, v_a_3768_, v_a_3769_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v___x_4474_, 1);
v___x_4476_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v_val_4456_, v___f_4457_, v_a_4475_, v_a_3768_, v_a_3769_);
lean_dec_ref(v_val_4456_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4476_;
goto v___jp_4303_;
}
else
{
lean_dec_ref(v___f_4457_);
lean_dec_ref(v_val_4456_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4474_;
goto v___jp_4303_;
}
}
}
else
{
lean_dec_ref(v_val_4456_);
v___y_4324_ = v___x_4427_;
v___y_4325_ = v_a_4339_;
v___y_4326_ = v___x_4407_;
v___y_4327_ = v___f_4457_;
goto v___jp_4323_;
}
}
}
}
else
{
lean_dec(v___x_4460_);
lean_dec_ref(v_env_4459_);
lean_dec_ref(v_val_4456_);
v___y_4324_ = v___x_4427_;
v___y_4325_ = v_a_4339_;
v___y_4326_ = v___x_4407_;
v___y_4327_ = v___f_4457_;
goto v___jp_4323_;
}
}
case 0:
{
lean_object* v_val_4477_; lean_object* v_toConstantVal_4478_; lean_object* v_name_4479_; lean_object* v___x_4481_; 
lean_dec_ref(v___f_4429_);
v_val_4477_ = lean_ctor_get(v_decl_3766_, 0);
v_toConstantVal_4478_ = lean_ctor_get(v_val_4477_, 0);
v_name_4479_ = lean_ctor_get(v_toConstantVal_4478_, 0);
lean_inc_ref(v_val_4477_);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 0, v_val_4477_);
v___x_4481_ = v___x_4341_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4487_; 
v_reuseFailAlloc_4487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_val_4477_);
v___x_4481_ = v_reuseFailAlloc_4487_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
uint8_t v___x_4482_; lean_object* v___x_4483_; lean_object* v___x_4484_; lean_object* v___x_4485_; lean_object* v___x_4486_; 
v___x_4482_ = 2;
v___x_4483_ = lean_box(v___x_4482_);
v___x_4484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4484_, 0, v___x_4481_);
lean_ctor_set(v___x_4484_, 1, v___x_4483_);
lean_inc(v_name_4479_);
v___x_4485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4485_, 0, v_name_4479_);
lean_ctor_set(v___x_4485_, 1, v___x_4484_);
v___x_4486_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__14(v_decl_3766_, v___x_4344_, v_cls_3960_, v___x_4423_, v___x_4427_, v___x_4485_, v___x_4427_, v_a_3768_, v_a_3769_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4486_;
goto v___jp_4303_;
}
}
default: 
{
lean_object* v___x_4488_; 
lean_dec_ref(v___f_4429_);
lean_del_object(v___x_4341_);
lean_inc(v_decl_3766_);
v___x_4488_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v_decl_3766_, v_cls_3960_, v_decl_3766_, v_a_3768_, v_a_3769_);
lean_dec(v_decl_3766_);
v___y_4304_ = v_a_4339_;
v___y_4305_ = v___x_4407_;
v___y_4306_ = v___x_4488_;
goto v___jp_4303_;
}
}
}
}
}
}
}
}
v___jp_3771_:
{
lean_object* v___x_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
v___x_3775_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3773_, v___y_3772_);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3782_ == 0)
{
lean_object* v_unused_3783_; 
v_unused_3783_ = lean_ctor_get(v___x_3775_, 0);
lean_dec(v_unused_3783_);
v___x_3777_ = v___x_3775_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_dec(v___x_3775_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
lean_ctor_set(v___x_3777_, 0, v_a_3774_);
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3774_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
v___jp_3784_:
{
lean_object* v___x_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
v___x_3788_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3786_, v___y_3785_);
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
lean_ctor_set_tag(v___x_3790_, 1);
lean_ctor_set(v___x_3790_, 0, v_a_3787_);
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
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
v___x_3801_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3799_, v___y_3798_);
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
lean_ctor_set(v___x_3803_, 0, v_a_3800_);
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(0, 1, 0);
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
lean_ctor_set_tag(v___x_3816_, 1);
lean_ctor_set(v___x_3816_, 0, v_a_3813_);
v___x_3819_ = v___x_3816_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_3827_:
{
lean_object* v___x_3840_; 
lean_inc_ref(v___y_3828_);
v___x_3840_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3838_, v___y_3828_, v___y_3831_, v___y_3839_);
if (lean_obj_tag(v___x_3840_) == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3887_; 
lean_dec_ref_known(v___x_3840_, 1);
lean_dec(v___y_3829_);
lean_inc_ref(v___y_3835_);
v___x_3841_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3835_, v___y_3832_);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3841_);
if (v_isSharedCheck_3887_ == 0)
{
lean_object* v_unused_3888_; 
v_unused_3888_ = lean_ctor_get(v___x_3841_, 0);
lean_dec(v_unused_3888_);
v___x_3843_ = v___x_3841_;
v_isShared_3844_ = v_isSharedCheck_3887_;
goto v_resetjp_3842_;
}
else
{
lean_dec(v___x_3841_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3887_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3845_; lean_object* v___x_3846_; uint8_t v___x_3847_; 
v___x_3845_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3837_);
v___x_3846_ = l_Lean_Elab_async;
v___x_3847_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v___x_3845_, v___x_3846_);
lean_dec_ref(v___x_3845_);
if (v___x_3847_ == 0)
{
lean_object* v___x_3848_; lean_object* v_r_3849_; 
lean_del_object(v___x_3843_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3830_);
v___x_3848_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3828_, v___y_3832_);
lean_dec_ref(v___x_3848_);
v_r_3849_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v___y_3837_, v___y_3832_);
if (lean_obj_tag(v_r_3849_) == 0)
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3859_; 
v_a_3850_ = lean_ctor_get(v_r_3849_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v_r_3849_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3852_ = v_r_3849_;
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v_r_3849_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3859_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
lean_inc(v_a_3850_);
if (v_isShared_3853_ == 0)
{
lean_ctor_set_tag(v___x_3852_, 1);
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
lean_object* v___x_3856_; 
v___x_3856_ = lean_apply_2(v___y_3834_, v___x_3855_, lean_box(0));
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_dec_ref_known(v___x_3856_, 1);
v___y_3798_ = v___y_3832_;
v___y_3799_ = v___y_3835_;
v_a_3800_ = v_a_3850_;
goto v___jp_3797_;
}
else
{
lean_object* v_a_3857_; 
lean_dec(v_a_3850_);
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3856_, 1);
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3835_;
v_a_3813_ = v_a_3857_;
goto v___jp_3810_;
}
}
}
}
else
{
lean_object* v_a_3860_; lean_object* v___x_3861_; lean_object* v___x_3862_; 
v_a_3860_ = lean_ctor_get(v_r_3849_, 0);
lean_inc(v_a_3860_);
lean_dec_ref_known(v_r_3849_, 1);
v___x_3861_ = lean_box(0);
v___x_3862_ = lean_apply_2(v___y_3834_, v___x_3861_, lean_box(0));
if (lean_obj_tag(v___x_3862_) == 0)
{
lean_dec_ref_known(v___x_3862_, 1);
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3835_;
v_a_3813_ = v_a_3860_;
goto v___jp_3810_;
}
else
{
lean_object* v_a_3863_; 
lean_dec(v_a_3860_);
v_a_3863_ = lean_ctor_get(v___x_3862_, 0);
lean_inc(v_a_3863_);
lean_dec_ref_known(v___x_3862_, 1);
v___y_3811_ = v___y_3832_;
v___y_3812_ = v___y_3835_;
v_a_3813_ = v_a_3863_;
goto v___jp_3810_;
}
}
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
lean_dec_ref(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v___y_3828_);
lean_dec(v_decl_3766_);
v___x_3864_ = l_IO_CancelToken_new();
if (v_isShared_3844_ == 0)
{
lean_ctor_set_tag(v___x_3843_, 1);
lean_ctor_set(v___x_3843_, 0, v___x_3864_);
v___x_3866_ = v___x_3843_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v___x_3867_ = lean_unsigned_to_nat(0u);
v___x_3868_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___closed__1));
v___x_3869_ = l_Lean_Name_toString(v___x_3868_, v___y_3836_);
lean_inc_ref(v___x_3866_);
v___x_3870_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3830_, v___x_3866_, v___x_3869_, v___y_3837_, v___y_3832_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_checked_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v_checked_3872_ = lean_ctor_get(v___y_3833_, 2);
lean_inc_ref(v_checked_3872_);
lean_dec_ref(v___y_3833_);
v___x_3873_ = lean_io_map_task(v_a_3871_, v_checked_3872_, v___x_3867_, v_hasTrace_3826_);
v___x_3874_ = lean_box(0);
v___x_3875_ = lean_box(2);
v___x_3876_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3874_);
lean_ctor_set(v___x_3876_, 1, v___x_3875_);
lean_ctor_set(v___x_3876_, 2, v___x_3866_);
lean_ctor_set(v___x_3876_, 3, v___x_3873_);
v___x_3877_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3876_, v___y_3832_);
return v___x_3877_;
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_dec_ref(v___x_3866_);
lean_dec_ref(v___y_3833_);
v_a_3878_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3870_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3870_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3900_; 
lean_dec_ref(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v___y_3830_);
lean_dec_ref(v___y_3828_);
lean_dec(v_decl_3766_);
v_a_3889_ = lean_ctor_get(v___x_3840_, 0);
v_isSharedCheck_3900_ = !lean_is_exclusive(v___x_3840_);
if (v_isSharedCheck_3900_ == 0)
{
v___x_3891_ = v___x_3840_;
v_isShared_3892_ = v_isSharedCheck_3900_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_a_3889_);
lean_dec(v___x_3840_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3900_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3895_; lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3893_ = lean_io_error_to_string(v_a_3889_);
v___x_3894_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
v___x_3895_ = l_Lean_MessageData_ofFormat(v___x_3894_);
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___y_3829_);
lean_ctor_set(v___x_3896_, 1, v___x_3895_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3896_);
v___x_3898_ = v___x_3891_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
v___jp_3901_:
{
lean_object* v_ref_3910_; uint8_t v___x_3911_; lean_object* v___x_3912_; 
v_ref_3910_ = lean_ctor_get(v___y_3906_, 2);
v___x_3911_ = 1;
lean_inc_ref(v___y_3908_);
v___x_3912_ = l_Lean_Environment_addConstAsync(v___y_3908_, v___y_3905_, v___y_3904_, v___y_3909_, v_hasTrace_3826_, v___x_3911_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; lean_object* v_mainEnv_3914_; lean_object* v_asyncEnv_3915_; lean_object* v___f_3916_; lean_object* v___f_3917_; lean_object* v___x_3918_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc_n(v_a_3913_, 3);
lean_dec_ref_known(v___x_3912_, 1);
v_mainEnv_3914_ = lean_ctor_get(v_a_3913_, 0);
lean_inc_ref(v_mainEnv_3914_);
v_asyncEnv_3915_ = lean_ctor_get(v_a_3913_, 1);
lean_inc_ref_n(v_asyncEnv_3915_, 2);
lean_inc(v_ref_3910_);
lean_inc(v___y_3903_);
v___f_3916_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3916_, 0, v___y_3903_);
lean_closure_set(v___f_3916_, 1, v_a_3913_);
lean_closure_set(v___f_3916_, 2, v_ref_3910_);
lean_inc(v_decl_3766_);
v___f_3917_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3917_, 0, v_a_3913_);
lean_closure_set(v___f_3917_, 1, v_asyncEnv_3915_);
lean_closure_set(v___f_3917_, 2, v_decl_3766_);
v___x_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___y_3902_);
if (lean_obj_tag(v___y_3907_) == 0)
{
lean_inc_ref(v___x_3918_);
lean_inc(v_ref_3910_);
v___y_3828_ = v_asyncEnv_3915_;
v___y_3829_ = v_ref_3910_;
v___y_3830_ = v___f_3917_;
v___y_3831_ = v___x_3918_;
v___y_3832_ = v___y_3903_;
v___y_3833_ = v___y_3908_;
v___y_3834_ = v___f_3916_;
v___y_3835_ = v_mainEnv_3914_;
v___y_3836_ = v___x_3911_;
v___y_3837_ = v___y_3906_;
v___y_3838_ = v_a_3913_;
v___y_3839_ = v___x_3918_;
goto v___jp_3827_;
}
else
{
lean_inc(v_ref_3910_);
v___y_3828_ = v_asyncEnv_3915_;
v___y_3829_ = v_ref_3910_;
v___y_3830_ = v___f_3917_;
v___y_3831_ = v___x_3918_;
v___y_3832_ = v___y_3903_;
v___y_3833_ = v___y_3908_;
v___y_3834_ = v___f_3916_;
v___y_3835_ = v_mainEnv_3914_;
v___y_3836_ = v___x_3911_;
v___y_3837_ = v___y_3906_;
v___y_3838_ = v_a_3913_;
v___y_3839_ = v___y_3907_;
goto v___jp_3827_;
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3930_; 
lean_dec_ref(v___y_3908_);
lean_dec(v___y_3907_);
lean_dec_ref(v___y_3902_);
lean_dec(v_decl_3766_);
v_a_3919_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3921_ = v___x_3912_;
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3912_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3930_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
v___x_3923_ = lean_io_error_to_string(v_a_3919_);
v___x_3924_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v___x_3925_ = l_Lean_MessageData_ofFormat(v___x_3924_);
lean_inc(v_ref_3910_);
v___x_3926_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3926_, 0, v_ref_3910_);
lean_ctor_set(v___x_3926_, 1, v___x_3925_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set(v___x_3921_, 0, v___x_3926_);
v___x_3928_ = v___x_3921_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
v___jp_3931_:
{
lean_object* v___x_3938_; 
v___x_3938_ = lean_st_ref_get(v___y_3937_);
if (lean_obj_tag(v_exportedInfo_x3f_3935_) == 0)
{
lean_object* v_env_3939_; lean_object* v___x_3940_; 
v_env_3939_ = lean_ctor_get(v___x_3938_, 0);
lean_inc_ref(v_env_3939_);
lean_dec(v___x_3938_);
v___x_3940_ = lean_box(0);
v___y_3902_ = v___y_3934_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v___y_3932_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_exportedInfo_x3f_3935_;
v___y_3908_ = v_env_3939_;
v___y_3909_ = v___x_3940_;
goto v___jp_3901_;
}
else
{
lean_object* v_env_3941_; lean_object* v_val_3942_; uint8_t v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v_env_3941_ = lean_ctor_get(v___x_3938_, 0);
lean_inc_ref(v_env_3941_);
lean_dec(v___x_3938_);
v_val_3942_ = lean_ctor_get(v_exportedInfo_x3f_3935_, 0);
v___x_3943_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3942_);
v___x_3944_ = lean_box(v___x_3943_);
v___x_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
v___y_3902_ = v___y_3934_;
v___y_3903_ = v___y_3937_;
v___y_3904_ = v___y_3933_;
v___y_3905_ = v___y_3932_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v_exportedInfo_x3f_3935_;
v___y_3908_ = v_env_3941_;
v___y_3909_ = v___x_3945_;
goto v___jp_3901_;
}
}
v___jp_3946_:
{
lean_object* v___x_3952_; 
lean_inc_ref(v___y_3949_);
v___x_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3952_, 0, v___y_3949_);
v___y_3932_ = v___y_3947_;
v___y_3933_ = v___y_3948_;
v___y_3934_ = v___y_3949_;
v_exportedInfo_x3f_3935_ = v___x_3952_;
v___y_3936_ = v___y_3950_;
v___y_3937_ = v___y_3951_;
goto v___jp_3931_;
}
v___jp_3953_:
{
lean_object* v___x_3959_; 
lean_inc_ref(v___y_3956_);
v___x_3959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3959_, 0, v___y_3956_);
v___y_3932_ = v___y_3954_;
v___y_3933_ = v___y_3955_;
v___y_3934_ = v___y_3956_;
v_exportedInfo_x3f_3935_ = v___x_3959_;
v___y_3936_ = v___y_3957_;
v___y_3937_ = v___y_3958_;
goto v___jp_3931_;
}
v___jp_3961_:
{
lean_object* v___x_3966_; uint8_t v___x_3967_; 
v___x_3966_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3967_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3964_, v_options_3963_, v___x_3966_);
if (v___x_3967_ == 0)
{
lean_object* v___x_3968_; 
v___x_3968_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v___y_3962_, v___y_3965_);
return v___x_3968_;
}
else
{
lean_object* v___x_3969_; lean_object* v___x_3970_; 
v___x_3969_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
v___x_3970_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3960_, v___x_3969_, v___y_3962_, v___y_3965_);
if (lean_obj_tag(v___x_3970_) == 0)
{
lean_object* v___x_3971_; 
lean_dec_ref_known(v___x_3970_, 1);
v___x_3971_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3766_, v___y_3962_, v___y_3965_);
return v___x_3971_;
}
else
{
lean_dec(v_decl_3766_);
return v___x_3970_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4870_, lean_object* v_forceExpose_4871_, lean_object* v_a_4872_, lean_object* v_a_4873_, lean_object* v_a_4874_){
_start:
{
uint8_t v_forceExpose_boxed_4875_; lean_object* v_res_4876_; 
v_forceExpose_boxed_4875_ = lean_unbox(v_forceExpose_4871_);
v_res_4876_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4870_, v_forceExpose_boxed_4875_, v_a_4872_, v_a_4873_);
lean_dec(v_a_4873_);
lean_dec_ref(v_a_4872_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4877_, lean_object* v___y_4878_, lean_object* v___y_4879_){
_start:
{
lean_object* v___x_4881_; 
v___x_4881_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4877_, v___y_4878_);
return v___x_4881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4882_, lean_object* v___y_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v_res_4886_; 
v_res_4886_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4882_, v___y_4883_, v___y_4884_);
lean_dec(v___y_4884_);
lean_dec_ref(v___y_4883_);
lean_dec_ref(v_opt_4882_);
return v_res_4886_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4887_, lean_object* v_x_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_){
_start:
{
if (lean_obj_tag(v_x_4887_) == 0)
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = l_List_reverse___redArg(v_x_4888_);
v___x_4893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
return v___x_4893_;
}
else
{
lean_object* v_head_4894_; lean_object* v_tail_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4913_; 
v_head_4894_ = lean_ctor_get(v_x_4887_, 0);
v_tail_4895_ = lean_ctor_get(v_x_4887_, 1);
v_isSharedCheck_4913_ = !lean_is_exclusive(v_x_4887_);
if (v_isSharedCheck_4913_ == 0)
{
v___x_4897_ = v_x_4887_;
v_isShared_4898_ = v_isSharedCheck_4913_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_tail_4895_);
lean_inc(v_head_4894_);
lean_dec(v_x_4887_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4913_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4899_; 
v___x_4899_ = l_Lean_snapshotEnvLinterOptions(v_head_4894_, v___y_4889_, v___y_4890_);
if (lean_obj_tag(v___x_4899_) == 0)
{
lean_object* v_a_4900_; lean_object* v___x_4902_; 
v_a_4900_ = lean_ctor_get(v___x_4899_, 0);
lean_inc(v_a_4900_);
lean_dec_ref_known(v___x_4899_, 1);
if (v_isShared_4898_ == 0)
{
lean_ctor_set(v___x_4897_, 1, v_x_4888_);
lean_ctor_set(v___x_4897_, 0, v_a_4900_);
v___x_4902_ = v___x_4897_;
goto v_reusejp_4901_;
}
else
{
lean_object* v_reuseFailAlloc_4904_; 
v_reuseFailAlloc_4904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4904_, 0, v_a_4900_);
lean_ctor_set(v_reuseFailAlloc_4904_, 1, v_x_4888_);
v___x_4902_ = v_reuseFailAlloc_4904_;
goto v_reusejp_4901_;
}
v_reusejp_4901_:
{
v_x_4887_ = v_tail_4895_;
v_x_4888_ = v___x_4902_;
goto _start;
}
}
else
{
lean_object* v_a_4905_; lean_object* v___x_4907_; uint8_t v_isShared_4908_; uint8_t v_isSharedCheck_4912_; 
lean_del_object(v___x_4897_);
lean_dec(v_tail_4895_);
lean_dec(v_x_4888_);
v_a_4905_ = lean_ctor_get(v___x_4899_, 0);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4899_);
if (v_isSharedCheck_4912_ == 0)
{
v___x_4907_ = v___x_4899_;
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
else
{
lean_inc(v_a_4905_);
lean_dec(v___x_4899_);
v___x_4907_ = lean_box(0);
v_isShared_4908_ = v_isSharedCheck_4912_;
goto v_resetjp_4906_;
}
v_resetjp_4906_:
{
lean_object* v___x_4910_; 
if (v_isShared_4908_ == 0)
{
v___x_4910_ = v___x_4907_;
goto v_reusejp_4909_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v_a_4905_);
v___x_4910_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4909_;
}
v_reusejp_4909_:
{
return v___x_4910_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4914_, lean_object* v_x_4915_, lean_object* v___y_4916_, lean_object* v___y_4917_, lean_object* v___y_4918_){
_start:
{
lean_object* v_res_4919_; 
v_res_4919_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4914_, v_x_4915_, v___y_4916_, v___y_4917_);
lean_dec(v___y_4917_);
lean_dec_ref(v___y_4916_);
return v_res_4919_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4920_, uint8_t v_forceExpose_4921_, lean_object* v_a_4922_, lean_object* v_a_4923_){
_start:
{
lean_object* v___x_4925_; 
lean_inc(v_decl_4920_);
v___x_4925_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4920_, v_forceExpose_4921_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_4925_) == 0)
{
lean_object* v___x_4926_; lean_object* v___x_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; 
lean_dec_ref_known(v___x_4925_, 1);
v___x_4926_ = l_Lean_Declaration_getTopLevelNames(v_decl_4920_);
v___x_4927_ = lean_box(0);
v___x_4928_ = lean_box(0);
v___x_4929_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4926_, v___x_4927_, v_a_4922_, v_a_4923_);
if (lean_obj_tag(v___x_4929_) == 0)
{
lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4936_; 
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v___x_4929_, 0);
lean_dec(v_unused_4937_);
v___x_4931_ = v___x_4929_;
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
else
{
lean_dec(v___x_4929_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4936_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4934_; 
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 0, v___x_4928_);
v___x_4934_ = v___x_4931_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4928_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
v_a_4938_ = lean_ctor_get(v___x_4929_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4929_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4929_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4929_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
else
{
lean_dec(v_decl_4920_);
return v___x_4925_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4946_, lean_object* v_forceExpose_4947_, lean_object* v_a_4948_, lean_object* v_a_4949_, lean_object* v_a_4950_){
_start:
{
uint8_t v_forceExpose_boxed_4951_; lean_object* v_res_4952_; 
v_forceExpose_boxed_4951_ = lean_unbox(v_forceExpose_4947_);
v_res_4952_ = l_Lean_addDecl(v_decl_4946_, v_forceExpose_boxed_4951_, v_a_4948_, v_a_4949_);
lean_dec(v_a_4949_);
lean_dec_ref(v_a_4948_);
return v_res_4952_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4953_, lean_object* v_b_4954_, lean_object* v___y_4955_){
_start:
{
if (lean_obj_tag(v_as_x27_4953_) == 0)
{
lean_object* v___x_4957_; 
v___x_4957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4957_, 0, v_b_4954_);
return v___x_4957_;
}
else
{
lean_object* v_head_4958_; lean_object* v_tail_4959_; lean_object* v___x_4960_; lean_object* v___x_4961_; lean_object* v_env_4962_; lean_object* v_nextMacroScope_4963_; lean_object* v_ngen_4964_; lean_object* v_auxDeclNGen_4965_; lean_object* v_traceState_4966_; lean_object* v_recordedDeps_4967_; lean_object* v_messages_4968_; lean_object* v_infoState_4969_; lean_object* v_snapshotTasks_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_4981_; 
v_head_4958_ = lean_ctor_get(v_as_x27_4953_, 0);
v_tail_4959_ = lean_ctor_get(v_as_x27_4953_, 1);
v___x_4960_ = lean_box(0);
v___x_4961_ = lean_st_ref_take(v___y_4955_);
v_env_4962_ = lean_ctor_get(v___x_4961_, 0);
v_nextMacroScope_4963_ = lean_ctor_get(v___x_4961_, 1);
v_ngen_4964_ = lean_ctor_get(v___x_4961_, 2);
v_auxDeclNGen_4965_ = lean_ctor_get(v___x_4961_, 3);
v_traceState_4966_ = lean_ctor_get(v___x_4961_, 4);
v_recordedDeps_4967_ = lean_ctor_get(v___x_4961_, 6);
v_messages_4968_ = lean_ctor_get(v___x_4961_, 7);
v_infoState_4969_ = lean_ctor_get(v___x_4961_, 8);
v_snapshotTasks_4970_ = lean_ctor_get(v___x_4961_, 9);
v_isSharedCheck_4981_ = !lean_is_exclusive(v___x_4961_);
if (v_isSharedCheck_4981_ == 0)
{
lean_object* v_unused_4982_; 
v_unused_4982_ = lean_ctor_get(v___x_4961_, 5);
lean_dec(v_unused_4982_);
v___x_4972_ = v___x_4961_;
v_isShared_4973_ = v_isSharedCheck_4981_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_snapshotTasks_4970_);
lean_inc(v_infoState_4969_);
lean_inc(v_messages_4968_);
lean_inc(v_recordedDeps_4967_);
lean_inc(v_traceState_4966_);
lean_inc(v_auxDeclNGen_4965_);
lean_inc(v_ngen_4964_);
lean_inc(v_nextMacroScope_4963_);
lean_inc(v_env_4962_);
lean_dec(v___x_4961_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_4981_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___x_4975_; lean_object* v___x_4977_; 
lean_inc(v_head_4958_);
v___x_4974_ = l_Lean_markMeta(v_env_4962_, v_head_4958_);
v___x_4975_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4973_ == 0)
{
lean_ctor_set(v___x_4972_, 5, v___x_4975_);
lean_ctor_set(v___x_4972_, 0, v___x_4974_);
v___x_4977_ = v___x_4972_;
goto v_reusejp_4976_;
}
else
{
lean_object* v_reuseFailAlloc_4980_; 
v_reuseFailAlloc_4980_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4980_, 0, v___x_4974_);
lean_ctor_set(v_reuseFailAlloc_4980_, 1, v_nextMacroScope_4963_);
lean_ctor_set(v_reuseFailAlloc_4980_, 2, v_ngen_4964_);
lean_ctor_set(v_reuseFailAlloc_4980_, 3, v_auxDeclNGen_4965_);
lean_ctor_set(v_reuseFailAlloc_4980_, 4, v_traceState_4966_);
lean_ctor_set(v_reuseFailAlloc_4980_, 5, v___x_4975_);
lean_ctor_set(v_reuseFailAlloc_4980_, 6, v_recordedDeps_4967_);
lean_ctor_set(v_reuseFailAlloc_4980_, 7, v_messages_4968_);
lean_ctor_set(v_reuseFailAlloc_4980_, 8, v_infoState_4969_);
lean_ctor_set(v_reuseFailAlloc_4980_, 9, v_snapshotTasks_4970_);
v___x_4977_ = v_reuseFailAlloc_4980_;
goto v_reusejp_4976_;
}
v_reusejp_4976_:
{
lean_object* v___x_4978_; 
v___x_4978_ = lean_st_ref_put(v___y_4955_, v___x_4977_);
v_as_x27_4953_ = v_tail_4959_;
v_b_4954_ = v___x_4960_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4983_, lean_object* v_b_4984_, lean_object* v___y_4985_, lean_object* v___y_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4983_, v_b_4984_, v___y_4985_);
lean_dec(v___y_4985_);
lean_dec(v_as_x27_4983_);
return v_res_4987_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4988_, uint8_t v_logCompileErrors_4989_, uint8_t v_markMeta_4990_, lean_object* v_a_4991_, lean_object* v_a_4992_){
_start:
{
uint8_t v___x_4994_; lean_object* v___x_4995_; 
v___x_4994_ = 0;
lean_inc(v_decl_4988_);
v___x_4995_ = l_Lean_addDecl(v_decl_4988_, v___x_4994_, v_a_4991_, v_a_4992_);
if (lean_obj_tag(v___x_4995_) == 0)
{
lean_dec_ref_known(v___x_4995_, 1);
if (v_markMeta_4990_ == 0)
{
lean_object* v___x_4996_; 
v___x_4996_ = l_Lean_compileDecl(v_decl_4988_, v_logCompileErrors_4989_, v_a_4991_, v_a_4992_);
return v___x_4996_;
}
else
{
lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; 
lean_inc(v_decl_4988_);
v___x_4997_ = l_Lean_Declaration_getNames(v_decl_4988_);
v___x_4998_ = lean_box(0);
v___x_4999_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4997_, v___x_4998_, v_a_4992_);
lean_dec(v___x_4997_);
lean_dec_ref(v___x_4999_);
v___x_5000_ = l_Lean_compileDecl(v_decl_4988_, v_logCompileErrors_4989_, v_a_4991_, v_a_4992_);
return v___x_5000_;
}
}
else
{
lean_dec(v_decl_4988_);
return v___x_4995_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_5001_, lean_object* v_logCompileErrors_5002_, lean_object* v_markMeta_5003_, lean_object* v_a_5004_, lean_object* v_a_5005_, lean_object* v_a_5006_){
_start:
{
uint8_t v_logCompileErrors_boxed_5007_; uint8_t v_markMeta_boxed_5008_; lean_object* v_res_5009_; 
v_logCompileErrors_boxed_5007_ = lean_unbox(v_logCompileErrors_5002_);
v_markMeta_boxed_5008_ = lean_unbox(v_markMeta_5003_);
v_res_5009_ = l_Lean_addAndCompile(v_decl_5001_, v_logCompileErrors_boxed_5007_, v_markMeta_boxed_5008_, v_a_5004_, v_a_5005_);
lean_dec(v_a_5005_);
lean_dec_ref(v_a_5004_);
return v_res_5009_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_5010_, lean_object* v_as_x27_5011_, lean_object* v_b_5012_, lean_object* v_a_5013_, lean_object* v___y_5014_, lean_object* v___y_5015_){
_start:
{
lean_object* v___x_5017_; 
v___x_5017_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_5011_, v_b_5012_, v___y_5015_);
return v___x_5017_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_5018_, lean_object* v_as_x27_5019_, lean_object* v_b_5020_, lean_object* v_a_5021_, lean_object* v___y_5022_, lean_object* v___y_5023_, lean_object* v___y_5024_){
_start:
{
lean_object* v_res_5025_; 
v_res_5025_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_5018_, v_as_x27_5019_, v_b_5020_, v_a_5021_, v___y_5022_, v___y_5023_);
lean_dec(v___y_5023_);
lean_dec_ref(v___y_5022_);
lean_dec(v_as_x27_5019_);
lean_dec(v_as_5018_);
return v_res_5025_;
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
