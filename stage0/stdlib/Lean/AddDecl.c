// Lean compiler output
// Module: Lean.AddDecl
// Imports: public import Lean.Meta.Sorry public import Lean.Util.CollectAxioms public import Lean.OriginalConstKind public import Lean.AutoDecl import Lean.Linter.Init import Lean.Compiler.MetaAttr import all Lean.OriginalConstKind
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
extern lean_object* l_Lean_debug_skipKernelTC;
lean_object* l_Lean_Environment_addDeclCore(lean_object*, size_t, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_add_decl(lean_object*, size_t, lean_object*, lean_object*);
lean_object* lean_add_decl_without_checking(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterOptionsRef;
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_isAutoDeclOrPrivate__Internal___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Linter_envLinterSnapshotExt;
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* l_Lean_compileDecl(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl(lean_object* v_env_15_, lean_object* v_opts_16_, lean_object* v_decl_17_, lean_object* v_cancelTk_x3f_18_){
_start:
{
lean_object* v___x_19_; uint8_t v___x_20_; 
v___x_19_ = l_Lean_debug_skipKernelTC;
v___x_20_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_16_, v___x_19_);
if (v___x_20_ == 0)
{
lean_object* v___x_21_; size_t v___x_22_; lean_object* v___x_23_; 
v___x_21_ = l_Lean_Core_getMaxHeartbeats(v_opts_16_);
v___x_22_ = lean_usize_of_nat(v___x_21_);
lean_dec(v___x_21_);
v___x_23_ = lean_add_decl(v_env_15_, v___x_22_, v_decl_17_, v_cancelTk_x3f_18_);
return v___x_23_;
}
else
{
lean_object* v___x_24_; 
v___x_24_ = lean_add_decl_without_checking(v_env_15_, v_decl_17_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Kernel_Environment_addDecl___boxed(lean_object* v_env_25_, lean_object* v_opts_26_, lean_object* v_decl_27_, lean_object* v_cancelTk_x3f_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_Kernel_Environment_addDecl(v_env_25_, v_opts_26_, v_decl_27_, v_cancelTk_x3f_28_);
lean_dec(v_cancelTk_x3f_28_);
lean_dec(v_decl_27_);
lean_dec_ref(v_opts_26_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(lean_object* v_env_30_, lean_object* v_opts_31_, lean_object* v_decl_32_, lean_object* v_cancelTk_x3f_33_){
_start:
{
lean_object* v___x_34_; size_t v___x_35_; lean_object* v___x_36_; uint8_t v___x_37_; 
v___x_34_ = l_Lean_Core_getMaxHeartbeats(v_opts_31_);
v___x_35_ = lean_usize_of_nat(v___x_34_);
lean_dec(v___x_34_);
v___x_36_ = l_Lean_debug_skipKernelTC;
v___x_37_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_31_, v___x_36_);
if (v___x_37_ == 0)
{
uint8_t v___x_38_; lean_object* v___x_39_; 
v___x_38_ = 1;
v___x_39_ = l_Lean_Environment_addDeclCore(v_env_30_, v___x_35_, v_decl_32_, v_cancelTk_x3f_33_, v___x_38_);
return v___x_39_;
}
else
{
uint8_t v___x_40_; lean_object* v___x_41_; 
v___x_40_ = 0;
v___x_41_ = l_Lean_Environment_addDeclCore(v_env_30_, v___x_35_, v_decl_32_, v_cancelTk_x3f_33_, v___x_40_);
return v___x_41_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux___boxed(lean_object* v_env_42_, lean_object* v_opts_43_, lean_object* v_decl_44_, lean_object* v_cancelTk_x3f_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_42_, v_opts_43_, v_decl_44_, v_cancelTk_x3f_45_);
lean_dec(v_cancelTk_x3f_45_);
lean_dec(v_decl_44_);
lean_dec_ref(v_opts_43_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(lean_object* v_a_47_, lean_object* v_as_48_, size_t v_sz_49_, size_t v_i_50_, lean_object* v_b_51_){
_start:
{
uint8_t v___x_53_; 
v___x_53_ = lean_usize_dec_lt(v_i_50_, v_sz_49_);
if (v___x_53_ == 0)
{
lean_object* v___x_54_; 
v___x_54_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_54_, 0, v_b_51_);
return v___x_54_;
}
else
{
lean_object* v_a_55_; lean_object* v_name_56_; uint8_t v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; size_t v___x_60_; size_t v___x_61_; 
v_a_55_ = lean_array_uget_borrowed(v_as_48_, v_i_50_);
v_name_56_ = lean_ctor_get(v_a_55_, 0);
v___x_57_ = l_Lean_Linter_getLinterValue(v_a_55_, v_a_47_);
v___x_58_ = lean_box(v___x_57_);
lean_inc(v_name_56_);
v___x_59_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_name_56_, v___x_58_, v_b_51_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_add(v_i_50_, v___x_60_);
v_i_50_ = v___x_61_;
v_b_51_ = v___x_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg___boxed(lean_object* v_a_63_, lean_object* v_as_64_, lean_object* v_sz_65_, lean_object* v_i_66_, lean_object* v_b_67_, lean_object* v___y_68_){
_start:
{
size_t v_sz_boxed_69_; size_t v_i_boxed_70_; lean_object* v_res_71_; 
v_sz_boxed_69_ = lean_unbox_usize(v_sz_65_);
lean_dec(v_sz_65_);
v_i_boxed_70_ = lean_unbox_usize(v_i_66_);
lean_dec(v_i_66_);
v_res_71_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_63_, v_as_64_, v_sz_boxed_69_, v_i_boxed_70_, v_b_67_);
lean_dec_ref(v_as_64_);
lean_dec_ref(v_a_63_);
return v_res_71_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(lean_object* v_o_72_, lean_object* v___y_73_){
_start:
{
lean_object* v___x_75_; lean_object* v_env_76_; lean_object* v___x_77_; lean_object* v_toEnvExtension_78_; lean_object* v_asyncMode_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v_merged_83_; lean_object* v___x_85_; uint8_t v_isShared_86_; uint8_t v_isSharedCheck_91_; 
v___x_75_ = lean_st_ref_get(v___y_73_);
v_env_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc_ref(v_env_76_);
lean_dec(v___x_75_);
v___x_77_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_78_ = lean_ctor_get(v___x_77_, 0);
v_asyncMode_79_ = lean_ctor_get(v_toEnvExtension_78_, 2);
v___x_80_ = l_Lean_Linter_instInhabitedLinterSetsState_default;
v___x_81_ = lean_box(0);
v___x_82_ = l_Lean_PersistentEnvExtension_getState___redArg(v___x_80_, v___x_77_, v_env_76_, v_asyncMode_79_, v___x_81_);
v_merged_83_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_82_, 1);
lean_dec(v_unused_92_);
v___x_85_ = v___x_82_;
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
else
{
lean_inc(v_merged_83_);
lean_dec(v___x_82_);
v___x_85_ = lean_box(0);
v_isShared_86_ = v_isSharedCheck_91_;
goto v_resetjp_84_;
}
v_resetjp_84_:
{
lean_object* v___x_88_; 
if (v_isShared_86_ == 0)
{
lean_ctor_set(v___x_85_, 1, v_merged_83_);
lean_ctor_set(v___x_85_, 0, v_o_72_);
v___x_88_ = v___x_85_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_o_72_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_merged_83_);
v___x_88_ = v_reuseFailAlloc_90_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
lean_object* v___x_89_; 
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg___boxed(lean_object* v_o_93_, lean_object* v___y_94_, lean_object* v___y_95_){
_start:
{
lean_object* v_res_96_; 
v_res_96_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_93_, v___y_94_);
lean_dec(v___y_94_);
return v_res_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(lean_object* v___y_97_, lean_object* v___y_98_){
_start:
{
lean_object* v_options_100_; lean_object* v___x_101_; 
v_options_100_ = lean_ctor_get(v___y_97_, 2);
lean_inc_ref(v_options_100_);
v___x_101_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_options_100_, v___y_98_);
return v___x_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0___boxed(lean_object* v___y_102_, lean_object* v___y_103_, lean_object* v___y_104_){
_start:
{
lean_object* v_res_105_; 
v_res_105_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v___y_102_, v___y_103_);
lean_dec(v___y_103_);
lean_dec_ref(v___y_102_);
return v_res_105_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__0(void){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_106_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__1(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__0, &l_Lean_snapshotEnvLinterOptions___closed__0_once, _init_l_Lean_snapshotEnvLinterOptions___closed__0);
v___x_108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_108_, 0, v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_snapshotEnvLinterOptions___closed__2(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__1, &l_Lean_snapshotEnvLinterOptions___closed__1_once, _init_l_Lean_snapshotEnvLinterOptions___closed__1);
v___x_110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_110_, 0, v___x_109_);
lean_ctor_set(v___x_110_, 1, v___x_109_);
return v___x_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions(lean_object* v_declName_111_, lean_object* v_a_112_, lean_object* v_a_113_){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; uint8_t v___x_119_; 
v___x_115_ = l_Lean_Linter_envLinterOptionsRef;
v___x_116_ = lean_st_ref_get(v___x_115_);
v___x_117_ = lean_array_get_size(v___x_116_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_nat_dec_eq(v___x_117_, v___x_118_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v_a_121_; lean_object* v___x_122_; 
v___x_120_ = l_Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0(v_a_112_, v_a_113_);
v_a_121_ = lean_ctor_get(v___x_120_, 0);
lean_inc(v_a_121_);
lean_dec_ref(v___x_120_);
lean_inc(v_declName_111_);
v___x_122_ = l_Lean_isAutoDeclOrPrivate__Internal___redArg(v_declName_111_, v_a_113_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_125_; uint8_t v_isShared_126_; uint8_t v_isSharedCheck_174_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_174_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_174_ == 0)
{
v___x_125_ = v___x_122_;
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
else
{
lean_inc(v_a_123_);
lean_dec(v___x_122_);
v___x_125_ = lean_box(0);
v_isShared_126_ = v_isSharedCheck_174_;
goto v_resetjp_124_;
}
v_resetjp_124_:
{
uint8_t v___x_127_; 
v___x_127_ = lean_unbox(v_a_123_);
lean_dec(v_a_123_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; size_t v_sz_129_; size_t v___x_130_; lean_object* v___x_131_; 
lean_del_object(v___x_125_);
v___x_128_ = lean_box(1);
v_sz_129_ = lean_array_size(v___x_116_);
v___x_130_ = ((size_t)0ULL);
v___x_131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_121_, v___x_116_, v_sz_129_, v___x_130_, v___x_128_);
lean_dec(v___x_116_);
lean_dec(v_a_121_);
if (lean_obj_tag(v___x_131_) == 0)
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_161_; 
v_a_132_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_161_ == 0)
{
v___x_134_ = v___x_131_;
v_isShared_135_ = v_isSharedCheck_161_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_161_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_136_; lean_object* v_env_137_; lean_object* v_nextMacroScope_138_; lean_object* v_ngen_139_; lean_object* v_auxDeclNGen_140_; lean_object* v_traceState_141_; lean_object* v_messages_142_; lean_object* v_infoState_143_; lean_object* v_snapshotTasks_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_159_; 
v___x_136_ = lean_st_ref_take(v_a_113_);
v_env_137_ = lean_ctor_get(v___x_136_, 0);
v_nextMacroScope_138_ = lean_ctor_get(v___x_136_, 1);
v_ngen_139_ = lean_ctor_get(v___x_136_, 2);
v_auxDeclNGen_140_ = lean_ctor_get(v___x_136_, 3);
v_traceState_141_ = lean_ctor_get(v___x_136_, 4);
v_messages_142_ = lean_ctor_get(v___x_136_, 6);
v_infoState_143_ = lean_ctor_get(v___x_136_, 7);
v_snapshotTasks_144_ = lean_ctor_get(v___x_136_, 8);
v_isSharedCheck_159_ = !lean_is_exclusive(v___x_136_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v___x_136_, 5);
lean_dec(v_unused_160_);
v___x_146_ = v___x_136_;
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snapshotTasks_144_);
lean_inc(v_infoState_143_);
lean_inc(v_messages_142_);
lean_inc(v_traceState_141_);
lean_inc(v_auxDeclNGen_140_);
lean_inc(v_ngen_139_);
lean_inc(v_nextMacroScope_138_);
lean_inc(v_env_137_);
lean_dec(v___x_136_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_159_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_152_; 
v___x_148_ = l_Lean_Linter_envLinterSnapshotExt;
v___x_149_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_148_, v_env_137_, v_declName_111_, v_a_132_);
v___x_150_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 5, v___x_150_);
lean_ctor_set(v___x_146_, 0, v___x_149_);
v___x_152_ = v___x_146_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v_nextMacroScope_138_);
lean_ctor_set(v_reuseFailAlloc_158_, 2, v_ngen_139_);
lean_ctor_set(v_reuseFailAlloc_158_, 3, v_auxDeclNGen_140_);
lean_ctor_set(v_reuseFailAlloc_158_, 4, v_traceState_141_);
lean_ctor_set(v_reuseFailAlloc_158_, 5, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_158_, 6, v_messages_142_);
lean_ctor_set(v_reuseFailAlloc_158_, 7, v_infoState_143_);
lean_ctor_set(v_reuseFailAlloc_158_, 8, v_snapshotTasks_144_);
v___x_152_ = v_reuseFailAlloc_158_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_153_ = lean_st_ref_set(v_a_113_, v___x_152_);
v___x_154_ = lean_box(0);
if (v_isShared_135_ == 0)
{
lean_ctor_set(v___x_134_, 0, v___x_154_);
v___x_156_ = v___x_134_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_154_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_declName_111_);
v_a_162_ = lean_ctor_get(v___x_131_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_131_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_131_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_131_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v___x_170_; lean_object* v___x_172_; 
lean_dec(v_a_121_);
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v___x_170_ = lean_box(0);
if (v_isShared_126_ == 0)
{
lean_ctor_set(v___x_125_, 0, v___x_170_);
v___x_172_ = v___x_125_;
goto v_reusejp_171_;
}
else
{
lean_object* v_reuseFailAlloc_173_; 
v_reuseFailAlloc_173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_173_, 0, v___x_170_);
v___x_172_ = v_reuseFailAlloc_173_;
goto v_reusejp_171_;
}
v_reusejp_171_:
{
return v___x_172_;
}
}
}
}
else
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_182_; 
lean_dec(v_a_121_);
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v_a_175_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_182_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_182_ == 0)
{
v___x_177_ = v___x_122_;
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_122_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_182_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_180_; 
if (v_isShared_178_ == 0)
{
v___x_180_ = v___x_177_;
goto v_reusejp_179_;
}
else
{
lean_object* v_reuseFailAlloc_181_; 
v_reuseFailAlloc_181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_181_, 0, v_a_175_);
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
else
{
lean_object* v___x_183_; lean_object* v___x_184_; 
lean_dec(v___x_116_);
lean_dec(v_declName_111_);
v___x_183_ = lean_box(0);
v___x_184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_184_, 0, v___x_183_);
return v___x_184_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_snapshotEnvLinterOptions___boxed(lean_object* v_declName_185_, lean_object* v_a_186_, lean_object* v_a_187_, lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_snapshotEnvLinterOptions(v_declName_185_, v_a_186_, v_a_187_);
lean_dec(v_a_187_);
lean_dec_ref(v_a_186_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(lean_object* v_o_190_, lean_object* v___y_191_, lean_object* v___y_192_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___redArg(v_o_190_, v___y_192_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0___boxed(lean_object* v_o_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l_Lean_Options_toLinterOptions___at___00Lean_Linter_getLinterOptions___at___00Lean_snapshotEnvLinterOptions_spec__0_spec__0(v_o_195_, v___y_196_, v___y_197_);
lean_dec(v___y_197_);
lean_dec_ref(v___y_196_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(lean_object* v_a_200_, lean_object* v_as_201_, size_t v_sz_202_, size_t v_i_203_, lean_object* v_b_204_, lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___redArg(v_a_200_, v_as_201_, v_sz_202_, v_i_203_, v_b_204_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1___boxed(lean_object* v_a_209_, lean_object* v_as_210_, lean_object* v_sz_211_, lean_object* v_i_212_, lean_object* v_b_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
size_t v_sz_boxed_217_; size_t v_i_boxed_218_; lean_object* v_res_219_; 
v_sz_boxed_217_ = lean_unbox_usize(v_sz_211_);
lean_dec(v_sz_211_);
v_i_boxed_218_ = lean_unbox_usize(v_i_212_);
lean_dec(v_i_212_);
v_res_219_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_snapshotEnvLinterOptions_spec__1(v_a_209_, v_as_210_, v_sz_boxed_217_, v_i_boxed_218_, v_b_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec_ref(v_as_210_);
lean_dec_ref(v_a_209_);
return v_res_219_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_AddDecl_0__Lean_isNamespaceName(lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 1)
{
lean_object* v_pre_221_; 
v_pre_221_ = lean_ctor_get(v_x_220_, 0);
if (lean_obj_tag(v_pre_221_) == 0)
{
uint8_t v___x_222_; 
v___x_222_ = 1;
return v___x_222_;
}
else
{
v_x_220_ = v_pre_221_;
goto _start;
}
}
else
{
uint8_t v___x_224_; 
v___x_224_ = 0;
return v___x_224_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_isNamespaceName___boxed(lean_object* v_x_225_){
_start:
{
uint8_t v_res_226_; lean_object* v_r_227_; 
v_res_226_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_x_225_);
lean_dec(v_x_225_);
v_r_227_ = lean_box(v_res_226_);
return v_r_227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(lean_object* v_env_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 1)
{
lean_object* v_pre_230_; uint8_t v___x_231_; 
v_pre_230_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_pre_230_);
lean_dec_ref_known(v_x_229_, 2);
v___x_231_ = l___private_Lean_AddDecl_0__Lean_isNamespaceName(v_pre_230_);
if (v___x_231_ == 0)
{
lean_dec(v_pre_230_);
return v_env_228_;
}
else
{
lean_object* v___x_232_; 
lean_inc(v_pre_230_);
v___x_232_ = l_Lean_Environment_registerNamespace(v_env_228_, v_pre_230_);
v_env_228_ = v___x_232_;
v_x_229_ = v_pre_230_;
goto _start;
}
}
else
{
lean_dec(v_x_229_);
return v_env_228_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(lean_object* v_env_234_, lean_object* v_name_235_){
_start:
{
lean_object* v_name_236_; uint32_t v___y_238_; 
v_name_236_ = l_Lean_privateToUserName(v_name_235_);
if (lean_obj_tag(v_name_236_) == 1)
{
lean_object* v_str_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_str_242_ = lean_ctor_get(v_name_236_, 1);
lean_inc_ref(v_str_242_);
v___x_243_ = lean_unsigned_to_nat(0u);
v___x_244_ = lean_string_utf8_byte_size(v_str_242_);
v___x_245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_245_, 0, v_str_242_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_244_);
v___x_246_ = l_String_Slice_Pos_get_x3f(v___x_245_, v___x_243_);
lean_dec_ref_known(v___x_245_, 3);
if (lean_obj_tag(v___x_246_) == 0)
{
uint32_t v___x_247_; 
v___x_247_ = 65;
v___y_238_ = v___x_247_;
goto v___jp_237_;
}
else
{
lean_object* v_val_248_; uint32_t v___x_249_; 
v_val_248_ = lean_ctor_get(v___x_246_, 0);
lean_inc(v_val_248_);
lean_dec_ref_known(v___x_246_, 1);
v___x_249_ = lean_unbox_uint32(v_val_248_);
lean_dec(v_val_248_);
v___y_238_ = v___x_249_;
goto v___jp_237_;
}
}
else
{
lean_dec(v_name_236_);
return v_env_234_;
}
v___jp_237_:
{
uint32_t v___x_239_; uint8_t v___x_240_; 
v___x_239_ = 95;
v___x_240_ = lean_uint32_dec_eq(v___y_238_, v___x_239_);
if (v___x_240_ == 0)
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes_go(v_env_234_, v_name_236_);
return v___x_241_;
}
else
{
lean_dec(v_name_236_);
return v_env_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(lean_object* v_name_250_, lean_object* v_decl_251_, lean_object* v_ref_252_){
_start:
{
lean_object* v_defValue_254_; lean_object* v_descr_255_; lean_object* v_deprecation_x3f_256_; lean_object* v___x_257_; uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v_defValue_254_ = lean_ctor_get(v_decl_251_, 0);
v_descr_255_ = lean_ctor_get(v_decl_251_, 1);
v_deprecation_x3f_256_ = lean_ctor_get(v_decl_251_, 2);
v___x_257_ = lean_alloc_ctor(1, 0, 1);
v___x_258_ = lean_unbox(v_defValue_254_);
lean_ctor_set_uint8(v___x_257_, 0, v___x_258_);
lean_inc(v_deprecation_x3f_256_);
lean_inc_ref(v_descr_255_);
lean_inc_n(v_name_250_, 2);
v___x_259_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_259_, 0, v_name_250_);
lean_ctor_set(v___x_259_, 1, v_ref_252_);
lean_ctor_set(v___x_259_, 2, v___x_257_);
lean_ctor_set(v___x_259_, 3, v_descr_255_);
lean_ctor_set(v___x_259_, 4, v_deprecation_x3f_256_);
v___x_260_ = lean_register_option(v_name_250_, v___x_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_268_; 
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_268_ == 0)
{
lean_object* v_unused_269_; 
v_unused_269_ = lean_ctor_get(v___x_260_, 0);
lean_dec(v_unused_269_);
v___x_262_ = v___x_260_;
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
else
{
lean_dec(v___x_260_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_268_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_266_; 
lean_inc(v_defValue_254_);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_name_250_);
lean_ctor_set(v___x_264_, 1, v_defValue_254_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 0, v___x_264_);
v___x_266_ = v___x_262_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
else
{
lean_object* v_a_270_; lean_object* v___x_272_; uint8_t v_isShared_273_; uint8_t v_isSharedCheck_277_; 
lean_dec(v_name_250_);
v_a_270_ = lean_ctor_get(v___x_260_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_260_);
if (v_isSharedCheck_277_ == 0)
{
v___x_272_ = v___x_260_;
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
else
{
lean_inc(v_a_270_);
lean_dec(v___x_260_);
v___x_272_ = lean_box(0);
v_isShared_273_ = v_isSharedCheck_277_;
goto v_resetjp_271_;
}
v_resetjp_271_:
{
lean_object* v___x_275_; 
if (v_isShared_273_ == 0)
{
v___x_275_ = v___x_272_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_a_270_);
v___x_275_ = v_reuseFailAlloc_276_;
goto v_reusejp_274_;
}
v_reusejp_274_:
{
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_278_, lean_object* v_decl_279_, lean_object* v_ref_280_, lean_object* v_a_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v_name_278_, v_decl_279_, v_ref_280_);
lean_dec_ref(v_decl_279_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_300_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__2_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_301_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__4_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_302_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__6_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_));
v___x_303_ = l_Lean_Option_register___at___00__private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4__spec__0(v___x_300_, v___x_301_, v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4____boxed(lean_object* v_a_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_1069955831____hygCtx___hyg_4_();
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(lean_object* v_msgData_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v___x_312_; lean_object* v_env_313_; lean_object* v___x_314_; lean_object* v_mctx_315_; lean_object* v_lctx_316_; lean_object* v_options_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_312_ = lean_st_ref_get(v___y_310_);
v_env_313_ = lean_ctor_get(v___x_312_, 0);
lean_inc_ref(v_env_313_);
lean_dec(v___x_312_);
v___x_314_ = lean_st_ref_get(v___y_308_);
v_mctx_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc_ref(v_mctx_315_);
lean_dec(v___x_314_);
v_lctx_316_ = lean_ctor_get(v___y_307_, 2);
v_options_317_ = lean_ctor_get(v___y_309_, 2);
lean_inc_ref(v_options_317_);
lean_inc_ref(v_lctx_316_);
v___x_318_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_318_, 0, v_env_313_);
lean_ctor_set(v___x_318_, 1, v_mctx_315_);
lean_ctor_set(v___x_318_, 2, v_lctx_316_);
lean_ctor_set(v___x_318_, 3, v_options_317_);
v___x_319_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_318_);
lean_ctor_set(v___x_319_, 1, v_msgData_306_);
v___x_320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0___boxed(lean_object* v_msgData_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v_msgData_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0(lean_object* v_s_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v_a_337_; lean_object* v___x_339_; uint8_t v_isShared_340_; uint8_t v_isSharedCheck_351_; 
lean_inc_ref(v_s_328_);
v___x_335_ = l_Lean_MessageData_ofExpr(v_s_328_);
v___x_336_ = l_Lean_addMessageContextFull___at___00Lean_warnIfUsesSorry_spec__0(v___x_335_, v___y_330_, v___y_331_, v___y_332_, v___y_333_);
v_a_337_ = lean_ctor_get(v___x_336_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_336_);
if (v_isSharedCheck_351_ == 0)
{
v___x_339_ = v___x_336_;
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
else
{
lean_inc(v_a_337_);
lean_dec(v___x_336_);
v___x_339_ = lean_box(0);
v_isShared_340_ = v_isSharedCheck_351_;
goto v_resetjp_338_;
}
v_resetjp_338_:
{
lean_object* v___x_341_; uint8_t v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_349_; 
v___x_341_ = lean_st_ref_take(v___y_329_);
v___x_342_ = l_Lean_Expr_isSyntheticSorry(v_s_328_);
lean_dec_ref(v_s_328_);
v___x_343_ = lean_box(v___x_342_);
v___x_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_343_);
lean_ctor_set(v___x_344_, 1, v_a_337_);
v___x_345_ = lean_array_push(v___x_341_, v___x_344_);
v___x_346_ = lean_st_ref_set(v___y_329_, v___x_345_);
v___x_347_ = lean_box(0);
if (v_isShared_340_ == 0)
{
lean_ctor_set(v___x_339_, 0, v___x_347_);
v___x_349_ = v___x_339_;
goto v_reusejp_348_;
}
else
{
lean_object* v_reuseFailAlloc_350_; 
v_reuseFailAlloc_350_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_350_, 0, v___x_347_);
v___x_349_ = v_reuseFailAlloc_350_;
goto v_reusejp_348_;
}
v_reusejp_348_:
{
return v___x_349_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___lam__0___boxed(lean_object* v_s_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_res_359_; 
v_res_359_ = l_Lean_warnIfUsesSorry___lam__0(v_s_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_);
lean_dec(v___y_357_);
lean_dec_ref(v___y_356_);
lean_dec(v___y_355_);
lean_dec_ref(v___y_354_);
lean_dec(v___y_353_);
return v_res_359_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(uint8_t v___y_368_, uint8_t v_suppressElabErrors_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 1)
{
lean_object* v_pre_371_; 
v_pre_371_ = lean_ctor_get(v_x_370_, 0);
switch(lean_obj_tag(v_pre_371_))
{
case 1:
{
lean_object* v_pre_372_; 
v_pre_372_ = lean_ctor_get(v_pre_371_, 0);
switch(lean_obj_tag(v_pre_372_))
{
case 0:
{
lean_object* v_str_373_; lean_object* v_str_374_; lean_object* v___x_375_; uint8_t v___x_376_; 
v_str_373_ = lean_ctor_get(v_x_370_, 1);
v_str_374_ = lean_ctor_get(v_pre_371_, 1);
v___x_375_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__0));
v___x_376_ = lean_string_dec_eq(v_str_374_, v___x_375_);
if (v___x_376_ == 0)
{
lean_object* v___x_377_; uint8_t v___x_378_; 
v___x_377_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__1));
v___x_378_ = lean_string_dec_eq(v_str_374_, v___x_377_);
if (v___x_378_ == 0)
{
return v___y_368_;
}
else
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__2));
v___x_380_ = lean_string_dec_eq(v_str_373_, v___x_379_);
if (v___x_380_ == 0)
{
return v___y_368_;
}
else
{
return v_suppressElabErrors_369_;
}
}
}
else
{
lean_object* v___x_381_; uint8_t v___x_382_; 
v___x_381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__3));
v___x_382_ = lean_string_dec_eq(v_str_373_, v___x_381_);
if (v___x_382_ == 0)
{
return v___y_368_;
}
else
{
return v_suppressElabErrors_369_;
}
}
}
case 1:
{
lean_object* v_pre_383_; 
v_pre_383_ = lean_ctor_get(v_pre_372_, 0);
if (lean_obj_tag(v_pre_383_) == 0)
{
lean_object* v_str_384_; lean_object* v_str_385_; lean_object* v_str_386_; lean_object* v___x_387_; uint8_t v___x_388_; 
v_str_384_ = lean_ctor_get(v_x_370_, 1);
v_str_385_ = lean_ctor_get(v_pre_371_, 1);
v_str_386_ = lean_ctor_get(v_pre_372_, 1);
v___x_387_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__4));
v___x_388_ = lean_string_dec_eq(v_str_386_, v___x_387_);
if (v___x_388_ == 0)
{
return v___y_368_;
}
else
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__5));
v___x_390_ = lean_string_dec_eq(v_str_385_, v___x_389_);
if (v___x_390_ == 0)
{
return v___y_368_;
}
else
{
lean_object* v___x_391_; uint8_t v___x_392_; 
v___x_391_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__6));
v___x_392_ = lean_string_dec_eq(v_str_384_, v___x_391_);
if (v___x_392_ == 0)
{
return v___y_368_;
}
else
{
return v_suppressElabErrors_369_;
}
}
}
}
else
{
return v___y_368_;
}
}
default: 
{
return v___y_368_;
}
}
}
case 0:
{
lean_object* v_str_393_; lean_object* v___x_394_; uint8_t v___x_395_; 
v_str_393_ = lean_ctor_get(v_x_370_, 1);
v___x_394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___closed__7));
v___x_395_ = lean_string_dec_eq(v_str_393_, v___x_394_);
if (v___x_395_ == 0)
{
return v___y_368_;
}
else
{
return v_suppressElabErrors_369_;
}
}
default: 
{
return v___y_368_;
}
}
}
else
{
return v___y_368_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed(lean_object* v___y_396_, lean_object* v_suppressElabErrors_397_, lean_object* v_x_398_){
_start:
{
uint8_t v___y_15938__boxed_399_; uint8_t v_suppressElabErrors_boxed_400_; uint8_t v_res_401_; lean_object* v_r_402_; 
v___y_15938__boxed_399_ = lean_unbox(v___y_396_);
v_suppressElabErrors_boxed_400_ = lean_unbox(v_suppressElabErrors_397_);
v_res_401_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0(v___y_15938__boxed_399_, v_suppressElabErrors_boxed_400_, v_x_398_);
lean_dec(v_x_398_);
v_r_402_ = lean_box(v_res_401_);
return v_r_402_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0(void){
_start:
{
lean_object* v___x_403_; 
v___x_403_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_403_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1(void){
_start:
{
lean_object* v___x_404_; lean_object* v___x_405_; 
v___x_404_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__0);
v___x_405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_405_, 0, v___x_404_);
return v___x_405_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2(void){
_start:
{
lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_406_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_408_, 0, v___x_407_);
lean_ctor_set(v___x_408_, 1, v___x_407_);
lean_ctor_set(v___x_408_, 2, v___x_407_);
lean_ctor_set(v___x_408_, 3, v___x_407_);
lean_ctor_set(v___x_408_, 4, v___x_406_);
lean_ctor_set(v___x_408_, 5, v___x_406_);
lean_ctor_set(v___x_408_, 6, v___x_406_);
lean_ctor_set(v___x_408_, 7, v___x_406_);
lean_ctor_set(v___x_408_, 8, v___x_406_);
lean_ctor_set(v___x_408_, 9, v___x_406_);
return v___x_408_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3(void){
_start:
{
lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
v___x_409_ = lean_unsigned_to_nat(32u);
v___x_410_ = lean_mk_empty_array_with_capacity(v___x_409_);
v___x_411_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_411_, 0, v___x_410_);
return v___x_411_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4(void){
_start:
{
size_t v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_412_ = ((size_t)5ULL);
v___x_413_ = lean_unsigned_to_nat(0u);
v___x_414_ = lean_unsigned_to_nat(32u);
v___x_415_ = lean_mk_empty_array_with_capacity(v___x_414_);
v___x_416_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__3);
v___x_417_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_417_, 0, v___x_416_);
lean_ctor_set(v___x_417_, 1, v___x_415_);
lean_ctor_set(v___x_417_, 2, v___x_413_);
lean_ctor_set(v___x_417_, 3, v___x_413_);
lean_ctor_set_usize(v___x_417_, 4, v___x_412_);
return v___x_417_;
}
}
static lean_object* _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5(void){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_418_ = lean_box(1);
v___x_419_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_420_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__1);
v___x_421_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_420_);
lean_ctor_set(v___x_421_, 1, v___x_419_);
lean_ctor_set(v___x_421_, 2, v___x_418_);
return v___x_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(lean_object* v_msgData_422_, lean_object* v___y_423_, lean_object* v___y_424_){
_start:
{
lean_object* v___x_426_; lean_object* v_env_427_; lean_object* v_options_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_426_ = lean_st_ref_get(v___y_424_);
v_env_427_ = lean_ctor_get(v___x_426_, 0);
lean_inc_ref(v_env_427_);
lean_dec(v___x_426_);
v_options_428_ = lean_ctor_get(v___y_423_, 2);
v___x_429_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__2);
v___x_430_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__5);
lean_inc_ref(v_options_428_);
v___x_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_431_, 0, v_env_427_);
lean_ctor_set(v___x_431_, 1, v___x_429_);
lean_ctor_set(v___x_431_, 2, v___x_430_);
lean_ctor_set(v___x_431_, 3, v_options_428_);
v___x_432_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_432_, 0, v___x_431_);
lean_ctor_set(v___x_432_, 1, v_msgData_422_);
v___x_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_433_, 0, v___x_432_);
return v___x_433_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___boxed(lean_object* v_msgData_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msgData_434_, v___y_435_, v___y_436_);
lean_dec(v___y_436_);
lean_dec_ref(v___y_435_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(lean_object* v_ref_440_, lean_object* v_msgData_441_, uint8_t v_severity_442_, uint8_t v_isSilent_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
uint8_t v___y_448_; lean_object* v___y_449_; lean_object* v___y_450_; lean_object* v___y_451_; lean_object* v___y_452_; lean_object* v___y_453_; uint8_t v___y_454_; lean_object* v___y_455_; lean_object* v___y_456_; lean_object* v___y_484_; uint8_t v___y_485_; lean_object* v___y_486_; lean_object* v___y_487_; lean_object* v___y_488_; uint8_t v___y_489_; uint8_t v___y_490_; lean_object* v___y_491_; lean_object* v___y_509_; lean_object* v___y_510_; uint8_t v___y_511_; lean_object* v___y_512_; lean_object* v___y_513_; uint8_t v___y_514_; uint8_t v___y_515_; lean_object* v___y_516_; lean_object* v___y_520_; uint8_t v___y_521_; lean_object* v___y_522_; lean_object* v___y_523_; lean_object* v___y_524_; uint8_t v___y_525_; uint8_t v___y_526_; uint8_t v___x_531_; lean_object* v___y_533_; lean_object* v___y_534_; lean_object* v___y_535_; lean_object* v___y_536_; uint8_t v___y_537_; uint8_t v___y_538_; uint8_t v___y_539_; uint8_t v___y_541_; uint8_t v___x_556_; 
v___x_531_ = 2;
v___x_556_ = l_Lean_instBEqMessageSeverity_beq(v_severity_442_, v___x_531_);
if (v___x_556_ == 0)
{
v___y_541_ = v___x_556_;
goto v___jp_540_;
}
else
{
uint8_t v___x_557_; 
lean_inc_ref(v_msgData_441_);
v___x_557_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_441_);
v___y_541_ = v___x_557_;
goto v___jp_540_;
}
v___jp_447_:
{
lean_object* v___x_457_; lean_object* v_currNamespace_458_; lean_object* v_openDecls_459_; lean_object* v_env_460_; lean_object* v_nextMacroScope_461_; lean_object* v_ngen_462_; lean_object* v_auxDeclNGen_463_; lean_object* v_traceState_464_; lean_object* v_cache_465_; lean_object* v_messages_466_; lean_object* v_infoState_467_; lean_object* v_snapshotTasks_468_; lean_object* v___x_470_; uint8_t v_isShared_471_; uint8_t v_isSharedCheck_482_; 
v___x_457_ = lean_st_ref_take(v___y_456_);
v_currNamespace_458_ = lean_ctor_get(v___y_455_, 6);
v_openDecls_459_ = lean_ctor_get(v___y_455_, 7);
v_env_460_ = lean_ctor_get(v___x_457_, 0);
v_nextMacroScope_461_ = lean_ctor_get(v___x_457_, 1);
v_ngen_462_ = lean_ctor_get(v___x_457_, 2);
v_auxDeclNGen_463_ = lean_ctor_get(v___x_457_, 3);
v_traceState_464_ = lean_ctor_get(v___x_457_, 4);
v_cache_465_ = lean_ctor_get(v___x_457_, 5);
v_messages_466_ = lean_ctor_get(v___x_457_, 6);
v_infoState_467_ = lean_ctor_get(v___x_457_, 7);
v_snapshotTasks_468_ = lean_ctor_get(v___x_457_, 8);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_457_);
if (v_isSharedCheck_482_ == 0)
{
v___x_470_ = v___x_457_;
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
else
{
lean_inc(v_snapshotTasks_468_);
lean_inc(v_infoState_467_);
lean_inc(v_messages_466_);
lean_inc(v_cache_465_);
lean_inc(v_traceState_464_);
lean_inc(v_auxDeclNGen_463_);
lean_inc(v_ngen_462_);
lean_inc(v_nextMacroScope_461_);
lean_inc(v_env_460_);
lean_dec(v___x_457_);
v___x_470_ = lean_box(0);
v_isShared_471_ = v_isSharedCheck_482_;
goto v_resetjp_469_;
}
v_resetjp_469_:
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_477_; 
lean_inc(v_openDecls_459_);
lean_inc(v_currNamespace_458_);
v___x_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_472_, 0, v_currNamespace_458_);
lean_ctor_set(v___x_472_, 1, v_openDecls_459_);
v___x_473_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___y_452_);
lean_inc_ref(v___y_450_);
lean_inc_ref(v___y_451_);
v___x_474_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_474_, 0, v___y_451_);
lean_ctor_set(v___x_474_, 1, v___y_449_);
lean_ctor_set(v___x_474_, 2, v___y_453_);
lean_ctor_set(v___x_474_, 3, v___y_450_);
lean_ctor_set(v___x_474_, 4, v___x_473_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*5, v___y_448_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*5 + 1, v___y_454_);
lean_ctor_set_uint8(v___x_474_, sizeof(void*)*5 + 2, v_isSilent_443_);
v___x_475_ = l_Lean_MessageLog_add(v___x_474_, v_messages_466_);
if (v_isShared_471_ == 0)
{
lean_ctor_set(v___x_470_, 6, v___x_475_);
v___x_477_ = v___x_470_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_env_460_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_nextMacroScope_461_);
lean_ctor_set(v_reuseFailAlloc_481_, 2, v_ngen_462_);
lean_ctor_set(v_reuseFailAlloc_481_, 3, v_auxDeclNGen_463_);
lean_ctor_set(v_reuseFailAlloc_481_, 4, v_traceState_464_);
lean_ctor_set(v_reuseFailAlloc_481_, 5, v_cache_465_);
lean_ctor_set(v_reuseFailAlloc_481_, 6, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_481_, 7, v_infoState_467_);
lean_ctor_set(v_reuseFailAlloc_481_, 8, v_snapshotTasks_468_);
v___x_477_ = v_reuseFailAlloc_481_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_478_ = lean_st_ref_set(v___y_456_, v___x_477_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
return v___x_480_;
}
}
}
v___jp_483_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_507_; 
v___x_492_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_441_);
v___x_493_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v___x_492_, v___y_444_, v___y_445_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_507_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_507_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; lean_object* v___x_501_; 
lean_inc_ref_n(v___y_486_, 2);
v___x_498_ = l_Lean_FileMap_toPosition(v___y_486_, v___y_487_);
lean_dec(v___y_487_);
v___x_499_ = l_Lean_FileMap_toPosition(v___y_486_, v___y_491_);
lean_dec(v___y_491_);
v___x_500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_500_, 0, v___x_499_);
v___x_501_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
if (v___y_489_ == 0)
{
lean_del_object(v___x_496_);
lean_dec_ref(v___y_484_);
v___y_448_ = v___y_485_;
v___y_449_ = v___x_498_;
v___y_450_ = v___x_501_;
v___y_451_ = v___y_488_;
v___y_452_ = v_a_494_;
v___y_453_ = v___x_500_;
v___y_454_ = v___y_490_;
v___y_455_ = v___y_444_;
v___y_456_ = v___y_445_;
goto v___jp_447_;
}
else
{
uint8_t v___x_502_; 
lean_inc(v_a_494_);
v___x_502_ = l_Lean_MessageData_hasTag(v___y_484_, v_a_494_);
if (v___x_502_ == 0)
{
lean_object* v___x_503_; lean_object* v___x_505_; 
lean_dec_ref_known(v___x_500_, 1);
lean_dec_ref(v___x_498_);
lean_dec(v_a_494_);
v___x_503_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
else
{
lean_del_object(v___x_496_);
v___y_448_ = v___y_485_;
v___y_449_ = v___x_498_;
v___y_450_ = v___x_501_;
v___y_451_ = v___y_488_;
v___y_452_ = v_a_494_;
v___y_453_ = v___x_500_;
v___y_454_ = v___y_490_;
v___y_455_ = v___y_444_;
v___y_456_ = v___y_445_;
goto v___jp_447_;
}
}
}
}
v___jp_508_:
{
lean_object* v___x_517_; 
v___x_517_ = l_Lean_Syntax_getTailPos_x3f(v___y_513_, v___y_511_);
lean_dec(v___y_513_);
if (lean_obj_tag(v___x_517_) == 0)
{
lean_inc(v___y_516_);
v___y_484_ = v___y_509_;
v___y_485_ = v___y_511_;
v___y_486_ = v___y_510_;
v___y_487_ = v___y_516_;
v___y_488_ = v___y_512_;
v___y_489_ = v___y_515_;
v___y_490_ = v___y_514_;
v___y_491_ = v___y_516_;
goto v___jp_483_;
}
else
{
lean_object* v_val_518_; 
v_val_518_ = lean_ctor_get(v___x_517_, 0);
lean_inc(v_val_518_);
lean_dec_ref_known(v___x_517_, 1);
v___y_484_ = v___y_509_;
v___y_485_ = v___y_511_;
v___y_486_ = v___y_510_;
v___y_487_ = v___y_516_;
v___y_488_ = v___y_512_;
v___y_489_ = v___y_515_;
v___y_490_ = v___y_514_;
v___y_491_ = v_val_518_;
goto v___jp_483_;
}
}
v___jp_519_:
{
lean_object* v_ref_527_; lean_object* v___x_528_; 
v_ref_527_ = l_Lean_replaceRef(v_ref_440_, v___y_524_);
v___x_528_ = l_Lean_Syntax_getPos_x3f(v_ref_527_, v___y_521_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_unsigned_to_nat(0u);
v___y_509_ = v___y_520_;
v___y_510_ = v___y_522_;
v___y_511_ = v___y_521_;
v___y_512_ = v___y_523_;
v___y_513_ = v_ref_527_;
v___y_514_ = v___y_526_;
v___y_515_ = v___y_525_;
v___y_516_ = v___x_529_;
goto v___jp_508_;
}
else
{
lean_object* v_val_530_; 
v_val_530_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_528_, 1);
v___y_509_ = v___y_520_;
v___y_510_ = v___y_522_;
v___y_511_ = v___y_521_;
v___y_512_ = v___y_523_;
v___y_513_ = v_ref_527_;
v___y_514_ = v___y_526_;
v___y_515_ = v___y_525_;
v___y_516_ = v_val_530_;
goto v___jp_508_;
}
}
v___jp_532_:
{
if (v___y_539_ == 0)
{
v___y_520_ = v___y_534_;
v___y_521_ = v___y_538_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_536_;
v___y_525_ = v___y_537_;
v___y_526_ = v_severity_442_;
goto v___jp_519_;
}
else
{
v___y_520_ = v___y_534_;
v___y_521_ = v___y_538_;
v___y_522_ = v___y_533_;
v___y_523_ = v___y_535_;
v___y_524_ = v___y_536_;
v___y_525_ = v___y_537_;
v___y_526_ = v___x_531_;
goto v___jp_519_;
}
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v_fileName_542_; lean_object* v_fileMap_543_; lean_object* v_options_544_; lean_object* v_ref_545_; uint8_t v_suppressElabErrors_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___f_549_; uint8_t v___x_550_; uint8_t v___x_551_; 
v_fileName_542_ = lean_ctor_get(v___y_444_, 0);
v_fileMap_543_ = lean_ctor_get(v___y_444_, 1);
v_options_544_ = lean_ctor_get(v___y_444_, 2);
v_ref_545_ = lean_ctor_get(v___y_444_, 5);
v_suppressElabErrors_546_ = lean_ctor_get_uint8(v___y_444_, sizeof(void*)*14 + 1);
v___x_547_ = lean_box(v___y_541_);
v___x_548_ = lean_box(v_suppressElabErrors_546_);
v___f_549_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___lam__0___boxed), 3, 2);
lean_closure_set(v___f_549_, 0, v___x_547_);
lean_closure_set(v___f_549_, 1, v___x_548_);
v___x_550_ = 1;
v___x_551_ = l_Lean_instBEqMessageSeverity_beq(v_severity_442_, v___x_550_);
if (v___x_551_ == 0)
{
v___y_533_ = v_fileMap_543_;
v___y_534_ = v___f_549_;
v___y_535_ = v_fileName_542_;
v___y_536_ = v_ref_545_;
v___y_537_ = v_suppressElabErrors_546_;
v___y_538_ = v___y_541_;
v___y_539_ = v___x_551_;
goto v___jp_532_;
}
else
{
lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_552_ = l_Lean_warningAsError;
v___x_553_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_544_, v___x_552_);
v___y_533_ = v_fileMap_543_;
v___y_534_ = v___f_549_;
v___y_535_ = v_fileName_542_;
v___y_536_ = v_ref_545_;
v___y_537_ = v_suppressElabErrors_546_;
v___y_538_ = v___y_541_;
v___y_539_ = v___x_553_;
goto v___jp_532_;
}
}
else
{
lean_object* v___x_554_; lean_object* v___x_555_; 
lean_dec_ref(v_msgData_441_);
v___x_554_ = lean_box(0);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v___x_554_);
return v___x_555_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___boxed(lean_object* v_ref_558_, lean_object* v_msgData_559_, lean_object* v_severity_560_, lean_object* v_isSilent_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
uint8_t v_severity_boxed_565_; uint8_t v_isSilent_boxed_566_; lean_object* v_res_567_; 
v_severity_boxed_565_ = lean_unbox(v_severity_560_);
v_isSilent_boxed_566_ = lean_unbox(v_isSilent_561_);
v_res_567_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_558_, v_msgData_559_, v_severity_boxed_565_, v_isSilent_boxed_566_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v_ref_558_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(lean_object* v_msgData_568_, uint8_t v_severity_569_, uint8_t v_isSilent_570_, lean_object* v___y_571_, lean_object* v___y_572_){
_start:
{
lean_object* v_ref_574_; lean_object* v___x_575_; 
v_ref_574_ = lean_ctor_get(v___y_571_, 5);
v___x_575_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9(v_ref_574_, v_msgData_568_, v_severity_569_, v_isSilent_570_, v___y_571_, v___y_572_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4___boxed(lean_object* v_msgData_576_, lean_object* v_severity_577_, lean_object* v_isSilent_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
uint8_t v_severity_boxed_582_; uint8_t v_isSilent_boxed_583_; lean_object* v_res_584_; 
v_severity_boxed_582_ = lean_unbox(v_severity_577_);
v_isSilent_boxed_583_ = lean_unbox(v_isSilent_578_);
v_res_584_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_576_, v_severity_boxed_582_, v_isSilent_boxed_583_, v___y_579_, v___y_580_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(lean_object* v_msgData_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
uint8_t v___x_589_; uint8_t v___x_590_; lean_object* v___x_591_; 
v___x_589_ = 1;
v___x_590_ = 0;
v___x_591_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4(v_msgData_585_, v___x_589_, v___x_590_, v___y_586_, v___y_587_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2___boxed(lean_object* v_msgData_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v_msgData_592_, v___y_593_, v___y_594_);
lean_dec(v___y_594_);
lean_dec_ref(v___y_593_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(lean_object* v_as_600_, size_t v_sz_601_, size_t v_i_602_, lean_object* v_b_603_){
_start:
{
uint8_t v___x_604_; 
v___x_604_ = lean_usize_dec_lt(v_i_602_, v_sz_601_);
if (v___x_604_ == 0)
{
lean_inc_ref(v_b_603_);
return v_b_603_;
}
else
{
lean_object* v_a_605_; lean_object* v_fst_606_; lean_object* v___x_607_; uint8_t v___x_608_; 
v_a_605_ = lean_array_uget_borrowed(v_as_600_, v_i_602_);
v_fst_606_ = lean_ctor_get(v_a_605_, 0);
v___x_607_ = lean_box(0);
v___x_608_ = lean_unbox(v_fst_606_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; size_t v___x_610_; size_t v___x_611_; 
v___x_609_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___closed__0));
v___x_610_ = ((size_t)1ULL);
v___x_611_ = lean_usize_add(v_i_602_, v___x_610_);
v_i_602_ = v___x_611_;
v_b_603_ = v___x_609_;
goto _start;
}
else
{
lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; 
lean_inc(v_a_605_);
v___x_613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_613_, 0, v_a_605_);
v___x_614_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_614_, 0, v___x_613_);
v___x_615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v___x_607_);
return v___x_615_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3___boxed(lean_object* v_as_616_, lean_object* v_sz_617_, lean_object* v_i_618_, lean_object* v_b_619_){
_start:
{
size_t v_sz_boxed_620_; size_t v_i_boxed_621_; lean_object* v_res_622_; 
v_sz_boxed_620_ = lean_unbox_usize(v_sz_617_);
lean_dec(v_sz_617_);
v_i_boxed_621_ = lean_unbox_usize(v_i_618_);
lean_dec(v_i_618_);
v_res_622_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v_as_616_, v_sz_boxed_620_, v_i_boxed_621_, v_b_619_);
lean_dec_ref(v_b_619_);
lean_dec_ref(v_as_616_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(lean_object* v_fn_623_, lean_object* v_e_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_){
_start:
{
lean_object* v___x_631_; 
v___x_631_ = l_Lean_Expr_getSorry_x3f(v_e_624_);
if (lean_obj_tag(v___x_631_) == 1)
{
lean_object* v_val_632_; lean_object* v___x_633_; 
v_val_632_ = lean_ctor_get(v___x_631_, 0);
lean_inc(v_val_632_);
lean_dec_ref_known(v___x_631_, 1);
lean_inc(v___y_629_);
lean_inc_ref(v___y_628_);
lean_inc(v___y_627_);
lean_inc_ref(v___y_626_);
lean_inc(v___y_625_);
v___x_633_ = lean_apply_7(v_fn_623_, v_val_632_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, lean_box(0));
if (lean_obj_tag(v___x_633_) == 0)
{
lean_object* v___x_635_; uint8_t v_isShared_636_; uint8_t v_isSharedCheck_642_; 
v_isSharedCheck_642_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_642_ == 0)
{
lean_object* v_unused_643_; 
v_unused_643_ = lean_ctor_get(v___x_633_, 0);
lean_dec(v_unused_643_);
v___x_635_ = v___x_633_;
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
else
{
lean_dec(v___x_633_);
v___x_635_ = lean_box(0);
v_isShared_636_ = v_isSharedCheck_642_;
goto v_resetjp_634_;
}
v_resetjp_634_:
{
uint8_t v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = 0;
v___x_638_ = lean_box(v___x_637_);
if (v_isShared_636_ == 0)
{
lean_ctor_set(v___x_635_, 0, v___x_638_);
v___x_640_ = v___x_635_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
else
{
lean_object* v_a_644_; lean_object* v___x_646_; uint8_t v_isShared_647_; uint8_t v_isSharedCheck_651_; 
v_a_644_ = lean_ctor_get(v___x_633_, 0);
v_isSharedCheck_651_ = !lean_is_exclusive(v___x_633_);
if (v_isSharedCheck_651_ == 0)
{
v___x_646_ = v___x_633_;
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
else
{
lean_inc(v_a_644_);
lean_dec(v___x_633_);
v___x_646_ = lean_box(0);
v_isShared_647_ = v_isSharedCheck_651_;
goto v_resetjp_645_;
}
v_resetjp_645_:
{
lean_object* v___x_649_; 
if (v_isShared_647_ == 0)
{
v___x_649_ = v___x_646_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v_a_644_);
v___x_649_ = v_reuseFailAlloc_650_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
return v___x_649_;
}
}
}
}
else
{
uint8_t v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
lean_dec(v___x_631_);
lean_dec_ref(v_fn_623_);
v___x_652_ = 1;
v___x_653_ = lean_box(v___x_652_);
v___x_654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_654_, 0, v___x_653_);
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed(lean_object* v_fn_655_, lean_object* v_e_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0(v_fn_655_, v_e_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_);
lean_dec(v___y_661_);
lean_dec_ref(v___y_660_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v_e_656_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_664_, lean_object* v_x_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; 
v___x_672_ = lean_apply_1(v_x_665_, lean_box(0));
v___x_673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_673_, 0, v___x_672_);
return v___x_673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_674_, lean_object* v_x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(v_00_u03b1_674_, v_x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(lean_object* v_k_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v___x_692_; 
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v___y_688_);
lean_inc_ref(v___y_687_);
lean_inc(v___y_685_);
lean_inc(v___y_684_);
v___x_692_ = lean_apply_8(v_k_683_, v_b_686_, v___y_684_, v___y_685_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, lean_box(0));
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed(lean_object* v_k_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v_b_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v_res_702_; 
v_res_702_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0(v_k_693_, v___y_694_, v___y_695_, v_b_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_);
lean_dec(v___y_700_);
lean_dec_ref(v___y_699_);
lean_dec(v___y_698_);
lean_dec_ref(v___y_697_);
lean_dec(v___y_695_);
lean_dec(v___y_694_);
return v_res_702_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(lean_object* v_name_703_, lean_object* v_type_704_, lean_object* v_val_705_, lean_object* v_k_706_, uint8_t v_nondep_707_, uint8_t v_kind_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_){
_start:
{
lean_object* v___f_716_; lean_object* v___x_717_; 
lean_inc(v___y_710_);
lean_inc(v___y_709_);
v___f_716_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_716_, 0, v_k_706_);
lean_closure_set(v___f_716_, 1, v___y_709_);
lean_closure_set(v___f_716_, 2, v___y_710_);
v___x_717_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_703_, v_type_704_, v_val_705_, v___f_716_, v_nondep_707_, v_kind_708_, v___y_711_, v___y_712_, v___y_713_, v___y_714_);
if (lean_obj_tag(v___x_717_) == 0)
{
return v___x_717_;
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
v_a_718_ = lean_ctor_get(v___x_717_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_717_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_717_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_717_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg___boxed(lean_object* v_name_726_, lean_object* v_type_727_, lean_object* v_val_728_, lean_object* v_k_729_, lean_object* v_nondep_730_, lean_object* v_kind_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_){
_start:
{
uint8_t v_nondep_boxed_739_; uint8_t v_kind_boxed_740_; lean_object* v_res_741_; 
v_nondep_boxed_739_ = lean_unbox(v_nondep_730_);
v_kind_boxed_740_ = lean_unbox(v_kind_731_);
v_res_741_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_726_, v_type_727_, v_val_728_, v_k_729_, v_nondep_boxed_739_, v_kind_boxed_740_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec(v___y_732_);
return v_res_741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed(lean_object* v_fvars_742_, lean_object* v_f_743_, lean_object* v_body_744_, lean_object* v_x_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_){
_start:
{
lean_object* v_res_753_; 
v_res_753_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(v_fvars_742_, v_f_743_, v_body_744_, v_x_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_);
lean_dec(v___y_751_);
lean_dec_ref(v___y_750_);
lean_dec(v___y_749_);
lean_dec_ref(v___y_748_);
lean_dec(v___y_747_);
lean_dec(v___y_746_);
return v_res_753_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(lean_object* v_f_754_, lean_object* v_fvars_755_, lean_object* v_a_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
if (lean_obj_tag(v_a_756_) == 8)
{
lean_object* v_declName_764_; lean_object* v_type_765_; lean_object* v_value_766_; lean_object* v_body_767_; lean_object* v_d_768_; lean_object* v___x_769_; 
v_declName_764_ = lean_ctor_get(v_a_756_, 0);
lean_inc(v_declName_764_);
v_type_765_ = lean_ctor_get(v_a_756_, 1);
lean_inc_ref(v_type_765_);
v_value_766_ = lean_ctor_get(v_a_756_, 2);
lean_inc_ref(v_value_766_);
v_body_767_ = lean_ctor_get(v_a_756_, 3);
lean_inc_ref(v_body_767_);
lean_dec_ref_known(v_a_756_, 4);
v_d_768_ = lean_expr_instantiate_rev(v_type_765_, v_fvars_755_);
lean_dec_ref(v_type_765_);
lean_inc_ref(v_f_754_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v_d_768_);
v___x_769_ = lean_apply_8(v_f_754_, v_d_768_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, lean_box(0));
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_v_770_; lean_object* v___x_771_; 
lean_dec_ref_known(v___x_769_, 1);
v_v_770_ = lean_expr_instantiate_rev(v_value_766_, v_fvars_755_);
lean_dec_ref(v_value_766_);
lean_inc_ref(v_f_754_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc(v___y_757_);
lean_inc_ref(v_v_770_);
v___x_771_ = lean_apply_8(v_f_754_, v_v_770_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, lean_box(0));
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v___f_772_; uint8_t v___x_773_; uint8_t v___x_774_; lean_object* v___x_775_; 
lean_dec_ref_known(v___x_771_, 1);
v___f_772_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0___boxed), 11, 3);
lean_closure_set(v___f_772_, 0, v_fvars_755_);
lean_closure_set(v___f_772_, 1, v_f_754_);
lean_closure_set(v___f_772_, 2, v_body_767_);
v___x_773_ = 0;
v___x_774_ = 0;
v___x_775_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_declName_764_, v_d_768_, v_v_770_, v___f_772_, v___x_773_, v___x_774_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
return v___x_775_;
}
else
{
lean_dec_ref(v_v_770_);
lean_dec_ref(v_d_768_);
lean_dec_ref(v_body_767_);
lean_dec(v_declName_764_);
lean_dec_ref(v_fvars_755_);
lean_dec_ref(v_f_754_);
return v___x_771_;
}
}
else
{
lean_dec_ref(v_d_768_);
lean_dec_ref(v_body_767_);
lean_dec_ref(v_value_766_);
lean_dec(v_declName_764_);
lean_dec_ref(v_fvars_755_);
lean_dec_ref(v_f_754_);
return v___x_769_;
}
}
else
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = lean_expr_instantiate_rev(v_a_756_, v_fvars_755_);
lean_dec_ref(v_fvars_755_);
lean_dec_ref(v_a_756_);
lean_inc(v___y_762_);
lean_inc_ref(v___y_761_);
lean_inc(v___y_760_);
lean_inc_ref(v___y_759_);
lean_inc(v___y_758_);
lean_inc(v___y_757_);
v___x_777_ = lean_apply_8(v_f_754_, v___x_776_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, lean_box(0));
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___lam__0(lean_object* v_fvars_778_, lean_object* v_f_779_, lean_object* v_body_780_, lean_object* v_x_781_, lean_object* v___y_782_, lean_object* v___y_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; 
v___x_789_ = lean_array_push(v_fvars_778_, v_x_781_);
v___x_790_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_779_, v___x_789_, v_body_780_, v___y_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_);
return v___x_790_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24___boxed(lean_object* v_f_791_, lean_object* v_fvars_792_, lean_object* v_a_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_791_, v_fvars_792_, v_a_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_794_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(lean_object* v_f_804_, lean_object* v_e_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_813_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_814_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24(v_f_804_, v___x_813_, v_e_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
return v___x_814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___boxed(lean_object* v_f_815_, lean_object* v_e_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v_f_815_, v_e_816_, v___y_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
lean_dec(v___y_818_);
lean_dec(v___y_817_);
return v_res_824_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(lean_object* v_name_825_, uint8_t v_bi_826_, lean_object* v_type_827_, lean_object* v_k_828_, uint8_t v_kind_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_){
_start:
{
lean_object* v___f_837_; lean_object* v___x_838_; 
lean_inc(v___y_831_);
lean_inc(v___y_830_);
v___f_837_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___lam__0___boxed), 9, 3);
lean_closure_set(v___f_837_, 0, v_k_828_);
lean_closure_set(v___f_837_, 1, v___y_830_);
lean_closure_set(v___f_837_, 2, v___y_831_);
v___x_838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_825_, v_bi_826_, v_type_827_, v___f_837_, v_kind_829_, v___y_832_, v___y_833_, v___y_834_, v___y_835_);
if (lean_obj_tag(v___x_838_) == 0)
{
return v___x_838_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_838_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_838_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg___boxed(lean_object* v_name_847_, lean_object* v_bi_848_, lean_object* v_type_849_, lean_object* v_k_850_, lean_object* v_kind_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_, lean_object* v___y_858_){
_start:
{
uint8_t v_bi_boxed_859_; uint8_t v_kind_boxed_860_; lean_object* v_res_861_; 
v_bi_boxed_859_ = lean_unbox(v_bi_848_);
v_kind_boxed_860_ = lean_unbox(v_kind_851_);
v_res_861_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_847_, v_bi_boxed_859_, v_type_849_, v_k_850_, v_kind_boxed_860_, v___y_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_, v___y_857_);
lean_dec(v___y_857_);
lean_dec_ref(v___y_856_);
lean_dec(v___y_855_);
lean_dec_ref(v___y_854_);
lean_dec(v___y_853_);
lean_dec(v___y_852_);
return v_res_861_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed(lean_object* v_fvars_862_, lean_object* v_f_863_, lean_object* v_body_864_, lean_object* v_x_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(v_fvars_862_, v_f_863_, v_body_864_, v_x_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_, v___y_871_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
lean_dec(v___y_869_);
lean_dec_ref(v___y_868_);
lean_dec(v___y_867_);
lean_dec(v___y_866_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(lean_object* v_f_874_, lean_object* v_fvars_875_, lean_object* v_a_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
if (lean_obj_tag(v_a_876_) == 7)
{
lean_object* v_binderName_884_; lean_object* v_binderType_885_; lean_object* v_body_886_; uint8_t v_binderInfo_887_; lean_object* v_d_888_; lean_object* v___x_889_; 
v_binderName_884_ = lean_ctor_get(v_a_876_, 0);
lean_inc(v_binderName_884_);
v_binderType_885_ = lean_ctor_get(v_a_876_, 1);
lean_inc_ref(v_binderType_885_);
v_body_886_ = lean_ctor_get(v_a_876_, 2);
lean_inc_ref(v_body_886_);
v_binderInfo_887_ = lean_ctor_get_uint8(v_a_876_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_876_, 3);
v_d_888_ = lean_expr_instantiate_rev(v_binderType_885_, v_fvars_875_);
lean_dec_ref(v_binderType_885_);
lean_inc_ref(v_f_874_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc(v___y_877_);
lean_inc_ref(v_d_888_);
v___x_889_ = lean_apply_8(v_f_874_, v_d_888_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v___f_890_; uint8_t v___x_891_; lean_object* v___x_892_; 
lean_dec_ref_known(v___x_889_, 1);
v___f_890_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0___boxed), 11, 3);
lean_closure_set(v___f_890_, 0, v_fvars_875_);
lean_closure_set(v___f_890_, 1, v_f_874_);
lean_closure_set(v___f_890_, 2, v_body_886_);
v___x_891_ = 0;
v___x_892_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_884_, v_binderInfo_887_, v_d_888_, v___f_890_, v___x_891_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_);
return v___x_892_;
}
else
{
lean_dec_ref(v_d_888_);
lean_dec_ref(v_body_886_);
lean_dec(v_binderName_884_);
lean_dec_ref(v_fvars_875_);
lean_dec_ref(v_f_874_);
return v___x_889_;
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_893_ = lean_expr_instantiate_rev(v_a_876_, v_fvars_875_);
lean_dec_ref(v_fvars_875_);
lean_dec_ref(v_a_876_);
lean_inc(v___y_882_);
lean_inc_ref(v___y_881_);
lean_inc(v___y_880_);
lean_inc_ref(v___y_879_);
lean_inc(v___y_878_);
lean_inc(v___y_877_);
v___x_894_ = lean_apply_8(v_f_874_, v___x_893_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, lean_box(0));
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___lam__0(lean_object* v_fvars_895_, lean_object* v_f_896_, lean_object* v_body_897_, lean_object* v_x_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_){
_start:
{
lean_object* v___x_906_; lean_object* v___x_907_; 
v___x_906_ = lean_array_push(v_fvars_895_, v_x_898_);
v___x_907_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_896_, v___x_906_, v_body_897_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20___boxed(lean_object* v_f_908_, lean_object* v_fvars_909_, lean_object* v_a_910_, lean_object* v___y_911_, lean_object* v___y_912_, lean_object* v___y_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_){
_start:
{
lean_object* v_res_918_; 
v_res_918_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_908_, v_fvars_909_, v_a_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_, v___y_916_);
lean_dec(v___y_916_);
lean_dec_ref(v___y_915_);
lean_dec(v___y_914_);
lean_dec_ref(v___y_913_);
lean_dec(v___y_912_);
lean_dec(v___y_911_);
return v_res_918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(lean_object* v_f_919_, lean_object* v_e_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_, lean_object* v___y_926_){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; 
v___x_928_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_929_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20(v_f_919_, v___x_928_, v_e_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_, v___y_925_, v___y_926_);
return v___x_929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10___boxed(lean_object* v_f_930_, lean_object* v_e_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_res_939_; 
v_res_939_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v_f_930_, v_e_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
lean_dec(v___y_937_);
lean_dec_ref(v___y_936_);
lean_dec(v___y_935_);
lean_dec_ref(v___y_934_);
lean_dec(v___y_933_);
lean_dec(v___y_932_);
return v_res_939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed(lean_object* v_fvars_940_, lean_object* v_f_941_, lean_object* v_body_942_, lean_object* v_x_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_){
_start:
{
lean_object* v_res_951_; 
v_res_951_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(v_fvars_940_, v_f_941_, v_body_942_, v_x_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___y_945_);
lean_dec(v___y_944_);
return v_res_951_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(lean_object* v_f_952_, lean_object* v_fvars_953_, lean_object* v_a_954_, lean_object* v___y_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
if (lean_obj_tag(v_a_954_) == 6)
{
lean_object* v_binderName_962_; lean_object* v_binderType_963_; lean_object* v_body_964_; uint8_t v_binderInfo_965_; lean_object* v_d_966_; lean_object* v___x_967_; 
v_binderName_962_ = lean_ctor_get(v_a_954_, 0);
lean_inc(v_binderName_962_);
v_binderType_963_ = lean_ctor_get(v_a_954_, 1);
lean_inc_ref(v_binderType_963_);
v_body_964_ = lean_ctor_get(v_a_954_, 2);
lean_inc_ref(v_body_964_);
v_binderInfo_965_ = lean_ctor_get_uint8(v_a_954_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v_a_954_, 3);
v_d_966_ = lean_expr_instantiate_rev(v_binderType_963_, v_fvars_953_);
lean_dec_ref(v_binderType_963_);
lean_inc_ref(v_f_952_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc(v___y_955_);
lean_inc_ref(v_d_966_);
v___x_967_ = lean_apply_8(v_f_952_, v_d_966_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, lean_box(0));
if (lean_obj_tag(v___x_967_) == 0)
{
lean_object* v___f_968_; uint8_t v___x_969_; lean_object* v___x_970_; 
lean_dec_ref_known(v___x_967_, 1);
v___f_968_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0___boxed), 11, 3);
lean_closure_set(v___f_968_, 0, v_fvars_953_);
lean_closure_set(v___f_968_, 1, v_f_952_);
lean_closure_set(v___f_968_, 2, v_body_964_);
v___x_969_ = 0;
v___x_970_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_binderName_962_, v_binderInfo_965_, v_d_966_, v___f_968_, v___x_969_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_);
return v___x_970_;
}
else
{
lean_dec_ref(v_d_966_);
lean_dec_ref(v_body_964_);
lean_dec(v_binderName_962_);
lean_dec_ref(v_fvars_953_);
lean_dec_ref(v_f_952_);
return v___x_967_;
}
}
else
{
lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_971_ = lean_expr_instantiate_rev(v_a_954_, v_fvars_953_);
lean_dec_ref(v_fvars_953_);
lean_dec_ref(v_a_954_);
lean_inc(v___y_960_);
lean_inc_ref(v___y_959_);
lean_inc(v___y_958_);
lean_inc_ref(v___y_957_);
lean_inc(v___y_956_);
lean_inc(v___y_955_);
v___x_972_ = lean_apply_8(v_f_952_, v___x_971_, v___y_955_, v___y_956_, v___y_957_, v___y_958_, v___y_959_, v___y_960_, lean_box(0));
return v___x_972_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___lam__0(lean_object* v_fvars_973_, lean_object* v_f_974_, lean_object* v_body_975_, lean_object* v_x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v___x_984_; lean_object* v___x_985_; 
v___x_984_ = lean_array_push(v_fvars_973_, v_x_976_);
v___x_985_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_974_, v___x_984_, v_body_975_, v___y_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_, v___y_982_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22___boxed(lean_object* v_f_986_, lean_object* v_fvars_987_, lean_object* v_a_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_){
_start:
{
lean_object* v_res_996_; 
v_res_996_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_986_, v_fvars_987_, v_a_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
lean_dec(v___y_994_);
lean_dec_ref(v___y_993_);
lean_dec(v___y_992_);
lean_dec_ref(v___y_991_);
lean_dec(v___y_990_);
lean_dec(v___y_989_);
return v_res_996_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(lean_object* v_f_997_, lean_object* v_e_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_){
_start:
{
lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1006_ = ((lean_object*)(l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12___closed__0));
v___x_1007_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLambda_visit___at___00Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11_spec__22(v_f_997_, v___x_1006_, v_e_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_, v___y_1003_, v___y_1004_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11___boxed(lean_object* v_f_1008_, lean_object* v_e_1009_, lean_object* v___y_1010_, lean_object* v___y_1011_, lean_object* v___y_1012_, lean_object* v___y_1013_, lean_object* v___y_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v_f_1008_, v_e_1009_, v___y_1010_, v___y_1011_, v___y_1012_, v___y_1013_, v___y_1014_, v___y_1015_);
lean_dec(v___y_1015_);
lean_dec_ref(v___y_1014_);
lean_dec(v___y_1013_);
lean_dec_ref(v___y_1012_);
lean_dec(v___y_1011_);
lean_dec(v___y_1010_);
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(lean_object* v_a_1018_, lean_object* v_x_1019_){
_start:
{
if (lean_obj_tag(v_x_1019_) == 0)
{
lean_object* v___x_1020_; 
v___x_1020_ = lean_box(0);
return v___x_1020_;
}
else
{
lean_object* v_key_1021_; lean_object* v_value_1022_; lean_object* v_tail_1023_; uint8_t v___x_1024_; 
v_key_1021_ = lean_ctor_get(v_x_1019_, 0);
v_value_1022_ = lean_ctor_get(v_x_1019_, 1);
v_tail_1023_ = lean_ctor_get(v_x_1019_, 2);
v___x_1024_ = lean_expr_eqv(v_key_1021_, v_a_1018_);
if (v___x_1024_ == 0)
{
v_x_1019_ = v_tail_1023_;
goto _start;
}
else
{
lean_object* v___x_1026_; 
lean_inc(v_value_1022_);
v___x_1026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1026_, 0, v_value_1022_);
return v___x_1026_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_a_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1027_, v_x_1028_);
lean_dec(v_x_1028_);
lean_dec_ref(v_a_1027_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(lean_object* v_m_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v_buckets_1032_; lean_object* v___x_1033_; uint64_t v___x_1034_; uint64_t v___x_1035_; uint64_t v___x_1036_; uint64_t v_fold_1037_; uint64_t v___x_1038_; uint64_t v___x_1039_; uint64_t v___x_1040_; size_t v___x_1041_; size_t v___x_1042_; size_t v___x_1043_; size_t v___x_1044_; size_t v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; 
v_buckets_1032_ = lean_ctor_get(v_m_1030_, 1);
v___x_1033_ = lean_array_get_size(v_buckets_1032_);
v___x_1034_ = l_Lean_Expr_hash(v_a_1031_);
v___x_1035_ = 32ULL;
v___x_1036_ = lean_uint64_shift_right(v___x_1034_, v___x_1035_);
v_fold_1037_ = lean_uint64_xor(v___x_1034_, v___x_1036_);
v___x_1038_ = 16ULL;
v___x_1039_ = lean_uint64_shift_right(v_fold_1037_, v___x_1038_);
v___x_1040_ = lean_uint64_xor(v_fold_1037_, v___x_1039_);
v___x_1041_ = lean_uint64_to_usize(v___x_1040_);
v___x_1042_ = lean_usize_of_nat(v___x_1033_);
v___x_1043_ = ((size_t)1ULL);
v___x_1044_ = lean_usize_sub(v___x_1042_, v___x_1043_);
v___x_1045_ = lean_usize_land(v___x_1041_, v___x_1044_);
v___x_1046_ = lean_array_uget_borrowed(v_buckets_1032_, v___x_1045_);
v___x_1047_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1031_, v___x_1046_);
return v___x_1047_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg___boxed(lean_object* v_m_1048_, lean_object* v_a_1049_){
_start:
{
lean_object* v_res_1050_; 
v_res_1050_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1048_, v_a_1049_);
lean_dec_ref(v_a_1049_);
lean_dec_ref(v_m_1048_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_object* v_00_u03b1_1051_, lean_object* v_x_1052_, lean_object* v___y_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = lean_apply_1(v_x_1052_, lean_box(0));
v___x_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1060_, 0, v___x_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_x_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(v_00_u03b1_1061_, v_x_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
lean_dec(v___y_1067_);
lean_dec_ref(v___y_1066_);
lean_dec(v___y_1065_);
lean_dec_ref(v___y_1064_);
lean_dec(v___y_1063_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(lean_object* v_x_1070_, lean_object* v_x_1071_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
return v_x_1070_;
}
else
{
lean_object* v_key_1072_; lean_object* v_value_1073_; lean_object* v_tail_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1097_; 
v_key_1072_ = lean_ctor_get(v_x_1071_, 0);
v_value_1073_ = lean_ctor_get(v_x_1071_, 1);
v_tail_1074_ = lean_ctor_get(v_x_1071_, 2);
v_isSharedCheck_1097_ = !lean_is_exclusive(v_x_1071_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1076_ = v_x_1071_;
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_tail_1074_);
lean_inc(v_value_1073_);
lean_inc(v_key_1072_);
lean_dec(v_x_1071_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1097_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; uint64_t v___x_1079_; uint64_t v___x_1080_; uint64_t v___x_1081_; uint64_t v_fold_1082_; uint64_t v___x_1083_; uint64_t v___x_1084_; uint64_t v___x_1085_; size_t v___x_1086_; size_t v___x_1087_; size_t v___x_1088_; size_t v___x_1089_; size_t v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1078_ = lean_array_get_size(v_x_1070_);
v___x_1079_ = l_Lean_Expr_hash(v_key_1072_);
v___x_1080_ = 32ULL;
v___x_1081_ = lean_uint64_shift_right(v___x_1079_, v___x_1080_);
v_fold_1082_ = lean_uint64_xor(v___x_1079_, v___x_1081_);
v___x_1083_ = 16ULL;
v___x_1084_ = lean_uint64_shift_right(v_fold_1082_, v___x_1083_);
v___x_1085_ = lean_uint64_xor(v_fold_1082_, v___x_1084_);
v___x_1086_ = lean_uint64_to_usize(v___x_1085_);
v___x_1087_ = lean_usize_of_nat(v___x_1078_);
v___x_1088_ = ((size_t)1ULL);
v___x_1089_ = lean_usize_sub(v___x_1087_, v___x_1088_);
v___x_1090_ = lean_usize_land(v___x_1086_, v___x_1089_);
v___x_1091_ = lean_array_uget_borrowed(v_x_1070_, v___x_1090_);
lean_inc(v___x_1091_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 2, v___x_1091_);
v___x_1093_ = v___x_1076_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v_key_1072_);
lean_ctor_set(v_reuseFailAlloc_1096_, 1, v_value_1073_);
lean_ctor_set(v_reuseFailAlloc_1096_, 2, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
lean_object* v___x_1094_; 
v___x_1094_ = lean_array_uset(v_x_1070_, v___x_1090_, v___x_1093_);
v_x_1070_ = v___x_1094_;
v_x_1071_ = v_tail_1074_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(lean_object* v_i_1098_, lean_object* v_source_1099_, lean_object* v_target_1100_){
_start:
{
lean_object* v___x_1101_; uint8_t v___x_1102_; 
v___x_1101_ = lean_array_get_size(v_source_1099_);
v___x_1102_ = lean_nat_dec_lt(v_i_1098_, v___x_1101_);
if (v___x_1102_ == 0)
{
lean_dec_ref(v_source_1099_);
lean_dec(v_i_1098_);
return v_target_1100_;
}
else
{
lean_object* v_es_1103_; lean_object* v___x_1104_; lean_object* v_source_1105_; lean_object* v_target_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; 
v_es_1103_ = lean_array_fget(v_source_1099_, v_i_1098_);
v___x_1104_ = lean_box(0);
v_source_1105_ = lean_array_fset(v_source_1099_, v_i_1098_, v___x_1104_);
v_target_1106_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_target_1100_, v_es_1103_);
v___x_1107_ = lean_unsigned_to_nat(1u);
v___x_1108_ = lean_nat_add(v_i_1098_, v___x_1107_);
lean_dec(v_i_1098_);
v_i_1098_ = v___x_1108_;
v_source_1099_ = v_source_1105_;
v_target_1100_ = v_target_1106_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(lean_object* v_data_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_nbuckets_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1111_ = lean_array_get_size(v_data_1110_);
v___x_1112_ = lean_unsigned_to_nat(2u);
v_nbuckets_1113_ = lean_nat_mul(v___x_1111_, v___x_1112_);
v___x_1114_ = lean_unsigned_to_nat(0u);
v___x_1115_ = lean_box(0);
v___x_1116_ = lean_mk_array(v_nbuckets_1113_, v___x_1115_);
v___x_1117_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v___x_1114_, v_data_1110_, v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(lean_object* v_a_1118_, lean_object* v_b_1119_, lean_object* v_x_1120_){
_start:
{
if (lean_obj_tag(v_x_1120_) == 0)
{
lean_dec(v_b_1119_);
lean_dec_ref(v_a_1118_);
return v_x_1120_;
}
else
{
lean_object* v_key_1121_; lean_object* v_value_1122_; lean_object* v_tail_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1135_; 
v_key_1121_ = lean_ctor_get(v_x_1120_, 0);
v_value_1122_ = lean_ctor_get(v_x_1120_, 1);
v_tail_1123_ = lean_ctor_get(v_x_1120_, 2);
v_isSharedCheck_1135_ = !lean_is_exclusive(v_x_1120_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1125_ = v_x_1120_;
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_tail_1123_);
lean_inc(v_value_1122_);
lean_inc(v_key_1121_);
lean_dec(v_x_1120_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1135_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
uint8_t v___x_1127_; 
v___x_1127_ = lean_expr_eqv(v_key_1121_, v_a_1118_);
if (v___x_1127_ == 0)
{
lean_object* v___x_1128_; lean_object* v___x_1130_; 
v___x_1128_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1118_, v_b_1119_, v_tail_1123_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 2, v___x_1128_);
v___x_1130_ = v___x_1125_;
goto v_reusejp_1129_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_key_1121_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_value_1122_);
lean_ctor_set(v_reuseFailAlloc_1131_, 2, v___x_1128_);
v___x_1130_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1129_;
}
v_reusejp_1129_:
{
return v___x_1130_;
}
}
else
{
lean_object* v___x_1133_; 
lean_dec(v_value_1122_);
lean_dec(v_key_1121_);
if (v_isShared_1126_ == 0)
{
lean_ctor_set(v___x_1125_, 1, v_b_1119_);
lean_ctor_set(v___x_1125_, 0, v_a_1118_);
v___x_1133_ = v___x_1125_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1118_);
lean_ctor_set(v_reuseFailAlloc_1134_, 1, v_b_1119_);
lean_ctor_set(v_reuseFailAlloc_1134_, 2, v_tail_1123_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(lean_object* v_a_1136_, lean_object* v_x_1137_){
_start:
{
if (lean_obj_tag(v_x_1137_) == 0)
{
uint8_t v___x_1138_; 
v___x_1138_ = 0;
return v___x_1138_;
}
else
{
lean_object* v_key_1139_; lean_object* v_tail_1140_; uint8_t v___x_1141_; 
v_key_1139_ = lean_ctor_get(v_x_1137_, 0);
v_tail_1140_ = lean_ctor_get(v_x_1137_, 2);
v___x_1141_ = lean_expr_eqv(v_key_1139_, v_a_1136_);
if (v___x_1141_ == 0)
{
v_x_1137_ = v_tail_1140_;
goto _start;
}
else
{
return v___x_1141_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg___boxed(lean_object* v_a_1143_, lean_object* v_x_1144_){
_start:
{
uint8_t v_res_1145_; lean_object* v_r_1146_; 
v_res_1145_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1143_, v_x_1144_);
lean_dec(v_x_1144_);
lean_dec_ref(v_a_1143_);
v_r_1146_ = lean_box(v_res_1145_);
return v_r_1146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(lean_object* v_m_1147_, lean_object* v_a_1148_, lean_object* v_b_1149_){
_start:
{
lean_object* v_size_1150_; lean_object* v_buckets_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1194_; 
v_size_1150_ = lean_ctor_get(v_m_1147_, 0);
v_buckets_1151_ = lean_ctor_get(v_m_1147_, 1);
v_isSharedCheck_1194_ = !lean_is_exclusive(v_m_1147_);
if (v_isSharedCheck_1194_ == 0)
{
v___x_1153_ = v_m_1147_;
v_isShared_1154_ = v_isSharedCheck_1194_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_buckets_1151_);
lean_inc(v_size_1150_);
lean_dec(v_m_1147_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1194_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1155_; uint64_t v___x_1156_; uint64_t v___x_1157_; uint64_t v___x_1158_; uint64_t v_fold_1159_; uint64_t v___x_1160_; uint64_t v___x_1161_; uint64_t v___x_1162_; size_t v___x_1163_; size_t v___x_1164_; size_t v___x_1165_; size_t v___x_1166_; size_t v___x_1167_; lean_object* v_bkt_1168_; uint8_t v___x_1169_; 
v___x_1155_ = lean_array_get_size(v_buckets_1151_);
v___x_1156_ = l_Lean_Expr_hash(v_a_1148_);
v___x_1157_ = 32ULL;
v___x_1158_ = lean_uint64_shift_right(v___x_1156_, v___x_1157_);
v_fold_1159_ = lean_uint64_xor(v___x_1156_, v___x_1158_);
v___x_1160_ = 16ULL;
v___x_1161_ = lean_uint64_shift_right(v_fold_1159_, v___x_1160_);
v___x_1162_ = lean_uint64_xor(v_fold_1159_, v___x_1161_);
v___x_1163_ = lean_uint64_to_usize(v___x_1162_);
v___x_1164_ = lean_usize_of_nat(v___x_1155_);
v___x_1165_ = ((size_t)1ULL);
v___x_1166_ = lean_usize_sub(v___x_1164_, v___x_1165_);
v___x_1167_ = lean_usize_land(v___x_1163_, v___x_1166_);
v_bkt_1168_ = lean_array_uget_borrowed(v_buckets_1151_, v___x_1167_);
v___x_1169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1148_, v_bkt_1168_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; lean_object* v_size_x27_1171_; lean_object* v___x_1172_; lean_object* v_buckets_x27_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v___x_1170_ = lean_unsigned_to_nat(1u);
v_size_x27_1171_ = lean_nat_add(v_size_1150_, v___x_1170_);
lean_dec(v_size_1150_);
lean_inc(v_bkt_1168_);
v___x_1172_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1172_, 0, v_a_1148_);
lean_ctor_set(v___x_1172_, 1, v_b_1149_);
lean_ctor_set(v___x_1172_, 2, v_bkt_1168_);
v_buckets_x27_1173_ = lean_array_uset(v_buckets_1151_, v___x_1167_, v___x_1172_);
v___x_1174_ = lean_unsigned_to_nat(4u);
v___x_1175_ = lean_nat_mul(v_size_x27_1171_, v___x_1174_);
v___x_1176_ = lean_unsigned_to_nat(3u);
v___x_1177_ = lean_nat_div(v___x_1175_, v___x_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_array_get_size(v_buckets_x27_1173_);
v___x_1179_ = lean_nat_dec_le(v___x_1177_, v___x_1178_);
lean_dec(v___x_1177_);
if (v___x_1179_ == 0)
{
lean_object* v_val_1180_; lean_object* v___x_1182_; 
v_val_1180_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_buckets_x27_1173_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_val_1180_);
lean_ctor_set(v___x_1153_, 0, v_size_x27_1171_);
v___x_1182_ = v___x_1153_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_size_x27_1171_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_val_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
else
{
lean_object* v___x_1185_; 
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v_buckets_x27_1173_);
lean_ctor_set(v___x_1153_, 0, v_size_x27_1171_);
v___x_1185_ = v___x_1153_;
goto v_reusejp_1184_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_size_x27_1171_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v_buckets_x27_1173_);
v___x_1185_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1184_;
}
v_reusejp_1184_:
{
return v___x_1185_;
}
}
}
else
{
lean_object* v___x_1187_; lean_object* v_buckets_x27_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1192_; 
lean_inc(v_bkt_1168_);
v___x_1187_ = lean_box(0);
v_buckets_x27_1188_ = lean_array_uset(v_buckets_1151_, v___x_1167_, v___x_1187_);
v___x_1189_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1148_, v_b_1149_, v_bkt_1168_);
v___x_1190_ = lean_array_uset(v_buckets_x27_1188_, v___x_1167_, v___x_1189_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 1, v___x_1190_);
v___x_1192_ = v___x_1153_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v_size_1150_);
lean_ctor_set(v_reuseFailAlloc_1193_, 1, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(lean_object* v_a_1195_, lean_object* v_e_1196_, lean_object* v_a_1197_){
_start:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1199_ = lean_st_ref_take(v_a_1195_);
v___x_1200_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v___x_1199_, v_e_1196_, v_a_1197_);
v___x_1201_ = lean_st_ref_set(v_a_1195_, v___x_1200_);
v___x_1202_ = lean_box(0);
return v___x_1202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed(lean_object* v_a_1203_, lean_object* v_e_1204_, lean_object* v_a_1205_, lean_object* v___y_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1(v_a_1203_, v_e_1204_, v_a_1205_);
lean_dec(v_a_1203_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1208_, lean_object* v_e_1209_, lean_object* v_a_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_){
_start:
{
lean_object* v_res_1217_; 
v_res_1217_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1208_, v_e_1209_, v_a_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_, v___y_1215_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec(v_a_1210_);
return v_res_1217_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(lean_object* v_fn_1218_, lean_object* v_e_1219_, lean_object* v_a_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_){
_start:
{
lean_object* v_a_1228_; lean_object* v___y_1240_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
lean_inc(v_a_1220_);
v___x_1242_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1242_, 0, lean_box(0));
lean_closure_set(v___x_1242_, 1, lean_box(0));
lean_closure_set(v___x_1242_, 2, v_a_1220_);
v___x_1243_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___x_1242_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; lean_object* v___x_1246_; uint8_t v_isShared_1247_; uint8_t v_isSharedCheck_1280_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1280_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1246_ = v___x_1243_;
v_isShared_1247_ = v_isSharedCheck_1280_;
goto v_resetjp_1245_;
}
else
{
lean_inc(v_a_1244_);
lean_dec(v___x_1243_);
v___x_1246_ = lean_box(0);
v_isShared_1247_ = v_isSharedCheck_1280_;
goto v_resetjp_1245_;
}
v_resetjp_1245_:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_a_1244_, v_e_1219_);
lean_dec(v_a_1244_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v___x_1249_; 
lean_del_object(v___x_1246_);
lean_inc_ref(v_fn_1218_);
lean_inc(v___y_1225_);
lean_inc_ref(v___y_1224_);
lean_inc(v___y_1223_);
lean_inc_ref(v___y_1222_);
lean_inc(v___y_1221_);
lean_inc_ref(v_e_1219_);
v___x_1249_ = lean_apply_7(v_fn_1218_, v_e_1219_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_, lean_box(0));
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_object* v_a_1250_; uint8_t v___x_1251_; 
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref_known(v___x_1249_, 1);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
lean_object* v___x_1252_; 
lean_dec_ref(v_fn_1218_);
v___x_1252_ = lean_box(0);
v_a_1228_ = v___x_1252_;
goto v___jp_1227_;
}
else
{
switch(lean_obj_tag(v_e_1219_))
{
case 7:
{
lean_object* v___x_1253_; lean_object* v___x_1254_; 
v___x_1253_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1253_, 0, v_fn_1218_);
lean_inc_ref(v_e_1219_);
v___x_1254_ = l_Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10(v___x_1253_, v_e_1219_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1254_;
goto v___jp_1239_;
}
case 6:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1255_, 0, v_fn_1218_);
lean_inc_ref(v_e_1219_);
v___x_1256_ = l_Lean_Meta_visitLambda___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__11(v___x_1255_, v_e_1219_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1256_;
goto v___jp_1239_;
}
case 8:
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1257_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___boxed), 9, 1);
lean_closure_set(v___x_1257_, 0, v_fn_1218_);
lean_inc_ref(v_e_1219_);
v___x_1258_ = l_Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12(v___x_1257_, v_e_1219_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1258_;
goto v___jp_1239_;
}
case 5:
{
lean_object* v_fn_1259_; lean_object* v_arg_1260_; lean_object* v___x_1261_; 
v_fn_1259_ = lean_ctor_get(v_e_1219_, 0);
v_arg_1260_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_fn_1259_);
lean_inc_ref(v_fn_1218_);
v___x_1261_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1218_, v_fn_1259_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref_known(v___x_1261_, 1);
lean_inc_ref(v_arg_1260_);
v___x_1262_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1218_, v_arg_1260_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1262_;
goto v___jp_1239_;
}
else
{
lean_dec_ref(v_fn_1218_);
v___y_1240_ = v___x_1261_;
goto v___jp_1239_;
}
}
case 10:
{
lean_object* v_expr_1263_; lean_object* v___x_1264_; 
v_expr_1263_ = lean_ctor_get(v_e_1219_, 1);
lean_inc_ref(v_expr_1263_);
v___x_1264_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1218_, v_expr_1263_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1264_;
goto v___jp_1239_;
}
case 11:
{
lean_object* v_struct_1265_; lean_object* v___x_1266_; 
v_struct_1265_ = lean_ctor_get(v_e_1219_, 2);
lean_inc_ref(v_struct_1265_);
v___x_1266_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1218_, v_struct_1265_, v_a_1220_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
v___y_1240_ = v___x_1266_;
goto v___jp_1239_;
}
default: 
{
lean_object* v___x_1267_; 
lean_dec_ref(v_fn_1218_);
v___x_1267_ = lean_box(0);
v_a_1228_ = v___x_1267_;
goto v___jp_1227_;
}
}
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec_ref(v_e_1219_);
lean_dec_ref(v_fn_1218_);
v_a_1268_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1249_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1249_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
else
{
lean_object* v_val_1276_; lean_object* v___x_1278_; 
lean_dec_ref(v_e_1219_);
lean_dec_ref(v_fn_1218_);
v_val_1276_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_val_1276_);
lean_dec_ref_known(v___x_1248_, 1);
if (v_isShared_1247_ == 0)
{
lean_ctor_set(v___x_1246_, 0, v_val_1276_);
v___x_1278_ = v___x_1246_;
goto v_reusejp_1277_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_val_1276_);
v___x_1278_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1277_;
}
v_reusejp_1277_:
{
return v___x_1278_;
}
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
lean_dec_ref(v_e_1219_);
lean_dec_ref(v_fn_1218_);
v_a_1281_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1243_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1243_);
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
v___jp_1227_:
{
lean_object* v___f_1229_; lean_object* v___x_1230_; 
lean_inc(v_a_1220_);
v___f_1229_ = lean_alloc_closure((void*)(l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__1___boxed), 4, 3);
lean_closure_set(v___f_1229_, 0, v_a_1220_);
lean_closure_set(v___f_1229_, 1, v_e_1219_);
lean_closure_set(v___f_1229_, 2, v_a_1228_);
v___x_1230_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5___lam__0(lean_box(0), v___f_1229_, v___y_1221_, v___y_1222_, v___y_1223_, v___y_1224_, v___y_1225_);
if (lean_obj_tag(v___x_1230_) == 0)
{
lean_object* v___x_1232_; uint8_t v_isShared_1233_; uint8_t v_isSharedCheck_1237_; 
v_isSharedCheck_1237_ = !lean_is_exclusive(v___x_1230_);
if (v_isSharedCheck_1237_ == 0)
{
lean_object* v_unused_1238_; 
v_unused_1238_ = lean_ctor_get(v___x_1230_, 0);
lean_dec(v_unused_1238_);
v___x_1232_ = v___x_1230_;
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
else
{
lean_dec(v___x_1230_);
v___x_1232_ = lean_box(0);
v_isShared_1233_ = v_isSharedCheck_1237_;
goto v_resetjp_1231_;
}
v_resetjp_1231_:
{
lean_object* v___x_1235_; 
if (v_isShared_1233_ == 0)
{
lean_ctor_set(v___x_1232_, 0, v_a_1228_);
v___x_1235_ = v___x_1232_;
goto v_reusejp_1234_;
}
else
{
lean_object* v_reuseFailAlloc_1236_; 
v_reuseFailAlloc_1236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1236_, 0, v_a_1228_);
v___x_1235_ = v_reuseFailAlloc_1236_;
goto v_reusejp_1234_;
}
v_reusejp_1234_:
{
return v___x_1235_;
}
}
}
else
{
return v___x_1230_;
}
}
v___jp_1239_:
{
if (lean_obj_tag(v___y_1240_) == 0)
{
lean_object* v_a_1241_; 
v_a_1241_ = lean_ctor_get(v___y_1240_, 0);
lean_inc(v_a_1241_);
lean_dec_ref_known(v___y_1240_, 1);
v_a_1228_ = v_a_1241_;
goto v___jp_1227_;
}
else
{
lean_dec_ref(v_e_1219_);
return v___y_1240_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1289_ = lean_box(0);
v___x_1290_ = lean_unsigned_to_nat(16u);
v___x_1291_ = lean_mk_array(v___x_1290_, v___x_1289_);
return v___x_1291_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1(void){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
v___x_1292_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__0);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
lean_ctor_set(v___x_1294_, 1, v___x_1292_);
return v___x_1294_;
}
}
static lean_object* _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2(void){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__1);
v___x_1296_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_1296_, 0, lean_box(0));
lean_closure_set(v___x_1296_, 1, lean_box(0));
lean_closure_set(v___x_1296_, 2, v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(lean_object* v_input_1297_, lean_object* v_fn_1298_, lean_object* v___y_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v_a_1307_; lean_object* v___x_1308_; 
v___x_1305_ = lean_obj_once(&l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2, &l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2_once, _init_l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___closed__2);
v___x_1306_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1305_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
lean_inc(v_a_1307_);
lean_dec_ref(v___x_1306_);
v___x_1308_ = l___private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5(v_fn_1298_, v_input_1297_, v_a_1307_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v___x_1310_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_1310_, 0, lean_box(0));
lean_closure_set(v___x_1310_, 1, lean_box(0));
lean_closure_set(v___x_1310_, 2, v_a_1307_);
v___x_1311_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___lam__0(lean_box(0), v___x_1310_, v___y_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1311_);
if (v_isSharedCheck_1318_ == 0)
{
lean_object* v_unused_1319_; 
v_unused_1319_ = lean_ctor_get(v___x_1311_, 0);
lean_dec(v_unused_1319_);
v___x_1313_ = v___x_1311_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_dec(v___x_1311_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
lean_ctor_set(v___x_1313_, 0, v_a_1309_);
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1309_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
else
{
lean_dec(v_a_1307_);
return v___x_1308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2___boxed(lean_object* v_input_1320_, lean_object* v_fn_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_){
_start:
{
lean_object* v_res_1328_; 
v_res_1328_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1320_, v_fn_1321_, v___y_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
lean_dec(v___y_1324_);
lean_dec_ref(v___y_1323_);
lean_dec(v___y_1322_);
return v_res_1328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(lean_object* v_input_1329_, lean_object* v_fn_1330_, lean_object* v___y_1331_, lean_object* v___y_1332_, lean_object* v___y_1333_, lean_object* v___y_1334_, lean_object* v___y_1335_){
_start:
{
lean_object* v___f_1337_; lean_object* v___x_1338_; 
v___f_1337_ = lean_alloc_closure((void*)(l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1337_, 0, v_fn_1330_);
v___x_1338_ = l_Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2(v_input_1329_, v___f_1337_, v___y_1331_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
return v___x_1338_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1___boxed(lean_object* v_input_1339_, lean_object* v_fn_1340_, lean_object* v___y_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_){
_start:
{
lean_object* v_res_1347_; 
v_res_1347_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_input_1339_, v_fn_1340_, v___y_1341_, v___y_1342_, v___y_1343_, v___y_1344_, v___y_1345_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
return v_res_1347_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(lean_object* v_fn_1348_, lean_object* v_x_1349_, lean_object* v_x_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_){
_start:
{
if (lean_obj_tag(v_x_1350_) == 0)
{
lean_object* v___x_1357_; 
lean_dec_ref(v_fn_1348_);
v___x_1357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1357_, 0, v_x_1349_);
return v___x_1357_;
}
else
{
lean_object* v_head_1358_; lean_object* v_tail_1359_; lean_object* v_type_1360_; lean_object* v___x_1361_; 
v_head_1358_ = lean_ctor_get(v_x_1350_, 0);
lean_inc(v_head_1358_);
v_tail_1359_ = lean_ctor_get(v_x_1350_, 1);
lean_inc(v_tail_1359_);
lean_dec_ref_known(v_x_1350_, 2);
v_type_1360_ = lean_ctor_get(v_head_1358_, 1);
lean_inc_ref(v_type_1360_);
lean_dec(v_head_1358_);
lean_inc_ref(v_fn_1348_);
v___x_1361_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1360_, v_fn_1348_, v___y_1351_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_object* v_a_1362_; 
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
lean_inc(v_a_1362_);
lean_dec_ref_known(v___x_1361_, 1);
v_x_1349_ = v_a_1362_;
v_x_1350_ = v_tail_1359_;
goto _start;
}
else
{
lean_dec(v_tail_1359_);
lean_dec_ref(v_fn_1348_);
return v___x_1361_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4___boxed(lean_object* v_fn_1364_, lean_object* v_x_1365_, lean_object* v_x_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v_res_1373_; 
v_res_1373_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1364_, v_x_1365_, v_x_1366_, v___y_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
lean_dec(v___y_1369_);
lean_dec_ref(v___y_1368_);
lean_dec(v___y_1367_);
return v_res_1373_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(lean_object* v_fn_1374_, lean_object* v_x_1375_, lean_object* v_x_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_){
_start:
{
if (lean_obj_tag(v_x_1376_) == 0)
{
lean_object* v___x_1383_; 
lean_dec_ref(v_fn_1374_);
v___x_1383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1383_, 0, v_x_1375_);
return v___x_1383_;
}
else
{
lean_object* v_head_1384_; lean_object* v_tail_1385_; lean_object* v___y_1387_; lean_object* v_type_1390_; lean_object* v_ctors_1391_; lean_object* v___x_1392_; 
v_head_1384_ = lean_ctor_get(v_x_1376_, 0);
lean_inc(v_head_1384_);
v_tail_1385_ = lean_ctor_get(v_x_1376_, 1);
lean_inc(v_tail_1385_);
lean_dec_ref_known(v_x_1376_, 2);
v_type_1390_ = lean_ctor_get(v_head_1384_, 1);
lean_inc_ref(v_type_1390_);
v_ctors_1391_ = lean_ctor_get(v_head_1384_, 2);
lean_inc(v_ctors_1391_);
lean_dec(v_head_1384_);
lean_inc_ref(v_fn_1374_);
v___x_1392_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1390_, v_fn_1374_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
if (lean_obj_tag(v___x_1392_) == 0)
{
lean_object* v_a_1393_; lean_object* v___x_1394_; 
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref_known(v___x_1392_, 1);
lean_inc_ref(v_fn_1374_);
v___x_1394_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__4(v_fn_1374_, v_a_1393_, v_ctors_1391_, v___y_1377_, v___y_1378_, v___y_1379_, v___y_1380_, v___y_1381_);
v___y_1387_ = v___x_1394_;
goto v___jp_1386_;
}
else
{
lean_dec(v_ctors_1391_);
v___y_1387_ = v___x_1392_;
goto v___jp_1386_;
}
v___jp_1386_:
{
if (lean_obj_tag(v___y_1387_) == 0)
{
lean_object* v_a_1388_; 
v_a_1388_ = lean_ctor_get(v___y_1387_, 0);
lean_inc(v_a_1388_);
lean_dec_ref_known(v___y_1387_, 1);
v_x_1375_ = v_a_1388_;
v_x_1376_ = v_tail_1385_;
goto _start;
}
else
{
lean_dec(v_tail_1385_);
lean_dec_ref(v_fn_1374_);
return v___y_1387_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6___boxed(lean_object* v_fn_1395_, lean_object* v_x_1396_, lean_object* v_x_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_, lean_object* v___y_1403_){
_start:
{
lean_object* v_res_1404_; 
v_res_1404_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1395_, v_x_1396_, v_x_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_, v___y_1402_);
lean_dec(v___y_1402_);
lean_dec_ref(v___y_1401_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(lean_object* v_fn_1405_, lean_object* v_x_1406_, lean_object* v_x_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_, lean_object* v___y_1411_, lean_object* v___y_1412_){
_start:
{
if (lean_obj_tag(v_x_1407_) == 0)
{
lean_object* v___x_1414_; 
lean_dec_ref(v_fn_1405_);
v___x_1414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1414_, 0, v_x_1406_);
return v___x_1414_;
}
else
{
lean_object* v_head_1415_; lean_object* v_tail_1416_; lean_object* v___y_1418_; lean_object* v_toConstantVal_1421_; lean_object* v_value_1422_; lean_object* v_type_1423_; lean_object* v___x_1424_; 
v_head_1415_ = lean_ctor_get(v_x_1407_, 0);
lean_inc(v_head_1415_);
v_tail_1416_ = lean_ctor_get(v_x_1407_, 1);
lean_inc(v_tail_1416_);
lean_dec_ref_known(v_x_1407_, 2);
v_toConstantVal_1421_ = lean_ctor_get(v_head_1415_, 0);
lean_inc_ref(v_toConstantVal_1421_);
v_value_1422_ = lean_ctor_get(v_head_1415_, 1);
lean_inc_ref(v_value_1422_);
lean_dec(v_head_1415_);
v_type_1423_ = lean_ctor_get(v_toConstantVal_1421_, 2);
lean_inc_ref(v_type_1423_);
lean_dec_ref(v_toConstantVal_1421_);
lean_inc_ref(v_fn_1405_);
v___x_1424_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1423_, v_fn_1405_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
if (lean_obj_tag(v___x_1424_) == 0)
{
lean_object* v___x_1425_; 
lean_dec_ref_known(v___x_1424_, 1);
lean_inc_ref(v_fn_1405_);
v___x_1425_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1422_, v_fn_1405_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_);
v___y_1418_ = v___x_1425_;
goto v___jp_1417_;
}
else
{
lean_dec_ref(v_value_1422_);
v___y_1418_ = v___x_1424_;
goto v___jp_1417_;
}
v___jp_1417_:
{
if (lean_obj_tag(v___y_1418_) == 0)
{
lean_object* v_a_1419_; 
v_a_1419_ = lean_ctor_get(v___y_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref_known(v___y_1418_, 1);
v_x_1406_ = v_a_1419_;
v_x_1407_ = v_tail_1416_;
goto _start;
}
else
{
lean_dec(v_tail_1416_);
lean_dec_ref(v_fn_1405_);
return v___y_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5___boxed(lean_object* v_fn_1426_, lean_object* v_x_1427_, lean_object* v_x_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_, lean_object* v___y_1431_, lean_object* v___y_1432_, lean_object* v___y_1433_, lean_object* v___y_1434_){
_start:
{
lean_object* v_res_1435_; 
v_res_1435_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1426_, v_x_1427_, v_x_1428_, v___y_1429_, v___y_1430_, v___y_1431_, v___y_1432_, v___y_1433_);
lean_dec(v___y_1433_);
lean_dec_ref(v___y_1432_);
lean_dec(v___y_1431_);
lean_dec_ref(v___y_1430_);
lean_dec(v___y_1429_);
return v_res_1435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(lean_object* v_fn_1436_, lean_object* v_d_1437_, lean_object* v_a_1438_, lean_object* v___y_1439_, lean_object* v___y_1440_, lean_object* v___y_1441_, lean_object* v___y_1442_, lean_object* v___y_1443_){
_start:
{
switch(lean_obj_tag(v_d_1437_))
{
case 0:
{
lean_object* v_val_1445_; lean_object* v_toConstantVal_1446_; lean_object* v_type_1447_; lean_object* v___x_1448_; 
v_val_1445_ = lean_ctor_get(v_d_1437_, 0);
lean_inc_ref(v_val_1445_);
lean_dec_ref_known(v_d_1437_, 1);
v_toConstantVal_1446_ = lean_ctor_get(v_val_1445_, 0);
lean_inc_ref(v_toConstantVal_1446_);
lean_dec_ref(v_val_1445_);
v_type_1447_ = lean_ctor_get(v_toConstantVal_1446_, 2);
lean_inc_ref(v_type_1447_);
lean_dec_ref(v_toConstantVal_1446_);
v___x_1448_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1447_, v_fn_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1448_;
}
case 4:
{
lean_object* v___x_1449_; 
lean_dec_ref(v_fn_1436_);
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v_a_1438_);
return v___x_1449_;
}
case 5:
{
lean_object* v_defns_1450_; lean_object* v___x_1451_; 
v_defns_1450_ = lean_ctor_get(v_d_1437_, 0);
lean_inc(v_defns_1450_);
lean_dec_ref_known(v_d_1437_, 1);
v___x_1451_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__5(v_fn_1436_, v_a_1438_, v_defns_1450_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1451_;
}
case 6:
{
lean_object* v_types_1452_; lean_object* v___x_1453_; 
v_types_1452_ = lean_ctor_get(v_d_1437_, 2);
lean_inc(v_types_1452_);
lean_dec_ref_known(v_d_1437_, 3);
v___x_1453_ = l_List_foldlM___at___00Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2_spec__6(v_fn_1436_, v_a_1438_, v_types_1452_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1453_;
}
default: 
{
lean_object* v_val_1454_; lean_object* v_toConstantVal_1455_; lean_object* v_value_1456_; lean_object* v_type_1457_; lean_object* v___x_1458_; 
v_val_1454_ = lean_ctor_get(v_d_1437_, 0);
lean_inc_ref(v_val_1454_);
lean_dec(v_d_1437_);
v_toConstantVal_1455_ = lean_ctor_get(v_val_1454_, 0);
lean_inc_ref(v_toConstantVal_1455_);
v_value_1456_ = lean_ctor_get(v_val_1454_, 1);
lean_inc_ref(v_value_1456_);
lean_dec_ref(v_val_1454_);
v_type_1457_ = lean_ctor_get(v_toConstantVal_1455_, 2);
lean_inc_ref(v_type_1457_);
lean_dec_ref(v_toConstantVal_1455_);
lean_inc_ref(v_fn_1436_);
v___x_1458_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_type_1457_, v_fn_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
if (lean_obj_tag(v___x_1458_) == 0)
{
lean_object* v___x_1459_; 
lean_dec_ref_known(v___x_1458_, 1);
v___x_1459_ = l_Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1(v_value_1456_, v_fn_1436_, v___y_1439_, v___y_1440_, v___y_1441_, v___y_1442_, v___y_1443_);
return v___x_1459_;
}
else
{
lean_dec_ref(v_value_1456_);
lean_dec_ref(v_fn_1436_);
return v___x_1458_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2___boxed(lean_object* v_fn_1460_, lean_object* v_d_1461_, lean_object* v_a_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1460_, v_d_1461_, v_a_1462_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
lean_dec(v___y_1467_);
lean_dec_ref(v___y_1466_);
lean_dec(v___y_1465_);
lean_dec_ref(v___y_1464_);
lean_dec(v___y_1463_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(lean_object* v_decl_1470_, lean_object* v_fn_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; 
v___x_1478_ = lean_box(0);
v___x_1479_ = l_Lean_Declaration_foldExprM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__2(v_fn_1471_, v_decl_1470_, v___x_1478_, v___y_1472_, v___y_1473_, v___y_1474_, v___y_1475_, v___y_1476_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1___boxed(lean_object* v_decl_1480_, lean_object* v_fn_1481_, lean_object* v___y_1482_, lean_object* v___y_1483_, lean_object* v___y_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_){
_start:
{
lean_object* v_res_1488_; 
v_res_1488_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1480_, v_fn_1481_, v___y_1482_, v___y_1483_, v___y_1484_, v___y_1485_, v___y_1486_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
lean_dec(v___y_1484_);
lean_dec_ref(v___y_1483_);
lean_dec(v___y_1482_);
return v_res_1488_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__0(void){
_start:
{
lean_object* v___x_1489_; 
v___x_1489_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_1489_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__1(void){
_start:
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
v___x_1490_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__0, &l_Lean_warnIfUsesSorry___closed__0_once, _init_l_Lean_warnIfUsesSorry___closed__0);
v___x_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
return v___x_1491_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__2(void){
_start:
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___x_1492_ = lean_box(1);
v___x_1493_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1494_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1493_);
lean_ctor_set(v___x_1495_, 2, v___x_1492_);
return v___x_1495_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__4(void){
_start:
{
lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; 
v___x_1498_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1499_ = lean_unsigned_to_nat(0u);
v___x_1500_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_1500_, 0, v___x_1499_);
lean_ctor_set(v___x_1500_, 1, v___x_1499_);
lean_ctor_set(v___x_1500_, 2, v___x_1499_);
lean_ctor_set(v___x_1500_, 3, v___x_1499_);
lean_ctor_set(v___x_1500_, 4, v___x_1498_);
lean_ctor_set(v___x_1500_, 5, v___x_1498_);
lean_ctor_set(v___x_1500_, 6, v___x_1498_);
lean_ctor_set(v___x_1500_, 7, v___x_1498_);
lean_ctor_set(v___x_1500_, 8, v___x_1498_);
lean_ctor_set(v___x_1500_, 9, v___x_1498_);
return v___x_1500_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__5(void){
_start:
{
lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1501_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1502_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1501_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
lean_ctor_set(v___x_1502_, 2, v___x_1501_);
lean_ctor_set(v___x_1502_, 3, v___x_1501_);
lean_ctor_set(v___x_1502_, 4, v___x_1501_);
lean_ctor_set(v___x_1502_, 5, v___x_1501_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__6(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1503_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__1, &l_Lean_warnIfUsesSorry___closed__1_once, _init_l_Lean_warnIfUsesSorry___closed__1);
v___x_1504_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1504_, 0, v___x_1503_);
lean_ctor_set(v___x_1504_, 1, v___x_1503_);
lean_ctor_set(v___x_1504_, 2, v___x_1503_);
lean_ctor_set(v___x_1504_, 3, v___x_1503_);
lean_ctor_set(v___x_1504_, 4, v___x_1503_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__7(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; 
v___x_1505_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__6, &l_Lean_warnIfUsesSorry___closed__6_once, _init_l_Lean_warnIfUsesSorry___closed__6);
v___x_1506_ = lean_obj_once(&l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4, &l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4_once, _init_l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12___closed__4);
v___x_1507_ = lean_box(1);
v___x_1508_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__5, &l_Lean_warnIfUsesSorry___closed__5_once, _init_l_Lean_warnIfUsesSorry___closed__5);
v___x_1509_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__4, &l_Lean_warnIfUsesSorry___closed__4_once, _init_l_Lean_warnIfUsesSorry___closed__4);
v___x_1510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1510_, 0, v___x_1509_);
lean_ctor_set(v___x_1510_, 1, v___x_1508_);
lean_ctor_set(v___x_1510_, 2, v___x_1507_);
lean_ctor_set(v___x_1510_, 3, v___x_1506_);
lean_ctor_set(v___x_1510_, 4, v___x_1505_);
return v___x_1510_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__12(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1516_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__11));
v___x_1517_ = l_Lean_stringToMessageData(v___x_1516_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__14(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; 
v___x_1519_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__13));
v___x_1520_ = l_Lean_stringToMessageData(v___x_1519_);
return v___x_1520_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__16(void){
_start:
{
lean_object* v___x_1522_; lean_object* v___x_1523_; 
v___x_1522_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__15));
v___x_1523_ = l_Lean_stringToMessageData(v___x_1522_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_warnIfUsesSorry___closed__17(void){
_start:
{
lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1524_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__16, &l_Lean_warnIfUsesSorry___closed__16_once, _init_l_Lean_warnIfUsesSorry___closed__16);
v___x_1525_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1526_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1526_, 0, v___x_1525_);
lean_ctor_set(v___x_1526_, 1, v___x_1524_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry(lean_object* v_decl_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_){
_start:
{
lean_object* v_options_1534_; lean_object* v___x_1535_; uint8_t v___x_1536_; 
v_options_1534_ = lean_ctor_get(v_a_1531_, 2);
v___x_1535_ = l_Lean_warn_sorry;
v___x_1536_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_1534_, v___x_1535_);
if (v___x_1536_ == 0)
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec(v_decl_1530_);
v___x_1537_ = lean_box(0);
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
else
{
lean_object* v___x_1539_; lean_object* v_messages_1543_; uint8_t v___x_1544_; 
v___x_1539_ = lean_st_ref_get(v_a_1532_);
v_messages_1543_ = lean_ctor_get(v___x_1539_, 6);
lean_inc_ref(v_messages_1543_);
lean_dec(v___x_1539_);
v___x_1544_ = l_Lean_MessageLog_hasErrors(v_messages_1543_);
lean_dec_ref(v_messages_1543_);
if (v___x_1544_ == 0)
{
if (v___x_1536_ == 0)
{
lean_dec(v_decl_1530_);
goto v___jp_1540_;
}
else
{
uint8_t v___x_1545_; 
v___x_1545_ = l_Lean_Declaration_hasSorry(v_decl_1530_);
if (v___x_1545_ == 0)
{
lean_dec(v_decl_1530_);
goto v___jp_1540_;
}
else
{
uint8_t v___x_1546_; uint8_t v___x_1547_; uint8_t v___x_1548_; lean_object* v___x_1549_; uint64_t v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___f_1561_; lean_object* v___x_1562_; 
v___x_1546_ = 1;
v___x_1547_ = 0;
v___x_1548_ = 2;
v___x_1549_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v___x_1549_, 0, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 1, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 2, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 3, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 4, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 5, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 6, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 7, v___x_1544_);
lean_ctor_set_uint8(v___x_1549_, 8, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 9, v___x_1546_);
lean_ctor_set_uint8(v___x_1549_, 10, v___x_1547_);
lean_ctor_set_uint8(v___x_1549_, 11, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 12, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 13, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 14, v___x_1548_);
lean_ctor_set_uint8(v___x_1549_, 15, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 16, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 17, v___x_1545_);
lean_ctor_set_uint8(v___x_1549_, 18, v___x_1545_);
v___x_1550_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_1549_);
v___x_1551_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_1551_, 0, v___x_1549_);
lean_ctor_set_uint64(v___x_1551_, sizeof(void*)*1, v___x_1550_);
v___x_1552_ = lean_box(1);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__2, &l_Lean_warnIfUsesSorry___closed__2_once, _init_l_Lean_warnIfUsesSorry___closed__2);
v___x_1555_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__3));
v___x_1556_ = lean_box(0);
v___x_1557_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1557_, 0, v___x_1551_);
lean_ctor_set(v___x_1557_, 1, v___x_1552_);
lean_ctor_set(v___x_1557_, 2, v___x_1554_);
lean_ctor_set(v___x_1557_, 3, v___x_1555_);
lean_ctor_set(v___x_1557_, 4, v___x_1556_);
lean_ctor_set(v___x_1557_, 5, v___x_1553_);
lean_ctor_set(v___x_1557_, 6, v___x_1556_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*7, v___x_1544_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*7 + 1, v___x_1544_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*7 + 2, v___x_1544_);
lean_ctor_set_uint8(v___x_1557_, sizeof(void*)*7 + 3, v___x_1536_);
v___x_1558_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__7, &l_Lean_warnIfUsesSorry___closed__7_once, _init_l_Lean_warnIfUsesSorry___closed__7);
v___x_1559_ = lean_st_mk_ref(v___x_1558_);
v___x_1560_ = lean_st_mk_ref(v___x_1555_);
v___f_1561_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__8));
v___x_1562_ = l_Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1(v_decl_1530_, v___f_1561_, v___x_1560_, v___x_1557_, v___x_1559_, v_a_1531_, v_a_1532_);
lean_dec_ref_known(v___x_1557_, 7);
if (lean_obj_tag(v___x_1562_) == 0)
{
lean_object* v___x_1563_; lean_object* v___x_1564_; lean_object* v_val_1566_; lean_object* v___x_1588_; size_t v_sz_1589_; size_t v___x_1590_; lean_object* v___x_1591_; lean_object* v_fst_1592_; 
lean_dec_ref_known(v___x_1562_, 1);
v___x_1563_ = lean_st_ref_get(v___x_1560_);
lean_dec(v___x_1560_);
v___x_1564_ = lean_st_ref_get(v___x_1559_);
lean_dec(v___x_1559_);
lean_dec(v___x_1564_);
v___x_1588_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__18));
v_sz_1589_ = lean_array_size(v___x_1563_);
v___x_1590_ = ((size_t)0ULL);
v___x_1591_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_warnIfUsesSorry_spec__3(v___x_1563_, v_sz_1589_, v___x_1590_, v___x_1588_);
v_fst_1592_ = lean_ctor_get(v___x_1591_, 0);
lean_inc(v_fst_1592_);
lean_dec_ref(v___x_1591_);
if (lean_obj_tag(v_fst_1592_) == 0)
{
goto v___jp_1582_;
}
else
{
lean_object* v_val_1593_; 
v_val_1593_ = lean_ctor_get(v_fst_1592_, 0);
lean_inc(v_val_1593_);
lean_dec_ref_known(v_fst_1592_, 1);
if (lean_obj_tag(v_val_1593_) == 0)
{
goto v___jp_1582_;
}
else
{
lean_object* v_val_1594_; 
lean_dec(v___x_1563_);
v_val_1594_ = lean_ctor_get(v_val_1593_, 0);
lean_inc(v_val_1594_);
lean_dec_ref_known(v_val_1593_, 1);
v_val_1566_ = v_val_1594_;
goto v___jp_1565_;
}
}
v___jp_1565_:
{
lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1580_; 
v_snd_1567_ = lean_ctor_get(v_val_1566_, 1);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_val_1566_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; 
v_unused_1581_ = lean_ctor_get(v_val_1566_, 0);
lean_dec(v_unused_1581_);
v___x_1569_ = v_val_1566_;
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_dec(v_val_1566_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1580_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; 
v___x_1571_ = ((lean_object*)(l_Lean_warnIfUsesSorry___closed__10));
v___x_1572_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__12, &l_Lean_warnIfUsesSorry___closed__12_once, _init_l_Lean_warnIfUsesSorry___closed__12);
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 7);
lean_ctor_set(v___x_1569_, 0, v___x_1572_);
v___x_1574_ = v___x_1569_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v_snd_1567_);
v___x_1574_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1575_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__14, &l_Lean_warnIfUsesSorry___closed__14_once, _init_l_Lean_warnIfUsesSorry___closed__14);
v___x_1576_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1574_);
lean_ctor_set(v___x_1576_, 1, v___x_1575_);
v___x_1577_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_1577_, 0, v___x_1571_);
lean_ctor_set(v___x_1577_, 1, v___x_1576_);
v___x_1578_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1577_, v_a_1531_, v_a_1532_);
return v___x_1578_;
}
}
}
v___jp_1582_:
{
lean_object* v___x_1583_; uint8_t v___x_1584_; 
v___x_1583_ = lean_array_get_size(v___x_1563_);
v___x_1584_ = lean_nat_dec_lt(v___x_1553_, v___x_1583_);
if (v___x_1584_ == 0)
{
lean_object* v___x_1585_; lean_object* v___x_1586_; 
lean_dec(v___x_1563_);
v___x_1585_ = lean_obj_once(&l_Lean_warnIfUsesSorry___closed__17, &l_Lean_warnIfUsesSorry___closed__17_once, _init_l_Lean_warnIfUsesSorry___closed__17);
v___x_1586_ = l_Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2(v___x_1585_, v_a_1531_, v_a_1532_);
return v___x_1586_;
}
else
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_array_fget(v___x_1563_, v___x_1553_);
lean_dec(v___x_1563_);
v_val_1566_ = v___x_1587_;
goto v___jp_1565_;
}
}
}
else
{
lean_dec(v___x_1560_);
lean_dec(v___x_1559_);
return v___x_1562_;
}
}
}
}
else
{
lean_dec(v_decl_1530_);
goto v___jp_1540_;
}
v___jp_1540_:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1542_, 0, v___x_1541_);
return v___x_1542_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_warnIfUsesSorry___boxed(lean_object* v_decl_1595_, lean_object* v_a_1596_, lean_object* v_a_1597_, lean_object* v_a_1598_){
_start:
{
lean_object* v_res_1599_; 
v_res_1599_ = l_Lean_warnIfUsesSorry(v_decl_1595_, v_a_1596_, v_a_1597_);
lean_dec(v_a_1597_);
lean_dec_ref(v_a_1596_);
return v_res_1599_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(lean_object* v_00_u03b2_1600_, lean_object* v_m_1601_, lean_object* v_a_1602_){
_start:
{
lean_object* v___x_1603_; 
v___x_1603_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___redArg(v_m_1601_, v_a_1602_);
return v___x_1603_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1604_, lean_object* v_m_1605_, lean_object* v_a_1606_){
_start:
{
lean_object* v_res_1607_; 
v_res_1607_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8(v_00_u03b2_1604_, v_m_1605_, v_a_1606_);
lean_dec_ref(v_a_1606_);
lean_dec_ref(v_m_1605_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9(lean_object* v_00_u03b2_1608_, lean_object* v_m_1609_, lean_object* v_a_1610_, lean_object* v_b_1611_){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9___redArg(v_m_1609_, v_a_1610_, v_b_1611_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1613_, lean_object* v_a_1614_, lean_object* v_x_1615_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___redArg(v_a_1614_, v_x_1615_);
return v___x_1616_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1617_, lean_object* v_a_1618_, lean_object* v_x_1619_){
_start:
{
lean_object* v_res_1620_; 
v_res_1620_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__8_spec__14(v_00_u03b2_1617_, v_a_1618_, v_x_1619_);
lean_dec(v_x_1619_);
lean_dec_ref(v_a_1618_);
return v_res_1620_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(lean_object* v_00_u03b2_1621_, lean_object* v_a_1622_, lean_object* v_x_1623_){
_start:
{
uint8_t v___x_1624_; 
v___x_1624_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___redArg(v_a_1622_, v_x_1623_);
return v___x_1624_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16___boxed(lean_object* v_00_u03b2_1625_, lean_object* v_a_1626_, lean_object* v_x_1627_){
_start:
{
uint8_t v_res_1628_; lean_object* v_r_1629_; 
v_res_1628_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__16(v_00_u03b2_1625_, v_a_1626_, v_x_1627_);
lean_dec(v_x_1627_);
lean_dec_ref(v_a_1626_);
v_r_1629_ = lean_box(v_res_1628_);
return v_r_1629_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17(lean_object* v_00_u03b2_1630_, lean_object* v_data_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17___redArg(v_data_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18(lean_object* v_00_u03b2_1633_, lean_object* v_a_1634_, lean_object* v_b_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__18___redArg(v_a_1634_, v_b_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(lean_object* v_00_u03b1_1638_, lean_object* v_name_1639_, uint8_t v_bi_1640_, lean_object* v_type_1641_, lean_object* v_k_1642_, uint8_t v_kind_1643_, lean_object* v___y_1644_, lean_object* v___y_1645_, lean_object* v___y_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___redArg(v_name_1639_, v_bi_1640_, v_type_1641_, v_k_1642_, v_kind_1643_, v___y_1644_, v___y_1645_, v___y_1646_, v___y_1647_, v___y_1648_, v___y_1649_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22___boxed(lean_object* v_00_u03b1_1652_, lean_object* v_name_1653_, lean_object* v_bi_1654_, lean_object* v_type_1655_, lean_object* v_k_1656_, lean_object* v_kind_1657_, lean_object* v___y_1658_, lean_object* v___y_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_bi_boxed_1665_; uint8_t v_kind_boxed_1666_; lean_object* v_res_1667_; 
v_bi_boxed_1665_ = lean_unbox(v_bi_1654_);
v_kind_boxed_1666_ = lean_unbox(v_kind_1657_);
v_res_1667_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitForall_visit___at___00Lean_Meta_visitForall___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__10_spec__20_spec__22(v_00_u03b1_1652_, v_name_1653_, v_bi_boxed_1665_, v_type_1655_, v_k_1656_, v_kind_boxed_1666_, v___y_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
lean_dec(v___y_1659_);
lean_dec(v___y_1658_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(lean_object* v_00_u03b1_1668_, lean_object* v_name_1669_, lean_object* v_type_1670_, lean_object* v_val_1671_, lean_object* v_k_1672_, uint8_t v_nondep_1673_, uint8_t v_kind_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___redArg(v_name_1669_, v_type_1670_, v_val_1671_, v_k_1672_, v_nondep_1673_, v_kind_1674_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27___boxed(lean_object* v_00_u03b1_1683_, lean_object* v_name_1684_, lean_object* v_type_1685_, lean_object* v_val_1686_, lean_object* v_k_1687_, lean_object* v_nondep_1688_, lean_object* v_kind_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
_start:
{
uint8_t v_nondep_boxed_1697_; uint8_t v_kind_boxed_1698_; lean_object* v_res_1699_; 
v_nondep_boxed_1697_ = lean_unbox(v_nondep_1688_);
v_kind_boxed_1698_ = lean_unbox(v_kind_1689_);
v_res_1699_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_visitLet_visit___at___00Lean_Meta_visitLet___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__12_spec__24_spec__27(v_00_u03b1_1683_, v_name_1684_, v_type_1685_, v_val_1686_, v_k_1687_, v_nondep_boxed_1697_, v_kind_boxed_1698_, v___y_1690_, v___y_1691_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_);
lean_dec(v___y_1695_);
lean_dec_ref(v___y_1694_);
lean_dec(v___y_1693_);
lean_dec_ref(v___y_1692_);
lean_dec(v___y_1691_);
lean_dec(v___y_1690_);
return v_res_1699_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18(lean_object* v_00_u03b2_1700_, lean_object* v_i_1701_, lean_object* v_source_1702_, lean_object* v_target_1703_){
_start:
{
lean_object* v___x_1704_; 
v___x_1704_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18___redArg(v_i_1701_, v_source_1702_, v_target_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22(lean_object* v_00_u03b2_1705_, lean_object* v_x_1706_, lean_object* v_x_1707_){
_start:
{
lean_object* v___x_1708_; 
v___x_1708_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_ForEachExpr_0__Lean_Meta_forEachExpr_x27_visit___at___00Lean_Meta_forEachExpr_x27___at___00Lean_Meta_forEachSorryM___at___00Lean_Declaration_forEachSorryM___at___00Lean_warnIfUsesSorry_spec__1_spec__1_spec__2_spec__5_spec__9_spec__17_spec__18_spec__22___redArg(v_x_1706_, v_x_1707_);
return v___x_1708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; 
v___x_1758_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1759_ = 0;
v___x_1760_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__20_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_1761_ = l_Lean_registerTraceClass(v___x_1758_, v___x_1759_, v___x_1760_);
return v___x_1761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2____boxed(lean_object* v_a_1762_){
_start:
{
lean_object* v_res_1763_; 
v_res_1763_ = l___private_Lean_AddDecl_0__Lean_initFn_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_();
return v_res_1763_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(lean_object* v_env_1764_, lean_object* v___y_1765_){
_start:
{
lean_object* v___x_1767_; lean_object* v_nextMacroScope_1768_; lean_object* v_ngen_1769_; lean_object* v_auxDeclNGen_1770_; lean_object* v_traceState_1771_; lean_object* v_messages_1772_; lean_object* v_infoState_1773_; lean_object* v_snapshotTasks_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1785_; 
v___x_1767_ = lean_st_ref_take(v___y_1765_);
v_nextMacroScope_1768_ = lean_ctor_get(v___x_1767_, 1);
v_ngen_1769_ = lean_ctor_get(v___x_1767_, 2);
v_auxDeclNGen_1770_ = lean_ctor_get(v___x_1767_, 3);
v_traceState_1771_ = lean_ctor_get(v___x_1767_, 4);
v_messages_1772_ = lean_ctor_get(v___x_1767_, 6);
v_infoState_1773_ = lean_ctor_get(v___x_1767_, 7);
v_snapshotTasks_1774_ = lean_ctor_get(v___x_1767_, 8);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1767_);
if (v_isSharedCheck_1785_ == 0)
{
lean_object* v_unused_1786_; lean_object* v_unused_1787_; 
v_unused_1786_ = lean_ctor_get(v___x_1767_, 5);
lean_dec(v_unused_1786_);
v_unused_1787_ = lean_ctor_get(v___x_1767_, 0);
lean_dec(v_unused_1787_);
v___x_1776_ = v___x_1767_;
v_isShared_1777_ = v_isSharedCheck_1785_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_snapshotTasks_1774_);
lean_inc(v_infoState_1773_);
lean_inc(v_messages_1772_);
lean_inc(v_traceState_1771_);
lean_inc(v_auxDeclNGen_1770_);
lean_inc(v_ngen_1769_);
lean_inc(v_nextMacroScope_1768_);
lean_dec(v___x_1767_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1785_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1778_; lean_object* v___x_1780_; 
v___x_1778_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_1777_ == 0)
{
lean_ctor_set(v___x_1776_, 5, v___x_1778_);
lean_ctor_set(v___x_1776_, 0, v_env_1764_);
v___x_1780_ = v___x_1776_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_env_1764_);
lean_ctor_set(v_reuseFailAlloc_1784_, 1, v_nextMacroScope_1768_);
lean_ctor_set(v_reuseFailAlloc_1784_, 2, v_ngen_1769_);
lean_ctor_set(v_reuseFailAlloc_1784_, 3, v_auxDeclNGen_1770_);
lean_ctor_set(v_reuseFailAlloc_1784_, 4, v_traceState_1771_);
lean_ctor_set(v_reuseFailAlloc_1784_, 5, v___x_1778_);
lean_ctor_set(v_reuseFailAlloc_1784_, 6, v_messages_1772_);
lean_ctor_set(v_reuseFailAlloc_1784_, 7, v_infoState_1773_);
lean_ctor_set(v_reuseFailAlloc_1784_, 8, v_snapshotTasks_1774_);
v___x_1780_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = lean_st_ref_set(v___y_1765_, v___x_1780_);
v___x_1782_ = lean_box(0);
v___x_1783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
return v___x_1783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg___boxed(lean_object* v_env_1788_, lean_object* v___y_1789_, lean_object* v___y_1790_){
_start:
{
lean_object* v_res_1791_; 
v_res_1791_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1788_, v___y_1789_);
lean_dec(v___y_1789_);
return v_res_1791_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(lean_object* v_env_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
lean_object* v___x_1796_; 
v___x_1796_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_env_1792_, v___y_1794_);
return v___x_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___boxed(lean_object* v_env_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
lean_object* v_res_1801_; 
v_res_1801_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1(v_env_1797_, v___y_1798_, v___y_1799_);
lean_dec(v___y_1799_);
lean_dec_ref(v___y_1798_);
return v_res_1801_;
}
}
static lean_object* _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = lean_box(0);
v___x_1803_ = l_Lean_interruptExceptionId;
v___x_1804_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1804_, 0, v___x_1803_);
lean_ctor_set(v___x_1804_, 1, v___x_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg(){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; 
v___x_1806_ = lean_obj_once(&l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0, &l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0_once, _init_l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___closed__0);
v___x_1807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1807_, 0, v___x_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v___y_1808_){
_start:
{
lean_object* v_res_1809_; 
v_res_1809_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v_res_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(lean_object* v_msg_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
lean_object* v_ref_1814_; lean_object* v___x_1815_; lean_object* v_a_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_1824_; 
v_ref_1814_ = lean_ctor_get(v___y_1811_, 5);
v___x_1815_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_1810_, v___y_1811_, v___y_1812_);
v_a_1816_ = lean_ctor_get(v___x_1815_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1815_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1818_ = v___x_1815_;
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_a_1816_);
lean_dec(v___x_1815_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_1824_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v___x_1820_; lean_object* v___x_1822_; 
lean_inc(v_ref_1814_);
v___x_1820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1820_, 0, v_ref_1814_);
lean_ctor_set(v___x_1820_, 1, v_a_1816_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set_tag(v___x_1818_, 1);
lean_ctor_set(v___x_1818_, 0, v___x_1820_);
v___x_1822_ = v___x_1818_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v___x_1820_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_msg_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_1825_, v___y_1826_, v___y_1827_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(lean_object* v_ex_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v___y_1835_; lean_object* v___y_1836_; 
if (lean_obj_tag(v_ex_1830_) == 16)
{
lean_object* v___x_1840_; lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
v___x_1840_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1840_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1843_ = lean_box(0);
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
v_resetjp_1842_:
{
lean_object* v___x_1846_; 
if (v_isShared_1844_ == 0)
{
v___x_1846_ = v___x_1843_;
goto v_reusejp_1845_;
}
else
{
lean_object* v_reuseFailAlloc_1847_; 
v_reuseFailAlloc_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_a_1841_);
v___x_1846_ = v_reuseFailAlloc_1847_;
goto v_reusejp_1845_;
}
v_reusejp_1845_:
{
return v___x_1846_;
}
}
}
else
{
v___y_1835_ = v___y_1831_;
v___y_1836_ = v___y_1832_;
goto v___jp_1834_;
}
v___jp_1834_:
{
lean_object* v_options_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v_options_1837_ = lean_ctor_get(v___y_1835_, 2);
lean_inc_ref(v_options_1837_);
v___x_1838_ = l_Lean_Kernel_Exception_toMessageData(v_ex_1830_, v_options_1837_);
v___x_1839_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v___x_1838_, v___y_1835_, v___y_1836_);
return v___x_1839_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg___boxed(lean_object* v_ex_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_){
_start:
{
lean_object* v_res_1853_; 
v_res_1853_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_1849_, v___y_1850_, v___y_1851_);
lean_dec(v___y_1851_);
lean_dec_ref(v___y_1850_);
return v_res_1853_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(lean_object* v_x_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_){
_start:
{
if (lean_obj_tag(v_x_1854_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; 
v_a_1858_ = lean_ctor_get(v_x_1854_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v_x_1854_, 1);
v___x_1859_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_a_1858_, v___y_1855_, v___y_1856_);
return v___x_1859_;
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
v_a_1860_ = lean_ctor_get(v_x_1854_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v_x_1854_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v_x_1854_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v_x_1854_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
lean_ctor_set_tag(v___x_1862_, 0);
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg___boxed(lean_object* v_x_1868_, lean_object* v___y_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_){
_start:
{
lean_object* v_res_1872_; 
v_res_1872_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_1868_, v___y_1869_, v___y_1870_);
lean_dec(v___y_1870_);
lean_dec_ref(v___y_1869_);
return v_res_1872_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = lean_unsigned_to_nat(1u);
v___x_1874_ = l_Lean_Level_ofNat(v___x_1873_);
return v___x_1874_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1875_ = lean_box(0);
v___x_1876_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__0);
v___x_1877_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___x_1875_);
return v___x_1877_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5(void){
_start:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; 
v___x_1884_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__1);
v___x_1885_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__4));
v___x_1886_ = l_Lean_mkConst(v___x_1885_, v___x_1884_);
return v___x_1886_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6(void){
_start:
{
lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1887_ = lean_unsigned_to_nat(0u);
v___x_1888_ = l_Lean_Level_ofNat(v___x_1887_);
return v___x_1888_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1889_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__6);
v___x_1890_ = l_Lean_mkSort(v___x_1889_);
return v___x_1890_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11(void){
_start:
{
lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1896_ = lean_box(0);
v___x_1897_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__10));
v___x_1898_ = l_Lean_mkConst(v___x_1897_, v___x_1896_);
return v___x_1898_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1899_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__11);
v___x_1900_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__7);
v___x_1901_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__5);
v___x_1902_ = l_Lean_mkAppB(v___x_1901_, v___x_1900_, v___x_1899_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(lean_object* v_as_x27_1908_, lean_object* v_b_1909_, lean_object* v___y_1910_, lean_object* v___y_1911_){
_start:
{
if (lean_obj_tag(v_as_x27_1908_) == 0)
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1913_, 0, v_b_1909_);
return v___x_1913_;
}
else
{
lean_object* v_head_1914_; lean_object* v_tail_1915_; lean_object* v___x_1916_; lean_object* v_env_1917_; lean_object* v_options_1918_; lean_object* v_cancelTk_x3f_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___y_1923_; uint8_t v___y_1924_; lean_object* v_a_1928_; lean_object* v___x_1931_; lean_object* v___x_1932_; uint8_t v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec_ref(v_b_1909_);
v_head_1914_ = lean_ctor_get(v_as_x27_1908_, 0);
v_tail_1915_ = lean_ctor_get(v_as_x27_1908_, 1);
v___x_1916_ = lean_st_ref_get(v___y_1911_);
v_env_1917_ = lean_ctor_get(v___x_1916_, 0);
lean_inc_ref(v_env_1917_);
lean_dec(v___x_1916_);
v_options_1918_ = lean_ctor_get(v___y_1910_, 2);
v_cancelTk_x3f_1919_ = lean_ctor_get(v___y_1910_, 12);
v___x_1920_ = lean_box(0);
v___x_1921_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1931_ = lean_obj_once(&l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12, &l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12_once, _init_l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__12);
lean_inc(v_head_1914_);
v___x_1932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1932_, 0, v_head_1914_);
lean_ctor_set(v___x_1932_, 1, v___x_1920_);
lean_ctor_set(v___x_1932_, 2, v___x_1931_);
v___x_1933_ = 0;
v___x_1934_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set_uint8(v___x_1934_, sizeof(void*)*1, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v___x_1934_);
v___x_1936_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_1917_, v_options_1918_, v___x_1935_, v_cancelTk_x3f_1919_);
lean_dec_ref_known(v___x_1935_, 1);
v___x_1937_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_1936_, v___y_1910_, v___y_1911_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_object* v_a_1938_; lean_object* v___x_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1947_; 
v_a_1938_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1938_);
lean_dec_ref_known(v___x_1937_, 1);
v___x_1939_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_1938_, v___y_1911_);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1947_ == 0)
{
lean_object* v_unused_1948_; 
v_unused_1948_ = lean_ctor_get(v___x_1939_, 0);
lean_dec(v_unused_1948_);
v___x_1941_ = v___x_1939_;
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
else
{
lean_dec(v___x_1939_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1947_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1943_; lean_object* v___x_1945_; 
v___x_1943_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__14));
if (v_isShared_1942_ == 0)
{
lean_ctor_set(v___x_1941_, 0, v___x_1943_);
v___x_1945_ = v___x_1941_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v___x_1943_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
else
{
lean_object* v_a_1949_; 
v_a_1949_ = lean_ctor_get(v___x_1937_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___x_1937_, 1);
v_a_1928_ = v_a_1949_;
goto v___jp_1927_;
}
v___jp_1922_:
{
if (v___y_1924_ == 0)
{
lean_dec_ref(v___y_1923_);
v_as_x27_1908_ = v_tail_1915_;
v_b_1909_ = v___x_1921_;
goto _start;
}
else
{
lean_object* v___x_1926_; 
v___x_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1926_, 0, v___y_1923_);
return v___x_1926_;
}
}
v___jp_1927_:
{
uint8_t v___x_1929_; 
v___x_1929_ = l_Lean_Exception_isInterrupt(v_a_1928_);
if (v___x_1929_ == 0)
{
uint8_t v___x_1930_; 
lean_inc_ref(v_a_1928_);
v___x_1930_ = l_Lean_Exception_isRuntime(v_a_1928_);
v___y_1923_ = v_a_1928_;
v___y_1924_ = v___x_1930_;
goto v___jp_1922_;
}
else
{
v___y_1923_ = v_a_1928_;
v___y_1924_ = v___x_1929_;
goto v___jp_1922_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___boxed(lean_object* v_as_x27_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_1950_, v_b_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_as_x27_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(lean_object* v_decl_1956_, lean_object* v_a_1957_, lean_object* v_a_1958_){
_start:
{
lean_object* v___y_1961_; lean_object* v___y_1962_; lean_object* v___y_1989_; uint8_t v___y_1990_; lean_object* v_a_1993_; lean_object* v___y_1997_; uint8_t v___y_1998_; lean_object* v_a_2001_; 
switch(lean_obj_tag(v_decl_1956_))
{
case 1:
{
lean_object* v_val_2004_; lean_object* v___x_2005_; lean_object* v_toConstantVal_2006_; lean_object* v_env_2007_; lean_object* v_options_2008_; lean_object* v_cancelTk_x3f_2009_; uint8_t v___x_2010_; lean_object* v___x_2011_; lean_object* v_fallbackDecl_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_val_2004_ = lean_ctor_get(v_decl_1956_, 0);
v___x_2005_ = lean_st_ref_get(v_a_1958_);
v_toConstantVal_2006_ = lean_ctor_get(v_val_2004_, 0);
v_env_2007_ = lean_ctor_get(v___x_2005_, 0);
lean_inc_ref(v_env_2007_);
lean_dec(v___x_2005_);
v_options_2008_ = lean_ctor_get(v_a_1957_, 2);
v_cancelTk_x3f_2009_ = lean_ctor_get(v_a_1957_, 12);
v___x_2010_ = 0;
lean_inc_ref(v_toConstantVal_2006_);
v___x_2011_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2011_, 0, v_toConstantVal_2006_);
lean_ctor_set_uint8(v___x_2011_, sizeof(void*)*1, v___x_2010_);
v_fallbackDecl_2012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2012_, 0, v___x_2011_);
v___x_2013_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2007_, v_options_2008_, v_fallbackDecl_2012_, v_cancelTk_x3f_2009_);
lean_dec_ref_known(v_fallbackDecl_2012_, 1);
v___x_2014_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2013_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2024_; 
lean_dec_ref_known(v_decl_1956_, 1);
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
v___x_2016_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2015_, v_a_1958_);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_2016_, 0);
lean_dec(v_unused_2025_);
v___x_2018_ = v___x_2016_;
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
else
{
lean_dec(v___x_2016_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2024_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2020_; lean_object* v___x_2022_; 
v___x_2020_ = lean_box(0);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2020_);
v___x_2022_ = v___x_2018_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
return v___x_2022_;
}
}
}
else
{
lean_object* v_a_2026_; 
v_a_2026_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2014_, 1);
v_a_1993_ = v_a_2026_;
goto v___jp_1992_;
}
}
case 2:
{
lean_object* v_val_2027_; lean_object* v___x_2028_; lean_object* v_toConstantVal_2029_; lean_object* v_env_2030_; lean_object* v_options_2031_; lean_object* v_cancelTk_x3f_2032_; uint8_t v___x_2033_; lean_object* v___x_2034_; lean_object* v_fallbackDecl_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v_val_2027_ = lean_ctor_get(v_decl_1956_, 0);
v___x_2028_ = lean_st_ref_get(v_a_1958_);
v_toConstantVal_2029_ = lean_ctor_get(v_val_2027_, 0);
v_env_2030_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_env_2030_);
lean_dec(v___x_2028_);
v_options_2031_ = lean_ctor_get(v_a_1957_, 2);
v_cancelTk_x3f_2032_ = lean_ctor_get(v_a_1957_, 12);
v___x_2033_ = 0;
lean_inc_ref(v_toConstantVal_2029_);
v___x_2034_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_2034_, 0, v_toConstantVal_2029_);
lean_ctor_set_uint8(v___x_2034_, sizeof(void*)*1, v___x_2033_);
v_fallbackDecl_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_fallbackDecl_2035_, 0, v___x_2034_);
v___x_2036_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2030_, v_options_2031_, v_fallbackDecl_2035_, v_cancelTk_x3f_2032_);
lean_dec_ref_known(v_fallbackDecl_2035_, 1);
v___x_2037_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2036_, v_a_1957_, v_a_1958_);
if (lean_obj_tag(v___x_2037_) == 0)
{
lean_object* v_a_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2047_; 
lean_dec_ref_known(v_decl_1956_, 1);
v_a_2038_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2037_, 1);
v___x_2039_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2038_, v_a_1958_);
v_isSharedCheck_2047_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2047_ == 0)
{
lean_object* v_unused_2048_; 
v_unused_2048_ = lean_ctor_get(v___x_2039_, 0);
lean_dec(v_unused_2048_);
v___x_2041_ = v___x_2039_;
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
else
{
lean_dec(v___x_2039_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2047_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2043_; lean_object* v___x_2045_; 
v___x_2043_ = lean_box(0);
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v___x_2043_);
v___x_2045_ = v___x_2041_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2046_; 
v_reuseFailAlloc_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2046_, 0, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2046_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
return v___x_2045_;
}
}
}
else
{
lean_object* v_a_2049_; 
v_a_2049_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_a_2049_);
lean_dec_ref_known(v___x_2037_, 1);
v_a_2001_ = v_a_2049_;
goto v___jp_2000_;
}
}
default: 
{
v___y_1961_ = v_a_1957_;
v___y_1962_ = v_a_1958_;
goto v___jp_1960_;
}
}
v___jp_1960_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1963_ = l_Lean_Declaration_getNames(v_decl_1956_);
v___x_1964_ = lean_box(0);
v___x_1965_ = ((lean_object*)(l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg___closed__2));
v___x_1966_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v___x_1963_, v___x_1965_, v___y_1961_, v___y_1962_);
lean_dec(v___x_1963_);
if (lean_obj_tag(v___x_1966_) == 0)
{
lean_object* v_a_1967_; lean_object* v___x_1969_; uint8_t v_isShared_1970_; uint8_t v_isSharedCheck_1979_; 
v_a_1967_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1979_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1979_ == 0)
{
v___x_1969_ = v___x_1966_;
v_isShared_1970_ = v_isSharedCheck_1979_;
goto v_resetjp_1968_;
}
else
{
lean_inc(v_a_1967_);
lean_dec(v___x_1966_);
v___x_1969_ = lean_box(0);
v_isShared_1970_ = v_isSharedCheck_1979_;
goto v_resetjp_1968_;
}
v_resetjp_1968_:
{
lean_object* v_fst_1971_; 
v_fst_1971_ = lean_ctor_get(v_a_1967_, 0);
lean_inc(v_fst_1971_);
lean_dec(v_a_1967_);
if (lean_obj_tag(v_fst_1971_) == 0)
{
lean_object* v___x_1973_; 
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v___x_1964_);
v___x_1973_ = v___x_1969_;
goto v_reusejp_1972_;
}
else
{
lean_object* v_reuseFailAlloc_1974_; 
v_reuseFailAlloc_1974_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1974_, 0, v___x_1964_);
v___x_1973_ = v_reuseFailAlloc_1974_;
goto v_reusejp_1972_;
}
v_reusejp_1972_:
{
return v___x_1973_;
}
}
else
{
lean_object* v_val_1975_; lean_object* v___x_1977_; 
v_val_1975_ = lean_ctor_get(v_fst_1971_, 0);
lean_inc(v_val_1975_);
lean_dec_ref_known(v_fst_1971_, 1);
if (v_isShared_1970_ == 0)
{
lean_ctor_set(v___x_1969_, 0, v_val_1975_);
v___x_1977_ = v___x_1969_;
goto v_reusejp_1976_;
}
else
{
lean_object* v_reuseFailAlloc_1978_; 
v_reuseFailAlloc_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1978_, 0, v_val_1975_);
v___x_1977_ = v_reuseFailAlloc_1978_;
goto v_reusejp_1976_;
}
v_reusejp_1976_:
{
return v___x_1977_;
}
}
}
}
else
{
lean_object* v_a_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_1987_; 
v_a_1980_ = lean_ctor_get(v___x_1966_, 0);
v_isSharedCheck_1987_ = !lean_is_exclusive(v___x_1966_);
if (v_isSharedCheck_1987_ == 0)
{
v___x_1982_ = v___x_1966_;
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_a_1980_);
lean_dec(v___x_1966_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_1987_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
lean_object* v___x_1985_; 
if (v_isShared_1983_ == 0)
{
v___x_1985_ = v___x_1982_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v_a_1980_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
return v___x_1985_;
}
}
}
}
v___jp_1988_:
{
if (v___y_1990_ == 0)
{
lean_dec_ref(v___y_1989_);
v___y_1961_ = v_a_1957_;
v___y_1962_ = v_a_1958_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1991_; 
lean_dec(v_decl_1956_);
v___x_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1991_, 0, v___y_1989_);
return v___x_1991_;
}
}
v___jp_1992_:
{
uint8_t v___x_1994_; 
v___x_1994_ = l_Lean_Exception_isInterrupt(v_a_1993_);
if (v___x_1994_ == 0)
{
uint8_t v___x_1995_; 
lean_inc_ref(v_a_1993_);
v___x_1995_ = l_Lean_Exception_isRuntime(v_a_1993_);
v___y_1989_ = v_a_1993_;
v___y_1990_ = v___x_1995_;
goto v___jp_1988_;
}
else
{
v___y_1989_ = v_a_1993_;
v___y_1990_ = v___x_1994_;
goto v___jp_1988_;
}
}
v___jp_1996_:
{
if (v___y_1998_ == 0)
{
lean_dec_ref(v___y_1997_);
v___y_1961_ = v_a_1957_;
v___y_1962_ = v_a_1958_;
goto v___jp_1960_;
}
else
{
lean_object* v___x_1999_; 
lean_dec(v_decl_1956_);
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___y_1997_);
return v___x_1999_;
}
}
v___jp_2000_:
{
uint8_t v___x_2002_; 
v___x_2002_ = l_Lean_Exception_isInterrupt(v_a_2001_);
if (v___x_2002_ == 0)
{
uint8_t v___x_2003_; 
lean_inc_ref(v_a_2001_);
v___x_2003_ = l_Lean_Exception_isRuntime(v_a_2001_);
v___y_1997_ = v_a_2001_;
v___y_1998_ = v___x_2003_;
goto v___jp_1996_;
}
else
{
v___y_1997_ = v_a_2001_;
v___y_1998_ = v___x_2002_;
goto v___jp_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom___boxed(lean_object* v_decl_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_, lean_object* v_a_2053_){
_start:
{
lean_object* v_res_2054_; 
v_res_2054_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2050_, v_a_2051_, v_a_2052_);
lean_dec(v_a_2052_);
lean_dec_ref(v_a_2051_);
return v_res_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(lean_object* v_00_u03b1_2055_, lean_object* v_x_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v_x_2056_, v___y_2057_, v___y_2058_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___boxed(lean_object* v_00_u03b1_2061_, lean_object* v_x_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0(v_00_u03b1_2061_, v_x_2062_, v___y_2063_, v___y_2064_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(lean_object* v_as_2067_, lean_object* v_as_x27_2068_, lean_object* v_b_2069_, lean_object* v_a_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___redArg(v_as_x27_2068_, v_b_2069_, v___y_2071_, v___y_2072_);
return v___x_2074_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2___boxed(lean_object* v_as_2075_, lean_object* v_as_x27_2076_, lean_object* v_b_2077_, lean_object* v_a_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
lean_object* v_res_2082_; 
v_res_2082_ = l_List_forIn_x27_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__2(v_as_2075_, v_as_x27_2076_, v_b_2077_, v_a_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v_as_x27_2076_);
lean_dec(v_as_2075_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(lean_object* v_00_u03b1_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_){
_start:
{
lean_object* v___x_2087_; 
v___x_2087_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___redArg();
return v___x_2087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b1_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_, lean_object* v___y_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l_Lean_throwInterruptException___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__3(v_00_u03b1_2088_, v___y_2089_, v___y_2090_);
lean_dec(v___y_2090_);
lean_dec_ref(v___y_2089_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(lean_object* v_00_u03b1_2093_, lean_object* v_ex_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v_ex_2094_, v___y_2095_, v___y_2096_);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___boxed(lean_object* v_00_u03b1_2099_, lean_object* v_ex_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_){
_start:
{
lean_object* v_res_2104_; 
v_res_2104_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0(v_00_u03b1_2099_, v_ex_2100_, v___y_2101_, v___y_2102_);
lean_dec(v___y_2102_);
lean_dec_ref(v___y_2101_);
return v_res_2104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(lean_object* v_00_u03b1_2105_, lean_object* v_msg_2106_, lean_object* v___y_2107_, lean_object* v___y_2108_){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___redArg(v_msg_2106_, v___y_2107_, v___y_2108_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b1_2111_, lean_object* v_msg_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lean_throwError___at___00Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0_spec__2(v_00_u03b1_2111_, v_msg_2112_, v___y_2113_, v___y_2114_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
return v_res_2116_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2117_ = lean_unsigned_to_nat(32u);
v___x_2118_ = lean_mk_empty_array_with_capacity(v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1(void){
_start:
{
size_t v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2120_ = ((size_t)5ULL);
v___x_2121_ = lean_unsigned_to_nat(0u);
v___x_2122_ = lean_unsigned_to_nat(32u);
v___x_2123_ = lean_mk_empty_array_with_capacity(v___x_2122_);
v___x_2124_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__0);
v___x_2125_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
lean_ctor_set(v___x_2125_, 1, v___x_2123_);
lean_ctor_set(v___x_2125_, 2, v___x_2121_);
lean_ctor_set(v___x_2125_, 3, v___x_2121_);
lean_ctor_set_usize(v___x_2125_, 4, v___x_2120_);
return v___x_2125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(lean_object* v___y_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v_traceState_2129_; lean_object* v_traces_2130_; lean_object* v___x_2131_; lean_object* v_traceState_2132_; lean_object* v_env_2133_; lean_object* v_nextMacroScope_2134_; lean_object* v_ngen_2135_; lean_object* v_auxDeclNGen_2136_; lean_object* v_cache_2137_; lean_object* v_messages_2138_; lean_object* v_infoState_2139_; lean_object* v_snapshotTasks_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2159_; 
v___x_2128_ = lean_st_ref_get(v___y_2126_);
v_traceState_2129_ = lean_ctor_get(v___x_2128_, 4);
lean_inc_ref(v_traceState_2129_);
lean_dec(v___x_2128_);
v_traces_2130_ = lean_ctor_get(v_traceState_2129_, 0);
lean_inc_ref(v_traces_2130_);
lean_dec_ref(v_traceState_2129_);
v___x_2131_ = lean_st_ref_take(v___y_2126_);
v_traceState_2132_ = lean_ctor_get(v___x_2131_, 4);
v_env_2133_ = lean_ctor_get(v___x_2131_, 0);
v_nextMacroScope_2134_ = lean_ctor_get(v___x_2131_, 1);
v_ngen_2135_ = lean_ctor_get(v___x_2131_, 2);
v_auxDeclNGen_2136_ = lean_ctor_get(v___x_2131_, 3);
v_cache_2137_ = lean_ctor_get(v___x_2131_, 5);
v_messages_2138_ = lean_ctor_get(v___x_2131_, 6);
v_infoState_2139_ = lean_ctor_get(v___x_2131_, 7);
v_snapshotTasks_2140_ = lean_ctor_get(v___x_2131_, 8);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2142_ = v___x_2131_;
v_isShared_2143_ = v_isSharedCheck_2159_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_snapshotTasks_2140_);
lean_inc(v_infoState_2139_);
lean_inc(v_messages_2138_);
lean_inc(v_cache_2137_);
lean_inc(v_traceState_2132_);
lean_inc(v_auxDeclNGen_2136_);
lean_inc(v_ngen_2135_);
lean_inc(v_nextMacroScope_2134_);
lean_inc(v_env_2133_);
lean_dec(v___x_2131_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2159_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
uint64_t v_tid_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2157_; 
v_tid_2144_ = lean_ctor_get_uint64(v_traceState_2132_, sizeof(void*)*1);
v_isSharedCheck_2157_ = !lean_is_exclusive(v_traceState_2132_);
if (v_isSharedCheck_2157_ == 0)
{
lean_object* v_unused_2158_; 
v_unused_2158_ = lean_ctor_get(v_traceState_2132_, 0);
lean_dec(v_unused_2158_);
v___x_2146_ = v_traceState_2132_;
v_isShared_2147_ = v_isSharedCheck_2157_;
goto v_resetjp_2145_;
}
else
{
lean_dec(v_traceState_2132_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2157_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2148_; lean_object* v___x_2150_; 
v___x_2148_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___closed__1);
if (v_isShared_2147_ == 0)
{
lean_ctor_set(v___x_2146_, 0, v___x_2148_);
v___x_2150_ = v___x_2146_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v___x_2148_);
lean_ctor_set_uint64(v_reuseFailAlloc_2156_, sizeof(void*)*1, v_tid_2144_);
v___x_2150_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2149_;
}
v_reusejp_2149_:
{
lean_object* v___x_2152_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 4, v___x_2150_);
v___x_2152_ = v___x_2142_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_env_2133_);
lean_ctor_set(v_reuseFailAlloc_2155_, 1, v_nextMacroScope_2134_);
lean_ctor_set(v_reuseFailAlloc_2155_, 2, v_ngen_2135_);
lean_ctor_set(v_reuseFailAlloc_2155_, 3, v_auxDeclNGen_2136_);
lean_ctor_set(v_reuseFailAlloc_2155_, 4, v___x_2150_);
lean_ctor_set(v_reuseFailAlloc_2155_, 5, v_cache_2137_);
lean_ctor_set(v_reuseFailAlloc_2155_, 6, v_messages_2138_);
lean_ctor_set(v_reuseFailAlloc_2155_, 7, v_infoState_2139_);
lean_ctor_set(v_reuseFailAlloc_2155_, 8, v_snapshotTasks_2140_);
v___x_2152_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2153_ = lean_st_ref_set(v___y_2126_, v___x_2152_);
v___x_2154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_traces_2130_);
return v___x_2154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg___boxed(lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2160_);
lean_dec(v___y_2160_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(lean_object* v___y_2163_, lean_object* v___y_2164_){
_start:
{
lean_object* v___x_2166_; 
v___x_2166_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___boxed(lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1(v___y_2167_, v___y_2168_);
lean_dec(v___y_2168_);
lean_dec_ref(v___y_2167_);
return v_res_2170_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(lean_object* v_category_2171_, lean_object* v_opts_2172_, lean_object* v_act_2173_, lean_object* v_decl_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
lean_object* v___x_2178_; lean_object* v___x_2179_; 
lean_inc(v___y_2176_);
lean_inc_ref(v___y_2175_);
v___x_2178_ = lean_apply_2(v_act_2173_, v___y_2175_, v___y_2176_);
v___x_2179_ = l_Lean_profileitIOUnsafe___redArg(v_category_2171_, v_opts_2172_, v___x_2178_, v_decl_2174_);
return v___x_2179_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg___boxed(lean_object* v_category_2180_, lean_object* v_opts_2181_, lean_object* v_act_2182_, lean_object* v_decl_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
lean_object* v_res_2187_; 
v_res_2187_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2180_, v_opts_2181_, v_act_2182_, v_decl_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_opts_2181_);
lean_dec_ref(v_category_2180_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(lean_object* v_00_u03b1_2188_, lean_object* v_category_2189_, lean_object* v_opts_2190_, lean_object* v_act_2191_, lean_object* v_decl_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v___x_2196_; 
v___x_2196_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v_category_2189_, v_opts_2190_, v_act_2191_, v_decl_2192_, v___y_2193_, v___y_2194_);
return v___x_2196_;
}
}
LEAN_EXPORT lean_object* l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___boxed(lean_object* v_00_u03b1_2197_, lean_object* v_category_2198_, lean_object* v_opts_2199_, lean_object* v_act_2200_, lean_object* v_decl_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_){
_start:
{
lean_object* v_res_2205_; 
v_res_2205_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3(v_00_u03b1_2197_, v_category_2198_, v_opts_2199_, v_act_2200_, v_decl_2201_, v___y_2202_, v___y_2203_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_opts_2199_);
lean_dec_ref(v_category_2198_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(lean_object* v_a_2206_, lean_object* v_a_2207_){
_start:
{
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_object* v___x_2208_; 
v___x_2208_ = l_List_reverse___redArg(v_a_2207_);
return v___x_2208_;
}
else
{
lean_object* v_head_2209_; lean_object* v_tail_2210_; lean_object* v___x_2212_; uint8_t v_isShared_2213_; uint8_t v_isSharedCheck_2219_; 
v_head_2209_ = lean_ctor_get(v_a_2206_, 0);
v_tail_2210_ = lean_ctor_get(v_a_2206_, 1);
v_isSharedCheck_2219_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2212_ = v_a_2206_;
v_isShared_2213_ = v_isSharedCheck_2219_;
goto v_resetjp_2211_;
}
else
{
lean_inc(v_tail_2210_);
lean_inc(v_head_2209_);
lean_dec(v_a_2206_);
v___x_2212_ = lean_box(0);
v_isShared_2213_ = v_isSharedCheck_2219_;
goto v_resetjp_2211_;
}
v_resetjp_2211_:
{
lean_object* v___x_2214_; lean_object* v___x_2216_; 
v___x_2214_ = l_Lean_MessageData_ofName(v_head_2209_);
if (v_isShared_2213_ == 0)
{
lean_ctor_set(v___x_2212_, 1, v_a_2207_);
lean_ctor_set(v___x_2212_, 0, v___x_2214_);
v___x_2216_ = v___x_2212_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v___x_2214_);
lean_ctor_set(v_reuseFailAlloc_2218_, 1, v_a_2207_);
v___x_2216_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
v_a_2206_ = v_tail_2210_;
v_a_2207_ = v___x_2216_;
goto _start;
}
}
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__0));
v___x_2222_ = l_Lean_stringToMessageData(v___x_2221_);
return v___x_2222_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(lean_object* v_decl_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2228_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___closed__1);
v___x_2229_ = l_Lean_Declaration_getTopLevelNames(v_decl_2223_);
v___x_2230_ = lean_box(0);
v___x_2231_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2229_, v___x_2230_);
v___x_2232_ = l_Lean_MessageData_ofList(v___x_2231_);
v___x_2233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2228_);
lean_ctor_set(v___x_2233_, 1, v___x_2232_);
v___x_2234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2234_, 0, v___x_2233_);
return v___x_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed(lean_object* v_decl_2235_, lean_object* v_x_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0(v_decl_2235_, v_x_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec_ref(v_x_2236_);
return v_res_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(size_t v_sz_2241_, size_t v_i_2242_, lean_object* v_bs_2243_){
_start:
{
uint8_t v___x_2244_; 
v___x_2244_ = lean_usize_dec_lt(v_i_2242_, v_sz_2241_);
if (v___x_2244_ == 0)
{
return v_bs_2243_;
}
else
{
lean_object* v_v_2245_; lean_object* v_msg_2246_; lean_object* v___x_2247_; lean_object* v_bs_x27_2248_; size_t v___x_2249_; size_t v___x_2250_; lean_object* v___x_2251_; 
v_v_2245_ = lean_array_uget_borrowed(v_bs_2243_, v_i_2242_);
v_msg_2246_ = lean_ctor_get(v_v_2245_, 1);
lean_inc_ref(v_msg_2246_);
v___x_2247_ = lean_unsigned_to_nat(0u);
v_bs_x27_2248_ = lean_array_uset(v_bs_2243_, v_i_2242_, v___x_2247_);
v___x_2249_ = ((size_t)1ULL);
v___x_2250_ = lean_usize_add(v_i_2242_, v___x_2249_);
v___x_2251_ = lean_array_uset(v_bs_x27_2248_, v_i_2242_, v_msg_2246_);
v_i_2242_ = v___x_2250_;
v_bs_2243_ = v___x_2251_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4___boxed(lean_object* v_sz_2253_, lean_object* v_i_2254_, lean_object* v_bs_2255_){
_start:
{
size_t v_sz_boxed_2256_; size_t v_i_boxed_2257_; lean_object* v_res_2258_; 
v_sz_boxed_2256_ = lean_unbox_usize(v_sz_2253_);
lean_dec(v_sz_2253_);
v_i_boxed_2257_ = lean_unbox_usize(v_i_2254_);
lean_dec(v_i_2254_);
v_res_2258_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_boxed_2256_, v_i_boxed_2257_, v_bs_2255_);
return v_res_2258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(lean_object* v_oldTraces_2259_, lean_object* v_data_2260_, lean_object* v_ref_2261_, lean_object* v_msg_2262_, lean_object* v___y_2263_, lean_object* v___y_2264_){
_start:
{
lean_object* v_fileName_2266_; lean_object* v_fileMap_2267_; lean_object* v_options_2268_; lean_object* v_currRecDepth_2269_; lean_object* v_maxRecDepth_2270_; lean_object* v_ref_2271_; lean_object* v_currNamespace_2272_; lean_object* v_openDecls_2273_; lean_object* v_initHeartbeats_2274_; lean_object* v_maxHeartbeats_2275_; lean_object* v_quotContext_2276_; lean_object* v_currMacroScope_2277_; uint8_t v_diag_2278_; lean_object* v_cancelTk_x3f_2279_; uint8_t v_suppressElabErrors_2280_; lean_object* v_inheritedTraceOptions_2281_; lean_object* v___x_2282_; lean_object* v_traceState_2283_; lean_object* v_traces_2284_; lean_object* v_ref_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; size_t v_sz_2288_; size_t v___x_2289_; lean_object* v___x_2290_; lean_object* v_msg_2291_; lean_object* v___x_2292_; lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2330_; 
v_fileName_2266_ = lean_ctor_get(v___y_2263_, 0);
v_fileMap_2267_ = lean_ctor_get(v___y_2263_, 1);
v_options_2268_ = lean_ctor_get(v___y_2263_, 2);
v_currRecDepth_2269_ = lean_ctor_get(v___y_2263_, 3);
v_maxRecDepth_2270_ = lean_ctor_get(v___y_2263_, 4);
v_ref_2271_ = lean_ctor_get(v___y_2263_, 5);
v_currNamespace_2272_ = lean_ctor_get(v___y_2263_, 6);
v_openDecls_2273_ = lean_ctor_get(v___y_2263_, 7);
v_initHeartbeats_2274_ = lean_ctor_get(v___y_2263_, 8);
v_maxHeartbeats_2275_ = lean_ctor_get(v___y_2263_, 9);
v_quotContext_2276_ = lean_ctor_get(v___y_2263_, 10);
v_currMacroScope_2277_ = lean_ctor_get(v___y_2263_, 11);
v_diag_2278_ = lean_ctor_get_uint8(v___y_2263_, sizeof(void*)*14);
v_cancelTk_x3f_2279_ = lean_ctor_get(v___y_2263_, 12);
v_suppressElabErrors_2280_ = lean_ctor_get_uint8(v___y_2263_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2281_ = lean_ctor_get(v___y_2263_, 13);
v___x_2282_ = lean_st_ref_get(v___y_2264_);
v_traceState_2283_ = lean_ctor_get(v___x_2282_, 4);
lean_inc_ref(v_traceState_2283_);
lean_dec(v___x_2282_);
v_traces_2284_ = lean_ctor_get(v_traceState_2283_, 0);
lean_inc_ref(v_traces_2284_);
lean_dec_ref(v_traceState_2283_);
v_ref_2285_ = l_Lean_replaceRef(v_ref_2261_, v_ref_2271_);
lean_inc_ref(v_inheritedTraceOptions_2281_);
lean_inc(v_cancelTk_x3f_2279_);
lean_inc(v_currMacroScope_2277_);
lean_inc(v_quotContext_2276_);
lean_inc(v_maxHeartbeats_2275_);
lean_inc(v_initHeartbeats_2274_);
lean_inc(v_openDecls_2273_);
lean_inc(v_currNamespace_2272_);
lean_inc(v_maxRecDepth_2270_);
lean_inc(v_currRecDepth_2269_);
lean_inc_ref(v_options_2268_);
lean_inc_ref(v_fileMap_2267_);
lean_inc_ref(v_fileName_2266_);
v___x_2286_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2286_, 0, v_fileName_2266_);
lean_ctor_set(v___x_2286_, 1, v_fileMap_2267_);
lean_ctor_set(v___x_2286_, 2, v_options_2268_);
lean_ctor_set(v___x_2286_, 3, v_currRecDepth_2269_);
lean_ctor_set(v___x_2286_, 4, v_maxRecDepth_2270_);
lean_ctor_set(v___x_2286_, 5, v_ref_2285_);
lean_ctor_set(v___x_2286_, 6, v_currNamespace_2272_);
lean_ctor_set(v___x_2286_, 7, v_openDecls_2273_);
lean_ctor_set(v___x_2286_, 8, v_initHeartbeats_2274_);
lean_ctor_set(v___x_2286_, 9, v_maxHeartbeats_2275_);
lean_ctor_set(v___x_2286_, 10, v_quotContext_2276_);
lean_ctor_set(v___x_2286_, 11, v_currMacroScope_2277_);
lean_ctor_set(v___x_2286_, 12, v_cancelTk_x3f_2279_);
lean_ctor_set(v___x_2286_, 13, v_inheritedTraceOptions_2281_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*14, v_diag_2278_);
lean_ctor_set_uint8(v___x_2286_, sizeof(void*)*14 + 1, v_suppressElabErrors_2280_);
v___x_2287_ = l_Lean_PersistentArray_toArray___redArg(v_traces_2284_);
lean_dec_ref(v_traces_2284_);
v_sz_2288_ = lean_array_size(v___x_2287_);
v___x_2289_ = ((size_t)0ULL);
v___x_2290_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2_spec__4(v_sz_2288_, v___x_2289_, v___x_2287_);
v_msg_2291_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_2291_, 0, v_data_2260_);
lean_ctor_set(v_msg_2291_, 1, v_msg_2262_);
lean_ctor_set(v_msg_2291_, 2, v___x_2290_);
v___x_2292_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2291_, v___x_2286_, v___y_2264_);
lean_dec_ref_known(v___x_2286_, 14);
v_a_2293_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2330_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2330_ == 0)
{
v___x_2295_ = v___x_2292_;
v_isShared_2296_ = v_isSharedCheck_2330_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2292_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2330_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2297_; lean_object* v_traceState_2298_; lean_object* v_env_2299_; lean_object* v_nextMacroScope_2300_; lean_object* v_ngen_2301_; lean_object* v_auxDeclNGen_2302_; lean_object* v_cache_2303_; lean_object* v_messages_2304_; lean_object* v_infoState_2305_; lean_object* v_snapshotTasks_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2329_; 
v___x_2297_ = lean_st_ref_take(v___y_2264_);
v_traceState_2298_ = lean_ctor_get(v___x_2297_, 4);
v_env_2299_ = lean_ctor_get(v___x_2297_, 0);
v_nextMacroScope_2300_ = lean_ctor_get(v___x_2297_, 1);
v_ngen_2301_ = lean_ctor_get(v___x_2297_, 2);
v_auxDeclNGen_2302_ = lean_ctor_get(v___x_2297_, 3);
v_cache_2303_ = lean_ctor_get(v___x_2297_, 5);
v_messages_2304_ = lean_ctor_get(v___x_2297_, 6);
v_infoState_2305_ = lean_ctor_get(v___x_2297_, 7);
v_snapshotTasks_2306_ = lean_ctor_get(v___x_2297_, 8);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2308_ = v___x_2297_;
v_isShared_2309_ = v_isSharedCheck_2329_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_snapshotTasks_2306_);
lean_inc(v_infoState_2305_);
lean_inc(v_messages_2304_);
lean_inc(v_cache_2303_);
lean_inc(v_traceState_2298_);
lean_inc(v_auxDeclNGen_2302_);
lean_inc(v_ngen_2301_);
lean_inc(v_nextMacroScope_2300_);
lean_inc(v_env_2299_);
lean_dec(v___x_2297_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2329_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
uint64_t v_tid_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2327_; 
v_tid_2310_ = lean_ctor_get_uint64(v_traceState_2298_, sizeof(void*)*1);
v_isSharedCheck_2327_ = !lean_is_exclusive(v_traceState_2298_);
if (v_isSharedCheck_2327_ == 0)
{
lean_object* v_unused_2328_; 
v_unused_2328_ = lean_ctor_get(v_traceState_2298_, 0);
lean_dec(v_unused_2328_);
v___x_2312_ = v_traceState_2298_;
v_isShared_2313_ = v_isSharedCheck_2327_;
goto v_resetjp_2311_;
}
else
{
lean_dec(v_traceState_2298_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2327_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2317_; 
v___x_2314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2314_, 0, v_ref_2261_);
lean_ctor_set(v___x_2314_, 1, v_a_2293_);
v___x_2315_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_2259_, v___x_2314_);
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 0, v___x_2315_);
v___x_2317_ = v___x_2312_;
goto v_reusejp_2316_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v___x_2315_);
lean_ctor_set_uint64(v_reuseFailAlloc_2326_, sizeof(void*)*1, v_tid_2310_);
v___x_2317_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2316_;
}
v_reusejp_2316_:
{
lean_object* v___x_2319_; 
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 4, v___x_2317_);
v___x_2319_ = v___x_2308_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_env_2299_);
lean_ctor_set(v_reuseFailAlloc_2325_, 1, v_nextMacroScope_2300_);
lean_ctor_set(v_reuseFailAlloc_2325_, 2, v_ngen_2301_);
lean_ctor_set(v_reuseFailAlloc_2325_, 3, v_auxDeclNGen_2302_);
lean_ctor_set(v_reuseFailAlloc_2325_, 4, v___x_2317_);
lean_ctor_set(v_reuseFailAlloc_2325_, 5, v_cache_2303_);
lean_ctor_set(v_reuseFailAlloc_2325_, 6, v_messages_2304_);
lean_ctor_set(v_reuseFailAlloc_2325_, 7, v_infoState_2305_);
lean_ctor_set(v_reuseFailAlloc_2325_, 8, v_snapshotTasks_2306_);
v___x_2319_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2323_; 
v___x_2320_ = lean_st_ref_set(v___y_2264_, v___x_2319_);
v___x_2321_ = lean_box(0);
if (v_isShared_2296_ == 0)
{
lean_ctor_set(v___x_2295_, 0, v___x_2321_);
v___x_2323_ = v___x_2295_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2___boxed(lean_object* v_oldTraces_2331_, lean_object* v_data_2332_, lean_object* v_ref_2333_, lean_object* v_msg_2334_, lean_object* v___y_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_){
_start:
{
lean_object* v_res_2338_; 
v_res_2338_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2331_, v_data_2332_, v_ref_2333_, v_msg_2334_, v___y_2335_, v___y_2336_);
lean_dec(v___y_2336_);
lean_dec_ref(v___y_2335_);
return v_res_2338_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(lean_object* v_x_2339_){
_start:
{
if (lean_obj_tag(v_x_2339_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v_x_2339_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v_x_2339_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v_x_2339_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v_x_2339_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
lean_ctor_set_tag(v___x_2343_, 1);
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
v_a_2349_ = lean_ctor_get(v_x_2339_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v_x_2339_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v_x_2339_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v_x_2339_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
lean_ctor_set_tag(v___x_2351_, 0);
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(0, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg___boxed(lean_object* v_x_2357_, lean_object* v___y_2358_){
_start:
{
lean_object* v_res_2359_; 
v_res_2359_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2357_);
return v_res_2359_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(lean_object* v_e_2360_){
_start:
{
if (lean_obj_tag(v_e_2360_) == 0)
{
uint8_t v___x_2361_; 
v___x_2361_ = 2;
return v___x_2361_;
}
else
{
uint8_t v___x_2362_; 
v___x_2362_ = 0;
return v___x_2362_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4___boxed(lean_object* v_e_2363_){
_start:
{
uint8_t v_res_2364_; lean_object* v_r_2365_; 
v_res_2364_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_e_2363_);
lean_dec_ref(v_e_2363_);
v_r_2365_ = lean_box(v_res_2364_);
return v_r_2365_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(lean_object* v_opts_2366_, lean_object* v_opt_2367_){
_start:
{
lean_object* v_name_2368_; lean_object* v_defValue_2369_; lean_object* v_map_2370_; lean_object* v___x_2371_; 
v_name_2368_ = lean_ctor_get(v_opt_2367_, 0);
v_defValue_2369_ = lean_ctor_get(v_opt_2367_, 1);
v_map_2370_ = lean_ctor_get(v_opts_2366_, 0);
v___x_2371_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2370_, v_name_2368_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_inc(v_defValue_2369_);
return v_defValue_2369_;
}
else
{
lean_object* v_val_2372_; 
v_val_2372_ = lean_ctor_get(v___x_2371_, 0);
lean_inc(v_val_2372_);
lean_dec_ref_known(v___x_2371_, 1);
if (lean_obj_tag(v_val_2372_) == 3)
{
lean_object* v_v_2373_; 
v_v_2373_ = lean_ctor_get(v_val_2372_, 0);
lean_inc(v_v_2373_);
lean_dec_ref_known(v_val_2372_, 1);
return v_v_2373_;
}
else
{
lean_dec(v_val_2372_);
lean_inc(v_defValue_2369_);
return v_defValue_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5___boxed(lean_object* v_opts_2374_, lean_object* v_opt_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2374_, v_opt_2375_);
lean_dec_ref(v_opt_2375_);
lean_dec_ref(v_opts_2374_);
return v_res_2376_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0(void){
_start:
{
lean_object* v___x_2377_; double v___x_2378_; 
v___x_2377_ = lean_unsigned_to_nat(0u);
v___x_2378_ = lean_float_of_nat(v___x_2377_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2(void){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; 
v___x_2380_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__1));
v___x_2381_ = l_Lean_stringToMessageData(v___x_2380_);
return v___x_2381_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3(void){
_start:
{
lean_object* v___x_2382_; double v___x_2383_; 
v___x_2382_ = lean_unsigned_to_nat(1000u);
v___x_2383_ = lean_float_of_nat(v___x_2382_);
return v___x_2383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(lean_object* v_cls_2384_, uint8_t v_collapsed_2385_, lean_object* v_tag_2386_, lean_object* v_opts_2387_, uint8_t v_clsEnabled_2388_, lean_object* v_oldTraces_2389_, lean_object* v_msg_2390_, lean_object* v_resStartStop_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_){
_start:
{
lean_object* v_fst_2395_; lean_object* v_snd_2396_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v_data_2400_; lean_object* v_fst_2403_; lean_object* v_snd_2404_; lean_object* v___x_2405_; uint8_t v___x_2406_; lean_object* v___y_2408_; lean_object* v_a_2409_; uint8_t v___y_2424_; double v___y_2455_; 
v_fst_2395_ = lean_ctor_get(v_resStartStop_2391_, 0);
lean_inc(v_fst_2395_);
v_snd_2396_ = lean_ctor_get(v_resStartStop_2391_, 1);
lean_inc(v_snd_2396_);
lean_dec_ref(v_resStartStop_2391_);
v_fst_2403_ = lean_ctor_get(v_snd_2396_, 0);
lean_inc(v_fst_2403_);
v_snd_2404_ = lean_ctor_get(v_snd_2396_, 1);
lean_inc(v_snd_2404_);
lean_dec(v_snd_2396_);
v___x_2405_ = l_Lean_trace_profiler;
v___x_2406_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2387_, v___x_2405_);
if (v___x_2406_ == 0)
{
v___y_2424_ = v___x_2406_;
goto v___jp_2423_;
}
else
{
lean_object* v___x_2460_; uint8_t v___x_2461_; 
v___x_2460_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2461_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_opts_2387_, v___x_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; lean_object* v___x_2463_; double v___x_2464_; double v___x_2465_; double v___x_2466_; 
v___x_2462_ = l_Lean_trace_profiler_threshold;
v___x_2463_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2387_, v___x_2462_);
v___x_2464_ = lean_float_of_nat(v___x_2463_);
v___x_2465_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__3);
v___x_2466_ = lean_float_div(v___x_2464_, v___x_2465_);
v___y_2455_ = v___x_2466_;
goto v___jp_2454_;
}
else
{
lean_object* v___x_2467_; lean_object* v___x_2468_; double v___x_2469_; 
v___x_2467_ = l_Lean_trace_profiler_threshold;
v___x_2468_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__5(v_opts_2387_, v___x_2467_);
v___x_2469_ = lean_float_of_nat(v___x_2468_);
v___y_2455_ = v___x_2469_;
goto v___jp_2454_;
}
}
v___jp_2397_:
{
lean_object* v___x_2401_; 
lean_inc(v___y_2398_);
v___x_2401_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__2(v_oldTraces_2389_, v_data_2400_, v___y_2398_, v___y_2399_, v___y_2392_, v___y_2393_);
if (lean_obj_tag(v___x_2401_) == 0)
{
lean_object* v___x_2402_; 
lean_dec_ref_known(v___x_2401_, 1);
v___x_2402_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2395_);
return v___x_2402_;
}
else
{
lean_dec(v_fst_2395_);
return v___x_2401_;
}
}
v___jp_2407_:
{
uint8_t v_result_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; double v___x_2413_; lean_object* v_data_2414_; 
v_result_2410_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__4(v_fst_2395_);
v___x_2411_ = lean_box(v_result_2410_);
v___x_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
v___x_2413_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
lean_inc_ref(v_tag_2386_);
lean_inc_ref(v___x_2412_);
lean_inc(v_cls_2384_);
v_data_2414_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2414_, 0, v_cls_2384_);
lean_ctor_set(v_data_2414_, 1, v___x_2412_);
lean_ctor_set(v_data_2414_, 2, v_tag_2386_);
lean_ctor_set_float(v_data_2414_, sizeof(void*)*3, v___x_2413_);
lean_ctor_set_float(v_data_2414_, sizeof(void*)*3 + 8, v___x_2413_);
lean_ctor_set_uint8(v_data_2414_, sizeof(void*)*3 + 16, v_collapsed_2385_);
if (v___x_2406_ == 0)
{
lean_dec_ref_known(v___x_2412_, 1);
lean_dec(v_snd_2404_);
lean_dec(v_fst_2403_);
lean_dec_ref(v_tag_2386_);
lean_dec(v_cls_2384_);
v___y_2398_ = v___y_2408_;
v___y_2399_ = v_a_2409_;
v_data_2400_ = v_data_2414_;
goto v___jp_2397_;
}
else
{
lean_object* v_data_2415_; double v___x_2416_; double v___x_2417_; 
lean_dec_ref_known(v_data_2414_, 3);
v_data_2415_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_2415_, 0, v_cls_2384_);
lean_ctor_set(v_data_2415_, 1, v___x_2412_);
lean_ctor_set(v_data_2415_, 2, v_tag_2386_);
v___x_2416_ = lean_unbox_float(v_fst_2403_);
lean_dec(v_fst_2403_);
lean_ctor_set_float(v_data_2415_, sizeof(void*)*3, v___x_2416_);
v___x_2417_ = lean_unbox_float(v_snd_2404_);
lean_dec(v_snd_2404_);
lean_ctor_set_float(v_data_2415_, sizeof(void*)*3 + 8, v___x_2417_);
lean_ctor_set_uint8(v_data_2415_, sizeof(void*)*3 + 16, v_collapsed_2385_);
v___y_2398_ = v___y_2408_;
v___y_2399_ = v_a_2409_;
v_data_2400_ = v_data_2415_;
goto v___jp_2397_;
}
}
v___jp_2418_:
{
lean_object* v_ref_2419_; lean_object* v___x_2420_; 
v_ref_2419_ = lean_ctor_get(v___y_2392_, 5);
lean_inc(v___y_2393_);
lean_inc_ref(v___y_2392_);
lean_inc(v_fst_2395_);
v___x_2420_ = lean_apply_4(v_msg_2390_, v_fst_2395_, v___y_2392_, v___y_2393_, lean_box(0));
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___y_2408_ = v_ref_2419_;
v_a_2409_ = v_a_2421_;
goto v___jp_2407_;
}
else
{
lean_object* v___x_2422_; 
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__2);
v___y_2408_ = v_ref_2419_;
v_a_2409_ = v___x_2422_;
goto v___jp_2407_;
}
}
v___jp_2423_:
{
if (v_clsEnabled_2388_ == 0)
{
if (v___y_2424_ == 0)
{
lean_object* v___x_2425_; lean_object* v_traceState_2426_; lean_object* v_env_2427_; lean_object* v_nextMacroScope_2428_; lean_object* v_ngen_2429_; lean_object* v_auxDeclNGen_2430_; lean_object* v_cache_2431_; lean_object* v_messages_2432_; lean_object* v_infoState_2433_; lean_object* v_snapshotTasks_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2453_; 
lean_dec(v_snd_2404_);
lean_dec(v_fst_2403_);
lean_dec_ref(v_msg_2390_);
lean_dec_ref(v_tag_2386_);
lean_dec(v_cls_2384_);
v___x_2425_ = lean_st_ref_take(v___y_2393_);
v_traceState_2426_ = lean_ctor_get(v___x_2425_, 4);
v_env_2427_ = lean_ctor_get(v___x_2425_, 0);
v_nextMacroScope_2428_ = lean_ctor_get(v___x_2425_, 1);
v_ngen_2429_ = lean_ctor_get(v___x_2425_, 2);
v_auxDeclNGen_2430_ = lean_ctor_get(v___x_2425_, 3);
v_cache_2431_ = lean_ctor_get(v___x_2425_, 5);
v_messages_2432_ = lean_ctor_get(v___x_2425_, 6);
v_infoState_2433_ = lean_ctor_get(v___x_2425_, 7);
v_snapshotTasks_2434_ = lean_ctor_get(v___x_2425_, 8);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2436_ = v___x_2425_;
v_isShared_2437_ = v_isSharedCheck_2453_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_snapshotTasks_2434_);
lean_inc(v_infoState_2433_);
lean_inc(v_messages_2432_);
lean_inc(v_cache_2431_);
lean_inc(v_traceState_2426_);
lean_inc(v_auxDeclNGen_2430_);
lean_inc(v_ngen_2429_);
lean_inc(v_nextMacroScope_2428_);
lean_inc(v_env_2427_);
lean_dec(v___x_2425_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2453_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
uint64_t v_tid_2438_; lean_object* v_traces_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2452_; 
v_tid_2438_ = lean_ctor_get_uint64(v_traceState_2426_, sizeof(void*)*1);
v_traces_2439_ = lean_ctor_get(v_traceState_2426_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_traceState_2426_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2441_ = v_traceState_2426_;
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_traces_2439_);
lean_dec(v_traceState_2426_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v___x_2443_; lean_object* v___x_2445_; 
v___x_2443_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_2389_, v_traces_2439_);
lean_dec_ref(v_traces_2439_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2443_);
v___x_2445_ = v___x_2441_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2443_);
lean_ctor_set_uint64(v_reuseFailAlloc_2451_, sizeof(void*)*1, v_tid_2438_);
v___x_2445_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2447_; 
if (v_isShared_2437_ == 0)
{
lean_ctor_set(v___x_2436_, 4, v___x_2445_);
v___x_2447_ = v___x_2436_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_env_2427_);
lean_ctor_set(v_reuseFailAlloc_2450_, 1, v_nextMacroScope_2428_);
lean_ctor_set(v_reuseFailAlloc_2450_, 2, v_ngen_2429_);
lean_ctor_set(v_reuseFailAlloc_2450_, 3, v_auxDeclNGen_2430_);
lean_ctor_set(v_reuseFailAlloc_2450_, 4, v___x_2445_);
lean_ctor_set(v_reuseFailAlloc_2450_, 5, v_cache_2431_);
lean_ctor_set(v_reuseFailAlloc_2450_, 6, v_messages_2432_);
lean_ctor_set(v_reuseFailAlloc_2450_, 7, v_infoState_2433_);
lean_ctor_set(v_reuseFailAlloc_2450_, 8, v_snapshotTasks_2434_);
v___x_2447_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_st_ref_set(v___y_2393_, v___x_2447_);
v___x_2449_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_fst_2395_);
return v___x_2449_;
}
}
}
}
}
else
{
goto v___jp_2418_;
}
}
else
{
goto v___jp_2418_;
}
}
v___jp_2454_:
{
double v___x_2456_; double v___x_2457_; double v___x_2458_; uint8_t v___x_2459_; 
v___x_2456_ = lean_unbox_float(v_snd_2404_);
v___x_2457_ = lean_unbox_float(v_fst_2403_);
v___x_2458_ = lean_float_sub(v___x_2456_, v___x_2457_);
v___x_2459_ = lean_float_decLt(v___y_2455_, v___x_2458_);
v___y_2424_ = v___x_2459_;
goto v___jp_2423_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___boxed(lean_object* v_cls_2470_, lean_object* v_collapsed_2471_, lean_object* v_tag_2472_, lean_object* v_opts_2473_, lean_object* v_clsEnabled_2474_, lean_object* v_oldTraces_2475_, lean_object* v_msg_2476_, lean_object* v_resStartStop_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v_collapsed_boxed_2481_; uint8_t v_clsEnabled_boxed_2482_; lean_object* v_res_2483_; 
v_collapsed_boxed_2481_ = lean_unbox(v_collapsed_2471_);
v_clsEnabled_boxed_2482_ = lean_unbox(v_clsEnabled_2474_);
v_res_2483_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_2470_, v_collapsed_boxed_2481_, v_tag_2472_, v_opts_2473_, v_clsEnabled_boxed_2482_, v_oldTraces_2475_, v_msg_2476_, v_resStartStop_2477_, v___y_2478_, v___y_2479_);
lean_dec(v___y_2479_);
lean_dec_ref(v___y_2478_);
lean_dec_ref(v_opts_2473_);
return v_res_2483_;
}
}
static double _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2486_; double v___x_2487_; 
v___x_2486_ = lean_unsigned_to_nat(1000000000u);
v___x_2487_ = lean_float_of_nat(v___x_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(lean_object* v_decl_2488_, lean_object* v___x_2489_, uint8_t v___x_2490_, lean_object* v___x_2491_, lean_object* v___f_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_){
_start:
{
lean_object* v___y_2497_; lean_object* v___y_2498_; uint8_t v___y_2499_; lean_object* v___y_2510_; lean_object* v_a_2511_; lean_object* v___y_2515_; lean_object* v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2528_; lean_object* v_a_2529_; lean_object* v_options_2532_; uint8_t v_hasTrace_2533_; 
v_options_2532_ = lean_ctor_get(v___y_2493_, 2);
v_hasTrace_2533_ = lean_ctor_get_uint8(v_options_2532_, sizeof(void*)*1);
if (v_hasTrace_2533_ == 0)
{
lean_object* v_cancelTk_x3f_2534_; lean_object* v___x_2535_; 
lean_dec_ref(v___f_2492_);
lean_dec_ref(v___x_2491_);
lean_dec(v___x_2489_);
v_cancelTk_x3f_2534_ = lean_ctor_get(v___y_2493_, 12);
lean_inc(v_decl_2488_);
v___x_2535_ = l_Lean_warnIfUsesSorry(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v___x_2536_; lean_object* v_env_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
lean_dec_ref_known(v___x_2535_, 1);
v___x_2536_ = lean_st_ref_get(v___y_2494_);
v_env_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc_ref(v_env_2537_);
lean_dec(v___x_2536_);
v___x_2538_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2537_, v_options_2532_, v_decl_2488_, v_cancelTk_x3f_2534_);
v___x_2539_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2538_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; 
lean_dec(v_decl_2488_);
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
v___x_2541_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2540_, v___y_2494_);
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
v___y_2528_ = v___x_2547_;
v_a_2529_ = v_a_2542_;
goto v___jp_2527_;
}
}
}
}
else
{
lean_dec(v_decl_2488_);
return v___x_2535_;
}
}
else
{
lean_object* v_cancelTk_x3f_2550_; lean_object* v_inheritedTraceOptions_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; uint8_t v___x_2554_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v_a_2558_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v_a_2573_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v_a_2578_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2583_; lean_object* v___y_2587_; lean_object* v___y_2588_; lean_object* v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v_a_2595_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v_a_2601_; lean_object* v___y_2611_; lean_object* v___y_2612_; lean_object* v_a_2613_; lean_object* v___y_2616_; lean_object* v___y_2617_; lean_object* v_a_2618_; lean_object* v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2627_; lean_object* v___y_2628_; lean_object* v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2633_; lean_object* v___y_2634_; lean_object* v_a_2635_; 
v_cancelTk_x3f_2550_ = lean_ctor_get(v___y_2493_, 12);
v_inheritedTraceOptions_2551_ = lean_ctor_get(v___y_2493_, 13);
v___x_2552_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v___x_2489_);
v___x_2553_ = l_Lean_Name_append(v___x_2552_, v___x_2489_);
v___x_2554_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2551_, v_options_2532_, v___x_2553_);
lean_dec(v___x_2553_);
if (v___x_2554_ == 0)
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = l_Lean_trace_profiler;
v___x_2664_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2532_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
lean_dec_ref(v___f_2492_);
lean_dec_ref(v___x_2491_);
lean_dec(v___x_2489_);
lean_inc(v_decl_2488_);
v___x_2665_ = l_Lean_warnIfUsesSorry(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2665_) == 0)
{
lean_object* v___x_2666_; lean_object* v_env_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; 
lean_dec_ref_known(v___x_2665_, 1);
v___x_2666_ = lean_st_ref_get(v___y_2494_);
v_env_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc_ref(v_env_2667_);
lean_dec(v___x_2666_);
v___x_2668_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2667_, v_options_2532_, v_decl_2488_, v_cancelTk_x3f_2550_);
v___x_2669_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2668_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2669_) == 0)
{
lean_object* v_a_2670_; lean_object* v___x_2671_; 
lean_dec(v_decl_2488_);
v_a_2670_ = lean_ctor_get(v___x_2669_, 0);
lean_inc(v_a_2670_);
lean_dec_ref_known(v___x_2669_, 1);
v___x_2671_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2670_, v___y_2494_);
return v___x_2671_;
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_a_2672_ = lean_ctor_get(v___x_2669_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2669_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___x_2669_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___x_2669_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
lean_inc(v_a_2672_);
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
v___y_2510_ = v___x_2677_;
v_a_2511_ = v_a_2672_;
goto v___jp_2509_;
}
}
}
}
else
{
lean_dec(v_decl_2488_);
return v___x_2665_;
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
v___x_2569_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2489_, v___x_2490_, v___x_2491_, v_options_2532_, v___x_2554_, v___y_2556_, v___f_2492_, v___x_2568_, v___y_2493_, v___y_2494_);
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
v___x_2591_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2488_, v___y_2493_, v___y_2494_);
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
lean_dec(v_decl_2488_);
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
v___x_2603_ = lean_float_of_nat(v___y_2600_);
v___x_2604_ = lean_float_of_nat(v___x_2602_);
v___x_2605_ = lean_box_float(v___x_2603_);
v___x_2606_ = lean_box_float(v___x_2604_);
v___x_2607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2601_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v___x_2489_, v___x_2490_, v___x_2491_, v_options_2532_, v___x_2554_, v___y_2599_, v___f_2492_, v___x_2608_, v___y_2493_, v___y_2494_);
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
v___x_2631_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2631_) == 0)
{
lean_dec_ref_known(v___x_2631_, 1);
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2629_;
v_a_2613_ = v___y_2628_;
goto v___jp_2610_;
}
else
{
lean_dec_ref(v___y_2628_);
v___y_2621_ = v___y_2627_;
v___y_2622_ = v___y_2629_;
v___y_2623_ = v___x_2631_;
goto v___jp_2620_;
}
}
else
{
lean_dec(v_decl_2488_);
v___y_2611_ = v___y_2627_;
v___y_2612_ = v___y_2629_;
v_a_2613_ = v___y_2628_;
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
v___y_2628_ = v_a_2635_;
v___y_2629_ = v___y_2634_;
v___y_2630_ = v___x_2637_;
goto v___jp_2626_;
}
else
{
v___y_2627_ = v___y_2633_;
v___y_2628_ = v_a_2635_;
v___y_2629_ = v___y_2634_;
v___y_2630_ = v___x_2636_;
goto v___jp_2626_;
}
}
v___jp_2638_:
{
lean_object* v___x_2639_; lean_object* v_a_2640_; lean_object* v___x_2641_; uint8_t v___x_2642_; 
v___x_2639_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v___y_2494_);
v_a_2640_ = lean_ctor_get(v___x_2639_, 0);
lean_inc(v_a_2640_);
lean_dec_ref(v___x_2639_);
v___x_2641_ = l_Lean_trace_profiler_useHeartbeats;
v___x_2642_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2532_, v___x_2641_);
if (v___x_2642_ == 0)
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = lean_io_mono_nanos_now();
lean_inc(v_decl_2488_);
v___x_2644_ = l_Lean_warnIfUsesSorry(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; lean_object* v_env_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = lean_st_ref_get(v___y_2494_);
v_env_2646_ = lean_ctor_get(v___x_2645_, 0);
lean_inc_ref(v_env_2646_);
lean_dec(v___x_2645_);
v___x_2647_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2646_, v_options_2532_, v_decl_2488_, v_cancelTk_x3f_2550_);
v___x_2648_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2647_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2648_) == 0)
{
lean_object* v_a_2649_; lean_object* v___x_2650_; lean_object* v_a_2651_; 
lean_dec(v_decl_2488_);
v_a_2649_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2649_);
lean_dec_ref_known(v___x_2648_, 1);
v___x_2650_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2649_, v___y_2494_);
v_a_2651_ = lean_ctor_get(v___x_2650_, 0);
lean_inc(v_a_2651_);
lean_dec_ref(v___x_2650_);
v___y_2576_ = v_a_2640_;
v___y_2577_ = v___x_2643_;
v_a_2578_ = v_a_2651_;
goto v___jp_2575_;
}
else
{
lean_object* v_a_2652_; 
v_a_2652_ = lean_ctor_get(v___x_2648_, 0);
lean_inc(v_a_2652_);
lean_dec_ref_known(v___x_2648_, 1);
v___y_2593_ = v_a_2640_;
v___y_2594_ = v___x_2643_;
v_a_2595_ = v_a_2652_;
goto v___jp_2592_;
}
}
else
{
lean_dec(v_decl_2488_);
v___y_2581_ = v_a_2640_;
v___y_2582_ = v___x_2643_;
v___y_2583_ = v___x_2644_;
goto v___jp_2580_;
}
}
else
{
lean_object* v___x_2653_; lean_object* v___x_2654_; 
v___x_2653_ = lean_io_get_num_heartbeats();
lean_inc(v_decl_2488_);
v___x_2654_ = l_Lean_warnIfUsesSorry(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2654_) == 0)
{
lean_object* v___x_2655_; lean_object* v_env_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; 
lean_dec_ref_known(v___x_2654_, 1);
v___x_2655_ = lean_st_ref_get(v___y_2494_);
v_env_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_ref(v_env_2656_);
lean_dec(v___x_2655_);
v___x_2657_ = l___private_Lean_AddDecl_0__Lean_Environment_addDeclAux(v_env_2656_, v_options_2532_, v_decl_2488_, v_cancelTk_x3f_2550_);
v___x_2658_ = l_Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0___redArg(v___x_2657_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_object* v_a_2659_; lean_object* v___x_2660_; lean_object* v_a_2661_; 
lean_dec(v_decl_2488_);
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
lean_dec_ref_known(v___x_2658_, 1);
v___x_2660_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_a_2659_, v___y_2494_);
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
v___y_2616_ = v_a_2640_;
v___y_2617_ = v___x_2653_;
v_a_2618_ = v_a_2661_;
goto v___jp_2615_;
}
else
{
lean_object* v_a_2662_; 
v_a_2662_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2662_);
lean_dec_ref_known(v___x_2658_, 1);
v___y_2633_ = v_a_2640_;
v___y_2634_ = v___x_2653_;
v_a_2635_ = v_a_2662_;
goto v___jp_2632_;
}
}
else
{
lean_dec(v_decl_2488_);
v___y_2621_ = v_a_2640_;
v___y_2622_ = v___x_2653_;
v___y_2623_ = v___x_2654_;
goto v___jp_2620_;
}
}
}
}
v___jp_2496_:
{
if (v___y_2499_ == 0)
{
lean_object* v___x_2500_; 
lean_dec_ref(v___y_2497_);
v___x_2500_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2488_, v___y_2493_, v___y_2494_);
if (lean_obj_tag(v___x_2500_) == 0)
{
lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2500_);
if (v_isSharedCheck_2507_ == 0)
{
lean_object* v_unused_2508_; 
v_unused_2508_ = lean_ctor_get(v___x_2500_, 0);
lean_dec(v_unused_2508_);
v___x_2502_ = v___x_2500_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_dec(v___x_2500_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
lean_ctor_set_tag(v___x_2502_, 1);
lean_ctor_set(v___x_2502_, 0, v___y_2498_);
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v___y_2498_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
else
{
lean_dec_ref(v___y_2498_);
return v___x_2500_;
}
}
else
{
lean_dec_ref(v___y_2498_);
lean_dec(v_decl_2488_);
return v___y_2497_;
}
}
v___jp_2509_:
{
uint8_t v___x_2512_; 
v___x_2512_ = l_Lean_Exception_isInterrupt(v_a_2511_);
if (v___x_2512_ == 0)
{
uint8_t v___x_2513_; 
lean_inc_ref(v_a_2511_);
v___x_2513_ = l_Lean_Exception_isRuntime(v_a_2511_);
v___y_2497_ = v___y_2510_;
v___y_2498_ = v_a_2511_;
v___y_2499_ = v___x_2513_;
goto v___jp_2496_;
}
else
{
v___y_2497_ = v___y_2510_;
v___y_2498_ = v_a_2511_;
v___y_2499_ = v___x_2512_;
goto v___jp_2496_;
}
}
v___jp_2514_:
{
if (v___y_2517_ == 0)
{
lean_object* v___x_2518_; 
lean_dec_ref(v___y_2516_);
v___x_2518_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom(v_decl_2488_, v___y_2493_, v___y_2494_);
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
lean_ctor_set(v___x_2520_, 0, v___y_2515_);
v___x_2523_ = v___x_2520_;
goto v_reusejp_2522_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___y_2515_);
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
lean_dec_ref(v___y_2515_);
return v___x_2518_;
}
}
else
{
lean_dec_ref(v___y_2515_);
lean_dec(v_decl_2488_);
return v___y_2516_;
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
v___y_2515_ = v_a_2529_;
v___y_2516_ = v___y_2528_;
v___y_2517_ = v___x_2531_;
goto v___jp_2514_;
}
else
{
v___y_2515_ = v_a_2529_;
v___y_2516_ = v___y_2528_;
v___y_2517_ = v___x_2530_;
goto v___jp_2514_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed(lean_object* v_decl_2680_, lean_object* v___x_2681_, lean_object* v___x_2682_, lean_object* v___x_2683_, lean_object* v___f_2684_, lean_object* v___y_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
_start:
{
uint8_t v___x_7968__boxed_2688_; lean_object* v_res_2689_; 
v___x_7968__boxed_2688_ = lean_unbox(v___x_2682_);
v_res_2689_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1(v_decl_2680_, v___x_2681_, v___x_7968__boxed_2688_, v___x_2683_, v___f_2684_, v___y_2685_, v___y_2686_);
lean_dec(v___y_2686_);
lean_dec_ref(v___y_2685_);
return v_res_2689_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(lean_object* v_decl_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v_options_2698_; lean_object* v___f_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; uint8_t v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v_options_2698_ = lean_ctor_get(v_a_2695_, 2);
lean_inc(v_decl_2694_);
v___f_2699_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__0___boxed), 5, 1);
lean_closure_set(v___f_2699_, 0, v_decl_2694_);
v___x_2700_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__0));
v___x_2701_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___closed__2));
v___x_2702_ = 1;
v___x_2703_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2704_ = lean_box(v___x_2702_);
v___f_2705_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___boxed), 8, 5);
lean_closure_set(v___f_2705_, 0, v_decl_2694_);
lean_closure_set(v___f_2705_, 1, v___x_2701_);
lean_closure_set(v___f_2705_, 2, v___x_2704_);
lean_closure_set(v___f_2705_, 3, v___x_2703_);
lean_closure_set(v___f_2705_, 4, v___f_2699_);
v___x_2706_ = lean_box(0);
v___x_2707_ = l_Lean_profileitM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__3___redArg(v___x_2700_, v_options_2698_, v___f_2705_, v___x_2706_, v_a_2695_, v_a_2696_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___boxed(lean_object* v_decl_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
return v_res_2712_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(lean_object* v_00_u03b1_2713_, lean_object* v_x_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___redArg(v_x_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3___boxed(lean_object* v_00_u03b1_2719_, lean_object* v_x_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2_spec__3(v_00_u03b1_2719_, v_x_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
return v_res_2724_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(lean_object* v___y_2725_, lean_object* v_a_2726_, lean_object* v___y_2727_, lean_object* v_a_x3f_2728_){
_start:
{
lean_object* v___x_2730_; lean_object* v_env_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_st_ref_get(v___y_2725_);
v_env_2731_ = lean_ctor_get(v___x_2730_, 0);
lean_inc_ref(v_env_2731_);
lean_dec(v___x_2730_);
v___x_2732_ = l_Lean_Environment_AddConstAsyncResult_commitCheckEnv(v_a_2726_, v_env_2731_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2732_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2732_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2738_; 
if (v_isShared_2736_ == 0)
{
v___x_2738_ = v___x_2735_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v_a_2733_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2753_; 
v_a_2741_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2753_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2743_ = v___x_2732_;
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2732_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2753_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v_ref_2745_; lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2751_; 
v_ref_2745_ = lean_ctor_get(v___y_2727_, 5);
v___x_2746_ = lean_io_error_to_string(v_a_2741_);
v___x_2747_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2747_, 0, v___x_2746_);
v___x_2748_ = l_Lean_MessageData_ofFormat(v___x_2747_);
lean_inc(v_ref_2745_);
v___x_2749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2749_, 0, v_ref_2745_);
lean_ctor_set(v___x_2749_, 1, v___x_2748_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set(v___x_2743_, 0, v___x_2749_);
v___x_2751_ = v___x_2743_;
goto v_reusejp_2750_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v___x_2749_);
v___x_2751_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2750_;
}
v_reusejp_2750_:
{
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed(lean_object* v___y_2754_, lean_object* v_a_2755_, lean_object* v___y_2756_, lean_object* v_a_x3f_2757_, lean_object* v___y_2758_){
_start:
{
lean_object* v_res_2759_; 
v_res_2759_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2754_, v_a_2755_, v___y_2756_, v_a_x3f_2757_);
lean_dec(v_a_x3f_2757_);
lean_dec_ref(v___y_2756_);
lean_dec(v___y_2754_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(lean_object* v_asyncEnv_2760_, lean_object* v_a_2761_, lean_object* v_decl_2762_, lean_object* v_x_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v___x_2767_; lean_object* v_r_2768_; 
v___x_2767_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v_asyncEnv_2760_, v___y_2765_);
lean_dec_ref(v___x_2767_);
v_r_2768_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2762_, v___y_2764_, v___y_2765_);
if (lean_obj_tag(v_r_2768_) == 0)
{
lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2785_; 
v_a_2769_ = lean_ctor_get(v_r_2768_, 0);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_r_2768_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2771_ = v_r_2768_;
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v_r_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2785_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2774_; 
lean_inc(v_a_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set_tag(v___x_2771_, 1);
v___x_2774_ = v___x_2771_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_a_2769_);
v___x_2774_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; 
v___x_2775_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2765_, v_a_2761_, v___y_2764_, v___x_2774_);
lean_dec_ref(v___x_2774_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; 
v_unused_2783_ = lean_ctor_get(v___x_2775_, 0);
lean_dec(v_unused_2783_);
v___x_2777_ = v___x_2775_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_dec(v___x_2775_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
lean_ctor_set(v___x_2777_, 0, v_a_2769_);
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2769_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
else
{
lean_dec(v_a_2769_);
return v___x_2775_;
}
}
}
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v_a_2786_ = lean_ctor_get(v_r_2768_, 0);
lean_inc(v_a_2786_);
lean_dec_ref_known(v_r_2768_, 1);
v___x_2787_ = lean_box(0);
v___x_2788_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0(v___y_2765_, v_a_2761_, v___y_2764_, v___x_2787_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2795_; 
v_isSharedCheck_2795_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2795_ == 0)
{
lean_object* v_unused_2796_; 
v_unused_2796_ = lean_ctor_get(v___x_2788_, 0);
lean_dec(v_unused_2796_);
v___x_2790_ = v___x_2788_;
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v___x_2788_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2795_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2793_; 
if (v_isShared_2791_ == 0)
{
lean_ctor_set_tag(v___x_2790_, 1);
lean_ctor_set(v___x_2790_, 0, v_a_2786_);
v___x_2793_ = v___x_2790_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2794_; 
v_reuseFailAlloc_2794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2794_, 0, v_a_2786_);
v___x_2793_ = v_reuseFailAlloc_2794_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
return v___x_2793_;
}
}
}
else
{
lean_dec(v_a_2786_);
return v___x_2788_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed(lean_object* v_asyncEnv_2797_, lean_object* v_a_2798_, lean_object* v_decl_2799_, lean_object* v_x_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2(v_asyncEnv_2797_, v_a_2798_, v_decl_2799_, v_x_2800_, v___y_2801_, v___y_2802_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v_x_2800_);
return v_res_2804_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2806_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__0));
v___x_2807_ = l_Lean_stringToMessageData(v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(lean_object* v_decl_2808_, lean_object* v_x_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2813_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___closed__1);
v___x_2814_ = l_Lean_Declaration_getNames(v_decl_2808_);
v___x_2815_ = lean_box(0);
v___x_2816_ = l_List_mapTR_loop___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__0(v___x_2814_, v___x_2815_);
v___x_2817_ = l_Lean_MessageData_ofList(v___x_2816_);
v___x_2818_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2813_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2819_, 0, v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed(lean_object* v_decl_2820_, lean_object* v_x_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_, lean_object* v___y_2824_){
_start:
{
lean_object* v_res_2825_; 
v_res_2825_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1(v_decl_2820_, v_x_2821_, v___y_2822_, v___y_2823_);
lean_dec(v___y_2823_);
lean_dec_ref(v___y_2822_);
lean_dec_ref(v_x_2821_);
return v_res_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(lean_object* v_cls_2828_, lean_object* v_msg_2829_, lean_object* v___y_2830_, lean_object* v___y_2831_){
_start:
{
lean_object* v_ref_2833_; lean_object* v___x_2834_; lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2879_; 
v_ref_2833_ = lean_ctor_get(v___y_2830_, 5);
v___x_2834_ = l_Lean_addMessageContextPartial___at___00Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9_spec__12(v_msg_2829_, v___y_2830_, v___y_2831_);
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2837_ = v___x_2834_;
v_isShared_2838_ = v_isSharedCheck_2879_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2834_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2879_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v_traceState_2840_; lean_object* v_env_2841_; lean_object* v_nextMacroScope_2842_; lean_object* v_ngen_2843_; lean_object* v_auxDeclNGen_2844_; lean_object* v_cache_2845_; lean_object* v_messages_2846_; lean_object* v_infoState_2847_; lean_object* v_snapshotTasks_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2878_; 
v___x_2839_ = lean_st_ref_take(v___y_2831_);
v_traceState_2840_ = lean_ctor_get(v___x_2839_, 4);
v_env_2841_ = lean_ctor_get(v___x_2839_, 0);
v_nextMacroScope_2842_ = lean_ctor_get(v___x_2839_, 1);
v_ngen_2843_ = lean_ctor_get(v___x_2839_, 2);
v_auxDeclNGen_2844_ = lean_ctor_get(v___x_2839_, 3);
v_cache_2845_ = lean_ctor_get(v___x_2839_, 5);
v_messages_2846_ = lean_ctor_get(v___x_2839_, 6);
v_infoState_2847_ = lean_ctor_get(v___x_2839_, 7);
v_snapshotTasks_2848_ = lean_ctor_get(v___x_2839_, 8);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2850_ = v___x_2839_;
v_isShared_2851_ = v_isSharedCheck_2878_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_snapshotTasks_2848_);
lean_inc(v_infoState_2847_);
lean_inc(v_messages_2846_);
lean_inc(v_cache_2845_);
lean_inc(v_traceState_2840_);
lean_inc(v_auxDeclNGen_2844_);
lean_inc(v_ngen_2843_);
lean_inc(v_nextMacroScope_2842_);
lean_inc(v_env_2841_);
lean_dec(v___x_2839_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2878_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
uint64_t v_tid_2852_; lean_object* v_traces_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2877_; 
v_tid_2852_ = lean_ctor_get_uint64(v_traceState_2840_, sizeof(void*)*1);
v_traces_2853_ = lean_ctor_get(v_traceState_2840_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v_traceState_2840_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2855_ = v_traceState_2840_;
v_isShared_2856_ = v_isSharedCheck_2877_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_traces_2853_);
lean_dec(v_traceState_2840_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2877_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; double v___x_2858_; uint8_t v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2867_; 
v___x_2857_ = lean_box(0);
v___x_2858_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2___closed__0);
v___x_2859_ = 0;
v___x_2860_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_2861_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2861_, 0, v_cls_2828_);
lean_ctor_set(v___x_2861_, 1, v___x_2857_);
lean_ctor_set(v___x_2861_, 2, v___x_2860_);
lean_ctor_set_float(v___x_2861_, sizeof(void*)*3, v___x_2858_);
lean_ctor_set_float(v___x_2861_, sizeof(void*)*3 + 8, v___x_2858_);
lean_ctor_set_uint8(v___x_2861_, sizeof(void*)*3 + 16, v___x_2859_);
v___x_2862_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___closed__0));
v___x_2863_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2863_, 0, v___x_2861_);
lean_ctor_set(v___x_2863_, 1, v_a_2835_);
lean_ctor_set(v___x_2863_, 2, v___x_2862_);
lean_inc(v_ref_2833_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v_ref_2833_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
v___x_2865_ = l_Lean_PersistentArray_push___redArg(v_traces_2853_, v___x_2864_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 0, v___x_2865_);
v___x_2867_ = v___x_2855_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v___x_2865_);
lean_ctor_set_uint64(v_reuseFailAlloc_2876_, sizeof(void*)*1, v_tid_2852_);
v___x_2867_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
lean_object* v___x_2869_; 
if (v_isShared_2851_ == 0)
{
lean_ctor_set(v___x_2850_, 4, v___x_2867_);
v___x_2869_ = v___x_2850_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2875_; 
v_reuseFailAlloc_2875_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2875_, 0, v_env_2841_);
lean_ctor_set(v_reuseFailAlloc_2875_, 1, v_nextMacroScope_2842_);
lean_ctor_set(v_reuseFailAlloc_2875_, 2, v_ngen_2843_);
lean_ctor_set(v_reuseFailAlloc_2875_, 3, v_auxDeclNGen_2844_);
lean_ctor_set(v_reuseFailAlloc_2875_, 4, v___x_2867_);
lean_ctor_set(v_reuseFailAlloc_2875_, 5, v_cache_2845_);
lean_ctor_set(v_reuseFailAlloc_2875_, 6, v_messages_2846_);
lean_ctor_set(v_reuseFailAlloc_2875_, 7, v_infoState_2847_);
lean_ctor_set(v_reuseFailAlloc_2875_, 8, v_snapshotTasks_2848_);
v___x_2869_ = v_reuseFailAlloc_2875_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; 
v___x_2870_ = lean_st_ref_set(v___y_2831_, v___x_2869_);
v___x_2871_ = lean_box(0);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2871_);
v___x_2873_ = v___x_2837_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v___x_2871_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0___boxed(lean_object* v_cls_2880_, lean_object* v_msg_2881_, lean_object* v___y_2882_, lean_object* v___y_2883_, lean_object* v___y_2884_){
_start:
{
lean_object* v_res_2885_; 
v_res_2885_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2880_, v_msg_2881_, v___y_2882_, v___y_2883_);
lean_dec(v___y_2883_);
lean_dec_ref(v___y_2882_);
return v_res_2885_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__0));
v___x_2888_ = l_Lean_stringToMessageData(v___x_2887_);
return v___x_2888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(lean_object* v_decl_2889_, lean_object* v_cls_2890_, lean_object* v_x_2891_, lean_object* v___y_2892_, lean_object* v___y_2893_){
_start:
{
lean_object* v_options_2895_; uint8_t v_hasTrace_2896_; 
v_options_2895_ = lean_ctor_get(v___y_2892_, 2);
v_hasTrace_2896_ = lean_ctor_get_uint8(v_options_2895_, sizeof(void*)*1);
if (v_hasTrace_2896_ == 0)
{
lean_object* v___x_2897_; 
lean_dec(v_cls_2890_);
v___x_2897_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2889_, v___y_2892_, v___y_2893_);
return v___x_2897_;
}
else
{
lean_object* v_inheritedTraceOptions_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; uint8_t v___x_2901_; 
v_inheritedTraceOptions_2898_ = lean_ctor_get(v___y_2892_, 13);
v___x_2899_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2890_);
v___x_2900_ = l_Lean_Name_append(v___x_2899_, v_cls_2890_);
v___x_2901_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2898_, v_options_2895_, v___x_2900_);
lean_dec(v___x_2900_);
if (v___x_2901_ == 0)
{
lean_object* v___x_2902_; 
lean_dec(v_cls_2890_);
v___x_2902_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2889_, v___y_2892_, v___y_2893_);
return v___x_2902_;
}
else
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_2904_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2890_, v___x_2903_, v___y_2892_, v___y_2893_);
if (lean_obj_tag(v___x_2904_) == 0)
{
lean_object* v___x_2905_; 
lean_dec_ref_known(v___x_2904_, 1);
v___x_2905_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2889_, v___y_2892_, v___y_2893_);
return v___x_2905_;
}
else
{
lean_dec(v_decl_2889_);
return v___x_2904_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___boxed(lean_object* v_decl_2906_, lean_object* v_cls_2907_, lean_object* v_x_2908_, lean_object* v___y_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_){
_start:
{
lean_object* v_res_2912_; 
v_res_2912_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_2906_, v_cls_2907_, v_x_2908_, v___y_2909_, v___y_2910_);
lean_dec(v___y_2910_);
lean_dec_ref(v___y_2909_);
lean_dec(v_x_2908_);
return v_res_2912_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(lean_object* v_opt_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_options_2916_; uint8_t v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; 
v_options_2916_ = lean_ctor_get(v___y_2914_, 2);
v___x_2917_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2916_, v_opt_2913_);
v___x_2918_ = lean_box(v___x_2917_);
v___x_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2918_);
return v___x_2919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg___boxed(lean_object* v_opt_2920_, lean_object* v___y_2921_, lean_object* v___y_2922_){
_start:
{
lean_object* v_res_2923_; 
v_res_2923_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_2920_, v___y_2921_);
lean_dec_ref(v___y_2921_);
lean_dec_ref(v_opt_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT uint8_t l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(lean_object* v_x_2924_){
_start:
{
if (lean_obj_tag(v_x_2924_) == 0)
{
uint8_t v___x_2925_; 
v___x_2925_ = 1;
return v___x_2925_;
}
else
{
lean_object* v_head_2926_; lean_object* v_tail_2927_; uint8_t v___x_2928_; 
v_head_2926_ = lean_ctor_get(v_x_2924_, 0);
v_tail_2927_ = lean_ctor_get(v_x_2924_, 1);
v___x_2928_ = l_Lean_isPrivateName(v_head_2926_);
if (v___x_2928_ == 0)
{
return v___x_2928_;
}
else
{
v_x_2924_ = v_tail_2927_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2___boxed(lean_object* v_x_2930_){
_start:
{
uint8_t v_res_2931_; lean_object* v_r_2932_; 
v_res_2931_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v_x_2930_);
lean_dec(v_x_2930_);
v_r_2932_ = lean_box(v_res_2931_);
return v_r_2932_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3(void){
_start:
{
lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2938_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__2));
v___x_2939_ = l_Lean_stringToMessageData(v___x_2938_);
return v___x_2939_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5(void){
_start:
{
lean_object* v___x_2941_; lean_object* v___x_2942_; 
v___x_2941_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__4));
v___x_2942_ = l_Lean_stringToMessageData(v___x_2941_);
return v___x_2942_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7(void){
_start:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; 
v___x_2944_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__6));
v___x_2945_ = l_Lean_stringToMessageData(v___x_2944_);
return v___x_2945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(lean_object* v_decl_2946_, uint8_t v_hasTrace_2947_, uint8_t v___x_2948_, lean_object* v___x_2949_, lean_object* v_cls_2950_, lean_object* v___x_2951_, lean_object* v_____x_2952_, lean_object* v_exportedInfo_x3f_2953_, lean_object* v___y_2954_, lean_object* v___y_2955_){
_start:
{
lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v_a_2960_; lean_object* v___y_2971_; lean_object* v___y_2972_; lean_object* v_a_2973_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v_snd_3056_; lean_object* v_fst_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3184_; 
v_snd_3056_ = lean_ctor_get(v_____x_2952_, 1);
v_fst_3057_ = lean_ctor_get(v_____x_2952_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v_____x_2952_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3059_ = v_____x_2952_;
v_isShared_3060_ = v_isSharedCheck_3184_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snd_3056_);
lean_inc(v_fst_3057_);
lean_dec(v_____x_2952_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3184_;
goto v_resetjp_3058_;
}
v___jp_2957_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
v___x_2961_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2958_, v___y_2959_);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2968_ == 0)
{
lean_object* v_unused_2969_; 
v_unused_2969_ = lean_ctor_get(v___x_2961_, 0);
lean_dec(v_unused_2969_);
v___x_2963_ = v___x_2961_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_dec(v___x_2961_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
lean_ctor_set_tag(v___x_2963_, 1);
lean_ctor_set(v___x_2963_, 0, v_a_2960_);
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2960_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
v___jp_2970_:
{
lean_object* v___x_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
v___x_2974_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2971_, v___y_2972_);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2974_);
if (v_isSharedCheck_2981_ == 0)
{
lean_object* v_unused_2982_; 
v_unused_2982_ = lean_ctor_get(v___x_2974_, 0);
lean_dec(v_unused_2982_);
v___x_2976_ = v___x_2974_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_dec(v___x_2974_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v_a_2973_);
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2973_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
v___jp_2983_:
{
lean_object* v___x_2994_; 
lean_inc_ref(v___y_2989_);
v___x_2994_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_2990_, v___y_2989_, v___y_2987_, v___y_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3041_; 
lean_dec_ref_known(v___x_2994_, 1);
lean_inc_ref(v___y_2984_);
v___x_2995_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2984_, v___y_2985_);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2995_);
if (v_isSharedCheck_3041_ == 0)
{
lean_object* v_unused_3042_; 
v_unused_3042_ = lean_ctor_get(v___x_2995_, 0);
lean_dec(v_unused_3042_);
v___x_2997_ = v___x_2995_;
v_isShared_2998_ = v_isSharedCheck_3041_;
goto v_resetjp_2996_;
}
else
{
lean_dec(v___x_2995_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3041_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v_options_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; 
v_options_2999_ = lean_ctor_get(v___y_2992_, 2);
v___x_3000_ = l_Lean_Elab_async;
v___x_3001_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_2999_, v___x_3000_);
if (v___x_3001_ == 0)
{
lean_object* v___x_3002_; lean_object* v_r_3003_; 
lean_del_object(v___x_2997_);
lean_dec_ref(v___y_2991_);
lean_dec_ref(v___y_2986_);
v___x_3002_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_2989_, v___y_2985_);
lean_dec_ref(v___x_3002_);
v_r_3003_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_2946_, v___y_2992_, v___y_2985_);
if (lean_obj_tag(v_r_3003_) == 0)
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3013_; 
v_a_3004_ = lean_ctor_get(v_r_3003_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v_r_3003_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3006_ = v_r_3003_;
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v_r_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3013_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
lean_inc(v_a_3004_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set_tag(v___x_3006_, 1);
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
lean_object* v___x_3010_; 
v___x_3010_ = lean_apply_2(v___y_2988_, v___x_3009_, lean_box(0));
if (lean_obj_tag(v___x_3010_) == 0)
{
lean_dec_ref_known(v___x_3010_, 1);
v___y_2971_ = v___y_2984_;
v___y_2972_ = v___y_2985_;
v_a_2973_ = v_a_3004_;
goto v___jp_2970_;
}
else
{
lean_object* v_a_3011_; 
lean_dec(v_a_3004_);
v_a_3011_ = lean_ctor_get(v___x_3010_, 0);
lean_inc(v_a_3011_);
lean_dec_ref_known(v___x_3010_, 1);
v___y_2958_ = v___y_2984_;
v___y_2959_ = v___y_2985_;
v_a_2960_ = v_a_3011_;
goto v___jp_2957_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; 
v_a_3014_ = lean_ctor_get(v_r_3003_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v_r_3003_, 1);
v___x_3015_ = lean_box(0);
v___x_3016_ = lean_apply_2(v___y_2988_, v___x_3015_, lean_box(0));
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_dec_ref_known(v___x_3016_, 1);
v___y_2958_ = v___y_2984_;
v___y_2959_ = v___y_2985_;
v_a_2960_ = v_a_3014_;
goto v___jp_2957_;
}
else
{
lean_object* v_a_3017_; 
lean_dec(v_a_3014_);
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___y_2958_ = v___y_2984_;
v___y_2959_ = v___y_2985_;
v_a_2960_ = v_a_3017_;
goto v___jp_2957_;
}
}
}
else
{
lean_object* v___x_3018_; lean_object* v___x_3020_; 
lean_dec_ref(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2984_);
lean_dec(v_decl_2946_);
v___x_3018_ = l_IO_CancelToken_new();
if (v_isShared_2998_ == 0)
{
lean_ctor_set_tag(v___x_2997_, 1);
lean_ctor_set(v___x_2997_, 0, v___x_3018_);
v___x_3020_ = v___x_2997_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v___x_3018_);
v___x_3020_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; lean_object* v___x_3024_; 
v___x_3021_ = lean_unsigned_to_nat(0u);
v___x_3022_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3023_ = l_Lean_Name_toString(v___x_3022_, v_hasTrace_2947_);
lean_inc_ref(v___x_3020_);
v___x_3024_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_2991_, v___x_3020_, v___x_3023_, v___y_2992_, v___y_2985_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v_checked_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; lean_object* v___x_3031_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
v_checked_3026_ = lean_ctor_get(v___y_2986_, 2);
lean_inc_ref(v_checked_3026_);
lean_dec_ref(v___y_2986_);
v___x_3027_ = lean_io_map_task(v_a_3025_, v_checked_3026_, v___x_3021_, v___x_2948_);
v___x_3028_ = lean_box(0);
v___x_3029_ = lean_box(2);
v___x_3030_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3030_, 0, v___x_3028_);
lean_ctor_set(v___x_3030_, 1, v___x_3029_);
lean_ctor_set(v___x_3030_, 2, v___x_3020_);
lean_ctor_set(v___x_3030_, 3, v___x_3027_);
v___x_3031_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3030_, v___y_2985_);
return v___x_3031_;
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_dec_ref(v___x_3020_);
lean_dec_ref(v___y_2986_);
v_a_3032_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3024_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3024_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v___y_2991_);
lean_dec_ref(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v___y_2984_);
lean_dec(v_decl_2946_);
v_a_3043_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3045_ = v___x_2994_;
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_2994_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3055_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v_ref_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3053_; 
v_ref_3047_ = lean_ctor_get(v___y_2992_, 5);
v___x_3048_ = lean_io_error_to_string(v_a_3043_);
v___x_3049_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
v___x_3050_ = l_Lean_MessageData_ofFormat(v___x_3049_);
lean_inc(v_ref_3047_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v_ref_3047_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
if (v_isShared_3046_ == 0)
{
lean_ctor_set(v___x_3045_, 0, v___x_3051_);
v___x_3053_ = v___x_3045_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v___x_3051_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
v_resetjp_3058_:
{
lean_object* v_fst_3061_; lean_object* v_snd_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3183_; 
v_fst_3061_ = lean_ctor_get(v_snd_3056_, 0);
v_snd_3062_ = lean_ctor_get(v_snd_3056_, 1);
v_isSharedCheck_3183_ = !lean_is_exclusive(v_snd_3056_);
if (v_isSharedCheck_3183_ == 0)
{
v___x_3064_ = v_snd_3056_;
v_isShared_3065_ = v_isSharedCheck_3183_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_snd_3062_);
lean_inc(v_fst_3061_);
lean_dec(v_snd_3056_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3183_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; lean_object* v___y_3073_; lean_object* v_exportedInfo_x3f_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3141_; lean_object* v___y_3142_; lean_object* v___x_3173_; lean_object* v_env_3174_; uint8_t v___x_3175_; 
v___x_3173_ = lean_st_ref_get(v___y_2955_);
v_env_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc_ref(v_env_3174_);
lean_dec(v___x_3173_);
v___x_3175_ = l_Lean_Environment_containsOnBranch(v_env_3174_, v_fst_3057_);
lean_dec_ref(v_env_3174_);
if (v___x_3175_ == 0)
{
lean_del_object(v___x_3059_);
v___y_3141_ = v___y_2954_;
v___y_3142_ = v___y_2955_;
goto v___jp_3140_;
}
else
{
lean_object* v___x_3176_; lean_object* v_env_3177_; lean_object* v___x_3178_; lean_object* v___x_3180_; 
lean_del_object(v___x_3064_);
lean_dec(v_snd_3062_);
lean_dec(v_fst_3061_);
lean_dec(v_exportedInfo_x3f_2953_);
lean_dec(v___x_2951_);
lean_dec(v_cls_2950_);
lean_dec_ref(v___x_2949_);
lean_dec(v_decl_2946_);
v___x_3176_ = lean_st_ref_get(v___y_2955_);
v_env_3177_ = lean_ctor_get(v___x_3176_, 0);
lean_inc_ref(v_env_3177_);
lean_dec(v___x_3176_);
v___x_3178_ = lean_elab_environment_to_kernel_env(v_env_3177_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set_tag(v___x_3059_, 1);
lean_ctor_set(v___x_3059_, 1, v_fst_3057_);
lean_ctor_set(v___x_3059_, 0, v___x_3178_);
v___x_3180_ = v___x_3059_;
goto v_reusejp_3179_;
}
else
{
lean_object* v_reuseFailAlloc_3182_; 
v_reuseFailAlloc_3182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3182_, 0, v___x_3178_);
lean_ctor_set(v_reuseFailAlloc_3182_, 1, v_fst_3057_);
v___x_3180_ = v_reuseFailAlloc_3182_;
goto v_reusejp_3179_;
}
v_reusejp_3179_:
{
lean_object* v___x_3181_; 
v___x_3181_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3180_, v___y_2954_, v___y_2955_);
return v___x_3181_;
}
}
v___jp_3066_:
{
uint8_t v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = lean_unbox(v_snd_3062_);
lean_dec(v_snd_3062_);
lean_inc_ref(v___y_3069_);
v___x_3075_ = l_Lean_Environment_addConstAsync(v___y_3069_, v_fst_3057_, v___x_3074_, v___y_3073_, v___x_2948_, v_hasTrace_2947_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; lean_object* v_mainEnv_3077_; lean_object* v_asyncEnv_3078_; lean_object* v___f_3079_; lean_object* v___f_3080_; lean_object* v___x_3081_; 
lean_del_object(v___x_3064_);
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc_n(v_a_3076_, 3);
lean_dec_ref_known(v___x_3075_, 1);
v_mainEnv_3077_ = lean_ctor_get(v_a_3076_, 0);
lean_inc_ref(v_mainEnv_3077_);
v_asyncEnv_3078_ = lean_ctor_get(v_a_3076_, 1);
lean_inc_ref_n(v_asyncEnv_3078_, 2);
lean_inc_ref(v___y_3067_);
lean_inc(v___y_3068_);
v___f_3079_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3079_, 0, v___y_3068_);
lean_closure_set(v___f_3079_, 1, v_a_3076_);
lean_closure_set(v___f_3079_, 2, v___y_3067_);
lean_inc(v_decl_2946_);
v___f_3080_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3080_, 0, v_asyncEnv_3078_);
lean_closure_set(v___f_3080_, 1, v_a_3076_);
lean_closure_set(v___f_3080_, 2, v_decl_2946_);
v___x_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3081_, 0, v_fst_3061_);
if (lean_obj_tag(v___y_3071_) == 0)
{
lean_inc_ref(v___x_3081_);
v___y_2984_ = v_mainEnv_3077_;
v___y_2985_ = v___y_3070_;
v___y_2986_ = v___y_3069_;
v___y_2987_ = v___x_3081_;
v___y_2988_ = v___f_3079_;
v___y_2989_ = v_asyncEnv_3078_;
v___y_2990_ = v_a_3076_;
v___y_2991_ = v___f_3080_;
v___y_2992_ = v___y_3072_;
v___y_2993_ = v___x_3081_;
goto v___jp_2983_;
}
else
{
v___y_2984_ = v_mainEnv_3077_;
v___y_2985_ = v___y_3070_;
v___y_2986_ = v___y_3069_;
v___y_2987_ = v___x_3081_;
v___y_2988_ = v___f_3079_;
v___y_2989_ = v_asyncEnv_3078_;
v___y_2990_ = v_a_3076_;
v___y_2991_ = v___f_3080_;
v___y_2992_ = v___y_3072_;
v___y_2993_ = v___y_3071_;
goto v___jp_2983_;
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v___y_3071_);
lean_dec_ref(v___y_3069_);
lean_dec(v_fst_3061_);
lean_dec(v_decl_2946_);
v_a_3082_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3084_ = v___x_3075_;
v_isShared_3085_ = v_isSharedCheck_3096_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_3075_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3096_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v_ref_3086_; lean_object* v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3091_; 
v_ref_3086_ = lean_ctor_get(v___y_3072_, 5);
v___x_3087_ = lean_io_error_to_string(v_a_3082_);
v___x_3088_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3088_, 0, v___x_3087_);
v___x_3089_ = l_Lean_MessageData_ofFormat(v___x_3088_);
lean_inc(v_ref_3086_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 1, v___x_3089_);
lean_ctor_set(v___x_3064_, 0, v_ref_3086_);
v___x_3091_ = v___x_3064_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_ref_3086_);
lean_ctor_set(v_reuseFailAlloc_3095_, 1, v___x_3089_);
v___x_3091_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
lean_object* v___x_3093_; 
if (v_isShared_3085_ == 0)
{
lean_ctor_set(v___x_3084_, 0, v___x_3091_);
v___x_3093_ = v___x_3084_;
goto v_reusejp_3092_;
}
else
{
lean_object* v_reuseFailAlloc_3094_; 
v_reuseFailAlloc_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3094_, 0, v___x_3091_);
v___x_3093_ = v_reuseFailAlloc_3094_;
goto v_reusejp_3092_;
}
v_reusejp_3092_:
{
return v___x_3093_;
}
}
}
}
}
v___jp_3097_:
{
lean_object* v___x_3101_; 
v___x_3101_ = lean_st_ref_get(v___y_3100_);
if (lean_obj_tag(v_exportedInfo_x3f_3098_) == 0)
{
lean_object* v_env_3102_; lean_object* v___x_3103_; 
v_env_3102_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_env_3102_);
lean_dec(v___x_3101_);
v___x_3103_ = lean_box(0);
v___y_3067_ = v___y_3099_;
v___y_3068_ = v___y_3100_;
v___y_3069_ = v_env_3102_;
v___y_3070_ = v___y_3100_;
v___y_3071_ = v_exportedInfo_x3f_3098_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___x_3103_;
goto v___jp_3066_;
}
else
{
lean_object* v_env_3104_; lean_object* v_val_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v_env_3104_ = lean_ctor_get(v___x_3101_, 0);
lean_inc_ref(v_env_3104_);
lean_dec(v___x_3101_);
v_val_3105_ = lean_ctor_get(v_exportedInfo_x3f_3098_, 0);
v___x_3106_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3105_);
v___x_3107_ = lean_box(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___y_3067_ = v___y_3099_;
v___y_3068_ = v___y_3100_;
v___y_3069_ = v_env_3104_;
v___y_3070_ = v___y_3100_;
v___y_3071_ = v_exportedInfo_x3f_3098_;
v___y_3072_ = v___y_3099_;
v___y_3073_ = v___x_3108_;
goto v___jp_3066_;
}
}
v___jp_3109_:
{
lean_object* v___x_3112_; 
lean_inc(v_fst_3061_);
v___x_3112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3112_, 0, v_fst_3061_);
v_exportedInfo_x3f_3098_ = v___x_3112_;
v___y_3099_ = v___y_3110_;
v___y_3100_ = v___y_3111_;
goto v___jp_3097_;
}
v___jp_3113_:
{
lean_object* v___x_3116_; 
lean_inc(v_fst_3061_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v_fst_3061_);
v_exportedInfo_x3f_3098_ = v___x_3116_;
v___y_3099_ = v___y_3114_;
v___y_3100_ = v___y_3115_;
goto v___jp_3097_;
}
v___jp_3117_:
{
lean_object* v___x_3120_; lean_object* v_env_3121_; lean_object* v_nextMacroScope_3122_; lean_object* v_ngen_3123_; lean_object* v_auxDeclNGen_3124_; lean_object* v_traceState_3125_; lean_object* v_messages_3126_; lean_object* v_infoState_3127_; lean_object* v_snapshotTasks_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3138_; 
v___x_3120_ = lean_st_ref_take(v___y_3118_);
v_env_3121_ = lean_ctor_get(v___x_3120_, 0);
v_nextMacroScope_3122_ = lean_ctor_get(v___x_3120_, 1);
v_ngen_3123_ = lean_ctor_get(v___x_3120_, 2);
v_auxDeclNGen_3124_ = lean_ctor_get(v___x_3120_, 3);
v_traceState_3125_ = lean_ctor_get(v___x_3120_, 4);
v_messages_3126_ = lean_ctor_get(v___x_3120_, 6);
v_infoState_3127_ = lean_ctor_get(v___x_3120_, 7);
v_snapshotTasks_3128_ = lean_ctor_get(v___x_3120_, 8);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3138_ == 0)
{
lean_object* v_unused_3139_; 
v_unused_3139_ = lean_ctor_get(v___x_3120_, 5);
lean_dec(v_unused_3139_);
v___x_3130_ = v___x_3120_;
v_isShared_3131_ = v_isSharedCheck_3138_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_snapshotTasks_3128_);
lean_inc(v_infoState_3127_);
lean_inc(v_messages_3126_);
lean_inc(v_traceState_3125_);
lean_inc(v_auxDeclNGen_3124_);
lean_inc(v_ngen_3123_);
lean_inc(v_nextMacroScope_3122_);
lean_inc(v_env_3121_);
lean_dec(v___x_3120_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3138_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3135_; 
v___x_3132_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3062_);
lean_inc(v_fst_3057_);
v___x_3133_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3132_, v_env_3121_, v_fst_3057_, v_snd_3062_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 5, v___x_2949_);
lean_ctor_set(v___x_3130_, 0, v___x_3133_);
v___x_3135_ = v___x_3130_;
goto v_reusejp_3134_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3133_);
lean_ctor_set(v_reuseFailAlloc_3137_, 1, v_nextMacroScope_3122_);
lean_ctor_set(v_reuseFailAlloc_3137_, 2, v_ngen_3123_);
lean_ctor_set(v_reuseFailAlloc_3137_, 3, v_auxDeclNGen_3124_);
lean_ctor_set(v_reuseFailAlloc_3137_, 4, v_traceState_3125_);
lean_ctor_set(v_reuseFailAlloc_3137_, 5, v___x_2949_);
lean_ctor_set(v_reuseFailAlloc_3137_, 6, v_messages_3126_);
lean_ctor_set(v_reuseFailAlloc_3137_, 7, v_infoState_3127_);
lean_ctor_set(v_reuseFailAlloc_3137_, 8, v_snapshotTasks_3128_);
v___x_3135_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3134_;
}
v_reusejp_3134_:
{
lean_object* v___x_3136_; 
v___x_3136_ = lean_st_ref_set(v___y_3118_, v___x_3135_);
v_exportedInfo_x3f_3098_ = v_exportedInfo_x3f_2953_;
v___y_3099_ = v___y_3119_;
v___y_3100_ = v___y_3118_;
goto v___jp_3097_;
}
}
}
v___jp_3140_:
{
lean_object* v___x_3143_; uint8_t v___x_3144_; 
lean_inc(v_decl_2946_);
v___x_3143_ = l_Lean_Declaration_getTopLevelNames(v_decl_2946_);
v___x_3144_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3143_);
lean_dec(v___x_3143_);
if (v___x_3144_ == 0)
{
lean_dec(v___x_2951_);
if (lean_obj_tag(v_exportedInfo_x3f_2953_) == 0)
{
if (v___x_2948_ == 0)
{
lean_object* v_options_3145_; uint8_t v_hasTrace_3146_; 
lean_dec_ref(v___x_2949_);
v_options_3145_ = lean_ctor_get(v___y_3141_, 2);
v_hasTrace_3146_ = lean_ctor_get_uint8(v_options_3145_, sizeof(void*)*1);
if (v_hasTrace_3146_ == 0)
{
lean_dec(v_cls_2950_);
v___y_3110_ = v___y_3141_;
v___y_3111_ = v___y_3142_;
goto v___jp_3109_;
}
else
{
lean_object* v_inheritedTraceOptions_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; uint8_t v___x_3150_; 
v_inheritedTraceOptions_3147_ = lean_ctor_get(v___y_3141_, 13);
v___x_3148_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2950_);
v___x_3149_ = l_Lean_Name_append(v___x_3148_, v_cls_2950_);
v___x_3150_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3147_, v_options_3145_, v___x_3149_);
lean_dec(v___x_3149_);
if (v___x_3150_ == 0)
{
lean_dec(v_cls_2950_);
v___y_3110_ = v___y_3141_;
v___y_3111_ = v___y_3142_;
goto v___jp_3109_;
}
else
{
lean_object* v___x_3151_; lean_object* v___x_3152_; 
v___x_3151_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3152_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2950_, v___x_3151_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3152_) == 0)
{
lean_dec_ref_known(v___x_3152_, 1);
v___y_3110_ = v___y_3141_;
v___y_3111_ = v___y_3142_;
goto v___jp_3109_;
}
else
{
lean_del_object(v___x_3064_);
lean_dec(v_snd_3062_);
lean_dec(v_fst_3061_);
lean_dec(v_fst_3057_);
lean_dec(v_decl_2946_);
return v___x_3152_;
}
}
}
}
else
{
lean_dec(v_cls_2950_);
v___y_3118_ = v___y_3142_;
v___y_3119_ = v___y_3141_;
goto v___jp_3117_;
}
}
else
{
lean_dec(v_cls_2950_);
v___y_3118_ = v___y_3142_;
v___y_3119_ = v___y_3141_;
goto v___jp_3117_;
}
}
else
{
lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v_a_3155_; uint8_t v___x_3156_; 
lean_dec(v_exportedInfo_x3f_2953_);
lean_dec_ref(v___x_2949_);
v___x_3153_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3154_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3153_, v___y_3141_);
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref(v___x_3154_);
v___x_3156_ = lean_unbox(v_a_3155_);
lean_dec(v_a_3155_);
if (v___x_3156_ == 0)
{
lean_object* v_options_3157_; uint8_t v_hasTrace_3158_; 
v_options_3157_ = lean_ctor_get(v___y_3141_, 2);
v_hasTrace_3158_ = lean_ctor_get_uint8(v_options_3157_, sizeof(void*)*1);
if (v_hasTrace_3158_ == 0)
{
lean_dec(v_cls_2950_);
v_exportedInfo_x3f_3098_ = v___x_2951_;
v___y_3099_ = v___y_3141_;
v___y_3100_ = v___y_3142_;
goto v___jp_3097_;
}
else
{
lean_object* v_inheritedTraceOptions_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; uint8_t v___x_3162_; 
v_inheritedTraceOptions_3159_ = lean_ctor_get(v___y_3141_, 13);
v___x_3160_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2950_);
v___x_3161_ = l_Lean_Name_append(v___x_3160_, v_cls_2950_);
v___x_3162_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3159_, v_options_3157_, v___x_3161_);
lean_dec(v___x_3161_);
if (v___x_3162_ == 0)
{
lean_dec(v_cls_2950_);
v_exportedInfo_x3f_3098_ = v___x_2951_;
v___y_3099_ = v___y_3141_;
v___y_3100_ = v___y_3142_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3163_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3164_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2950_, v___x_3163_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_dec_ref_known(v___x_3164_, 1);
v_exportedInfo_x3f_3098_ = v___x_2951_;
v___y_3099_ = v___y_3141_;
v___y_3100_ = v___y_3142_;
goto v___jp_3097_;
}
else
{
lean_del_object(v___x_3064_);
lean_dec(v_snd_3062_);
lean_dec(v_fst_3061_);
lean_dec(v_fst_3057_);
lean_dec(v___x_2951_);
lean_dec(v_decl_2946_);
return v___x_3164_;
}
}
}
}
else
{
lean_object* v_options_3165_; uint8_t v_hasTrace_3166_; 
lean_dec(v___x_2951_);
v_options_3165_ = lean_ctor_get(v___y_3141_, 2);
v_hasTrace_3166_ = lean_ctor_get_uint8(v_options_3165_, sizeof(void*)*1);
if (v_hasTrace_3166_ == 0)
{
lean_dec(v_cls_2950_);
v___y_3114_ = v___y_3141_;
v___y_3115_ = v___y_3142_;
goto v___jp_3113_;
}
else
{
lean_object* v_inheritedTraceOptions_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; uint8_t v___x_3170_; 
v_inheritedTraceOptions_3167_ = lean_ctor_get(v___y_3141_, 13);
v___x_3168_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_2950_);
v___x_3169_ = l_Lean_Name_append(v___x_3168_, v_cls_2950_);
v___x_3170_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3167_, v_options_3165_, v___x_3169_);
lean_dec(v___x_3169_);
if (v___x_3170_ == 0)
{
lean_dec(v_cls_2950_);
v___y_3114_ = v___y_3141_;
v___y_3115_ = v___y_3142_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3172_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_2950_, v___x_3171_, v___y_3141_, v___y_3142_);
if (lean_obj_tag(v___x_3172_) == 0)
{
lean_dec_ref_known(v___x_3172_, 1);
v___y_3114_ = v___y_3141_;
v___y_3115_ = v___y_3142_;
goto v___jp_3113_;
}
else
{
lean_del_object(v___x_3064_);
lean_dec(v_snd_3062_);
lean_dec(v_fst_3061_);
lean_dec(v_fst_3057_);
lean_dec(v_decl_2946_);
return v___x_3172_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed(lean_object* v_decl_3185_, lean_object* v_hasTrace_3186_, lean_object* v___x_3187_, lean_object* v___x_3188_, lean_object* v_cls_3189_, lean_object* v___x_3190_, lean_object* v_____x_3191_, lean_object* v_exportedInfo_x3f_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
uint8_t v_hasTrace_boxed_3196_; uint8_t v___x_62744__boxed_3197_; lean_object* v_res_3198_; 
v_hasTrace_boxed_3196_ = lean_unbox(v_hasTrace_3186_);
v___x_62744__boxed_3197_ = lean_unbox(v___x_3187_);
v_res_3198_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3185_, v_hasTrace_boxed_3196_, v___x_62744__boxed_3197_, v___x_3188_, v_cls_3189_, v___x_3190_, v_____x_3191_, v_exportedInfo_x3f_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
return v_res_3198_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1(void){
_start:
{
lean_object* v___x_3200_; lean_object* v___x_3201_; 
v___x_3200_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__0));
v___x_3201_ = l_Lean_stringToMessageData(v___x_3200_);
return v___x_3201_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3(void){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__2));
v___x_3204_ = l_Lean_stringToMessageData(v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(lean_object* v___f_3205_, lean_object* v_cls_3206_, lean_object* v___x_3207_, uint8_t v___x_3208_, uint8_t v_forceExpose_3209_, lean_object* v_defn_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_){
_start:
{
lean_object* v_exportedInfo_x3f_3215_; lean_object* v___y_3216_; lean_object* v___y_3217_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v_env_3253_; lean_object* v_env_3254_; 
v___x_3236_ = lean_st_ref_get(v___y_3212_);
v___x_3237_ = lean_st_ref_get(v___y_3212_);
v_env_3253_ = lean_ctor_get(v___x_3236_, 0);
lean_inc_ref(v_env_3253_);
lean_dec(v___x_3236_);
v_env_3254_ = lean_ctor_get(v___x_3237_, 0);
lean_inc_ref(v_env_3254_);
lean_dec(v___x_3237_);
if (v_forceExpose_3209_ == 0)
{
goto v___jp_3255_;
}
else
{
if (v___x_3208_ == 0)
{
lean_dec_ref(v_env_3254_);
lean_dec_ref(v_env_3253_);
lean_dec(v_cls_3206_);
v_exportedInfo_x3f_3215_ = v___x_3207_;
v___y_3216_ = v___y_3211_;
v___y_3217_ = v___y_3212_;
goto v___jp_3214_;
}
else
{
goto v___jp_3255_;
}
}
v___jp_3214_:
{
lean_object* v_toConstantVal_3218_; lean_object* v_name_3219_; lean_object* v___x_3220_; uint8_t v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_toConstantVal_3218_ = lean_ctor_get(v_defn_3210_, 0);
v_name_3219_ = lean_ctor_get(v_toConstantVal_3218_, 0);
lean_inc(v_name_3219_);
v___x_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3220_, 0, v_defn_3210_);
v___x_3221_ = 0;
v___x_3222_ = lean_box(v___x_3221_);
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3220_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v_name_3219_);
lean_ctor_set(v___x_3224_, 1, v___x_3223_);
lean_inc(v___y_3217_);
lean_inc_ref(v___y_3216_);
v___x_3225_ = lean_apply_5(v___f_3205_, v___x_3224_, v_exportedInfo_x3f_3215_, v___y_3216_, v___y_3217_, lean_box(0));
return v___x_3225_;
}
v___jp_3226_:
{
lean_object* v_toConstantVal_3229_; uint8_t v_safety_3230_; uint8_t v___x_3231_; uint8_t v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; 
v_toConstantVal_3229_ = lean_ctor_get(v_defn_3210_, 0);
v_safety_3230_ = lean_ctor_get_uint8(v_defn_3210_, sizeof(void*)*4);
v___x_3231_ = 0;
v___x_3232_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3230_, v___x_3231_);
lean_inc_ref(v_toConstantVal_3229_);
v___x_3233_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3233_, 0, v_toConstantVal_3229_);
lean_ctor_set_uint8(v___x_3233_, sizeof(void*)*1, v___x_3232_);
v___x_3234_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3233_);
v___x_3235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3235_, 0, v___x_3234_);
v_exportedInfo_x3f_3215_ = v___x_3235_;
v___y_3216_ = v___y_3227_;
v___y_3217_ = v___y_3228_;
goto v___jp_3214_;
}
v___jp_3238_:
{
lean_object* v_options_3239_; uint8_t v_hasTrace_3240_; 
v_options_3239_ = lean_ctor_get(v___y_3211_, 2);
v_hasTrace_3240_ = lean_ctor_get_uint8(v_options_3239_, sizeof(void*)*1);
if (v_hasTrace_3240_ == 0)
{
lean_dec(v_cls_3206_);
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
goto v___jp_3226_;
}
else
{
lean_object* v_inheritedTraceOptions_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; uint8_t v___x_3244_; 
v_inheritedTraceOptions_3241_ = lean_ctor_get(v___y_3211_, 13);
v___x_3242_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3206_);
v___x_3243_ = l_Lean_Name_append(v___x_3242_, v_cls_3206_);
v___x_3244_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3241_, v_options_3239_, v___x_3243_);
lean_dec(v___x_3243_);
if (v___x_3244_ == 0)
{
lean_dec(v_cls_3206_);
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
goto v___jp_3226_;
}
else
{
lean_object* v_toConstantVal_3245_; lean_object* v_name_3246_; lean_object* v___x_3247_; lean_object* v___x_3248_; lean_object* v___x_3249_; lean_object* v___x_3250_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v_toConstantVal_3245_ = lean_ctor_get(v_defn_3210_, 0);
v_name_3246_ = lean_ctor_get(v_toConstantVal_3245_, 0);
v___x_3247_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3246_);
v___x_3248_ = l_Lean_MessageData_ofName(v_name_3246_);
v___x_3249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3249_, 0, v___x_3247_);
lean_ctor_set(v___x_3249_, 1, v___x_3248_);
v___x_3250_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3249_);
lean_ctor_set(v___x_3251_, 1, v___x_3250_);
v___x_3252_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3206_, v___x_3251_, v___y_3211_, v___y_3212_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_dec_ref_known(v___x_3252_, 1);
v___y_3227_ = v___y_3211_;
v___y_3228_ = v___y_3212_;
goto v___jp_3226_;
}
else
{
lean_dec_ref(v_defn_3210_);
lean_dec_ref(v___f_3205_);
return v___x_3252_;
}
}
}
}
v___jp_3255_:
{
lean_object* v___x_3256_; uint8_t v_isModule_3257_; 
v___x_3256_ = l_Lean_Environment_header(v_env_3253_);
lean_dec_ref(v_env_3253_);
v_isModule_3257_ = lean_ctor_get_uint8(v___x_3256_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3256_);
if (v_isModule_3257_ == 0)
{
lean_dec_ref(v_env_3254_);
lean_dec(v_cls_3206_);
v_exportedInfo_x3f_3215_ = v___x_3207_;
v___y_3216_ = v___y_3211_;
v___y_3217_ = v___y_3212_;
goto v___jp_3214_;
}
else
{
uint8_t v_isExporting_3258_; 
v_isExporting_3258_ = lean_ctor_get_uint8(v_env_3254_, sizeof(void*)*8);
lean_dec_ref(v_env_3254_);
if (v_isExporting_3258_ == 0)
{
lean_dec(v___x_3207_);
goto v___jp_3238_;
}
else
{
if (v___x_3208_ == 0)
{
lean_dec(v_cls_3206_);
v_exportedInfo_x3f_3215_ = v___x_3207_;
v___y_3216_ = v___y_3211_;
v___y_3217_ = v___y_3212_;
goto v___jp_3214_;
}
else
{
lean_dec(v___x_3207_);
goto v___jp_3238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___boxed(lean_object* v___f_3259_, lean_object* v_cls_3260_, lean_object* v___x_3261_, lean_object* v___x_3262_, lean_object* v_forceExpose_3263_, lean_object* v_defn_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
uint8_t v___x_63218__boxed_3268_; uint8_t v_forceExpose_boxed_3269_; lean_object* v_res_3270_; 
v___x_63218__boxed_3268_ = lean_unbox(v___x_3262_);
v_forceExpose_boxed_3269_ = lean_unbox(v_forceExpose_3263_);
v_res_3270_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_3259_, v_cls_3260_, v___x_3261_, v___x_63218__boxed_3268_, v_forceExpose_boxed_3269_, v_defn_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
return v_res_3270_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(lean_object* v_val_3271_, lean_object* v___f_3272_, lean_object* v_____r_3273_, lean_object* v_exportedInfo_x3f_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_toConstantVal_3278_; lean_object* v_name_3279_; lean_object* v___x_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; 
v_toConstantVal_3278_ = lean_ctor_get(v_val_3271_, 0);
v_name_3279_ = lean_ctor_get(v_toConstantVal_3278_, 0);
lean_inc(v_name_3279_);
v___x_3280_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_3280_, 0, v_val_3271_);
v___x_3281_ = 1;
v___x_3282_ = lean_box(v___x_3281_);
v___x_3283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3280_);
lean_ctor_set(v___x_3283_, 1, v___x_3282_);
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v_name_3279_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
lean_inc(v___y_3276_);
lean_inc_ref(v___y_3275_);
v___x_3285_ = lean_apply_5(v___f_3272_, v___x_3284_, v_exportedInfo_x3f_3274_, v___y_3275_, v___y_3276_, lean_box(0));
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed(lean_object* v_val_3286_, lean_object* v___f_3287_, lean_object* v_____r_3288_, lean_object* v_exportedInfo_x3f_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5(v_val_3286_, v___f_3287_, v_____r_3288_, v_exportedInfo_x3f_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(lean_object* v_val_3294_, uint8_t v___x_3295_, lean_object* v___f_3296_, lean_object* v_____r_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v_toConstantVal_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3306_; 
v_toConstantVal_3301_ = lean_ctor_get(v_val_3294_, 0);
lean_inc_ref(v_toConstantVal_3301_);
v___x_3302_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3302_, 0, v_toConstantVal_3301_);
lean_ctor_set_uint8(v___x_3302_, sizeof(void*)*1, v___x_3295_);
v___x_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3303_, 0, v___x_3302_);
v___x_3304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3304_, 0, v___x_3303_);
v___x_3305_ = lean_box(0);
lean_inc(v___y_3299_);
lean_inc_ref(v___y_3298_);
v___x_3306_ = lean_apply_5(v___f_3296_, v___x_3305_, v___x_3304_, v___y_3298_, v___y_3299_, lean_box(0));
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed(lean_object* v_val_3307_, lean_object* v___x_3308_, lean_object* v___f_3309_, lean_object* v_____r_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_){
_start:
{
uint8_t v___x_63337__boxed_3314_; lean_object* v_res_3315_; 
v___x_63337__boxed_3314_ = lean_unbox(v___x_3308_);
v_res_3315_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6(v_val_3307_, v___x_63337__boxed_3314_, v___f_3309_, v_____r_3310_, v___y_3311_, v___y_3312_);
lean_dec(v___y_3312_);
lean_dec_ref(v___y_3311_);
lean_dec_ref(v_val_3307_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(lean_object* v_val_3316_, lean_object* v___f_3317_, lean_object* v_____r_3318_, lean_object* v_exportedInfo_x3f_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_toConstantVal_3323_; lean_object* v_name_3324_; lean_object* v___x_3325_; uint8_t v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; 
v_toConstantVal_3323_ = lean_ctor_get(v_val_3316_, 0);
v_name_3324_ = lean_ctor_get(v_toConstantVal_3323_, 0);
lean_inc(v_name_3324_);
v___x_3325_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3325_, 0, v_val_3316_);
v___x_3326_ = 3;
v___x_3327_ = lean_box(v___x_3326_);
v___x_3328_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3328_, 0, v___x_3325_);
lean_ctor_set(v___x_3328_, 1, v___x_3327_);
v___x_3329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3329_, 0, v_name_3324_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3320_);
v___x_3330_ = lean_apply_5(v___f_3317_, v___x_3329_, v_exportedInfo_x3f_3319_, v___y_3320_, v___y_3321_, lean_box(0));
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed(lean_object* v_val_3331_, lean_object* v___f_3332_, lean_object* v_____r_3333_, lean_object* v_exportedInfo_x3f_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7(v_val_3331_, v___f_3332_, v_____r_3333_, v_exportedInfo_x3f_3334_, v___y_3335_, v___y_3336_);
lean_dec(v___y_3336_);
lean_dec_ref(v___y_3335_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(lean_object* v_val_3339_, lean_object* v___f_3340_, lean_object* v_____r_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v_toConstantVal_3345_; uint8_t v_isUnsafe_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_toConstantVal_3345_ = lean_ctor_get(v_val_3339_, 0);
v_isUnsafe_3346_ = lean_ctor_get_uint8(v_val_3339_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_3345_);
v___x_3347_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3347_, 0, v_toConstantVal_3345_);
lean_ctor_set_uint8(v___x_3347_, sizeof(void*)*1, v_isUnsafe_3346_);
v___x_3348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3348_, 0, v___x_3347_);
v___x_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
v___x_3350_ = lean_box(0);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
v___x_3351_ = lean_apply_5(v___f_3340_, v___x_3350_, v___x_3349_, v___y_3342_, v___y_3343_, lean_box(0));
return v___x_3351_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed(lean_object* v_val_3352_, lean_object* v___f_3353_, lean_object* v_____r_3354_, lean_object* v___y_3355_, lean_object* v___y_3356_, lean_object* v___y_3357_){
_start:
{
lean_object* v_res_3358_; 
v_res_3358_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_3352_, v___f_3353_, v_____r_3354_, v___y_3355_, v___y_3356_);
lean_dec(v___y_3356_);
lean_dec_ref(v___y_3355_);
lean_dec_ref(v_val_3352_);
return v_res_3358_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(lean_object* v_decl_3359_, uint8_t v___x_3360_, lean_object* v_cls_3361_, lean_object* v___x_3362_, lean_object* v___x_3363_, lean_object* v_____x_3364_, lean_object* v_exportedInfo_x3f_3365_, lean_object* v___y_3366_, lean_object* v___y_3367_){
_start:
{
lean_object* v___y_3370_; lean_object* v___y_3371_; lean_object* v_a_3372_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v_a_3385_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v_snd_3469_; lean_object* v_fst_3470_; lean_object* v___x_3472_; uint8_t v_isShared_3473_; uint8_t v_isSharedCheck_3599_; 
v_snd_3469_ = lean_ctor_get(v_____x_3364_, 1);
v_fst_3470_ = lean_ctor_get(v_____x_3364_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v_____x_3364_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3472_ = v_____x_3364_;
v_isShared_3473_ = v_isSharedCheck_3599_;
goto v_resetjp_3471_;
}
else
{
lean_inc(v_snd_3469_);
lean_inc(v_fst_3470_);
lean_dec(v_____x_3364_);
v___x_3472_ = lean_box(0);
v_isShared_3473_ = v_isSharedCheck_3599_;
goto v_resetjp_3471_;
}
v___jp_3369_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v___x_3373_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3371_, v___y_3370_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3373_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3373_, 0);
lean_dec(v_unused_3381_);
v___x_3375_ = v___x_3373_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_dec(v___x_3373_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
lean_ctor_set_tag(v___x_3375_, 1);
lean_ctor_set(v___x_3375_, 0, v_a_3372_);
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3372_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
v___jp_3382_:
{
lean_object* v___x_3386_; lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
v___x_3386_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3384_, v___y_3383_);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3393_ == 0)
{
lean_object* v_unused_3394_; 
v_unused_3394_ = lean_ctor_get(v___x_3386_, 0);
lean_dec(v_unused_3394_);
v___x_3388_ = v___x_3386_;
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3386_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3393_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3391_; 
if (v_isShared_3389_ == 0)
{
lean_ctor_set(v___x_3388_, 0, v_a_3385_);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3385_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
v___jp_3395_:
{
lean_object* v___x_3407_; 
lean_inc_ref(v___y_3399_);
v___x_3407_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3401_, v___y_3399_, v___y_3397_, v___y_3406_);
if (lean_obj_tag(v___x_3407_) == 0)
{
lean_object* v___x_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3454_; 
lean_dec_ref_known(v___x_3407_, 1);
lean_inc_ref(v___y_3404_);
v___x_3408_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3404_, v___y_3405_);
v_isSharedCheck_3454_ = !lean_is_exclusive(v___x_3408_);
if (v_isSharedCheck_3454_ == 0)
{
lean_object* v_unused_3455_; 
v_unused_3455_ = lean_ctor_get(v___x_3408_, 0);
lean_dec(v_unused_3455_);
v___x_3410_ = v___x_3408_;
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
else
{
lean_dec(v___x_3408_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3454_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
lean_object* v_options_3412_; lean_object* v___x_3413_; uint8_t v___x_3414_; 
v_options_3412_ = lean_ctor_get(v___y_3396_, 2);
v___x_3413_ = l_Lean_Elab_async;
v___x_3414_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3412_, v___x_3413_);
if (v___x_3414_ == 0)
{
lean_object* v___x_3415_; lean_object* v_r_3416_; 
lean_del_object(v___x_3410_);
lean_dec_ref(v___y_3403_);
lean_dec_ref(v___y_3400_);
v___x_3415_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3399_, v___y_3405_);
lean_dec_ref(v___x_3415_);
v_r_3416_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3359_, v___y_3396_, v___y_3405_);
if (lean_obj_tag(v_r_3416_) == 0)
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3426_; 
v_a_3417_ = lean_ctor_get(v_r_3416_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v_r_3416_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3419_ = v_r_3416_;
v_isShared_3420_ = v_isSharedCheck_3426_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v_r_3416_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3426_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
lean_inc(v_a_3417_);
if (v_isShared_3420_ == 0)
{
lean_ctor_set_tag(v___x_3419_, 1);
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
lean_object* v___x_3423_; 
v___x_3423_ = lean_apply_2(v___y_3402_, v___x_3422_, lean_box(0));
if (lean_obj_tag(v___x_3423_) == 0)
{
lean_dec_ref_known(v___x_3423_, 1);
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3404_;
v_a_3385_ = v_a_3417_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3424_; 
lean_dec(v_a_3417_);
v_a_3424_ = lean_ctor_get(v___x_3423_, 0);
lean_inc(v_a_3424_);
lean_dec_ref_known(v___x_3423_, 1);
v___y_3370_ = v___y_3405_;
v___y_3371_ = v___y_3404_;
v_a_3372_ = v_a_3424_;
goto v___jp_3369_;
}
}
}
}
else
{
lean_object* v_a_3427_; lean_object* v___x_3428_; lean_object* v___x_3429_; 
v_a_3427_ = lean_ctor_get(v_r_3416_, 0);
lean_inc(v_a_3427_);
lean_dec_ref_known(v_r_3416_, 1);
v___x_3428_ = lean_box(0);
v___x_3429_ = lean_apply_2(v___y_3402_, v___x_3428_, lean_box(0));
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_dec_ref_known(v___x_3429_, 1);
v___y_3370_ = v___y_3405_;
v___y_3371_ = v___y_3404_;
v_a_3372_ = v_a_3427_;
goto v___jp_3369_;
}
else
{
lean_object* v_a_3430_; 
lean_dec(v_a_3427_);
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref_known(v___x_3429_, 1);
v___y_3370_ = v___y_3405_;
v___y_3371_ = v___y_3404_;
v_a_3372_ = v_a_3430_;
goto v___jp_3369_;
}
}
}
else
{
lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_dec_ref(v___y_3404_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v___y_3399_);
lean_dec(v_decl_3359_);
v___x_3431_ = l_IO_CancelToken_new();
if (v_isShared_3411_ == 0)
{
lean_ctor_set_tag(v___x_3410_, 1);
lean_ctor_set(v___x_3410_, 0, v___x_3431_);
v___x_3433_ = v___x_3410_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3453_; 
v_reuseFailAlloc_3453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3453_, 0, v___x_3431_);
v___x_3433_ = v_reuseFailAlloc_3453_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3434_ = lean_unsigned_to_nat(0u);
v___x_3435_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3436_ = l_Lean_Name_toString(v___x_3435_, v___x_3360_);
lean_inc_ref(v___x_3433_);
v___x_3437_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3403_, v___x_3433_, v___x_3436_, v___y_3396_, v___y_3405_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; lean_object* v_checked_3439_; lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref_known(v___x_3437_, 1);
v_checked_3439_ = lean_ctor_get(v___y_3400_, 2);
lean_inc_ref(v_checked_3439_);
lean_dec_ref(v___y_3400_);
v___x_3440_ = lean_io_map_task(v_a_3438_, v_checked_3439_, v___x_3434_, v___y_3398_);
v___x_3441_ = lean_box(0);
v___x_3442_ = lean_box(2);
v___x_3443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3441_);
lean_ctor_set(v___x_3443_, 1, v___x_3442_);
lean_ctor_set(v___x_3443_, 2, v___x_3433_);
lean_ctor_set(v___x_3443_, 3, v___x_3440_);
v___x_3444_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3443_, v___y_3405_);
return v___x_3444_;
}
else
{
lean_object* v_a_3445_; lean_object* v___x_3447_; uint8_t v_isShared_3448_; uint8_t v_isSharedCheck_3452_; 
lean_dec_ref(v___x_3433_);
lean_dec_ref(v___y_3400_);
v_a_3445_ = lean_ctor_get(v___x_3437_, 0);
v_isSharedCheck_3452_ = !lean_is_exclusive(v___x_3437_);
if (v_isSharedCheck_3452_ == 0)
{
v___x_3447_ = v___x_3437_;
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
else
{
lean_inc(v_a_3445_);
lean_dec(v___x_3437_);
v___x_3447_ = lean_box(0);
v_isShared_3448_ = v_isSharedCheck_3452_;
goto v_resetjp_3446_;
}
v_resetjp_3446_:
{
lean_object* v___x_3450_; 
if (v_isShared_3448_ == 0)
{
v___x_3450_ = v___x_3447_;
goto v_reusejp_3449_;
}
else
{
lean_object* v_reuseFailAlloc_3451_; 
v_reuseFailAlloc_3451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3451_, 0, v_a_3445_);
v___x_3450_ = v_reuseFailAlloc_3451_;
goto v_reusejp_3449_;
}
v_reusejp_3449_:
{
return v___x_3450_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3456_; lean_object* v___x_3458_; uint8_t v_isShared_3459_; uint8_t v_isSharedCheck_3468_; 
lean_dec_ref(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec_ref(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v_decl_3359_);
v_a_3456_ = lean_ctor_get(v___x_3407_, 0);
v_isSharedCheck_3468_ = !lean_is_exclusive(v___x_3407_);
if (v_isSharedCheck_3468_ == 0)
{
v___x_3458_ = v___x_3407_;
v_isShared_3459_ = v_isSharedCheck_3468_;
goto v_resetjp_3457_;
}
else
{
lean_inc(v_a_3456_);
lean_dec(v___x_3407_);
v___x_3458_ = lean_box(0);
v_isShared_3459_ = v_isSharedCheck_3468_;
goto v_resetjp_3457_;
}
v_resetjp_3457_:
{
lean_object* v_ref_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3466_; 
v_ref_3460_ = lean_ctor_get(v___y_3396_, 5);
v___x_3461_ = lean_io_error_to_string(v_a_3456_);
v___x_3462_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
v___x_3463_ = l_Lean_MessageData_ofFormat(v___x_3462_);
lean_inc(v_ref_3460_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v_ref_3460_);
lean_ctor_set(v___x_3464_, 1, v___x_3463_);
if (v_isShared_3459_ == 0)
{
lean_ctor_set(v___x_3458_, 0, v___x_3464_);
v___x_3466_ = v___x_3458_;
goto v_reusejp_3465_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3464_);
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
v_resetjp_3471_:
{
lean_object* v_fst_3474_; lean_object* v_snd_3475_; lean_object* v___x_3477_; uint8_t v_isShared_3478_; uint8_t v_isSharedCheck_3598_; 
v_fst_3474_ = lean_ctor_get(v_snd_3469_, 0);
v_snd_3475_ = lean_ctor_get(v_snd_3469_, 1);
v_isSharedCheck_3598_ = !lean_is_exclusive(v_snd_3469_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3477_ = v_snd_3469_;
v_isShared_3478_ = v_isSharedCheck_3598_;
goto v_resetjp_3476_;
}
else
{
lean_inc(v_snd_3475_);
lean_inc(v_fst_3474_);
lean_dec(v_snd_3469_);
v___x_3477_ = lean_box(0);
v_isShared_3478_ = v_isSharedCheck_3598_;
goto v_resetjp_3476_;
}
v_resetjp_3476_:
{
lean_object* v___y_3480_; lean_object* v___y_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v_exportedInfo_x3f_3512_; lean_object* v___y_3513_; lean_object* v___y_3514_; lean_object* v___y_3524_; lean_object* v___y_3525_; lean_object* v___y_3528_; lean_object* v___y_3529_; lean_object* v___y_3532_; lean_object* v___y_3533_; uint8_t v___y_3534_; lean_object* v___y_3564_; lean_object* v___y_3565_; lean_object* v___x_3588_; lean_object* v_env_3589_; uint8_t v___x_3590_; 
v___x_3588_ = lean_st_ref_get(v___y_3367_);
v_env_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc_ref(v_env_3589_);
lean_dec(v___x_3588_);
v___x_3590_ = l_Lean_Environment_containsOnBranch(v_env_3589_, v_fst_3470_);
lean_dec_ref(v_env_3589_);
if (v___x_3590_ == 0)
{
lean_del_object(v___x_3472_);
v___y_3564_ = v___y_3366_;
v___y_3565_ = v___y_3367_;
goto v___jp_3563_;
}
else
{
lean_object* v___x_3591_; lean_object* v_env_3592_; lean_object* v___x_3593_; lean_object* v___x_3595_; 
lean_del_object(v___x_3477_);
lean_dec(v_snd_3475_);
lean_dec(v_fst_3474_);
lean_dec(v_exportedInfo_x3f_3365_);
lean_dec(v___x_3363_);
lean_dec_ref(v___x_3362_);
lean_dec(v_cls_3361_);
lean_dec(v_decl_3359_);
v___x_3591_ = lean_st_ref_get(v___y_3367_);
v_env_3592_ = lean_ctor_get(v___x_3591_, 0);
lean_inc_ref(v_env_3592_);
lean_dec(v___x_3591_);
v___x_3593_ = lean_elab_environment_to_kernel_env(v_env_3592_);
if (v_isShared_3473_ == 0)
{
lean_ctor_set_tag(v___x_3472_, 1);
lean_ctor_set(v___x_3472_, 1, v_fst_3470_);
lean_ctor_set(v___x_3472_, 0, v___x_3593_);
v___x_3595_ = v___x_3472_;
goto v_reusejp_3594_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3593_);
lean_ctor_set(v_reuseFailAlloc_3597_, 1, v_fst_3470_);
v___x_3595_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3594_;
}
v_reusejp_3594_:
{
lean_object* v___x_3596_; 
v___x_3596_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3595_, v___y_3366_, v___y_3367_);
return v___x_3596_;
}
}
v___jp_3479_:
{
uint8_t v___x_3487_; uint8_t v___x_3488_; lean_object* v___x_3489_; 
v___x_3487_ = 0;
v___x_3488_ = lean_unbox(v_snd_3475_);
lean_dec(v_snd_3475_);
lean_inc_ref(v___y_3482_);
v___x_3489_ = l_Lean_Environment_addConstAsync(v___y_3482_, v_fst_3470_, v___x_3488_, v___y_3486_, v___x_3487_, v___x_3360_);
if (lean_obj_tag(v___x_3489_) == 0)
{
lean_object* v_a_3490_; lean_object* v_mainEnv_3491_; lean_object* v_asyncEnv_3492_; lean_object* v___f_3493_; lean_object* v___f_3494_; lean_object* v___x_3495_; 
lean_del_object(v___x_3477_);
v_a_3490_ = lean_ctor_get(v___x_3489_, 0);
lean_inc_n(v_a_3490_, 3);
lean_dec_ref_known(v___x_3489_, 1);
v_mainEnv_3491_ = lean_ctor_get(v_a_3490_, 0);
lean_inc_ref(v_mainEnv_3491_);
v_asyncEnv_3492_ = lean_ctor_get(v_a_3490_, 1);
lean_inc_ref_n(v_asyncEnv_3492_, 2);
lean_inc_ref(v___y_3481_);
lean_inc(v___y_3480_);
v___f_3493_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3493_, 0, v___y_3480_);
lean_closure_set(v___f_3493_, 1, v_a_3490_);
lean_closure_set(v___f_3493_, 2, v___y_3481_);
lean_inc(v_decl_3359_);
v___f_3494_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3494_, 0, v_asyncEnv_3492_);
lean_closure_set(v___f_3494_, 1, v_a_3490_);
lean_closure_set(v___f_3494_, 2, v_decl_3359_);
v___x_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3495_, 0, v_fst_3474_);
if (lean_obj_tag(v___y_3484_) == 0)
{
lean_inc_ref(v___x_3495_);
v___y_3396_ = v___y_3483_;
v___y_3397_ = v___x_3495_;
v___y_3398_ = v___x_3487_;
v___y_3399_ = v_asyncEnv_3492_;
v___y_3400_ = v___y_3482_;
v___y_3401_ = v_a_3490_;
v___y_3402_ = v___f_3493_;
v___y_3403_ = v___f_3494_;
v___y_3404_ = v_mainEnv_3491_;
v___y_3405_ = v___y_3485_;
v___y_3406_ = v___x_3495_;
goto v___jp_3395_;
}
else
{
v___y_3396_ = v___y_3483_;
v___y_3397_ = v___x_3495_;
v___y_3398_ = v___x_3487_;
v___y_3399_ = v_asyncEnv_3492_;
v___y_3400_ = v___y_3482_;
v___y_3401_ = v_a_3490_;
v___y_3402_ = v___f_3493_;
v___y_3403_ = v___f_3494_;
v___y_3404_ = v_mainEnv_3491_;
v___y_3405_ = v___y_3485_;
v___y_3406_ = v___y_3484_;
goto v___jp_3395_;
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v___y_3484_);
lean_dec_ref(v___y_3482_);
lean_dec(v_fst_3474_);
lean_dec(v_decl_3359_);
v_a_3496_ = lean_ctor_get(v___x_3489_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3489_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3498_ = v___x_3489_;
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3489_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3510_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_ref_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; lean_object* v___x_3505_; 
v_ref_3500_ = lean_ctor_get(v___y_3483_, 5);
v___x_3501_ = lean_io_error_to_string(v_a_3496_);
v___x_3502_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3502_, 0, v___x_3501_);
v___x_3503_ = l_Lean_MessageData_ofFormat(v___x_3502_);
lean_inc(v_ref_3500_);
if (v_isShared_3478_ == 0)
{
lean_ctor_set(v___x_3477_, 1, v___x_3503_);
lean_ctor_set(v___x_3477_, 0, v_ref_3500_);
v___x_3505_ = v___x_3477_;
goto v_reusejp_3504_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_ref_3500_);
lean_ctor_set(v_reuseFailAlloc_3509_, 1, v___x_3503_);
v___x_3505_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3504_;
}
v_reusejp_3504_:
{
lean_object* v___x_3507_; 
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3505_);
v___x_3507_ = v___x_3498_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v___x_3505_);
v___x_3507_ = v_reuseFailAlloc_3508_;
goto v_reusejp_3506_;
}
v_reusejp_3506_:
{
return v___x_3507_;
}
}
}
}
}
v___jp_3511_:
{
lean_object* v___x_3515_; 
v___x_3515_ = lean_st_ref_get(v___y_3514_);
if (lean_obj_tag(v_exportedInfo_x3f_3512_) == 0)
{
lean_object* v_env_3516_; lean_object* v___x_3517_; 
v_env_3516_ = lean_ctor_get(v___x_3515_, 0);
lean_inc_ref(v_env_3516_);
lean_dec(v___x_3515_);
v___x_3517_ = lean_box(0);
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3513_;
v___y_3482_ = v_env_3516_;
v___y_3483_ = v___y_3513_;
v___y_3484_ = v_exportedInfo_x3f_3512_;
v___y_3485_ = v___y_3514_;
v___y_3486_ = v___x_3517_;
goto v___jp_3479_;
}
else
{
lean_object* v_env_3518_; lean_object* v_val_3519_; uint8_t v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v_env_3518_ = lean_ctor_get(v___x_3515_, 0);
lean_inc_ref(v_env_3518_);
lean_dec(v___x_3515_);
v_val_3519_ = lean_ctor_get(v_exportedInfo_x3f_3512_, 0);
v___x_3520_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3519_);
v___x_3521_ = lean_box(v___x_3520_);
v___x_3522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v___y_3480_ = v___y_3514_;
v___y_3481_ = v___y_3513_;
v___y_3482_ = v_env_3518_;
v___y_3483_ = v___y_3513_;
v___y_3484_ = v_exportedInfo_x3f_3512_;
v___y_3485_ = v___y_3514_;
v___y_3486_ = v___x_3522_;
goto v___jp_3479_;
}
}
v___jp_3523_:
{
lean_object* v___x_3526_; 
lean_inc(v_fst_3474_);
v___x_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3526_, 0, v_fst_3474_);
v_exportedInfo_x3f_3512_ = v___x_3526_;
v___y_3513_ = v___y_3524_;
v___y_3514_ = v___y_3525_;
goto v___jp_3511_;
}
v___jp_3527_:
{
lean_object* v___x_3530_; 
lean_inc(v_fst_3474_);
v___x_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3530_, 0, v_fst_3474_);
v_exportedInfo_x3f_3512_ = v___x_3530_;
v___y_3513_ = v___y_3528_;
v___y_3514_ = v___y_3529_;
goto v___jp_3511_;
}
v___jp_3531_:
{
if (v___y_3534_ == 0)
{
lean_object* v_options_3535_; uint8_t v_hasTrace_3536_; 
lean_dec(v_exportedInfo_x3f_3365_);
lean_dec_ref(v___x_3362_);
v_options_3535_ = lean_ctor_get(v___y_3532_, 2);
v_hasTrace_3536_ = lean_ctor_get_uint8(v_options_3535_, sizeof(void*)*1);
if (v_hasTrace_3536_ == 0)
{
lean_dec(v_cls_3361_);
v___y_3524_ = v___y_3532_;
v___y_3525_ = v___y_3533_;
goto v___jp_3523_;
}
else
{
lean_object* v_inheritedTraceOptions_3537_; lean_object* v___x_3538_; lean_object* v___x_3539_; uint8_t v___x_3540_; 
v_inheritedTraceOptions_3537_ = lean_ctor_get(v___y_3532_, 13);
v___x_3538_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3361_);
v___x_3539_ = l_Lean_Name_append(v___x_3538_, v_cls_3361_);
v___x_3540_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3537_, v_options_3535_, v___x_3539_);
lean_dec(v___x_3539_);
if (v___x_3540_ == 0)
{
lean_dec(v_cls_3361_);
v___y_3524_ = v___y_3532_;
v___y_3525_ = v___y_3533_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3541_; lean_object* v___x_3542_; 
v___x_3541_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3542_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3361_, v___x_3541_, v___y_3532_, v___y_3533_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_dec_ref_known(v___x_3542_, 1);
v___y_3524_ = v___y_3532_;
v___y_3525_ = v___y_3533_;
goto v___jp_3523_;
}
else
{
lean_del_object(v___x_3477_);
lean_dec(v_snd_3475_);
lean_dec(v_fst_3474_);
lean_dec(v_fst_3470_);
lean_dec(v_decl_3359_);
return v___x_3542_;
}
}
}
}
else
{
lean_object* v___x_3543_; lean_object* v_env_3544_; lean_object* v_nextMacroScope_3545_; lean_object* v_ngen_3546_; lean_object* v_auxDeclNGen_3547_; lean_object* v_traceState_3548_; lean_object* v_messages_3549_; lean_object* v_infoState_3550_; lean_object* v_snapshotTasks_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3561_; 
lean_dec(v_cls_3361_);
v___x_3543_ = lean_st_ref_take(v___y_3533_);
v_env_3544_ = lean_ctor_get(v___x_3543_, 0);
v_nextMacroScope_3545_ = lean_ctor_get(v___x_3543_, 1);
v_ngen_3546_ = lean_ctor_get(v___x_3543_, 2);
v_auxDeclNGen_3547_ = lean_ctor_get(v___x_3543_, 3);
v_traceState_3548_ = lean_ctor_get(v___x_3543_, 4);
v_messages_3549_ = lean_ctor_get(v___x_3543_, 6);
v_infoState_3550_ = lean_ctor_get(v___x_3543_, 7);
v_snapshotTasks_3551_ = lean_ctor_get(v___x_3543_, 8);
v_isSharedCheck_3561_ = !lean_is_exclusive(v___x_3543_);
if (v_isSharedCheck_3561_ == 0)
{
lean_object* v_unused_3562_; 
v_unused_3562_ = lean_ctor_get(v___x_3543_, 5);
lean_dec(v_unused_3562_);
v___x_3553_ = v___x_3543_;
v_isShared_3554_ = v_isSharedCheck_3561_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_snapshotTasks_3551_);
lean_inc(v_infoState_3550_);
lean_inc(v_messages_3549_);
lean_inc(v_traceState_3548_);
lean_inc(v_auxDeclNGen_3547_);
lean_inc(v_ngen_3546_);
lean_inc(v_nextMacroScope_3545_);
lean_inc(v_env_3544_);
lean_dec(v___x_3543_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3561_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3555_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
lean_inc(v_snd_3475_);
lean_inc(v_fst_3470_);
v___x_3556_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3555_, v_env_3544_, v_fst_3470_, v_snd_3475_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 5, v___x_3362_);
lean_ctor_set(v___x_3553_, 0, v___x_3556_);
v___x_3558_ = v___x_3553_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3560_; 
v_reuseFailAlloc_3560_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3560_, 0, v___x_3556_);
lean_ctor_set(v_reuseFailAlloc_3560_, 1, v_nextMacroScope_3545_);
lean_ctor_set(v_reuseFailAlloc_3560_, 2, v_ngen_3546_);
lean_ctor_set(v_reuseFailAlloc_3560_, 3, v_auxDeclNGen_3547_);
lean_ctor_set(v_reuseFailAlloc_3560_, 4, v_traceState_3548_);
lean_ctor_set(v_reuseFailAlloc_3560_, 5, v___x_3362_);
lean_ctor_set(v_reuseFailAlloc_3560_, 6, v_messages_3549_);
lean_ctor_set(v_reuseFailAlloc_3560_, 7, v_infoState_3550_);
lean_ctor_set(v_reuseFailAlloc_3560_, 8, v_snapshotTasks_3551_);
v___x_3558_ = v_reuseFailAlloc_3560_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
lean_object* v___x_3559_; 
v___x_3559_ = lean_st_ref_set(v___y_3533_, v___x_3558_);
v_exportedInfo_x3f_3512_ = v_exportedInfo_x3f_3365_;
v___y_3513_ = v___y_3532_;
v___y_3514_ = v___y_3533_;
goto v___jp_3511_;
}
}
}
}
v___jp_3563_:
{
lean_object* v___x_3566_; uint8_t v___x_3567_; 
lean_inc(v_decl_3359_);
v___x_3566_ = l_Lean_Declaration_getTopLevelNames(v_decl_3359_);
v___x_3567_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3566_);
lean_dec(v___x_3566_);
if (v___x_3567_ == 0)
{
lean_dec(v___x_3363_);
if (lean_obj_tag(v_exportedInfo_x3f_3365_) == 0)
{
v___y_3532_ = v___y_3564_;
v___y_3533_ = v___y_3565_;
v___y_3534_ = v___x_3567_;
goto v___jp_3531_;
}
else
{
v___y_3532_ = v___y_3564_;
v___y_3533_ = v___y_3565_;
v___y_3534_ = v___x_3360_;
goto v___jp_3531_;
}
}
else
{
lean_object* v___x_3568_; lean_object* v___x_3569_; lean_object* v_a_3570_; uint8_t v___x_3571_; 
lean_dec(v_exportedInfo_x3f_3365_);
lean_dec_ref(v___x_3362_);
v___x_3568_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3569_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3568_, v___y_3564_);
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref(v___x_3569_);
v___x_3571_ = lean_unbox(v_a_3570_);
lean_dec(v_a_3570_);
if (v___x_3571_ == 0)
{
lean_object* v_options_3572_; uint8_t v_hasTrace_3573_; 
v_options_3572_ = lean_ctor_get(v___y_3564_, 2);
v_hasTrace_3573_ = lean_ctor_get_uint8(v_options_3572_, sizeof(void*)*1);
if (v_hasTrace_3573_ == 0)
{
lean_dec(v_cls_3361_);
v_exportedInfo_x3f_3512_ = v___x_3363_;
v___y_3513_ = v___y_3564_;
v___y_3514_ = v___y_3565_;
goto v___jp_3511_;
}
else
{
lean_object* v_inheritedTraceOptions_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v_inheritedTraceOptions_3574_ = lean_ctor_get(v___y_3564_, 13);
v___x_3575_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3361_);
v___x_3576_ = l_Lean_Name_append(v___x_3575_, v_cls_3361_);
v___x_3577_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3574_, v_options_3572_, v___x_3576_);
lean_dec(v___x_3576_);
if (v___x_3577_ == 0)
{
lean_dec(v_cls_3361_);
v_exportedInfo_x3f_3512_ = v___x_3363_;
v___y_3513_ = v___y_3564_;
v___y_3514_ = v___y_3565_;
goto v___jp_3511_;
}
else
{
lean_object* v___x_3578_; lean_object* v___x_3579_; 
v___x_3578_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3579_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3361_, v___x_3578_, v___y_3564_, v___y_3565_);
if (lean_obj_tag(v___x_3579_) == 0)
{
lean_dec_ref_known(v___x_3579_, 1);
v_exportedInfo_x3f_3512_ = v___x_3363_;
v___y_3513_ = v___y_3564_;
v___y_3514_ = v___y_3565_;
goto v___jp_3511_;
}
else
{
lean_del_object(v___x_3477_);
lean_dec(v_snd_3475_);
lean_dec(v_fst_3474_);
lean_dec(v_fst_3470_);
lean_dec(v___x_3363_);
lean_dec(v_decl_3359_);
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_options_3580_; uint8_t v_hasTrace_3581_; 
lean_dec(v___x_3363_);
v_options_3580_ = lean_ctor_get(v___y_3564_, 2);
v_hasTrace_3581_ = lean_ctor_get_uint8(v_options_3580_, sizeof(void*)*1);
if (v_hasTrace_3581_ == 0)
{
lean_dec(v_cls_3361_);
v___y_3528_ = v___y_3564_;
v___y_3529_ = v___y_3565_;
goto v___jp_3527_;
}
else
{
lean_object* v_inheritedTraceOptions_3582_; lean_object* v___x_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v_inheritedTraceOptions_3582_ = lean_ctor_get(v___y_3564_, 13);
v___x_3583_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3361_);
v___x_3584_ = l_Lean_Name_append(v___x_3583_, v_cls_3361_);
v___x_3585_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3582_, v_options_3580_, v___x_3584_);
lean_dec(v___x_3584_);
if (v___x_3585_ == 0)
{
lean_dec(v_cls_3361_);
v___y_3528_ = v___y_3564_;
v___y_3529_ = v___y_3565_;
goto v___jp_3527_;
}
else
{
lean_object* v___x_3586_; lean_object* v___x_3587_; 
v___x_3586_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3587_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3361_, v___x_3586_, v___y_3564_, v___y_3565_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_dec_ref_known(v___x_3587_, 1);
v___y_3528_ = v___y_3564_;
v___y_3529_ = v___y_3565_;
goto v___jp_3527_;
}
else
{
lean_del_object(v___x_3477_);
lean_dec(v_snd_3475_);
lean_dec(v_fst_3474_);
lean_dec(v_fst_3470_);
lean_dec(v_decl_3359_);
return v___x_3587_;
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
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed(lean_object* v_decl_3600_, lean_object* v___x_3601_, lean_object* v_cls_3602_, lean_object* v___x_3603_, lean_object* v___x_3604_, lean_object* v_____x_3605_, lean_object* v_exportedInfo_x3f_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
uint8_t v___x_63468__boxed_3610_; lean_object* v_res_3611_; 
v___x_63468__boxed_3610_ = lean_unbox(v___x_3601_);
v_res_3611_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3600_, v___x_63468__boxed_3610_, v_cls_3602_, v___x_3603_, v___x_3604_, v_____x_3605_, v_exportedInfo_x3f_3606_, v___y_3607_, v___y_3608_);
lean_dec(v___y_3608_);
lean_dec_ref(v___y_3607_);
return v_res_3611_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(lean_object* v___f_3612_, uint8_t v_forceExpose_3613_, uint8_t v___x_3614_, lean_object* v___x_3615_, lean_object* v_cls_3616_, lean_object* v_defn_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_){
_start:
{
lean_object* v_exportedInfo_x3f_3622_; lean_object* v___y_3623_; lean_object* v___y_3624_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_st_ref_get(v___y_3619_);
v___x_3644_ = lean_st_ref_get(v___y_3619_);
if (v_forceExpose_3613_ == 0)
{
if (v___x_3614_ == 0)
{
lean_dec(v___x_3644_);
lean_dec(v___x_3643_);
lean_dec(v_cls_3616_);
v_exportedInfo_x3f_3622_ = v___x_3615_;
v___y_3623_ = v___y_3618_;
v___y_3624_ = v___y_3619_;
goto v___jp_3621_;
}
else
{
lean_object* v_env_3645_; lean_object* v_env_3646_; lean_object* v___x_3647_; uint8_t v_isModule_3648_; 
v_env_3645_ = lean_ctor_get(v___x_3643_, 0);
lean_inc_ref(v_env_3645_);
lean_dec(v___x_3643_);
v_env_3646_ = lean_ctor_get(v___x_3644_, 0);
lean_inc_ref(v_env_3646_);
lean_dec(v___x_3644_);
v___x_3647_ = l_Lean_Environment_header(v_env_3645_);
lean_dec_ref(v_env_3645_);
v_isModule_3648_ = lean_ctor_get_uint8(v___x_3647_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_3647_);
if (v_isModule_3648_ == 0)
{
lean_dec_ref(v_env_3646_);
lean_dec(v_cls_3616_);
v_exportedInfo_x3f_3622_ = v___x_3615_;
v___y_3623_ = v___y_3618_;
v___y_3624_ = v___y_3619_;
goto v___jp_3621_;
}
else
{
uint8_t v_isExporting_3649_; 
v_isExporting_3649_ = lean_ctor_get_uint8(v_env_3646_, sizeof(void*)*8);
lean_dec_ref(v_env_3646_);
if (v_isExporting_3649_ == 0)
{
lean_object* v_options_3650_; uint8_t v_hasTrace_3651_; 
lean_dec(v___x_3615_);
v_options_3650_ = lean_ctor_get(v___y_3618_, 2);
v_hasTrace_3651_ = lean_ctor_get_uint8(v_options_3650_, sizeof(void*)*1);
if (v_hasTrace_3651_ == 0)
{
lean_dec(v_cls_3616_);
v___y_3634_ = v___y_3618_;
v___y_3635_ = v___y_3619_;
goto v___jp_3633_;
}
else
{
lean_object* v_inheritedTraceOptions_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v_inheritedTraceOptions_3652_ = lean_ctor_get(v___y_3618_, 13);
v___x_3653_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
lean_inc(v_cls_3616_);
v___x_3654_ = l_Lean_Name_append(v___x_3653_, v_cls_3616_);
v___x_3655_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3652_, v_options_3650_, v___x_3654_);
lean_dec(v___x_3654_);
if (v___x_3655_ == 0)
{
lean_dec(v_cls_3616_);
v___y_3634_ = v___y_3618_;
v___y_3635_ = v___y_3619_;
goto v___jp_3633_;
}
else
{
lean_object* v_toConstantVal_3656_; lean_object* v_name_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; 
v_toConstantVal_3656_ = lean_ctor_get(v_defn_3617_, 0);
v_name_3657_ = lean_ctor_get(v_toConstantVal_3656_, 0);
v___x_3658_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_3657_);
v___x_3659_ = l_Lean_MessageData_ofName(v_name_3657_);
v___x_3660_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3660_, 0, v___x_3658_);
lean_ctor_set(v___x_3660_, 1, v___x_3659_);
v___x_3661_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_3662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3660_);
lean_ctor_set(v___x_3662_, 1, v___x_3661_);
v___x_3663_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3616_, v___x_3662_, v___y_3618_, v___y_3619_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_dec_ref_known(v___x_3663_, 1);
v___y_3634_ = v___y_3618_;
v___y_3635_ = v___y_3619_;
goto v___jp_3633_;
}
else
{
lean_dec_ref(v_defn_3617_);
lean_dec_ref(v___f_3612_);
return v___x_3663_;
}
}
}
}
else
{
lean_dec(v_cls_3616_);
v_exportedInfo_x3f_3622_ = v___x_3615_;
v___y_3623_ = v___y_3618_;
v___y_3624_ = v___y_3619_;
goto v___jp_3621_;
}
}
}
}
else
{
lean_dec(v___x_3644_);
lean_dec(v___x_3643_);
lean_dec(v_cls_3616_);
v_exportedInfo_x3f_3622_ = v___x_3615_;
v___y_3623_ = v___y_3618_;
v___y_3624_ = v___y_3619_;
goto v___jp_3621_;
}
v___jp_3621_:
{
lean_object* v_toConstantVal_3625_; lean_object* v_name_3626_; lean_object* v___x_3627_; uint8_t v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; 
v_toConstantVal_3625_ = lean_ctor_get(v_defn_3617_, 0);
v_name_3626_ = lean_ctor_get(v_toConstantVal_3625_, 0);
lean_inc(v_name_3626_);
v___x_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_defn_3617_);
v___x_3628_ = 0;
v___x_3629_ = lean_box(v___x_3628_);
v___x_3630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3630_, 0, v___x_3627_);
lean_ctor_set(v___x_3630_, 1, v___x_3629_);
v___x_3631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3631_, 0, v_name_3626_);
lean_ctor_set(v___x_3631_, 1, v___x_3630_);
lean_inc(v___y_3624_);
lean_inc_ref(v___y_3623_);
v___x_3632_ = lean_apply_5(v___f_3612_, v___x_3631_, v_exportedInfo_x3f_3622_, v___y_3623_, v___y_3624_, lean_box(0));
return v___x_3632_;
}
v___jp_3633_:
{
lean_object* v_toConstantVal_3636_; uint8_t v_safety_3637_; uint8_t v___x_3638_; uint8_t v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v_toConstantVal_3636_ = lean_ctor_get(v_defn_3617_, 0);
v_safety_3637_ = lean_ctor_get_uint8(v_defn_3617_, sizeof(void*)*4);
v___x_3638_ = 0;
v___x_3639_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_3637_, v___x_3638_);
lean_inc_ref(v_toConstantVal_3636_);
v___x_3640_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3640_, 0, v_toConstantVal_3636_);
lean_ctor_set_uint8(v___x_3640_, sizeof(void*)*1, v___x_3639_);
v___x_3641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3640_);
v___x_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
v_exportedInfo_x3f_3622_ = v___x_3642_;
v___y_3623_ = v___y_3634_;
v___y_3624_ = v___y_3635_;
goto v___jp_3621_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10___boxed(lean_object* v___f_3664_, lean_object* v_forceExpose_3665_, lean_object* v___x_3666_, lean_object* v___x_3667_, lean_object* v_cls_3668_, lean_object* v_defn_3669_, lean_object* v___y_3670_, lean_object* v___y_3671_, lean_object* v___y_3672_){
_start:
{
uint8_t v_forceExpose_boxed_3673_; uint8_t v___x_63943__boxed_3674_; lean_object* v_res_3675_; 
v_forceExpose_boxed_3673_ = lean_unbox(v_forceExpose_3665_);
v___x_63943__boxed_3674_ = lean_unbox(v___x_3666_);
v_res_3675_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_3664_, v_forceExpose_boxed_3673_, v___x_63943__boxed_3674_, v___x_3667_, v_cls_3668_, v_defn_3669_, v___y_3670_, v___y_3671_);
lean_dec(v___y_3671_);
lean_dec_ref(v___y_3670_);
return v_res_3675_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(lean_object* v_val_3676_, uint8_t v_forceExpose_3677_, lean_object* v___f_3678_, lean_object* v_____r_3679_, lean_object* v___y_3680_, lean_object* v___y_3681_){
_start:
{
lean_object* v_toConstantVal_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; 
v_toConstantVal_3683_ = lean_ctor_get(v_val_3676_, 0);
lean_inc_ref(v_toConstantVal_3683_);
v___x_3684_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_3684_, 0, v_toConstantVal_3683_);
lean_ctor_set_uint8(v___x_3684_, sizeof(void*)*1, v_forceExpose_3677_);
v___x_3685_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
v___x_3687_ = lean_box(0);
lean_inc(v___y_3681_);
lean_inc_ref(v___y_3680_);
v___x_3688_ = lean_apply_5(v___f_3678_, v___x_3687_, v___x_3686_, v___y_3680_, v___y_3681_, lean_box(0));
return v___x_3688_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12___boxed(lean_object* v_val_3689_, lean_object* v_forceExpose_3690_, lean_object* v___f_3691_, lean_object* v_____r_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
uint8_t v_forceExpose_boxed_3696_; lean_object* v_res_3697_; 
v_forceExpose_boxed_3696_ = lean_unbox(v_forceExpose_3690_);
v_res_3697_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_3689_, v_forceExpose_boxed_3696_, v___f_3691_, v_____r_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v_val_3689_);
return v_res_3697_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(lean_object* v_x_3698_, lean_object* v_x_3699_){
_start:
{
if (lean_obj_tag(v_x_3699_) == 0)
{
return v_x_3698_;
}
else
{
lean_object* v_head_3700_; lean_object* v_tail_3701_; lean_object* v___x_3702_; 
v_head_3700_ = lean_ctor_get(v_x_3699_, 0);
lean_inc(v_head_3700_);
v_tail_3701_ = lean_ctor_get(v_x_3699_, 1);
lean_inc(v_tail_3701_);
lean_dec_ref_known(v_x_3699_, 2);
v___x_3702_ = l___private_Lean_AddDecl_0__Lean_registerNamePrefixes(v_x_3698_, v_head_3700_);
v_x_3698_ = v___x_3702_;
v_x_3699_ = v_tail_3701_;
goto _start;
}
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0(void){
_start:
{
lean_object* v_cls_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; 
v_cls_3704_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
v___x_3705_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__0));
v___x_3706_ = l_Lean_Name_append(v___x_3705_, v_cls_3704_);
return v___x_3706_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__1));
v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__3));
v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
return v___x_3712_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore(lean_object* v_decl_3713_, uint8_t v_forceExpose_3714_, lean_object* v_a_3715_, lean_object* v_a_3716_){
_start:
{
lean_object* v___y_3719_; lean_object* v___y_3720_; lean_object* v_a_3721_; lean_object* v___y_3732_; lean_object* v___y_3733_; lean_object* v_a_3734_; lean_object* v___y_3745_; lean_object* v___y_3746_; lean_object* v_a_3747_; lean_object* v___y_3758_; lean_object* v___y_3759_; lean_object* v_a_3760_; lean_object* v_options_3770_; lean_object* v_inheritedTraceOptions_3771_; uint8_t v_hasTrace_3772_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; lean_object* v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; uint8_t v___y_3783_; lean_object* v___y_3784_; lean_object* v___y_3848_; lean_object* v___y_3849_; lean_object* v___y_3850_; lean_object* v___y_3851_; uint8_t v___y_3852_; lean_object* v___y_3853_; lean_object* v___y_3854_; lean_object* v___y_3855_; lean_object* v___y_3856_; lean_object* v___y_3857_; lean_object* v___y_3880_; uint8_t v___y_3881_; lean_object* v___y_3882_; lean_object* v_exportedInfo_x3f_3883_; lean_object* v___y_3884_; lean_object* v___y_3885_; lean_object* v___y_3895_; uint8_t v___y_3896_; lean_object* v___y_3897_; lean_object* v___y_3898_; lean_object* v___y_3899_; lean_object* v___y_3902_; uint8_t v___y_3903_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v_cls_3908_; 
v_options_3770_ = lean_ctor_get(v_a_3715_, 2);
v_inheritedTraceOptions_3771_ = lean_ctor_get(v_a_3715_, 13);
v_hasTrace_3772_ = lean_ctor_get_uint8(v_options_3770_, sizeof(void*)*1);
v_cls_3908_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_initFn___closed__1_00___x40_Lean_AddDecl_337188874____hygCtx___hyg_2_));
if (v_hasTrace_3772_ == 0)
{
lean_object* v___x_3909_; lean_object* v_env_3910_; lean_object* v_nextMacroScope_3911_; lean_object* v_ngen_3912_; lean_object* v_auxDeclNGen_3913_; lean_object* v_traceState_3914_; lean_object* v_messages_3915_; lean_object* v_infoState_3916_; lean_object* v_snapshotTasks_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_4106_; 
v___x_3909_ = lean_st_ref_take(v_a_3716_);
v_env_3910_ = lean_ctor_get(v___x_3909_, 0);
v_nextMacroScope_3911_ = lean_ctor_get(v___x_3909_, 1);
v_ngen_3912_ = lean_ctor_get(v___x_3909_, 2);
v_auxDeclNGen_3913_ = lean_ctor_get(v___x_3909_, 3);
v_traceState_3914_ = lean_ctor_get(v___x_3909_, 4);
v_messages_3915_ = lean_ctor_get(v___x_3909_, 6);
v_infoState_3916_ = lean_ctor_get(v___x_3909_, 7);
v_snapshotTasks_3917_ = lean_ctor_get(v___x_3909_, 8);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_4106_ == 0)
{
lean_object* v_unused_4107_; 
v_unused_4107_ = lean_ctor_get(v___x_3909_, 5);
lean_dec(v_unused_4107_);
v___x_3919_ = v___x_3909_;
v_isShared_3920_ = v_isSharedCheck_4106_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_snapshotTasks_3917_);
lean_inc(v_infoState_3916_);
lean_inc(v_messages_3915_);
lean_inc(v_traceState_3914_);
lean_inc(v_auxDeclNGen_3913_);
lean_inc(v_ngen_3912_);
lean_inc(v_nextMacroScope_3911_);
lean_inc(v_env_3910_);
lean_dec(v___x_3909_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_4106_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3925_; 
lean_inc(v_decl_3713_);
v___x_3921_ = l_Lean_Declaration_getNames(v_decl_3713_);
v___x_3922_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_3910_, v___x_3921_);
v___x_3923_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 5, v___x_3923_);
lean_ctor_set(v___x_3919_, 0, v___x_3922_);
v___x_3925_ = v___x_3919_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_3922_);
lean_ctor_set(v_reuseFailAlloc_4105_, 1, v_nextMacroScope_3911_);
lean_ctor_set(v_reuseFailAlloc_4105_, 2, v_ngen_3912_);
lean_ctor_set(v_reuseFailAlloc_4105_, 3, v_auxDeclNGen_3913_);
lean_ctor_set(v_reuseFailAlloc_4105_, 4, v_traceState_3914_);
lean_ctor_set(v_reuseFailAlloc_4105_, 5, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_4105_, 6, v_messages_3915_);
lean_ctor_set(v_reuseFailAlloc_4105_, 7, v_infoState_3916_);
lean_ctor_set(v_reuseFailAlloc_4105_, 8, v_snapshotTasks_3917_);
v___x_3925_ = v_reuseFailAlloc_4105_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___y_3929_; uint8_t v___y_3930_; lean_object* v___y_3931_; lean_object* v___y_3932_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v_fst_3984_; lean_object* v_fst_3985_; uint8_t v_snd_3986_; lean_object* v_exportedInfo_x3f_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3999_; lean_object* v_toConstantVal_4000_; lean_object* v_exportedInfo_x3f_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4008_; lean_object* v_exportedInfo_x3f_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4014_; lean_object* v_toConstantVal_4015_; uint8_t v_safety_4016_; lean_object* v___y_4017_; lean_object* v___y_4018_; lean_object* v___y_4025_; lean_object* v___y_4026_; lean_object* v___y_4027_; lean_object* v_defn_4031_; lean_object* v___y_4032_; lean_object* v___y_4033_; 
v___x_3926_ = lean_st_ref_set(v_a_3716_, v___x_3925_);
v___x_3927_ = lean_box(0);
switch(lean_obj_tag(v_decl_3713_))
{
case 2:
{
lean_object* v_val_4055_; lean_object* v_exportedInfo_x3f_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___x_4064_; 
v_val_4055_ = lean_ctor_get(v_decl_3713_, 0);
v___x_4064_ = lean_st_ref_get(v_a_3716_);
if (v_forceExpose_3714_ == 0)
{
lean_object* v_env_4065_; lean_object* v___x_4066_; uint8_t v_isModule_4067_; 
v_env_4065_ = lean_ctor_get(v___x_4064_, 0);
lean_inc_ref(v_env_4065_);
lean_dec(v___x_4064_);
v___x_4066_ = l_Lean_Environment_header(v_env_4065_);
lean_dec_ref(v_env_4065_);
v_isModule_4067_ = lean_ctor_get_uint8(v___x_4066_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4066_);
if (v_isModule_4067_ == 0)
{
v_exportedInfo_x3f_4057_ = v___x_3927_;
v___y_4058_ = v_a_3715_;
v___y_4059_ = v_a_3716_;
goto v___jp_4056_;
}
else
{
lean_object* v_toConstantVal_4068_; lean_object* v___x_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; 
v_toConstantVal_4068_ = lean_ctor_get(v_val_4055_, 0);
lean_inc_ref(v_toConstantVal_4068_);
v___x_4069_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4069_, 0, v_toConstantVal_4068_);
lean_ctor_set_uint8(v___x_4069_, sizeof(void*)*1, v_hasTrace_3772_);
v___x_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4070_, 0, v___x_4069_);
v___x_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4071_, 0, v___x_4070_);
v_exportedInfo_x3f_4057_ = v___x_4071_;
v___y_4058_ = v_a_3715_;
v___y_4059_ = v_a_3716_;
goto v___jp_4056_;
}
}
else
{
lean_dec(v___x_4064_);
v_exportedInfo_x3f_4057_ = v___x_3927_;
v___y_4058_ = v_a_3715_;
v___y_4059_ = v_a_3716_;
goto v___jp_4056_;
}
v___jp_4056_:
{
lean_object* v_toConstantVal_4060_; lean_object* v_name_4061_; lean_object* v___x_4062_; uint8_t v___x_4063_; 
v_toConstantVal_4060_ = lean_ctor_get(v_val_4055_, 0);
v_name_4061_ = lean_ctor_get(v_toConstantVal_4060_, 0);
lean_inc_ref(v_val_4055_);
v___x_4062_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4062_, 0, v_val_4055_);
v___x_4063_ = 1;
lean_inc(v_name_4061_);
v_fst_3984_ = v_name_4061_;
v_fst_3985_ = v___x_4062_;
v_snd_3986_ = v___x_4063_;
v_exportedInfo_x3f_3987_ = v_exportedInfo_x3f_4057_;
v___y_3988_ = v___y_4058_;
v___y_3989_ = v___y_4059_;
goto v___jp_3983_;
}
}
case 1:
{
lean_object* v_val_4072_; 
v_val_4072_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref(v_val_4072_);
v_defn_4031_ = v_val_4072_;
v___y_4032_ = v_a_3715_;
v___y_4033_ = v_a_3716_;
goto v___jp_4030_;
}
case 5:
{
lean_object* v_defns_4073_; 
v_defns_4073_ = lean_ctor_get(v_decl_3713_, 0);
if (lean_obj_tag(v_defns_4073_) == 1)
{
lean_object* v_tail_4074_; 
v_tail_4074_ = lean_ctor_get(v_defns_4073_, 1);
if (lean_obj_tag(v_tail_4074_) == 0)
{
lean_object* v_head_4075_; 
v_head_4075_ = lean_ctor_get(v_defns_4073_, 0);
lean_inc(v_head_4075_);
v_defn_4031_ = v_head_4075_;
v___y_4032_ = v_a_3715_;
v___y_4033_ = v_a_3716_;
goto v___jp_4030_;
}
else
{
lean_object* v___x_4076_; 
v___x_4076_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v_a_3715_, v_a_3716_);
return v___x_4076_;
}
}
else
{
lean_object* v___x_4077_; 
v___x_4077_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v_a_3715_, v_a_3716_);
return v___x_4077_;
}
}
case 3:
{
lean_object* v_val_4078_; lean_object* v_exportedInfo_x3f_4080_; lean_object* v___y_4081_; lean_object* v___y_4082_; lean_object* v___x_4087_; lean_object* v___x_4088_; 
v_val_4078_ = lean_ctor_get(v_decl_3713_, 0);
v___x_4087_ = lean_st_ref_get(v_a_3716_);
v___x_4088_ = lean_st_ref_get(v_a_3716_);
if (v_forceExpose_3714_ == 0)
{
lean_object* v_env_4089_; lean_object* v_env_4090_; lean_object* v___x_4091_; uint8_t v_isModule_4092_; 
v_env_4089_ = lean_ctor_get(v___x_4087_, 0);
lean_inc_ref(v_env_4089_);
lean_dec(v___x_4087_);
v_env_4090_ = lean_ctor_get(v___x_4088_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4088_);
v___x_4091_ = l_Lean_Environment_header(v_env_4089_);
lean_dec_ref(v_env_4089_);
v_isModule_4092_ = lean_ctor_get_uint8(v___x_4091_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4091_);
if (v_isModule_4092_ == 0)
{
lean_dec_ref(v_env_4090_);
v_exportedInfo_x3f_4080_ = v___x_3927_;
v___y_4081_ = v_a_3715_;
v___y_4082_ = v_a_3716_;
goto v___jp_4079_;
}
else
{
uint8_t v_isExporting_4093_; 
v_isExporting_4093_ = lean_ctor_get_uint8(v_env_4090_, sizeof(void*)*8);
lean_dec_ref(v_env_4090_);
if (v_isExporting_4093_ == 0)
{
lean_object* v_toConstantVal_4094_; uint8_t v_isUnsafe_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; 
v_toConstantVal_4094_ = lean_ctor_get(v_val_4078_, 0);
v_isUnsafe_4095_ = lean_ctor_get_uint8(v_val_4078_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4094_);
v___x_4096_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4096_, 0, v_toConstantVal_4094_);
lean_ctor_set_uint8(v___x_4096_, sizeof(void*)*1, v_isUnsafe_4095_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v___x_4096_);
v___x_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4098_, 0, v___x_4097_);
v_exportedInfo_x3f_4080_ = v___x_4098_;
v___y_4081_ = v_a_3715_;
v___y_4082_ = v_a_3716_;
goto v___jp_4079_;
}
else
{
v_exportedInfo_x3f_4080_ = v___x_3927_;
v___y_4081_ = v_a_3715_;
v___y_4082_ = v_a_3716_;
goto v___jp_4079_;
}
}
}
else
{
lean_dec(v___x_4088_);
lean_dec(v___x_4087_);
v_exportedInfo_x3f_4080_ = v___x_3927_;
v___y_4081_ = v_a_3715_;
v___y_4082_ = v_a_3716_;
goto v___jp_4079_;
}
v___jp_4079_:
{
lean_object* v_toConstantVal_4083_; lean_object* v_name_4084_; lean_object* v___x_4085_; uint8_t v___x_4086_; 
v_toConstantVal_4083_ = lean_ctor_get(v_val_4078_, 0);
v_name_4084_ = lean_ctor_get(v_toConstantVal_4083_, 0);
lean_inc_ref(v_val_4078_);
v___x_4085_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4085_, 0, v_val_4078_);
v___x_4086_ = 3;
lean_inc(v_name_4084_);
v_fst_3984_ = v_name_4084_;
v_fst_3985_ = v___x_4085_;
v_snd_3986_ = v___x_4086_;
v_exportedInfo_x3f_3987_ = v_exportedInfo_x3f_4080_;
v___y_3988_ = v___y_4081_;
v___y_3989_ = v___y_4082_;
goto v___jp_3983_;
}
}
case 0:
{
lean_object* v_val_4099_; lean_object* v_toConstantVal_4100_; lean_object* v_name_4101_; lean_object* v___x_4102_; uint8_t v___x_4103_; 
v_val_4099_ = lean_ctor_get(v_decl_3713_, 0);
v_toConstantVal_4100_ = lean_ctor_get(v_val_4099_, 0);
v_name_4101_ = lean_ctor_get(v_toConstantVal_4100_, 0);
lean_inc_ref(v_val_4099_);
v___x_4102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4102_, 0, v_val_4099_);
v___x_4103_ = 2;
lean_inc(v_name_4101_);
v_fst_3984_ = v_name_4101_;
v_fst_3985_ = v___x_4102_;
v_snd_3986_ = v___x_4103_;
v_exportedInfo_x3f_3987_ = v___x_3927_;
v___y_3988_ = v_a_3715_;
v___y_3989_ = v_a_3716_;
goto v___jp_3983_;
}
default: 
{
lean_object* v___x_4104_; 
v___x_4104_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v_a_3715_, v_a_3716_);
return v___x_4104_;
}
}
v___jp_3928_:
{
lean_object* v___x_3935_; uint8_t v___x_3936_; 
lean_inc(v_decl_3713_);
v___x_3935_ = l_Lean_Declaration_getTopLevelNames(v_decl_3713_);
v___x_3936_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_3935_);
lean_dec(v___x_3935_);
if (v___x_3936_ == 0)
{
if (lean_obj_tag(v___y_3932_) == 0)
{
lean_object* v_options_3937_; uint8_t v_hasTrace_3938_; 
v_options_3937_ = lean_ctor_get(v___y_3933_, 2);
v_hasTrace_3938_ = lean_ctor_get_uint8(v_options_3937_, sizeof(void*)*1);
if (v_hasTrace_3938_ == 0)
{
v___y_3895_ = v___y_3929_;
v___y_3896_ = v___y_3930_;
v___y_3897_ = v___y_3931_;
v___y_3898_ = v___y_3933_;
v___y_3899_ = v___y_3934_;
goto v___jp_3894_;
}
else
{
lean_object* v_inheritedTraceOptions_3939_; lean_object* v___x_3940_; uint8_t v___x_3941_; 
v_inheritedTraceOptions_3939_ = lean_ctor_get(v___y_3933_, 13);
v___x_3940_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3941_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3939_, v_options_3937_, v___x_3940_);
if (v___x_3941_ == 0)
{
v___y_3895_ = v___y_3929_;
v___y_3896_ = v___y_3930_;
v___y_3897_ = v___y_3931_;
v___y_3898_ = v___y_3933_;
v___y_3899_ = v___y_3934_;
goto v___jp_3894_;
}
else
{
lean_object* v___x_3942_; lean_object* v___x_3943_; 
v___x_3942_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_3943_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_3942_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3943_) == 0)
{
lean_dec_ref_known(v___x_3943_, 1);
v___y_3895_ = v___y_3929_;
v___y_3896_ = v___y_3930_;
v___y_3897_ = v___y_3931_;
v___y_3898_ = v___y_3933_;
v___y_3899_ = v___y_3934_;
goto v___jp_3894_;
}
else
{
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3929_);
lean_dec(v_decl_3713_);
return v___x_3943_;
}
}
}
}
else
{
lean_object* v___x_3944_; lean_object* v_env_3945_; lean_object* v_nextMacroScope_3946_; lean_object* v_ngen_3947_; lean_object* v_auxDeclNGen_3948_; lean_object* v_traceState_3949_; lean_object* v_messages_3950_; lean_object* v_infoState_3951_; lean_object* v_snapshotTasks_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3963_; 
v___x_3944_ = lean_st_ref_take(v___y_3934_);
v_env_3945_ = lean_ctor_get(v___x_3944_, 0);
v_nextMacroScope_3946_ = lean_ctor_get(v___x_3944_, 1);
v_ngen_3947_ = lean_ctor_get(v___x_3944_, 2);
v_auxDeclNGen_3948_ = lean_ctor_get(v___x_3944_, 3);
v_traceState_3949_ = lean_ctor_get(v___x_3944_, 4);
v_messages_3950_ = lean_ctor_get(v___x_3944_, 6);
v_infoState_3951_ = lean_ctor_get(v___x_3944_, 7);
v_snapshotTasks_3952_ = lean_ctor_get(v___x_3944_, 8);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3944_);
if (v_isSharedCheck_3963_ == 0)
{
lean_object* v_unused_3964_; 
v_unused_3964_ = lean_ctor_get(v___x_3944_, 5);
lean_dec(v_unused_3964_);
v___x_3954_ = v___x_3944_;
v_isShared_3955_ = v_isSharedCheck_3963_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_snapshotTasks_3952_);
lean_inc(v_infoState_3951_);
lean_inc(v_messages_3950_);
lean_inc(v_traceState_3949_);
lean_inc(v_auxDeclNGen_3948_);
lean_inc(v_ngen_3947_);
lean_inc(v_nextMacroScope_3946_);
lean_inc(v_env_3945_);
lean_dec(v___x_3944_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3963_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3960_; 
v___x_3956_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_3957_ = lean_box(v___y_3930_);
lean_inc(v___y_3929_);
v___x_3958_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_3956_, v_env_3945_, v___y_3929_, v___x_3957_);
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 5, v___x_3923_);
lean_ctor_set(v___x_3954_, 0, v___x_3958_);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_nextMacroScope_3946_);
lean_ctor_set(v_reuseFailAlloc_3962_, 2, v_ngen_3947_);
lean_ctor_set(v_reuseFailAlloc_3962_, 3, v_auxDeclNGen_3948_);
lean_ctor_set(v_reuseFailAlloc_3962_, 4, v_traceState_3949_);
lean_ctor_set(v_reuseFailAlloc_3962_, 5, v___x_3923_);
lean_ctor_set(v_reuseFailAlloc_3962_, 6, v_messages_3950_);
lean_ctor_set(v_reuseFailAlloc_3962_, 7, v_infoState_3951_);
lean_ctor_set(v_reuseFailAlloc_3962_, 8, v_snapshotTasks_3952_);
v___x_3960_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
lean_object* v___x_3961_; 
v___x_3961_ = lean_st_ref_set(v___y_3934_, v___x_3960_);
v___y_3880_ = v___y_3929_;
v___y_3881_ = v___y_3930_;
v___y_3882_ = v___y_3931_;
v_exportedInfo_x3f_3883_ = v___y_3932_;
v___y_3884_ = v___y_3933_;
v___y_3885_ = v___y_3934_;
goto v___jp_3879_;
}
}
}
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_a_3967_; uint8_t v___x_3968_; 
lean_dec(v___y_3932_);
v___x_3965_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_3966_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_3965_, v___y_3933_);
v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
lean_inc(v_a_3967_);
lean_dec_ref(v___x_3966_);
v___x_3968_ = lean_unbox(v_a_3967_);
lean_dec(v_a_3967_);
if (v___x_3968_ == 0)
{
lean_object* v_options_3969_; uint8_t v_hasTrace_3970_; 
v_options_3969_ = lean_ctor_get(v___y_3933_, 2);
v_hasTrace_3970_ = lean_ctor_get_uint8(v_options_3969_, sizeof(void*)*1);
if (v_hasTrace_3970_ == 0)
{
v___y_3880_ = v___y_3929_;
v___y_3881_ = v___y_3930_;
v___y_3882_ = v___y_3931_;
v_exportedInfo_x3f_3883_ = v___x_3927_;
v___y_3884_ = v___y_3933_;
v___y_3885_ = v___y_3934_;
goto v___jp_3879_;
}
else
{
lean_object* v_inheritedTraceOptions_3971_; lean_object* v___x_3972_; uint8_t v___x_3973_; 
v_inheritedTraceOptions_3971_ = lean_ctor_get(v___y_3933_, 13);
v___x_3972_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3973_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3971_, v_options_3969_, v___x_3972_);
if (v___x_3973_ == 0)
{
v___y_3880_ = v___y_3929_;
v___y_3881_ = v___y_3930_;
v___y_3882_ = v___y_3931_;
v_exportedInfo_x3f_3883_ = v___x_3927_;
v___y_3884_ = v___y_3933_;
v___y_3885_ = v___y_3934_;
goto v___jp_3879_;
}
else
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_3975_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_3974_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_dec_ref_known(v___x_3975_, 1);
v___y_3880_ = v___y_3929_;
v___y_3881_ = v___y_3930_;
v___y_3882_ = v___y_3931_;
v_exportedInfo_x3f_3883_ = v___x_3927_;
v___y_3884_ = v___y_3933_;
v___y_3885_ = v___y_3934_;
goto v___jp_3879_;
}
else
{
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3929_);
lean_dec(v_decl_3713_);
return v___x_3975_;
}
}
}
}
else
{
lean_object* v_options_3976_; uint8_t v_hasTrace_3977_; 
v_options_3976_ = lean_ctor_get(v___y_3933_, 2);
v_hasTrace_3977_ = lean_ctor_get_uint8(v_options_3976_, sizeof(void*)*1);
if (v_hasTrace_3977_ == 0)
{
v___y_3902_ = v___y_3929_;
v___y_3903_ = v___y_3930_;
v___y_3904_ = v___y_3931_;
v___y_3905_ = v___y_3933_;
v___y_3906_ = v___y_3934_;
goto v___jp_3901_;
}
else
{
lean_object* v_inheritedTraceOptions_3978_; lean_object* v___x_3979_; uint8_t v___x_3980_; 
v_inheritedTraceOptions_3978_ = lean_ctor_get(v___y_3933_, 13);
v___x_3979_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_3980_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3978_, v_options_3976_, v___x_3979_);
if (v___x_3980_ == 0)
{
v___y_3902_ = v___y_3929_;
v___y_3903_ = v___y_3930_;
v___y_3904_ = v___y_3931_;
v___y_3905_ = v___y_3933_;
v___y_3906_ = v___y_3934_;
goto v___jp_3901_;
}
else
{
lean_object* v___x_3981_; lean_object* v___x_3982_; 
v___x_3981_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_3982_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_3981_, v___y_3933_, v___y_3934_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_dec_ref_known(v___x_3982_, 1);
v___y_3902_ = v___y_3929_;
v___y_3903_ = v___y_3930_;
v___y_3904_ = v___y_3931_;
v___y_3905_ = v___y_3933_;
v___y_3906_ = v___y_3934_;
goto v___jp_3901_;
}
else
{
lean_dec_ref(v___y_3931_);
lean_dec(v___y_3929_);
lean_dec(v_decl_3713_);
return v___x_3982_;
}
}
}
}
}
}
v___jp_3983_:
{
lean_object* v___x_3990_; lean_object* v_env_3991_; uint8_t v___x_3992_; 
v___x_3990_ = lean_st_ref_get(v___y_3989_);
v_env_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc_ref(v_env_3991_);
lean_dec(v___x_3990_);
v___x_3992_ = l_Lean_Environment_containsOnBranch(v_env_3991_, v_fst_3984_);
lean_dec_ref(v_env_3991_);
if (v___x_3992_ == 0)
{
v___y_3929_ = v_fst_3984_;
v___y_3930_ = v_snd_3986_;
v___y_3931_ = v_fst_3985_;
v___y_3932_ = v_exportedInfo_x3f_3987_;
v___y_3933_ = v___y_3988_;
v___y_3934_ = v___y_3989_;
goto v___jp_3928_;
}
else
{
lean_object* v___x_3993_; lean_object* v_env_3994_; lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
lean_dec(v_exportedInfo_x3f_3987_);
lean_dec_ref(v_fst_3985_);
lean_dec(v_decl_3713_);
v___x_3993_ = lean_st_ref_get(v___y_3989_);
v_env_3994_ = lean_ctor_get(v___x_3993_, 0);
lean_inc_ref(v_env_3994_);
lean_dec(v___x_3993_);
v___x_3995_ = lean_elab_environment_to_kernel_env(v_env_3994_);
v___x_3996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3996_, 0, v___x_3995_);
lean_ctor_set(v___x_3996_, 1, v_fst_3984_);
v___x_3997_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_3996_, v___y_3988_, v___y_3989_);
return v___x_3997_;
}
}
v___jp_3998_:
{
lean_object* v_name_4004_; lean_object* v___x_4005_; uint8_t v___x_4006_; 
v_name_4004_ = lean_ctor_get(v_toConstantVal_4000_, 0);
lean_inc(v_name_4004_);
lean_dec_ref(v_toConstantVal_4000_);
v___x_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4005_, 0, v___y_3999_);
v___x_4006_ = 0;
v_fst_3984_ = v_name_4004_;
v_fst_3985_ = v___x_4005_;
v_snd_3986_ = v___x_4006_;
v_exportedInfo_x3f_3987_ = v_exportedInfo_x3f_4001_;
v___y_3988_ = v___y_4002_;
v___y_3989_ = v___y_4003_;
goto v___jp_3983_;
}
v___jp_4007_:
{
lean_object* v_toConstantVal_4012_; 
v_toConstantVal_4012_ = lean_ctor_get(v___y_4008_, 0);
lean_inc_ref(v_toConstantVal_4012_);
v___y_3999_ = v___y_4008_;
v_toConstantVal_4000_ = v_toConstantVal_4012_;
v_exportedInfo_x3f_4001_ = v_exportedInfo_x3f_4009_;
v___y_4002_ = v___y_4010_;
v___y_4003_ = v___y_4011_;
goto v___jp_3998_;
}
v___jp_4013_:
{
uint8_t v___x_4019_; uint8_t v___x_4020_; lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4019_ = 0;
v___x_4020_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4016_, v___x_4019_);
lean_inc_ref(v_toConstantVal_4015_);
v___x_4021_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4021_, 0, v_toConstantVal_4015_);
lean_ctor_set_uint8(v___x_4021_, sizeof(void*)*1, v___x_4020_);
v___x_4022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4022_, 0, v___x_4021_);
v___x_4023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
v___y_3999_ = v___y_4014_;
v_toConstantVal_4000_ = v_toConstantVal_4015_;
v_exportedInfo_x3f_4001_ = v___x_4023_;
v___y_4002_ = v___y_4017_;
v___y_4003_ = v___y_4018_;
goto v___jp_3998_;
}
v___jp_4024_:
{
lean_object* v_toConstantVal_4028_; uint8_t v_safety_4029_; 
v_toConstantVal_4028_ = lean_ctor_get(v___y_4025_, 0);
lean_inc_ref(v_toConstantVal_4028_);
v_safety_4029_ = lean_ctor_get_uint8(v___y_4025_, sizeof(void*)*4);
v___y_4014_ = v___y_4025_;
v_toConstantVal_4015_ = v_toConstantVal_4028_;
v_safety_4016_ = v_safety_4029_;
v___y_4017_ = v___y_4026_;
v___y_4018_ = v___y_4027_;
goto v___jp_4013_;
}
v___jp_4030_:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_st_ref_get(v___y_4033_);
v___x_4035_ = lean_st_ref_get(v___y_4033_);
if (v_forceExpose_3714_ == 0)
{
lean_object* v_env_4036_; lean_object* v_env_4037_; lean_object* v___x_4038_; uint8_t v_isModule_4039_; 
v_env_4036_ = lean_ctor_get(v___x_4034_, 0);
lean_inc_ref(v_env_4036_);
lean_dec(v___x_4034_);
v_env_4037_ = lean_ctor_get(v___x_4035_, 0);
lean_inc_ref(v_env_4037_);
lean_dec(v___x_4035_);
v___x_4038_ = l_Lean_Environment_header(v_env_4036_);
lean_dec_ref(v_env_4036_);
v_isModule_4039_ = lean_ctor_get_uint8(v___x_4038_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4038_);
if (v_isModule_4039_ == 0)
{
lean_dec_ref(v_env_4037_);
v___y_4008_ = v_defn_4031_;
v_exportedInfo_x3f_4009_ = v___x_3927_;
v___y_4010_ = v___y_4032_;
v___y_4011_ = v___y_4033_;
goto v___jp_4007_;
}
else
{
uint8_t v_isExporting_4040_; 
v_isExporting_4040_ = lean_ctor_get_uint8(v_env_4037_, sizeof(void*)*8);
lean_dec_ref(v_env_4037_);
if (v_isExporting_4040_ == 0)
{
lean_object* v_options_4041_; uint8_t v_hasTrace_4042_; 
v_options_4041_ = lean_ctor_get(v___y_4032_, 2);
v_hasTrace_4042_ = lean_ctor_get_uint8(v_options_4041_, sizeof(void*)*1);
if (v_hasTrace_4042_ == 0)
{
v___y_4025_ = v_defn_4031_;
v___y_4026_ = v___y_4032_;
v___y_4027_ = v___y_4033_;
goto v___jp_4024_;
}
else
{
lean_object* v_inheritedTraceOptions_4043_; lean_object* v___x_4044_; uint8_t v___x_4045_; 
v_inheritedTraceOptions_4043_ = lean_ctor_get(v___y_4032_, 13);
v___x_4044_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4045_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4043_, v_options_4041_, v___x_4044_);
if (v___x_4045_ == 0)
{
v___y_4025_ = v_defn_4031_;
v___y_4026_ = v___y_4032_;
v___y_4027_ = v___y_4033_;
goto v___jp_4024_;
}
else
{
lean_object* v_toConstantVal_4046_; uint8_t v_safety_4047_; lean_object* v_name_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v_toConstantVal_4046_ = lean_ctor_get(v_defn_4031_, 0);
lean_inc_ref(v_toConstantVal_4046_);
v_safety_4047_ = lean_ctor_get_uint8(v_defn_4031_, sizeof(void*)*4);
v_name_4048_ = lean_ctor_get(v_toConstantVal_4046_, 0);
v___x_4049_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4048_);
v___x_4050_ = l_Lean_MessageData_ofName(v_name_4048_);
v___x_4051_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4049_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
v___x_4052_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4051_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
v___x_4054_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4053_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_dec_ref_known(v___x_4054_, 1);
v___y_4014_ = v_defn_4031_;
v_toConstantVal_4015_ = v_toConstantVal_4046_;
v_safety_4016_ = v_safety_4047_;
v___y_4017_ = v___y_4032_;
v___y_4018_ = v___y_4033_;
goto v___jp_4013_;
}
else
{
lean_dec_ref(v_toConstantVal_4046_);
lean_dec_ref(v_defn_4031_);
lean_dec(v_decl_3713_);
return v___x_4054_;
}
}
}
}
else
{
v___y_4008_ = v_defn_4031_;
v_exportedInfo_x3f_4009_ = v___x_3927_;
v___y_4010_ = v___y_4032_;
v___y_4011_ = v___y_4033_;
goto v___jp_4007_;
}
}
}
else
{
lean_dec(v___x_4035_);
lean_dec(v___x_4034_);
v___y_4008_ = v_defn_4031_;
v_exportedInfo_x3f_4009_ = v___x_3927_;
v___y_4010_ = v___y_4032_;
v___y_4011_ = v___y_4033_;
goto v___jp_4007_;
}
}
}
}
}
else
{
lean_object* v___f_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; uint8_t v___x_4111_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v_a_4115_; lean_object* v___y_4125_; lean_object* v___y_4126_; lean_object* v___y_4127_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; lean_object* v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4159_; lean_object* v___y_4160_; lean_object* v_a_4161_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4201_; lean_object* v___y_4202_; lean_object* v___y_4203_; lean_object* v___y_4204_; lean_object* v___y_4218_; lean_object* v___y_4219_; lean_object* v___y_4220_; lean_object* v___y_4221_; lean_object* v___y_4222_; lean_object* v___y_4223_; uint8_t v___y_4224_; lean_object* v___y_4225_; lean_object* v___y_4226_; lean_object* v___y_4231_; lean_object* v___y_4232_; lean_object* v___y_4233_; lean_object* v___y_4234_; lean_object* v___y_4238_; lean_object* v___y_4239_; lean_object* v___y_4240_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; 
lean_inc(v_decl_3713_);
v___f_4108_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__1___boxed), 5, 1);
lean_closure_set(v___f_4108_, 0, v_decl_3713_);
v___x_4109_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_warnIfUsesSorry_spec__2_spec__4_spec__9___closed__0));
v___x_4110_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__0);
v___x_4111_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3771_, v_options_3770_, v___x_4110_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4411_; uint8_t v___x_4412_; lean_object* v___y_4414_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4420_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; uint8_t v___y_4493_; lean_object* v___y_4494_; lean_object* v___y_4495_; lean_object* v___y_4496_; uint8_t v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v_exportedInfo_x3f_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; uint8_t v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4537_; uint8_t v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; lean_object* v___y_4543_; lean_object* v___y_4544_; 
v___x_4411_ = l_Lean_trace_profiler;
v___x_4412_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3770_, v___x_4411_);
if (v___x_4412_ == 0)
{
lean_object* v___x_4546_; lean_object* v_env_4547_; lean_object* v_nextMacroScope_4548_; lean_object* v_ngen_4549_; lean_object* v_auxDeclNGen_4550_; lean_object* v_traceState_4551_; lean_object* v_messages_4552_; lean_object* v_infoState_4553_; lean_object* v_snapshotTasks_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4790_; 
lean_dec_ref(v___f_4108_);
v___x_4546_ = lean_st_ref_take(v_a_3716_);
v_env_4547_ = lean_ctor_get(v___x_4546_, 0);
v_nextMacroScope_4548_ = lean_ctor_get(v___x_4546_, 1);
v_ngen_4549_ = lean_ctor_get(v___x_4546_, 2);
v_auxDeclNGen_4550_ = lean_ctor_get(v___x_4546_, 3);
v_traceState_4551_ = lean_ctor_get(v___x_4546_, 4);
v_messages_4552_ = lean_ctor_get(v___x_4546_, 6);
v_infoState_4553_ = lean_ctor_get(v___x_4546_, 7);
v_snapshotTasks_4554_ = lean_ctor_get(v___x_4546_, 8);
v_isSharedCheck_4790_ = !lean_is_exclusive(v___x_4546_);
if (v_isSharedCheck_4790_ == 0)
{
lean_object* v_unused_4791_; 
v_unused_4791_ = lean_ctor_get(v___x_4546_, 5);
lean_dec(v_unused_4791_);
v___x_4556_ = v___x_4546_;
v_isShared_4557_ = v_isSharedCheck_4790_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_snapshotTasks_4554_);
lean_inc(v_infoState_4553_);
lean_inc(v_messages_4552_);
lean_inc(v_traceState_4551_);
lean_inc(v_auxDeclNGen_4550_);
lean_inc(v_ngen_4549_);
lean_inc(v_nextMacroScope_4548_);
lean_inc(v_env_4547_);
lean_dec(v___x_4546_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4790_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___y_4562_; lean_object* v___y_4563_; lean_object* v___y_4564_; lean_object* v___y_4565_; uint8_t v___y_4566_; lean_object* v___y_4567_; lean_object* v___x_4590_; 
lean_inc(v_decl_3713_);
v___x_4558_ = l_Lean_Declaration_getNames(v_decl_3713_);
v___x_4559_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4547_, v___x_4558_);
v___x_4560_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4557_ == 0)
{
lean_ctor_set(v___x_4556_, 5, v___x_4560_);
lean_ctor_set(v___x_4556_, 0, v___x_4559_);
v___x_4590_ = v___x_4556_;
goto v_reusejp_4589_;
}
else
{
lean_object* v_reuseFailAlloc_4789_; 
v_reuseFailAlloc_4789_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4789_, 0, v___x_4559_);
lean_ctor_set(v_reuseFailAlloc_4789_, 1, v_nextMacroScope_4548_);
lean_ctor_set(v_reuseFailAlloc_4789_, 2, v_ngen_4549_);
lean_ctor_set(v_reuseFailAlloc_4789_, 3, v_auxDeclNGen_4550_);
lean_ctor_set(v_reuseFailAlloc_4789_, 4, v_traceState_4551_);
lean_ctor_set(v_reuseFailAlloc_4789_, 5, v___x_4560_);
lean_ctor_set(v_reuseFailAlloc_4789_, 6, v_messages_4552_);
lean_ctor_set(v_reuseFailAlloc_4789_, 7, v_infoState_4553_);
lean_ctor_set(v_reuseFailAlloc_4789_, 8, v_snapshotTasks_4554_);
v___x_4590_ = v_reuseFailAlloc_4789_;
goto v_reusejp_4589_;
}
v___jp_4561_:
{
lean_object* v___x_4568_; lean_object* v_env_4569_; lean_object* v_nextMacroScope_4570_; lean_object* v_ngen_4571_; lean_object* v_auxDeclNGen_4572_; lean_object* v_traceState_4573_; lean_object* v_messages_4574_; lean_object* v_infoState_4575_; lean_object* v_snapshotTasks_4576_; lean_object* v___x_4578_; uint8_t v_isShared_4579_; uint8_t v_isSharedCheck_4587_; 
v___x_4568_ = lean_st_ref_take(v___y_4562_);
v_env_4569_ = lean_ctor_get(v___x_4568_, 0);
v_nextMacroScope_4570_ = lean_ctor_get(v___x_4568_, 1);
v_ngen_4571_ = lean_ctor_get(v___x_4568_, 2);
v_auxDeclNGen_4572_ = lean_ctor_get(v___x_4568_, 3);
v_traceState_4573_ = lean_ctor_get(v___x_4568_, 4);
v_messages_4574_ = lean_ctor_get(v___x_4568_, 6);
v_infoState_4575_ = lean_ctor_get(v___x_4568_, 7);
v_snapshotTasks_4576_ = lean_ctor_get(v___x_4568_, 8);
v_isSharedCheck_4587_ = !lean_is_exclusive(v___x_4568_);
if (v_isSharedCheck_4587_ == 0)
{
lean_object* v_unused_4588_; 
v_unused_4588_ = lean_ctor_get(v___x_4568_, 5);
lean_dec(v_unused_4588_);
v___x_4578_ = v___x_4568_;
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
else
{
lean_inc(v_snapshotTasks_4576_);
lean_inc(v_infoState_4575_);
lean_inc(v_messages_4574_);
lean_inc(v_traceState_4573_);
lean_inc(v_auxDeclNGen_4572_);
lean_inc(v_ngen_4571_);
lean_inc(v_nextMacroScope_4570_);
lean_inc(v_env_4569_);
lean_dec(v___x_4568_);
v___x_4578_ = lean_box(0);
v_isShared_4579_ = v_isSharedCheck_4587_;
goto v_resetjp_4577_;
}
v_resetjp_4577_:
{
lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v___x_4584_; 
v___x_4580_ = l___private_Lean_OriginalConstKind_0__Lean_privateConstKindsExt;
v___x_4581_ = lean_box(v___y_4566_);
lean_inc(v___y_4567_);
v___x_4582_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_4580_, v_env_4569_, v___y_4567_, v___x_4581_);
if (v_isShared_4579_ == 0)
{
lean_ctor_set(v___x_4578_, 5, v___x_4560_);
lean_ctor_set(v___x_4578_, 0, v___x_4582_);
v___x_4584_ = v___x_4578_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4586_; 
v_reuseFailAlloc_4586_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4586_, 0, v___x_4582_);
lean_ctor_set(v_reuseFailAlloc_4586_, 1, v_nextMacroScope_4570_);
lean_ctor_set(v_reuseFailAlloc_4586_, 2, v_ngen_4571_);
lean_ctor_set(v_reuseFailAlloc_4586_, 3, v_auxDeclNGen_4572_);
lean_ctor_set(v_reuseFailAlloc_4586_, 4, v_traceState_4573_);
lean_ctor_set(v_reuseFailAlloc_4586_, 5, v___x_4560_);
lean_ctor_set(v_reuseFailAlloc_4586_, 6, v_messages_4574_);
lean_ctor_set(v_reuseFailAlloc_4586_, 7, v_infoState_4575_);
lean_ctor_set(v_reuseFailAlloc_4586_, 8, v_snapshotTasks_4576_);
v___x_4584_ = v_reuseFailAlloc_4586_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
lean_object* v___x_4585_; 
v___x_4585_ = lean_st_ref_set(v___y_4562_, v___x_4584_);
v___y_4518_ = v___y_4566_;
v___y_4519_ = v___y_4565_;
v___y_4520_ = v___y_4567_;
v_exportedInfo_x3f_4521_ = v___y_4564_;
v___y_4522_ = v___y_4563_;
v___y_4523_ = v___y_4562_;
goto v___jp_4517_;
}
}
}
v_reusejp_4589_:
{
lean_object* v___x_4591_; lean_object* v___y_4593_; lean_object* v_options_4594_; lean_object* v_inheritedTraceOptions_4595_; lean_object* v___y_4596_; lean_object* v___x_4602_; lean_object* v___y_4604_; uint8_t v___y_4605_; lean_object* v___y_4606_; lean_object* v___y_4607_; lean_object* v___y_4608_; lean_object* v___y_4609_; lean_object* v_fst_4635_; lean_object* v_fst_4636_; uint8_t v_snd_4637_; lean_object* v_exportedInfo_x3f_4638_; lean_object* v___y_4639_; lean_object* v___y_4640_; lean_object* v___y_4650_; lean_object* v_toConstantVal_4651_; lean_object* v_exportedInfo_x3f_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4659_; lean_object* v_toConstantVal_4660_; uint8_t v_safety_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4670_; lean_object* v___y_4671_; lean_object* v___y_4672_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4693_; lean_object* v_exportedInfo_x3f_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4699_; lean_object* v___y_4700_; lean_object* v___y_4701_; lean_object* v___y_4702_; lean_object* v___y_4703_; lean_object* v_defn_4708_; lean_object* v___y_4709_; lean_object* v___y_4710_; 
v___x_4591_ = lean_st_ref_set(v_a_3716_, v___x_4590_);
v___x_4602_ = lean_box(0);
switch(lean_obj_tag(v_decl_3713_))
{
case 2:
{
lean_object* v_val_4717_; lean_object* v_exportedInfo_x3f_4719_; lean_object* v___y_4720_; lean_object* v___y_4721_; lean_object* v___y_4727_; lean_object* v___y_4728_; lean_object* v___x_4733_; lean_object* v_env_4734_; 
v_val_4717_ = lean_ctor_get(v_decl_3713_, 0);
v___x_4733_ = lean_st_ref_get(v_a_3716_);
v_env_4734_ = lean_ctor_get(v___x_4733_, 0);
lean_inc_ref(v_env_4734_);
lean_dec(v___x_4733_);
if (v_forceExpose_3714_ == 0)
{
goto v___jp_4735_;
}
else
{
if (v___x_4412_ == 0)
{
lean_dec_ref(v_env_4734_);
v_exportedInfo_x3f_4719_ = v___x_4602_;
v___y_4720_ = v_a_3715_;
v___y_4721_ = v_a_3716_;
goto v___jp_4718_;
}
else
{
goto v___jp_4735_;
}
}
v___jp_4718_:
{
lean_object* v_toConstantVal_4722_; lean_object* v_name_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v_toConstantVal_4722_ = lean_ctor_get(v_val_4717_, 0);
v_name_4723_ = lean_ctor_get(v_toConstantVal_4722_, 0);
lean_inc_ref(v_val_4717_);
v___x_4724_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4724_, 0, v_val_4717_);
v___x_4725_ = 1;
lean_inc(v_name_4723_);
v_fst_4635_ = v_name_4723_;
v_fst_4636_ = v___x_4724_;
v_snd_4637_ = v___x_4725_;
v_exportedInfo_x3f_4638_ = v_exportedInfo_x3f_4719_;
v___y_4639_ = v___y_4720_;
v___y_4640_ = v___y_4721_;
goto v___jp_4634_;
}
v___jp_4726_:
{
lean_object* v_toConstantVal_4729_; lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4732_; 
v_toConstantVal_4729_ = lean_ctor_get(v_val_4717_, 0);
lean_inc_ref(v_toConstantVal_4729_);
v___x_4730_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4730_, 0, v_toConstantVal_4729_);
lean_ctor_set_uint8(v___x_4730_, sizeof(void*)*1, v___x_4412_);
v___x_4731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4731_, 0, v___x_4730_);
v___x_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4732_, 0, v___x_4731_);
v_exportedInfo_x3f_4719_ = v___x_4732_;
v___y_4720_ = v___y_4727_;
v___y_4721_ = v___y_4728_;
goto v___jp_4718_;
}
v___jp_4735_:
{
lean_object* v___x_4736_; uint8_t v_isModule_4737_; 
v___x_4736_ = l_Lean_Environment_header(v_env_4734_);
lean_dec_ref(v_env_4734_);
v_isModule_4737_ = lean_ctor_get_uint8(v___x_4736_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4736_);
if (v_isModule_4737_ == 0)
{
v_exportedInfo_x3f_4719_ = v___x_4602_;
v___y_4720_ = v_a_3715_;
v___y_4721_ = v_a_3716_;
goto v___jp_4718_;
}
else
{
if (v___x_4111_ == 0)
{
v___y_4727_ = v_a_3715_;
v___y_4728_ = v_a_3716_;
goto v___jp_4726_;
}
else
{
lean_object* v_toConstantVal_4738_; lean_object* v_name_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; lean_object* v___x_4744_; lean_object* v___x_4745_; 
v_toConstantVal_4738_ = lean_ctor_get(v_val_4717_, 0);
v_name_4739_ = lean_ctor_get(v_toConstantVal_4738_, 0);
v___x_4740_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4739_);
v___x_4741_ = l_Lean_MessageData_ofName(v_name_4739_);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4740_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4744_, 0, v___x_4742_);
lean_ctor_set(v___x_4744_, 1, v___x_4743_);
v___x_4745_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4744_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_dec_ref_known(v___x_4745_, 1);
v___y_4727_ = v_a_3715_;
v___y_4728_ = v_a_3716_;
goto v___jp_4726_;
}
else
{
lean_dec_ref_known(v_decl_3713_, 1);
return v___x_4745_;
}
}
}
}
}
case 1:
{
lean_object* v_val_4746_; 
v_val_4746_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref(v_val_4746_);
v_defn_4708_ = v_val_4746_;
v___y_4709_ = v_a_3715_;
v___y_4710_ = v_a_3716_;
goto v___jp_4707_;
}
case 5:
{
lean_object* v_defns_4747_; 
v_defns_4747_ = lean_ctor_get(v_decl_3713_, 0);
if (lean_obj_tag(v_defns_4747_) == 1)
{
lean_object* v_tail_4748_; 
v_tail_4748_ = lean_ctor_get(v_defns_4747_, 1);
if (lean_obj_tag(v_tail_4748_) == 0)
{
lean_object* v_head_4749_; 
v_head_4749_ = lean_ctor_get(v_defns_4747_, 0);
lean_inc(v_head_4749_);
v_defn_4708_ = v_head_4749_;
v___y_4709_ = v_a_3715_;
v___y_4710_ = v_a_3716_;
goto v___jp_4707_;
}
else
{
v___y_4593_ = v_a_3715_;
v_options_4594_ = v_options_3770_;
v_inheritedTraceOptions_4595_ = v_inheritedTraceOptions_3771_;
v___y_4596_ = v_a_3716_;
goto v___jp_4592_;
}
}
else
{
v___y_4593_ = v_a_3715_;
v_options_4594_ = v_options_3770_;
v_inheritedTraceOptions_4595_ = v_inheritedTraceOptions_3771_;
v___y_4596_ = v_a_3716_;
goto v___jp_4592_;
}
}
case 3:
{
lean_object* v_val_4750_; lean_object* v_exportedInfo_x3f_4752_; lean_object* v___y_4753_; lean_object* v___y_4754_; lean_object* v___y_4760_; lean_object* v___y_4761_; lean_object* v___x_4767_; lean_object* v___x_4768_; lean_object* v_env_4778_; lean_object* v_env_4779_; 
v_val_4750_ = lean_ctor_get(v_decl_3713_, 0);
v___x_4767_ = lean_st_ref_get(v_a_3716_);
v___x_4768_ = lean_st_ref_get(v_a_3716_);
v_env_4778_ = lean_ctor_get(v___x_4767_, 0);
lean_inc_ref(v_env_4778_);
lean_dec(v___x_4767_);
v_env_4779_ = lean_ctor_get(v___x_4768_, 0);
lean_inc_ref(v_env_4779_);
lean_dec(v___x_4768_);
if (v_forceExpose_3714_ == 0)
{
goto v___jp_4780_;
}
else
{
if (v___x_4412_ == 0)
{
lean_dec_ref(v_env_4779_);
lean_dec_ref(v_env_4778_);
v_exportedInfo_x3f_4752_ = v___x_4602_;
v___y_4753_ = v_a_3715_;
v___y_4754_ = v_a_3716_;
goto v___jp_4751_;
}
else
{
goto v___jp_4780_;
}
}
v___jp_4751_:
{
lean_object* v_toConstantVal_4755_; lean_object* v_name_4756_; lean_object* v___x_4757_; uint8_t v___x_4758_; 
v_toConstantVal_4755_ = lean_ctor_get(v_val_4750_, 0);
v_name_4756_ = lean_ctor_get(v_toConstantVal_4755_, 0);
lean_inc_ref(v_val_4750_);
v___x_4757_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4757_, 0, v_val_4750_);
v___x_4758_ = 3;
lean_inc(v_name_4756_);
v_fst_4635_ = v_name_4756_;
v_fst_4636_ = v___x_4757_;
v_snd_4637_ = v___x_4758_;
v_exportedInfo_x3f_4638_ = v_exportedInfo_x3f_4752_;
v___y_4639_ = v___y_4753_;
v___y_4640_ = v___y_4754_;
goto v___jp_4634_;
}
v___jp_4759_:
{
lean_object* v_toConstantVal_4762_; uint8_t v_isUnsafe_4763_; lean_object* v___x_4764_; lean_object* v___x_4765_; lean_object* v___x_4766_; 
v_toConstantVal_4762_ = lean_ctor_get(v_val_4750_, 0);
v_isUnsafe_4763_ = lean_ctor_get_uint8(v_val_4750_, sizeof(void*)*3);
lean_inc_ref(v_toConstantVal_4762_);
v___x_4764_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4764_, 0, v_toConstantVal_4762_);
lean_ctor_set_uint8(v___x_4764_, sizeof(void*)*1, v_isUnsafe_4763_);
v___x_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4765_, 0, v___x_4764_);
v___x_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4766_, 0, v___x_4765_);
v_exportedInfo_x3f_4752_ = v___x_4766_;
v___y_4753_ = v___y_4760_;
v___y_4754_ = v___y_4761_;
goto v___jp_4751_;
}
v___jp_4769_:
{
if (v___x_4111_ == 0)
{
v___y_4760_ = v_a_3715_;
v___y_4761_ = v_a_3716_;
goto v___jp_4759_;
}
else
{
lean_object* v_toConstantVal_4770_; lean_object* v_name_4771_; lean_object* v___x_4772_; lean_object* v___x_4773_; lean_object* v___x_4774_; lean_object* v___x_4775_; lean_object* v___x_4776_; lean_object* v___x_4777_; 
v_toConstantVal_4770_ = lean_ctor_get(v_val_4750_, 0);
v_name_4771_ = lean_ctor_get(v_toConstantVal_4770_, 0);
v___x_4772_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4771_);
v___x_4773_ = l_Lean_MessageData_ofName(v_name_4771_);
v___x_4774_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4774_, 0, v___x_4772_);
lean_ctor_set(v___x_4774_, 1, v___x_4773_);
v___x_4775_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4776_, 0, v___x_4774_);
lean_ctor_set(v___x_4776_, 1, v___x_4775_);
v___x_4777_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4776_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4777_) == 0)
{
lean_dec_ref_known(v___x_4777_, 1);
v___y_4760_ = v_a_3715_;
v___y_4761_ = v_a_3716_;
goto v___jp_4759_;
}
else
{
lean_dec_ref_known(v_decl_3713_, 1);
return v___x_4777_;
}
}
}
v___jp_4780_:
{
lean_object* v___x_4781_; uint8_t v_isModule_4782_; 
v___x_4781_ = l_Lean_Environment_header(v_env_4778_);
lean_dec_ref(v_env_4778_);
v_isModule_4782_ = lean_ctor_get_uint8(v___x_4781_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4781_);
if (v_isModule_4782_ == 0)
{
lean_dec_ref(v_env_4779_);
v_exportedInfo_x3f_4752_ = v___x_4602_;
v___y_4753_ = v_a_3715_;
v___y_4754_ = v_a_3716_;
goto v___jp_4751_;
}
else
{
uint8_t v_isExporting_4783_; 
v_isExporting_4783_ = lean_ctor_get_uint8(v_env_4779_, sizeof(void*)*8);
lean_dec_ref(v_env_4779_);
if (v_isExporting_4783_ == 0)
{
goto v___jp_4769_;
}
else
{
if (v___x_4412_ == 0)
{
v_exportedInfo_x3f_4752_ = v___x_4602_;
v___y_4753_ = v_a_3715_;
v___y_4754_ = v_a_3716_;
goto v___jp_4751_;
}
else
{
goto v___jp_4769_;
}
}
}
}
}
case 0:
{
lean_object* v_val_4784_; lean_object* v_toConstantVal_4785_; lean_object* v_name_4786_; lean_object* v___x_4787_; uint8_t v___x_4788_; 
v_val_4784_ = lean_ctor_get(v_decl_3713_, 0);
v_toConstantVal_4785_ = lean_ctor_get(v_val_4784_, 0);
v_name_4786_ = lean_ctor_get(v_toConstantVal_4785_, 0);
lean_inc_ref(v_val_4784_);
v___x_4787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4787_, 0, v_val_4784_);
v___x_4788_ = 2;
lean_inc(v_name_4786_);
v_fst_4635_ = v_name_4786_;
v_fst_4636_ = v___x_4787_;
v_snd_4637_ = v___x_4788_;
v_exportedInfo_x3f_4638_ = v___x_4602_;
v___y_4639_ = v_a_3715_;
v___y_4640_ = v_a_3716_;
goto v___jp_4634_;
}
default: 
{
v___y_4593_ = v_a_3715_;
v_options_4594_ = v_options_3770_;
v_inheritedTraceOptions_4595_ = v_inheritedTraceOptions_3771_;
v___y_4596_ = v_a_3716_;
goto v___jp_4592_;
}
}
v___jp_4592_:
{
uint8_t v___x_4597_; 
v___x_4597_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4595_, v_options_4594_, v___x_4110_);
if (v___x_4597_ == 0)
{
lean_object* v___x_4598_; 
v___x_4598_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v___y_4593_, v___y_4596_);
return v___x_4598_;
}
else
{
lean_object* v___x_4599_; lean_object* v___x_4600_; 
v___x_4599_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3___closed__1);
v___x_4600_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4599_, v___y_4593_, v___y_4596_);
if (lean_obj_tag(v___x_4600_) == 0)
{
lean_object* v___x_4601_; 
lean_dec_ref_known(v___x_4600_, 1);
v___x_4601_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v___y_4593_, v___y_4596_);
return v___x_4601_;
}
else
{
lean_dec(v_decl_3713_);
return v___x_4600_;
}
}
}
v___jp_4603_:
{
lean_object* v___x_4610_; uint8_t v___x_4611_; 
lean_inc(v_decl_3713_);
v___x_4610_ = l_Lean_Declaration_getTopLevelNames(v_decl_3713_);
v___x_4611_ = l_List_all___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__2(v___x_4610_);
lean_dec(v___x_4610_);
if (v___x_4611_ == 0)
{
if (lean_obj_tag(v___y_4604_) == 0)
{
if (v___x_4412_ == 0)
{
lean_object* v_options_4612_; uint8_t v_hasTrace_4613_; 
v_options_4612_ = lean_ctor_get(v___y_4608_, 2);
v_hasTrace_4613_ = lean_ctor_get_uint8(v_options_4612_, sizeof(void*)*1);
if (v_hasTrace_4613_ == 0)
{
v___y_4533_ = v___y_4605_;
v___y_4534_ = v___y_4606_;
v___y_4535_ = v___y_4607_;
v___y_4536_ = v___y_4608_;
v___y_4537_ = v___y_4609_;
goto v___jp_4532_;
}
else
{
lean_object* v_inheritedTraceOptions_4614_; uint8_t v___x_4615_; 
v_inheritedTraceOptions_4614_ = lean_ctor_get(v___y_4608_, 13);
v___x_4615_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4614_, v_options_4612_, v___x_4110_);
if (v___x_4615_ == 0)
{
v___y_4533_ = v___y_4605_;
v___y_4534_ = v___y_4606_;
v___y_4535_ = v___y_4607_;
v___y_4536_ = v___y_4608_;
v___y_4537_ = v___y_4609_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4616_; lean_object* v___x_4617_; 
v___x_4616_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__3);
v___x_4617_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4616_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4617_) == 0)
{
lean_dec_ref_known(v___x_4617_, 1);
v___y_4533_ = v___y_4605_;
v___y_4534_ = v___y_4606_;
v___y_4535_ = v___y_4607_;
v___y_4536_ = v___y_4608_;
v___y_4537_ = v___y_4609_;
goto v___jp_4532_;
}
else
{
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v_decl_3713_);
return v___x_4617_;
}
}
}
}
else
{
v___y_4562_ = v___y_4609_;
v___y_4563_ = v___y_4608_;
v___y_4564_ = v___y_4604_;
v___y_4565_ = v___y_4606_;
v___y_4566_ = v___y_4605_;
v___y_4567_ = v___y_4607_;
goto v___jp_4561_;
}
}
else
{
v___y_4562_ = v___y_4609_;
v___y_4563_ = v___y_4608_;
v___y_4564_ = v___y_4604_;
v___y_4565_ = v___y_4606_;
v___y_4566_ = v___y_4605_;
v___y_4567_ = v___y_4607_;
goto v___jp_4561_;
}
}
else
{
lean_object* v___x_4618_; lean_object* v___x_4619_; lean_object* v_a_4620_; uint8_t v___x_4621_; 
lean_dec(v___y_4604_);
v___x_4618_ = l_Lean_ResolveName_backward_privateInPublic;
v___x_4619_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v___x_4618_, v___y_4608_);
v_a_4620_ = lean_ctor_get(v___x_4619_, 0);
lean_inc(v_a_4620_);
lean_dec_ref(v___x_4619_);
v___x_4621_ = lean_unbox(v_a_4620_);
lean_dec(v_a_4620_);
if (v___x_4621_ == 0)
{
lean_object* v_options_4622_; uint8_t v_hasTrace_4623_; 
v_options_4622_ = lean_ctor_get(v___y_4608_, 2);
v_hasTrace_4623_ = lean_ctor_get_uint8(v_options_4622_, sizeof(void*)*1);
if (v_hasTrace_4623_ == 0)
{
v___y_4518_ = v___y_4605_;
v___y_4519_ = v___y_4606_;
v___y_4520_ = v___y_4607_;
v_exportedInfo_x3f_4521_ = v___x_4602_;
v___y_4522_ = v___y_4608_;
v___y_4523_ = v___y_4609_;
goto v___jp_4517_;
}
else
{
lean_object* v_inheritedTraceOptions_4624_; uint8_t v___x_4625_; 
v_inheritedTraceOptions_4624_ = lean_ctor_get(v___y_4608_, 13);
v___x_4625_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4624_, v_options_4622_, v___x_4110_);
if (v___x_4625_ == 0)
{
v___y_4518_ = v___y_4605_;
v___y_4519_ = v___y_4606_;
v___y_4520_ = v___y_4607_;
v_exportedInfo_x3f_4521_ = v___x_4602_;
v___y_4522_ = v___y_4608_;
v___y_4523_ = v___y_4609_;
goto v___jp_4517_;
}
else
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__5);
v___x_4627_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4626_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4627_) == 0)
{
lean_dec_ref_known(v___x_4627_, 1);
v___y_4518_ = v___y_4605_;
v___y_4519_ = v___y_4606_;
v___y_4520_ = v___y_4607_;
v_exportedInfo_x3f_4521_ = v___x_4602_;
v___y_4522_ = v___y_4608_;
v___y_4523_ = v___y_4609_;
goto v___jp_4517_;
}
else
{
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v_decl_3713_);
return v___x_4627_;
}
}
}
}
else
{
lean_object* v_options_4628_; uint8_t v_hasTrace_4629_; 
v_options_4628_ = lean_ctor_get(v___y_4608_, 2);
v_hasTrace_4629_ = lean_ctor_get_uint8(v_options_4628_, sizeof(void*)*1);
if (v_hasTrace_4629_ == 0)
{
v___y_4540_ = v___y_4605_;
v___y_4541_ = v___y_4606_;
v___y_4542_ = v___y_4607_;
v___y_4543_ = v___y_4608_;
v___y_4544_ = v___y_4609_;
goto v___jp_4539_;
}
else
{
lean_object* v_inheritedTraceOptions_4630_; uint8_t v___x_4631_; 
v_inheritedTraceOptions_4630_ = lean_ctor_get(v___y_4608_, 13);
v___x_4631_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4630_, v_options_4628_, v___x_4110_);
if (v___x_4631_ == 0)
{
v___y_4540_ = v___y_4605_;
v___y_4541_ = v___y_4606_;
v___y_4542_ = v___y_4607_;
v___y_4543_ = v___y_4608_;
v___y_4544_ = v___y_4609_;
goto v___jp_4539_;
}
else
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__7);
v___x_4633_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4632_, v___y_4608_, v___y_4609_);
if (lean_obj_tag(v___x_4633_) == 0)
{
lean_dec_ref_known(v___x_4633_, 1);
v___y_4540_ = v___y_4605_;
v___y_4541_ = v___y_4606_;
v___y_4542_ = v___y_4607_;
v___y_4543_ = v___y_4608_;
v___y_4544_ = v___y_4609_;
goto v___jp_4539_;
}
else
{
lean_dec(v___y_4607_);
lean_dec_ref(v___y_4606_);
lean_dec(v_decl_3713_);
return v___x_4633_;
}
}
}
}
}
}
v___jp_4634_:
{
lean_object* v___x_4641_; lean_object* v_env_4642_; uint8_t v___x_4643_; 
v___x_4641_ = lean_st_ref_get(v___y_4640_);
v_env_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc_ref(v_env_4642_);
lean_dec(v___x_4641_);
v___x_4643_ = l_Lean_Environment_containsOnBranch(v_env_4642_, v_fst_4635_);
lean_dec_ref(v_env_4642_);
if (v___x_4643_ == 0)
{
v___y_4604_ = v_exportedInfo_x3f_4638_;
v___y_4605_ = v_snd_4637_;
v___y_4606_ = v_fst_4636_;
v___y_4607_ = v_fst_4635_;
v___y_4608_ = v___y_4639_;
v___y_4609_ = v___y_4640_;
goto v___jp_4603_;
}
else
{
lean_object* v___x_4644_; lean_object* v_env_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_dec(v_exportedInfo_x3f_4638_);
lean_dec_ref(v_fst_4636_);
lean_dec(v_decl_3713_);
v___x_4644_ = lean_st_ref_get(v___y_4640_);
v_env_4645_ = lean_ctor_get(v___x_4644_, 0);
lean_inc_ref(v_env_4645_);
lean_dec(v___x_4644_);
v___x_4646_ = lean_elab_environment_to_kernel_env(v_env_4645_);
v___x_4647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4647_, 0, v___x_4646_);
lean_ctor_set(v___x_4647_, 1, v_fst_4635_);
v___x_4648_ = l_Lean_throwKernelException___at___00Lean_ofExceptKernelException___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__0_spec__0___redArg(v___x_4647_, v___y_4639_, v___y_4640_);
return v___x_4648_;
}
}
v___jp_4649_:
{
lean_object* v_name_4655_; lean_object* v___x_4656_; uint8_t v___x_4657_; 
v_name_4655_ = lean_ctor_get(v_toConstantVal_4651_, 0);
lean_inc(v_name_4655_);
lean_dec_ref(v_toConstantVal_4651_);
v___x_4656_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4656_, 0, v___y_4650_);
v___x_4657_ = 0;
v_fst_4635_ = v_name_4655_;
v_fst_4636_ = v___x_4656_;
v_snd_4637_ = v___x_4657_;
v_exportedInfo_x3f_4638_ = v_exportedInfo_x3f_4652_;
v___y_4639_ = v___y_4653_;
v___y_4640_ = v___y_4654_;
goto v___jp_4634_;
}
v___jp_4658_:
{
uint8_t v___x_4664_; uint8_t v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4664_ = 0;
v___x_4665_ = l_Lean_instBEqDefinitionSafety_beq(v_safety_4661_, v___x_4664_);
lean_inc_ref(v_toConstantVal_4660_);
v___x_4666_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_4666_, 0, v_toConstantVal_4660_);
lean_ctor_set_uint8(v___x_4666_, sizeof(void*)*1, v___x_4665_);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
v___x_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
v___y_4650_ = v___y_4659_;
v_toConstantVal_4651_ = v_toConstantVal_4660_;
v_exportedInfo_x3f_4652_ = v___x_4668_;
v___y_4653_ = v___y_4662_;
v___y_4654_ = v___y_4663_;
goto v___jp_4649_;
}
v___jp_4669_:
{
lean_object* v_toConstantVal_4673_; uint8_t v_safety_4674_; 
v_toConstantVal_4673_ = lean_ctor_get(v___y_4670_, 0);
lean_inc_ref(v_toConstantVal_4673_);
v_safety_4674_ = lean_ctor_get_uint8(v___y_4670_, sizeof(void*)*4);
v___y_4659_ = v___y_4670_;
v_toConstantVal_4660_ = v_toConstantVal_4673_;
v_safety_4661_ = v_safety_4674_;
v___y_4662_ = v___y_4671_;
v___y_4663_ = v___y_4672_;
goto v___jp_4658_;
}
v___jp_4675_:
{
lean_object* v_options_4679_; uint8_t v_hasTrace_4680_; 
v_options_4679_ = lean_ctor_get(v___y_4677_, 2);
v_hasTrace_4680_ = lean_ctor_get_uint8(v_options_4679_, sizeof(void*)*1);
if (v_hasTrace_4680_ == 0)
{
v___y_4670_ = v___y_4676_;
v___y_4671_ = v___y_4677_;
v___y_4672_ = v___y_4678_;
goto v___jp_4669_;
}
else
{
lean_object* v_inheritedTraceOptions_4681_; uint8_t v___x_4682_; 
v_inheritedTraceOptions_4681_ = lean_ctor_get(v___y_4677_, 13);
v___x_4682_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4681_, v_options_4679_, v___x_4110_);
if (v___x_4682_ == 0)
{
v___y_4670_ = v___y_4676_;
v___y_4671_ = v___y_4677_;
v___y_4672_ = v___y_4678_;
goto v___jp_4669_;
}
else
{
lean_object* v_toConstantVal_4683_; uint8_t v_safety_4684_; lean_object* v_name_4685_; lean_object* v___x_4686_; lean_object* v___x_4687_; lean_object* v___x_4688_; lean_object* v___x_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; 
v_toConstantVal_4683_ = lean_ctor_get(v___y_4676_, 0);
lean_inc_ref(v_toConstantVal_4683_);
v_safety_4684_ = lean_ctor_get_uint8(v___y_4676_, sizeof(void*)*4);
v_name_4685_ = lean_ctor_get(v_toConstantVal_4683_, 0);
v___x_4686_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__1);
lean_inc(v_name_4685_);
v___x_4687_ = l_Lean_MessageData_ofName(v_name_4685_);
v___x_4688_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4688_, 0, v___x_4686_);
lean_ctor_set(v___x_4688_, 1, v___x_4687_);
v___x_4689_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4690_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4690_, 0, v___x_4688_);
lean_ctor_set(v___x_4690_, 1, v___x_4689_);
v___x_4691_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4690_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4691_) == 0)
{
lean_dec_ref_known(v___x_4691_, 1);
v___y_4659_ = v___y_4676_;
v_toConstantVal_4660_ = v_toConstantVal_4683_;
v_safety_4661_ = v_safety_4684_;
v___y_4662_ = v___y_4677_;
v___y_4663_ = v___y_4678_;
goto v___jp_4658_;
}
else
{
lean_dec_ref(v_toConstantVal_4683_);
lean_dec_ref(v___y_4676_);
lean_dec(v_decl_3713_);
return v___x_4691_;
}
}
}
}
v___jp_4692_:
{
lean_object* v_toConstantVal_4697_; 
v_toConstantVal_4697_ = lean_ctor_get(v___y_4693_, 0);
lean_inc_ref(v_toConstantVal_4697_);
v___y_4650_ = v___y_4693_;
v_toConstantVal_4651_ = v_toConstantVal_4697_;
v_exportedInfo_x3f_4652_ = v_exportedInfo_x3f_4694_;
v___y_4653_ = v___y_4695_;
v___y_4654_ = v___y_4696_;
goto v___jp_4649_;
}
v___jp_4698_:
{
lean_object* v___x_4704_; uint8_t v_isModule_4705_; 
v___x_4704_ = l_Lean_Environment_header(v___y_4701_);
lean_dec_ref(v___y_4701_);
v_isModule_4705_ = lean_ctor_get_uint8(v___x_4704_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4704_);
if (v_isModule_4705_ == 0)
{
lean_dec_ref(v___y_4702_);
v___y_4693_ = v___y_4699_;
v_exportedInfo_x3f_4694_ = v___x_4602_;
v___y_4695_ = v___y_4700_;
v___y_4696_ = v___y_4703_;
goto v___jp_4692_;
}
else
{
uint8_t v_isExporting_4706_; 
v_isExporting_4706_ = lean_ctor_get_uint8(v___y_4702_, sizeof(void*)*8);
lean_dec_ref(v___y_4702_);
if (v_isExporting_4706_ == 0)
{
v___y_4676_ = v___y_4699_;
v___y_4677_ = v___y_4700_;
v___y_4678_ = v___y_4703_;
goto v___jp_4675_;
}
else
{
if (v___x_4412_ == 0)
{
v___y_4693_ = v___y_4699_;
v_exportedInfo_x3f_4694_ = v___x_4602_;
v___y_4695_ = v___y_4700_;
v___y_4696_ = v___y_4703_;
goto v___jp_4692_;
}
else
{
v___y_4676_ = v___y_4699_;
v___y_4677_ = v___y_4700_;
v___y_4678_ = v___y_4703_;
goto v___jp_4675_;
}
}
}
}
v___jp_4707_:
{
lean_object* v___x_4711_; lean_object* v___x_4712_; 
v___x_4711_ = lean_st_ref_get(v___y_4710_);
v___x_4712_ = lean_st_ref_get(v___y_4710_);
if (v_forceExpose_3714_ == 0)
{
lean_object* v_env_4713_; lean_object* v_env_4714_; 
v_env_4713_ = lean_ctor_get(v___x_4711_, 0);
lean_inc_ref(v_env_4713_);
lean_dec(v___x_4711_);
v_env_4714_ = lean_ctor_get(v___x_4712_, 0);
lean_inc_ref(v_env_4714_);
lean_dec(v___x_4712_);
v___y_4699_ = v_defn_4708_;
v___y_4700_ = v___y_4709_;
v___y_4701_ = v_env_4713_;
v___y_4702_ = v_env_4714_;
v___y_4703_ = v___y_4710_;
goto v___jp_4698_;
}
else
{
if (v___x_4412_ == 0)
{
lean_dec(v___x_4712_);
lean_dec(v___x_4711_);
v___y_4693_ = v_defn_4708_;
v_exportedInfo_x3f_4694_ = v___x_4602_;
v___y_4695_ = v___y_4709_;
v___y_4696_ = v___y_4710_;
goto v___jp_4692_;
}
else
{
lean_object* v_env_4715_; lean_object* v_env_4716_; 
v_env_4715_ = lean_ctor_get(v___x_4711_, 0);
lean_inc_ref(v_env_4715_);
lean_dec(v___x_4711_);
v_env_4716_ = lean_ctor_get(v___x_4712_, 0);
lean_inc_ref(v_env_4716_);
lean_dec(v___x_4712_);
v___y_4699_ = v_defn_4708_;
v___y_4700_ = v___y_4709_;
v___y_4701_ = v_env_4715_;
v___y_4702_ = v_env_4716_;
v___y_4703_ = v___y_4710_;
goto v___jp_4698_;
}
}
}
}
}
}
else
{
goto v___jp_4259_;
}
v___jp_4413_:
{
lean_object* v___x_4424_; 
lean_inc_ref(v___y_4418_);
v___x_4424_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_4415_, v___y_4418_, v___y_4417_, v___y_4423_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v___x_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4471_; 
lean_dec_ref_known(v___x_4424_, 1);
lean_inc_ref(v___y_4414_);
v___x_4425_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4414_, v___y_4419_);
v_isSharedCheck_4471_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4471_ == 0)
{
lean_object* v_unused_4472_; 
v_unused_4472_ = lean_ctor_get(v___x_4425_, 0);
lean_dec(v_unused_4472_);
v___x_4427_ = v___x_4425_;
v_isShared_4428_ = v_isSharedCheck_4471_;
goto v_resetjp_4426_;
}
else
{
lean_dec(v___x_4425_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4471_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v_options_4429_; lean_object* v___x_4430_; uint8_t v___x_4431_; 
v_options_4429_ = lean_ctor_get(v___y_4421_, 2);
v___x_4430_ = l_Lean_Elab_async;
v___x_4431_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_4429_, v___x_4430_);
if (v___x_4431_ == 0)
{
lean_object* v___x_4432_; lean_object* v_r_4433_; 
lean_del_object(v___x_4427_);
lean_dec_ref(v___y_4422_);
lean_dec_ref(v___y_4420_);
v___x_4432_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_4418_, v___y_4419_);
lean_dec_ref(v___x_4432_);
v_r_4433_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v___y_4421_, v___y_4419_);
if (lean_obj_tag(v_r_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4443_; 
v_a_4434_ = lean_ctor_get(v_r_4433_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v_r_4433_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4436_ = v_r_4433_;
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v_r_4433_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4443_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
lean_inc(v_a_4434_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set_tag(v___x_4436_, 1);
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
lean_object* v___x_4440_; 
v___x_4440_ = lean_apply_2(v___y_4416_, v___x_4439_, lean_box(0));
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_dec_ref_known(v___x_4440_, 1);
v___y_3745_ = v___y_4414_;
v___y_3746_ = v___y_4419_;
v_a_3747_ = v_a_4434_;
goto v___jp_3744_;
}
else
{
lean_object* v_a_4441_; 
lean_dec(v_a_4434_);
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___y_3758_ = v___y_4414_;
v___y_3759_ = v___y_4419_;
v_a_3760_ = v_a_4441_;
goto v___jp_3757_;
}
}
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v_a_4444_ = lean_ctor_get(v_r_4433_, 0);
lean_inc(v_a_4444_);
lean_dec_ref_known(v_r_4433_, 1);
v___x_4445_ = lean_box(0);
v___x_4446_ = lean_apply_2(v___y_4416_, v___x_4445_, lean_box(0));
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_dec_ref_known(v___x_4446_, 1);
v___y_3758_ = v___y_4414_;
v___y_3759_ = v___y_4419_;
v_a_3760_ = v_a_4444_;
goto v___jp_3757_;
}
else
{
lean_object* v_a_4447_; 
lean_dec(v_a_4444_);
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref_known(v___x_4446_, 1);
v___y_3758_ = v___y_4414_;
v___y_3759_ = v___y_4419_;
v_a_3760_ = v_a_4447_;
goto v___jp_3757_;
}
}
}
else
{
lean_object* v___x_4448_; lean_object* v___x_4450_; 
lean_dec_ref(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4414_);
lean_dec(v_decl_3713_);
v___x_4448_ = l_IO_CancelToken_new();
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 1);
lean_ctor_set(v___x_4427_, 0, v___x_4448_);
v___x_4450_ = v___x_4427_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4470_; 
v_reuseFailAlloc_4470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4470_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4470_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
lean_object* v___x_4451_; lean_object* v___x_4452_; lean_object* v___x_4453_; lean_object* v___x_4454_; 
v___x_4451_ = lean_unsigned_to_nat(0u);
v___x_4452_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_4453_ = l_Lean_Name_toString(v___x_4452_, v_hasTrace_3772_);
lean_inc_ref(v___x_4450_);
v___x_4454_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_4422_, v___x_4450_, v___x_4453_, v___y_4421_, v___y_4419_);
if (lean_obj_tag(v___x_4454_) == 0)
{
lean_object* v_a_4455_; lean_object* v_checked_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; 
v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
lean_inc(v_a_4455_);
lean_dec_ref_known(v___x_4454_, 1);
v_checked_4456_ = lean_ctor_get(v___y_4420_, 2);
lean_inc_ref(v_checked_4456_);
lean_dec_ref(v___y_4420_);
v___x_4457_ = lean_io_map_task(v_a_4455_, v_checked_4456_, v___x_4451_, v___x_4412_);
v___x_4458_ = lean_box(0);
v___x_4459_ = lean_box(2);
v___x_4460_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
lean_ctor_set(v___x_4460_, 2, v___x_4450_);
lean_ctor_set(v___x_4460_, 3, v___x_4457_);
v___x_4461_ = l_Lean_Core_logSnapshotTask___redArg(v___x_4460_, v___y_4419_);
return v___x_4461_;
}
else
{
lean_object* v_a_4462_; lean_object* v___x_4464_; uint8_t v_isShared_4465_; uint8_t v_isSharedCheck_4469_; 
lean_dec_ref(v___x_4450_);
lean_dec_ref(v___y_4420_);
v_a_4462_ = lean_ctor_get(v___x_4454_, 0);
v_isSharedCheck_4469_ = !lean_is_exclusive(v___x_4454_);
if (v_isSharedCheck_4469_ == 0)
{
v___x_4464_ = v___x_4454_;
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
else
{
lean_inc(v_a_4462_);
lean_dec(v___x_4454_);
v___x_4464_ = lean_box(0);
v_isShared_4465_ = v_isSharedCheck_4469_;
goto v_resetjp_4463_;
}
v_resetjp_4463_:
{
lean_object* v___x_4467_; 
if (v_isShared_4465_ == 0)
{
v___x_4467_ = v___x_4464_;
goto v_reusejp_4466_;
}
else
{
lean_object* v_reuseFailAlloc_4468_; 
v_reuseFailAlloc_4468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_a_4462_);
v___x_4467_ = v_reuseFailAlloc_4468_;
goto v_reusejp_4466_;
}
v_reusejp_4466_:
{
return v___x_4467_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4473_; lean_object* v___x_4475_; uint8_t v_isShared_4476_; uint8_t v_isSharedCheck_4485_; 
lean_dec_ref(v___y_4422_);
lean_dec_ref(v___y_4420_);
lean_dec_ref(v___y_4418_);
lean_dec_ref(v___y_4416_);
lean_dec_ref(v___y_4414_);
lean_dec(v_decl_3713_);
v_a_4473_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4475_ = v___x_4424_;
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
else
{
lean_inc(v_a_4473_);
lean_dec(v___x_4424_);
v___x_4475_ = lean_box(0);
v_isShared_4476_ = v_isSharedCheck_4485_;
goto v_resetjp_4474_;
}
v_resetjp_4474_:
{
lean_object* v_ref_4477_; lean_object* v___x_4478_; lean_object* v___x_4479_; lean_object* v___x_4480_; lean_object* v___x_4481_; lean_object* v___x_4483_; 
v_ref_4477_ = lean_ctor_get(v___y_4421_, 5);
v___x_4478_ = lean_io_error_to_string(v_a_4473_);
v___x_4479_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4479_, 0, v___x_4478_);
v___x_4480_ = l_Lean_MessageData_ofFormat(v___x_4479_);
lean_inc(v_ref_4477_);
v___x_4481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4481_, 0, v_ref_4477_);
lean_ctor_set(v___x_4481_, 1, v___x_4480_);
if (v_isShared_4476_ == 0)
{
lean_ctor_set(v___x_4475_, 0, v___x_4481_);
v___x_4483_ = v___x_4475_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v___x_4481_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
v___jp_4486_:
{
lean_object* v___x_4497_; 
lean_inc_ref(v___y_4488_);
v___x_4497_ = l_Lean_Environment_addConstAsync(v___y_4488_, v___y_4494_, v___y_4493_, v___y_4496_, v___x_4412_, v_hasTrace_3772_);
if (lean_obj_tag(v___x_4497_) == 0)
{
lean_object* v_a_4498_; lean_object* v_mainEnv_4499_; lean_object* v_asyncEnv_4500_; lean_object* v___f_4501_; lean_object* v___f_4502_; lean_object* v___x_4503_; 
v_a_4498_ = lean_ctor_get(v___x_4497_, 0);
lean_inc_n(v_a_4498_, 3);
lean_dec_ref_known(v___x_4497_, 1);
v_mainEnv_4499_ = lean_ctor_get(v_a_4498_, 0);
lean_inc_ref(v_mainEnv_4499_);
v_asyncEnv_4500_ = lean_ctor_get(v_a_4498_, 1);
lean_inc_ref_n(v_asyncEnv_4500_, 2);
lean_inc_ref(v___y_4489_);
lean_inc(v___y_4487_);
v___f_4501_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_4501_, 0, v___y_4487_);
lean_closure_set(v___f_4501_, 1, v_a_4498_);
lean_closure_set(v___f_4501_, 2, v___y_4489_);
lean_inc(v_decl_3713_);
v___f_4502_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_4502_, 0, v_asyncEnv_4500_);
lean_closure_set(v___f_4502_, 1, v_a_4498_);
lean_closure_set(v___f_4502_, 2, v_decl_3713_);
v___x_4503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4503_, 0, v___y_4492_);
if (lean_obj_tag(v___y_4490_) == 0)
{
lean_inc_ref(v___x_4503_);
v___y_4414_ = v_mainEnv_4499_;
v___y_4415_ = v_a_4498_;
v___y_4416_ = v___f_4501_;
v___y_4417_ = v___x_4503_;
v___y_4418_ = v_asyncEnv_4500_;
v___y_4419_ = v___y_4491_;
v___y_4420_ = v___y_4488_;
v___y_4421_ = v___y_4495_;
v___y_4422_ = v___f_4502_;
v___y_4423_ = v___x_4503_;
goto v___jp_4413_;
}
else
{
v___y_4414_ = v_mainEnv_4499_;
v___y_4415_ = v_a_4498_;
v___y_4416_ = v___f_4501_;
v___y_4417_ = v___x_4503_;
v___y_4418_ = v_asyncEnv_4500_;
v___y_4419_ = v___y_4491_;
v___y_4420_ = v___y_4488_;
v___y_4421_ = v___y_4495_;
v___y_4422_ = v___f_4502_;
v___y_4423_ = v___y_4490_;
goto v___jp_4413_;
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4516_; 
lean_dec_ref(v___y_4492_);
lean_dec(v___y_4490_);
lean_dec_ref(v___y_4488_);
lean_dec(v_decl_3713_);
v_a_4504_ = lean_ctor_get(v___x_4497_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4497_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4506_ = v___x_4497_;
v_isShared_4507_ = v_isSharedCheck_4516_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4497_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4516_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v_ref_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; lean_object* v___x_4512_; lean_object* v___x_4514_; 
v_ref_4508_ = lean_ctor_get(v___y_4495_, 5);
v___x_4509_ = lean_io_error_to_string(v_a_4504_);
v___x_4510_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4509_);
v___x_4511_ = l_Lean_MessageData_ofFormat(v___x_4510_);
lean_inc(v_ref_4508_);
v___x_4512_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4512_, 0, v_ref_4508_);
lean_ctor_set(v___x_4512_, 1, v___x_4511_);
if (v_isShared_4507_ == 0)
{
lean_ctor_set(v___x_4506_, 0, v___x_4512_);
v___x_4514_ = v___x_4506_;
goto v_reusejp_4513_;
}
else
{
lean_object* v_reuseFailAlloc_4515_; 
v_reuseFailAlloc_4515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4515_, 0, v___x_4512_);
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
v___jp_4517_:
{
lean_object* v___x_4524_; 
v___x_4524_ = lean_st_ref_get(v___y_4523_);
if (lean_obj_tag(v_exportedInfo_x3f_4521_) == 0)
{
lean_object* v_env_4525_; lean_object* v___x_4526_; 
v_env_4525_ = lean_ctor_get(v___x_4524_, 0);
lean_inc_ref(v_env_4525_);
lean_dec(v___x_4524_);
v___x_4526_ = lean_box(0);
v___y_4487_ = v___y_4523_;
v___y_4488_ = v_env_4525_;
v___y_4489_ = v___y_4522_;
v___y_4490_ = v_exportedInfo_x3f_4521_;
v___y_4491_ = v___y_4523_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4518_;
v___y_4494_ = v___y_4520_;
v___y_4495_ = v___y_4522_;
v___y_4496_ = v___x_4526_;
goto v___jp_4486_;
}
else
{
lean_object* v_env_4527_; lean_object* v_val_4528_; uint8_t v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; 
v_env_4527_ = lean_ctor_get(v___x_4524_, 0);
lean_inc_ref(v_env_4527_);
lean_dec(v___x_4524_);
v_val_4528_ = lean_ctor_get(v_exportedInfo_x3f_4521_, 0);
v___x_4529_ = l_Lean_ConstantKind_ofConstantInfo(v_val_4528_);
v___x_4530_ = lean_box(v___x_4529_);
v___x_4531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4530_);
v___y_4487_ = v___y_4523_;
v___y_4488_ = v_env_4527_;
v___y_4489_ = v___y_4522_;
v___y_4490_ = v_exportedInfo_x3f_4521_;
v___y_4491_ = v___y_4523_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4518_;
v___y_4494_ = v___y_4520_;
v___y_4495_ = v___y_4522_;
v___y_4496_ = v___x_4531_;
goto v___jp_4486_;
}
}
v___jp_4532_:
{
lean_object* v___x_4538_; 
lean_inc_ref(v___y_4534_);
v___x_4538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4538_, 0, v___y_4534_);
v___y_4518_ = v___y_4533_;
v___y_4519_ = v___y_4534_;
v___y_4520_ = v___y_4535_;
v_exportedInfo_x3f_4521_ = v___x_4538_;
v___y_4522_ = v___y_4536_;
v___y_4523_ = v___y_4537_;
goto v___jp_4517_;
}
v___jp_4539_:
{
lean_object* v___x_4545_; 
lean_inc_ref(v___y_4541_);
v___x_4545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4545_, 0, v___y_4541_);
v___y_4518_ = v___y_4540_;
v___y_4519_ = v___y_4541_;
v___y_4520_ = v___y_4542_;
v_exportedInfo_x3f_4521_ = v___x_4545_;
v___y_4522_ = v___y_4543_;
v___y_4523_ = v___y_4544_;
goto v___jp_4517_;
}
}
else
{
goto v___jp_4259_;
}
v___jp_4112_:
{
lean_object* v___x_4116_; double v___x_4117_; double v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; 
v___x_4116_ = lean_io_get_num_heartbeats();
v___x_4117_ = lean_float_of_nat(v___y_4114_);
v___x_4118_ = lean_float_of_nat(v___x_4116_);
v___x_4119_ = lean_box_float(v___x_4117_);
v___x_4120_ = lean_box_float(v___x_4118_);
v___x_4121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4119_);
lean_ctor_set(v___x_4121_, 1, v___x_4120_);
v___x_4122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4122_, 0, v_a_4115_);
lean_ctor_set(v___x_4122_, 1, v___x_4121_);
v___x_4123_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3908_, v_hasTrace_3772_, v___x_4109_, v_options_3770_, v___x_4111_, v___y_4113_, v___f_4108_, v___x_4122_, v_a_3715_, v_a_3716_);
return v___x_4123_;
}
v___jp_4124_:
{
if (lean_obj_tag(v___y_4127_) == 0)
{
lean_object* v_a_4128_; lean_object* v___x_4130_; uint8_t v_isShared_4131_; uint8_t v_isSharedCheck_4135_; 
v_a_4128_ = lean_ctor_get(v___y_4127_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v___y_4127_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4130_ = v___y_4127_;
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
else
{
lean_inc(v_a_4128_);
lean_dec(v___y_4127_);
v___x_4130_ = lean_box(0);
v_isShared_4131_ = v_isSharedCheck_4135_;
goto v_resetjp_4129_;
}
v_resetjp_4129_:
{
lean_object* v___x_4133_; 
if (v_isShared_4131_ == 0)
{
lean_ctor_set_tag(v___x_4130_, 1);
v___x_4133_ = v___x_4130_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v_a_4128_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
v___y_4113_ = v___y_4126_;
v___y_4114_ = v___y_4125_;
v_a_4115_ = v___x_4133_;
goto v___jp_4112_;
}
}
}
else
{
lean_object* v_a_4136_; lean_object* v___x_4138_; uint8_t v_isShared_4139_; uint8_t v_isSharedCheck_4143_; 
v_a_4136_ = lean_ctor_get(v___y_4127_, 0);
v_isSharedCheck_4143_ = !lean_is_exclusive(v___y_4127_);
if (v_isSharedCheck_4143_ == 0)
{
v___x_4138_ = v___y_4127_;
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
else
{
lean_inc(v_a_4136_);
lean_dec(v___y_4127_);
v___x_4138_ = lean_box(0);
v_isShared_4139_ = v_isSharedCheck_4143_;
goto v_resetjp_4137_;
}
v_resetjp_4137_:
{
lean_object* v___x_4141_; 
if (v_isShared_4139_ == 0)
{
lean_ctor_set_tag(v___x_4138_, 0);
v___x_4141_ = v___x_4138_;
goto v_reusejp_4140_;
}
else
{
lean_object* v_reuseFailAlloc_4142_; 
v_reuseFailAlloc_4142_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4142_, 0, v_a_4136_);
v___x_4141_ = v_reuseFailAlloc_4142_;
goto v_reusejp_4140_;
}
v_reusejp_4140_:
{
v___y_4113_ = v___y_4126_;
v___y_4114_ = v___y_4125_;
v_a_4115_ = v___x_4141_;
goto v___jp_4112_;
}
}
}
}
v___jp_4144_:
{
lean_object* v___x_4149_; lean_object* v___x_4150_; 
v___x_4149_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4150_ = lean_apply_5(v___y_4146_, v___x_4149_, v___y_4145_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4125_ = v___y_4148_;
v___y_4126_ = v___y_4147_;
v___y_4127_ = v___x_4150_;
goto v___jp_4124_;
}
v___jp_4151_:
{
lean_object* v___x_4156_; lean_object* v___x_4157_; 
v___x_4156_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4157_ = lean_apply_5(v___y_4152_, v___x_4156_, v___y_4153_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4125_ = v___y_4155_;
v___y_4126_ = v___y_4154_;
v___y_4127_ = v___x_4157_;
goto v___jp_4124_;
}
v___jp_4158_:
{
lean_object* v___x_4162_; double v___x_4163_; double v___x_4164_; double v___x_4165_; double v___x_4166_; double v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4162_ = lean_io_mono_nanos_now();
v___x_4163_ = lean_float_of_nat(v___y_4159_);
v___x_4164_ = lean_float_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1, &l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd___lam__1___closed__1);
v___x_4165_ = lean_float_div(v___x_4163_, v___x_4164_);
v___x_4166_ = lean_float_of_nat(v___x_4162_);
v___x_4167_ = lean_float_div(v___x_4166_, v___x_4164_);
v___x_4168_ = lean_box_float(v___x_4165_);
v___x_4169_ = lean_box_float(v___x_4167_);
v___x_4170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4168_);
lean_ctor_set(v___x_4170_, 1, v___x_4169_);
v___x_4171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4171_, 0, v_a_4161_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__2(v_cls_3908_, v_hasTrace_3772_, v___x_4109_, v_options_3770_, v___x_4111_, v___y_4160_, v___f_4108_, v___x_4171_, v_a_3715_, v_a_3716_);
return v___x_4172_;
}
v___jp_4173_:
{
if (lean_obj_tag(v___y_4176_) == 0)
{
lean_object* v_a_4177_; lean_object* v___x_4179_; uint8_t v_isShared_4180_; uint8_t v_isSharedCheck_4184_; 
v_a_4177_ = lean_ctor_get(v___y_4176_, 0);
v_isSharedCheck_4184_ = !lean_is_exclusive(v___y_4176_);
if (v_isSharedCheck_4184_ == 0)
{
v___x_4179_ = v___y_4176_;
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
else
{
lean_inc(v_a_4177_);
lean_dec(v___y_4176_);
v___x_4179_ = lean_box(0);
v_isShared_4180_ = v_isSharedCheck_4184_;
goto v_resetjp_4178_;
}
v_resetjp_4178_:
{
lean_object* v___x_4182_; 
if (v_isShared_4180_ == 0)
{
lean_ctor_set_tag(v___x_4179_, 1);
v___x_4182_ = v___x_4179_;
goto v_reusejp_4181_;
}
else
{
lean_object* v_reuseFailAlloc_4183_; 
v_reuseFailAlloc_4183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4183_, 0, v_a_4177_);
v___x_4182_ = v_reuseFailAlloc_4183_;
goto v_reusejp_4181_;
}
v_reusejp_4181_:
{
v___y_4159_ = v___y_4174_;
v___y_4160_ = v___y_4175_;
v_a_4161_ = v___x_4182_;
goto v___jp_4158_;
}
}
}
else
{
lean_object* v_a_4185_; lean_object* v___x_4187_; uint8_t v_isShared_4188_; uint8_t v_isSharedCheck_4192_; 
v_a_4185_ = lean_ctor_get(v___y_4176_, 0);
v_isSharedCheck_4192_ = !lean_is_exclusive(v___y_4176_);
if (v_isSharedCheck_4192_ == 0)
{
v___x_4187_ = v___y_4176_;
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
else
{
lean_inc(v_a_4185_);
lean_dec(v___y_4176_);
v___x_4187_ = lean_box(0);
v_isShared_4188_ = v_isSharedCheck_4192_;
goto v_resetjp_4186_;
}
v_resetjp_4186_:
{
lean_object* v___x_4190_; 
if (v_isShared_4188_ == 0)
{
lean_ctor_set_tag(v___x_4187_, 0);
v___x_4190_ = v___x_4187_;
goto v_reusejp_4189_;
}
else
{
lean_object* v_reuseFailAlloc_4191_; 
v_reuseFailAlloc_4191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4191_, 0, v_a_4185_);
v___x_4190_ = v_reuseFailAlloc_4191_;
goto v_reusejp_4189_;
}
v_reusejp_4189_:
{
v___y_4159_ = v___y_4174_;
v___y_4160_ = v___y_4175_;
v_a_4161_ = v___x_4190_;
goto v___jp_4158_;
}
}
}
}
v___jp_4193_:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4199_ = lean_apply_5(v___y_4195_, v___x_4198_, v___y_4196_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4194_;
v___y_4175_ = v___y_4197_;
v___y_4176_ = v___x_4199_;
goto v___jp_4173_;
}
v___jp_4200_:
{
if (v___x_4111_ == 0)
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
lean_dec_ref(v___y_4203_);
v___x_4205_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4206_ = lean_apply_4(v___y_4201_, v___x_4205_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4202_;
v___y_4175_ = v___y_4204_;
v___y_4176_ = v___x_4206_;
goto v___jp_4173_;
}
else
{
lean_object* v_toConstantVal_4207_; lean_object* v_name_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; 
v_toConstantVal_4207_ = lean_ctor_get(v___y_4203_, 0);
lean_inc_ref(v_toConstantVal_4207_);
lean_dec_ref(v___y_4203_);
v_name_4208_ = lean_ctor_get(v_toConstantVal_4207_, 0);
lean_inc(v_name_4208_);
lean_dec_ref(v_toConstantVal_4207_);
v___x_4209_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
v___x_4210_ = l_Lean_MessageData_ofName(v_name_4208_);
v___x_4211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4211_, 0, v___x_4209_);
lean_ctor_set(v___x_4211_, 1, v___x_4210_);
v___x_4212_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4211_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4213_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4216_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
lean_inc(v_a_4215_);
lean_dec_ref_known(v___x_4214_, 1);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4216_ = lean_apply_4(v___y_4201_, v_a_4215_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4202_;
v___y_4175_ = v___y_4204_;
v___y_4176_ = v___x_4216_;
goto v___jp_4173_;
}
else
{
lean_dec_ref(v___y_4201_);
v___y_4174_ = v___y_4202_;
v___y_4175_ = v___y_4204_;
v___y_4176_ = v___x_4214_;
goto v___jp_4173_;
}
}
}
v___jp_4217_:
{
lean_object* v___x_4227_; uint8_t v_isModule_4228_; 
v___x_4227_ = l_Lean_Environment_header(v___y_4226_);
lean_dec_ref(v___y_4226_);
v_isModule_4228_ = lean_ctor_get_uint8(v___x_4227_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4227_);
if (v_isModule_4228_ == 0)
{
lean_dec_ref(v___y_4222_);
lean_dec_ref(v___y_4220_);
lean_dec_ref(v___y_4218_);
v___y_4194_ = v___y_4219_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
goto v___jp_4193_;
}
else
{
uint8_t v_isExporting_4229_; 
v_isExporting_4229_ = lean_ctor_get_uint8(v___y_4222_, sizeof(void*)*8);
lean_dec_ref(v___y_4222_);
if (v_isExporting_4229_ == 0)
{
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4221_);
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4225_;
goto v___jp_4200_;
}
else
{
if (v___y_4224_ == 0)
{
lean_dec_ref(v___y_4220_);
lean_dec_ref(v___y_4218_);
v___y_4194_ = v___y_4219_;
v___y_4195_ = v___y_4221_;
v___y_4196_ = v___y_4223_;
v___y_4197_ = v___y_4225_;
goto v___jp_4193_;
}
else
{
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4221_);
v___y_4201_ = v___y_4218_;
v___y_4202_ = v___y_4219_;
v___y_4203_ = v___y_4220_;
v___y_4204_ = v___y_4225_;
goto v___jp_4200_;
}
}
}
}
v___jp_4230_:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4235_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4236_ = lean_apply_5(v___y_4232_, v___x_4235_, v___y_4233_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4231_;
v___y_4175_ = v___y_4234_;
v___y_4176_ = v___x_4236_;
goto v___jp_4173_;
}
v___jp_4237_:
{
lean_object* v___x_4245_; uint8_t v_isModule_4246_; 
v___x_4245_ = l_Lean_Environment_header(v___y_4243_);
lean_dec_ref(v___y_4243_);
v_isModule_4246_ = lean_ctor_get_uint8(v___x_4245_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4245_);
if (v_isModule_4246_ == 0)
{
lean_dec_ref(v___y_4241_);
lean_dec_ref(v___y_4240_);
v___y_4231_ = v___y_4238_;
v___y_4232_ = v___y_4239_;
v___y_4233_ = v___y_4242_;
v___y_4234_ = v___y_4244_;
goto v___jp_4230_;
}
else
{
lean_dec(v___y_4242_);
lean_dec_ref(v___y_4239_);
if (v___x_4111_ == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; 
lean_dec_ref(v___y_4240_);
v___x_4247_ = lean_box(0);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4248_ = lean_apply_4(v___y_4241_, v___x_4247_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4238_;
v___y_4175_ = v___y_4244_;
v___y_4176_ = v___x_4248_;
goto v___jp_4173_;
}
else
{
lean_object* v_toConstantVal_4249_; lean_object* v_name_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v_toConstantVal_4249_ = lean_ctor_get(v___y_4240_, 0);
lean_inc_ref(v_toConstantVal_4249_);
lean_dec_ref(v___y_4240_);
v_name_4250_ = lean_ctor_get(v_toConstantVal_4249_, 0);
lean_inc(v_name_4250_);
lean_dec_ref(v_toConstantVal_4249_);
v___x_4251_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
v___x_4252_ = l_Lean_MessageData_ofName(v_name_4250_);
v___x_4253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4253_, 0, v___x_4251_);
lean_ctor_set(v___x_4253_, 1, v___x_4252_);
v___x_4254_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4255_, 0, v___x_4253_);
lean_ctor_set(v___x_4255_, 1, v___x_4254_);
v___x_4256_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4255_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; lean_object* v___x_4258_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
lean_inc(v_a_3716_);
lean_inc_ref(v_a_3715_);
v___x_4258_ = lean_apply_4(v___y_4241_, v_a_4257_, v_a_3715_, v_a_3716_, lean_box(0));
v___y_4174_ = v___y_4238_;
v___y_4175_ = v___y_4244_;
v___y_4176_ = v___x_4258_;
goto v___jp_4173_;
}
else
{
lean_dec_ref(v___y_4241_);
v___y_4174_ = v___y_4238_;
v___y_4175_ = v___y_4244_;
v___y_4176_ = v___x_4256_;
goto v___jp_4173_;
}
}
}
}
v___jp_4259_:
{
lean_object* v___x_4260_; lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4410_; 
v___x_4260_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_doAdd_spec__1___redArg(v_a_3716_);
v_a_4261_ = lean_ctor_get(v___x_4260_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4260_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4263_ = v___x_4260_;
v_isShared_4264_ = v_isSharedCheck_4410_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4260_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4410_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; 
v___x_4265_ = l_Lean_trace_profiler_useHeartbeats;
v___x_4266_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3770_, v___x_4265_);
if (v___x_4266_ == 0)
{
lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v_env_4269_; lean_object* v_nextMacroScope_4270_; lean_object* v_ngen_4271_; lean_object* v_auxDeclNGen_4272_; lean_object* v_traceState_4273_; lean_object* v_messages_4274_; lean_object* v_infoState_4275_; lean_object* v_snapshotTasks_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4324_; 
v___x_4267_ = lean_io_mono_nanos_now();
v___x_4268_ = lean_st_ref_take(v_a_3716_);
v_env_4269_ = lean_ctor_get(v___x_4268_, 0);
v_nextMacroScope_4270_ = lean_ctor_get(v___x_4268_, 1);
v_ngen_4271_ = lean_ctor_get(v___x_4268_, 2);
v_auxDeclNGen_4272_ = lean_ctor_get(v___x_4268_, 3);
v_traceState_4273_ = lean_ctor_get(v___x_4268_, 4);
v_messages_4274_ = lean_ctor_get(v___x_4268_, 6);
v_infoState_4275_ = lean_ctor_get(v___x_4268_, 7);
v_snapshotTasks_4276_ = lean_ctor_get(v___x_4268_, 8);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4324_ == 0)
{
lean_object* v_unused_4325_; 
v_unused_4325_ = lean_ctor_get(v___x_4268_, 5);
lean_dec(v_unused_4325_);
v___x_4278_ = v___x_4268_;
v_isShared_4279_ = v_isSharedCheck_4324_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_snapshotTasks_4276_);
lean_inc(v_infoState_4275_);
lean_inc(v_messages_4274_);
lean_inc(v_traceState_4273_);
lean_inc(v_auxDeclNGen_4272_);
lean_inc(v_ngen_4271_);
lean_inc(v_nextMacroScope_4270_);
lean_inc(v_env_4269_);
lean_dec(v___x_4268_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4324_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4284_; 
lean_inc(v_decl_3713_);
v___x_4280_ = l_Lean_Declaration_getNames(v_decl_3713_);
v___x_4281_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4269_, v___x_4280_);
v___x_4282_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4279_ == 0)
{
lean_ctor_set(v___x_4278_, 5, v___x_4282_);
lean_ctor_set(v___x_4278_, 0, v___x_4281_);
v___x_4284_ = v___x_4278_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4281_);
lean_ctor_set(v_reuseFailAlloc_4323_, 1, v_nextMacroScope_4270_);
lean_ctor_set(v_reuseFailAlloc_4323_, 2, v_ngen_4271_);
lean_ctor_set(v_reuseFailAlloc_4323_, 3, v_auxDeclNGen_4272_);
lean_ctor_set(v_reuseFailAlloc_4323_, 4, v_traceState_4273_);
lean_ctor_set(v_reuseFailAlloc_4323_, 5, v___x_4282_);
lean_ctor_set(v_reuseFailAlloc_4323_, 6, v_messages_4274_);
lean_ctor_set(v_reuseFailAlloc_4323_, 7, v_infoState_4275_);
lean_ctor_set(v_reuseFailAlloc_4323_, 8, v_snapshotTasks_4276_);
v___x_4284_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
lean_object* v___x_4285_; lean_object* v___x_4286_; lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___f_4289_; 
v___x_4285_ = lean_st_ref_set(v_a_3716_, v___x_4284_);
v___x_4286_ = lean_box(0);
v___x_4287_ = lean_box(v_hasTrace_3772_);
v___x_4288_ = lean_box(v___x_4266_);
lean_inc(v_decl_3713_);
v___f_4289_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___boxed), 11, 6);
lean_closure_set(v___f_4289_, 0, v_decl_3713_);
lean_closure_set(v___f_4289_, 1, v___x_4287_);
lean_closure_set(v___f_4289_, 2, v___x_4288_);
lean_closure_set(v___f_4289_, 3, v___x_4282_);
lean_closure_set(v___f_4289_, 4, v_cls_3908_);
lean_closure_set(v___f_4289_, 5, v___x_4286_);
switch(lean_obj_tag(v_decl_3713_))
{
case 2:
{
lean_object* v_val_4290_; lean_object* v___x_4291_; lean_object* v_env_4292_; lean_object* v___f_4293_; lean_object* v___x_4294_; lean_object* v___f_4295_; 
lean_del_object(v___x_4263_);
v_val_4290_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref_n(v_val_4290_, 3);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4291_ = lean_st_ref_get(v_a_3716_);
v_env_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc_ref(v_env_4292_);
lean_dec(v___x_4291_);
v___f_4293_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4293_, 0, v_val_4290_);
lean_closure_set(v___f_4293_, 1, v___f_4289_);
v___x_4294_ = lean_box(v___x_4266_);
lean_inc_ref(v___f_4293_);
v___f_4295_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__6___boxed), 7, 3);
lean_closure_set(v___f_4295_, 0, v_val_4290_);
lean_closure_set(v___f_4295_, 1, v___x_4294_);
lean_closure_set(v___f_4295_, 2, v___f_4293_);
if (v_forceExpose_3714_ == 0)
{
v___y_4238_ = v___x_4267_;
v___y_4239_ = v___f_4293_;
v___y_4240_ = v_val_4290_;
v___y_4241_ = v___f_4295_;
v___y_4242_ = v___x_4286_;
v___y_4243_ = v_env_4292_;
v___y_4244_ = v_a_4261_;
goto v___jp_4237_;
}
else
{
if (v___x_4266_ == 0)
{
lean_dec_ref(v___f_4295_);
lean_dec_ref(v_env_4292_);
lean_dec_ref(v_val_4290_);
v___y_4231_ = v___x_4267_;
v___y_4232_ = v___f_4293_;
v___y_4233_ = v___x_4286_;
v___y_4234_ = v_a_4261_;
goto v___jp_4230_;
}
else
{
v___y_4238_ = v___x_4267_;
v___y_4239_ = v___f_4293_;
v___y_4240_ = v_val_4290_;
v___y_4241_ = v___f_4295_;
v___y_4242_ = v___x_4286_;
v___y_4243_ = v_env_4292_;
v___y_4244_ = v_a_4261_;
goto v___jp_4237_;
}
}
}
case 1:
{
lean_object* v_val_4296_; lean_object* v___x_4297_; 
lean_del_object(v___x_4263_);
v_val_4296_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref(v_val_4296_);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4297_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4289_, v_cls_3908_, v___x_4286_, v___x_4266_, v_forceExpose_3714_, v_val_4296_, v_a_3715_, v_a_3716_);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4297_;
goto v___jp_4173_;
}
case 5:
{
lean_object* v_defns_4298_; 
lean_del_object(v___x_4263_);
v_defns_4298_ = lean_ctor_get(v_decl_3713_, 0);
if (lean_obj_tag(v_defns_4298_) == 1)
{
lean_object* v_tail_4299_; 
v_tail_4299_ = lean_ctor_get(v_defns_4298_, 1);
if (lean_obj_tag(v_tail_4299_) == 0)
{
lean_object* v_head_4300_; lean_object* v___x_4301_; 
lean_inc_ref(v_defns_4298_);
lean_dec_ref_known(v_decl_3713_, 1);
v_head_4300_ = lean_ctor_get(v_defns_4298_, 0);
lean_inc(v_head_4300_);
lean_dec_ref_known(v_defns_4298_, 2);
v___x_4301_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4(v___f_4289_, v_cls_3908_, v___x_4286_, v___x_4266_, v_forceExpose_3714_, v_head_4300_, v_a_3715_, v_a_3716_);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4301_;
goto v___jp_4173_;
}
else
{
lean_object* v___x_4302_; 
lean_dec_ref(v___f_4289_);
lean_inc_ref(v_decl_3713_);
v___x_4302_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec_ref_known(v_decl_3713_, 1);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4302_;
goto v___jp_4173_;
}
}
else
{
lean_object* v___x_4303_; 
lean_dec_ref(v___f_4289_);
lean_inc_ref(v_decl_3713_);
v___x_4303_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec_ref_known(v_decl_3713_, 1);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4303_;
goto v___jp_4173_;
}
}
case 3:
{
lean_object* v_val_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v_env_4307_; lean_object* v_env_4308_; lean_object* v___f_4309_; lean_object* v___f_4310_; 
lean_del_object(v___x_4263_);
v_val_4304_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref_n(v_val_4304_, 3);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4305_ = lean_st_ref_get(v_a_3716_);
v___x_4306_ = lean_st_ref_get(v_a_3716_);
v_env_4307_ = lean_ctor_get(v___x_4305_, 0);
lean_inc_ref(v_env_4307_);
lean_dec(v___x_4305_);
v_env_4308_ = lean_ctor_get(v___x_4306_, 0);
lean_inc_ref(v_env_4308_);
lean_dec(v___x_4306_);
v___f_4309_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4309_, 0, v_val_4304_);
lean_closure_set(v___f_4309_, 1, v___f_4289_);
lean_inc_ref(v___f_4309_);
v___f_4310_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9___boxed), 6, 2);
lean_closure_set(v___f_4310_, 0, v_val_4304_);
lean_closure_set(v___f_4310_, 1, v___f_4309_);
if (v_forceExpose_3714_ == 0)
{
v___y_4218_ = v___f_4310_;
v___y_4219_ = v___x_4267_;
v___y_4220_ = v_val_4304_;
v___y_4221_ = v___f_4309_;
v___y_4222_ = v_env_4308_;
v___y_4223_ = v___x_4286_;
v___y_4224_ = v___x_4266_;
v___y_4225_ = v_a_4261_;
v___y_4226_ = v_env_4307_;
goto v___jp_4217_;
}
else
{
if (v___x_4266_ == 0)
{
lean_dec_ref(v___f_4310_);
lean_dec_ref(v_env_4308_);
lean_dec_ref(v_env_4307_);
lean_dec_ref(v_val_4304_);
v___y_4194_ = v___x_4267_;
v___y_4195_ = v___f_4309_;
v___y_4196_ = v___x_4286_;
v___y_4197_ = v_a_4261_;
goto v___jp_4193_;
}
else
{
v___y_4218_ = v___f_4310_;
v___y_4219_ = v___x_4267_;
v___y_4220_ = v_val_4304_;
v___y_4221_ = v___f_4309_;
v___y_4222_ = v_env_4308_;
v___y_4223_ = v___x_4286_;
v___y_4224_ = v___x_4266_;
v___y_4225_ = v_a_4261_;
v___y_4226_ = v_env_4307_;
goto v___jp_4217_;
}
}
}
case 0:
{
lean_object* v_val_4311_; lean_object* v_toConstantVal_4312_; lean_object* v_name_4313_; lean_object* v___x_4315_; 
lean_dec_ref(v___f_4289_);
v_val_4311_ = lean_ctor_get(v_decl_3713_, 0);
v_toConstantVal_4312_ = lean_ctor_get(v_val_4311_, 0);
v_name_4313_ = lean_ctor_get(v_toConstantVal_4312_, 0);
lean_inc_ref(v_val_4311_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v_val_4311_);
v___x_4315_ = v___x_4263_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4321_; 
v_reuseFailAlloc_4321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4321_, 0, v_val_4311_);
v___x_4315_ = v_reuseFailAlloc_4321_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
uint8_t v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; 
v___x_4316_ = 2;
v___x_4317_ = lean_box(v___x_4316_);
v___x_4318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4318_, 0, v___x_4315_);
lean_ctor_set(v___x_4318_, 1, v___x_4317_);
lean_inc(v_name_4313_);
v___x_4319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4319_, 0, v_name_4313_);
lean_ctor_set(v___x_4319_, 1, v___x_4318_);
v___x_4320_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8(v_decl_3713_, v_hasTrace_3772_, v___x_4266_, v___x_4282_, v_cls_3908_, v___x_4286_, v___x_4319_, v___x_4286_, v_a_3715_, v_a_3716_);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4320_;
goto v___jp_4173_;
}
}
default: 
{
lean_object* v___x_4322_; 
lean_dec_ref(v___f_4289_);
lean_del_object(v___x_4263_);
lean_inc(v_decl_3713_);
v___x_4322_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec(v_decl_3713_);
v___y_4174_ = v___x_4267_;
v___y_4175_ = v_a_4261_;
v___y_4176_ = v___x_4322_;
goto v___jp_4173_;
}
}
}
}
}
else
{
lean_object* v___x_4326_; lean_object* v___x_4327_; lean_object* v_env_4328_; lean_object* v_nextMacroScope_4329_; lean_object* v_ngen_4330_; lean_object* v_auxDeclNGen_4331_; lean_object* v_traceState_4332_; lean_object* v_messages_4333_; lean_object* v_infoState_4334_; lean_object* v_snapshotTasks_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4408_; 
v___x_4326_ = lean_io_get_num_heartbeats();
v___x_4327_ = lean_st_ref_take(v_a_3716_);
v_env_4328_ = lean_ctor_get(v___x_4327_, 0);
v_nextMacroScope_4329_ = lean_ctor_get(v___x_4327_, 1);
v_ngen_4330_ = lean_ctor_get(v___x_4327_, 2);
v_auxDeclNGen_4331_ = lean_ctor_get(v___x_4327_, 3);
v_traceState_4332_ = lean_ctor_get(v___x_4327_, 4);
v_messages_4333_ = lean_ctor_get(v___x_4327_, 6);
v_infoState_4334_ = lean_ctor_get(v___x_4327_, 7);
v_snapshotTasks_4335_ = lean_ctor_get(v___x_4327_, 8);
v_isSharedCheck_4408_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4408_ == 0)
{
lean_object* v_unused_4409_; 
v_unused_4409_ = lean_ctor_get(v___x_4327_, 5);
lean_dec(v_unused_4409_);
v___x_4337_ = v___x_4327_;
v_isShared_4338_ = v_isSharedCheck_4408_;
goto v_resetjp_4336_;
}
else
{
lean_inc(v_snapshotTasks_4335_);
lean_inc(v_infoState_4334_);
lean_inc(v_messages_4333_);
lean_inc(v_traceState_4332_);
lean_inc(v_auxDeclNGen_4331_);
lean_inc(v_ngen_4330_);
lean_inc(v_nextMacroScope_4329_);
lean_inc(v_env_4328_);
lean_dec(v___x_4327_);
v___x_4337_ = lean_box(0);
v_isShared_4338_ = v_isSharedCheck_4408_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
lean_inc(v_decl_3713_);
v___x_4339_ = l_Lean_Declaration_getNames(v_decl_3713_);
v___x_4340_ = l_List_foldl___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__1(v_env_4328_, v___x_4339_);
v___x_4341_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 5, v___x_4341_);
lean_ctor_set(v___x_4337_, 0, v___x_4340_);
v___x_4343_ = v___x_4337_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4407_; 
v_reuseFailAlloc_4407_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4407_, 0, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4407_, 1, v_nextMacroScope_4329_);
lean_ctor_set(v_reuseFailAlloc_4407_, 2, v_ngen_4330_);
lean_ctor_set(v_reuseFailAlloc_4407_, 3, v_auxDeclNGen_4331_);
lean_ctor_set(v_reuseFailAlloc_4407_, 4, v_traceState_4332_);
lean_ctor_set(v_reuseFailAlloc_4407_, 5, v___x_4341_);
lean_ctor_set(v_reuseFailAlloc_4407_, 6, v_messages_4333_);
lean_ctor_set(v_reuseFailAlloc_4407_, 7, v_infoState_4334_);
lean_ctor_set(v_reuseFailAlloc_4407_, 8, v_snapshotTasks_4335_);
v___x_4343_ = v_reuseFailAlloc_4407_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; lean_object* v___x_4346_; lean_object* v___f_4347_; 
v___x_4344_ = lean_st_ref_set(v_a_3716_, v___x_4343_);
v___x_4345_ = lean_box(0);
v___x_4346_ = lean_box(v___x_4266_);
lean_inc(v_decl_3713_);
v___f_4347_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13___boxed), 10, 5);
lean_closure_set(v___f_4347_, 0, v_decl_3713_);
lean_closure_set(v___f_4347_, 1, v___x_4346_);
lean_closure_set(v___f_4347_, 2, v_cls_3908_);
lean_closure_set(v___f_4347_, 3, v___x_4341_);
lean_closure_set(v___f_4347_, 4, v___x_4345_);
switch(lean_obj_tag(v_decl_3713_))
{
case 2:
{
lean_object* v_val_4348_; lean_object* v___x_4349_; lean_object* v_env_4350_; lean_object* v___f_4351_; 
lean_del_object(v___x_4263_);
v_val_4348_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref_n(v_val_4348_, 2);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4349_ = lean_st_ref_get(v_a_3716_);
v_env_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc_ref(v_env_4350_);
lean_dec(v___x_4349_);
v___f_4351_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__5___boxed), 7, 2);
lean_closure_set(v___f_4351_, 0, v_val_4348_);
lean_closure_set(v___f_4351_, 1, v___f_4347_);
if (v_forceExpose_3714_ == 0)
{
if (v___x_4266_ == 0)
{
lean_dec_ref(v_env_4350_);
lean_dec_ref(v_val_4348_);
v___y_4145_ = v___x_4345_;
v___y_4146_ = v___f_4351_;
v___y_4147_ = v_a_4261_;
v___y_4148_ = v___x_4326_;
goto v___jp_4144_;
}
else
{
lean_object* v___x_4352_; uint8_t v_isModule_4353_; 
v___x_4352_ = l_Lean_Environment_header(v_env_4350_);
lean_dec_ref(v_env_4350_);
v_isModule_4353_ = lean_ctor_get_uint8(v___x_4352_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4352_);
if (v_isModule_4353_ == 0)
{
lean_dec_ref(v_val_4348_);
v___y_4145_ = v___x_4345_;
v___y_4146_ = v___f_4351_;
v___y_4147_ = v_a_4261_;
v___y_4148_ = v___x_4326_;
goto v___jp_4144_;
}
else
{
if (v___x_4111_ == 0)
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_box(0);
v___x_4355_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4348_, v_forceExpose_3714_, v___f_4351_, v___x_4354_, v_a_3715_, v_a_3716_);
lean_dec_ref(v_val_4348_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4355_;
goto v___jp_4124_;
}
else
{
lean_object* v_toConstantVal_4356_; lean_object* v_name_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; lean_object* v___x_4362_; lean_object* v___x_4363_; 
v_toConstantVal_4356_ = lean_ctor_get(v_val_4348_, 0);
v_name_4357_ = lean_ctor_get(v_toConstantVal_4356_, 0);
v___x_4358_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__4);
lean_inc(v_name_4357_);
v___x_4359_ = l_Lean_MessageData_ofName(v_name_4357_);
v___x_4360_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4360_, 0, v___x_4358_);
lean_ctor_set(v___x_4360_, 1, v___x_4359_);
v___x_4361_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4360_);
lean_ctor_set(v___x_4362_, 1, v___x_4361_);
v___x_4363_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4362_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v_a_4364_; lean_object* v___x_4365_; 
v_a_4364_ = lean_ctor_get(v___x_4363_, 0);
lean_inc(v_a_4364_);
lean_dec_ref_known(v___x_4363_, 1);
v___x_4365_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__12(v_val_4348_, v_forceExpose_3714_, v___f_4351_, v_a_4364_, v_a_3715_, v_a_3716_);
lean_dec_ref(v_val_4348_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4365_;
goto v___jp_4124_;
}
else
{
lean_dec_ref(v___f_4351_);
lean_dec_ref(v_val_4348_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4363_;
goto v___jp_4124_;
}
}
}
}
}
else
{
lean_dec_ref(v_env_4350_);
lean_dec_ref(v_val_4348_);
v___y_4145_ = v___x_4345_;
v___y_4146_ = v___f_4351_;
v___y_4147_ = v_a_4261_;
v___y_4148_ = v___x_4326_;
goto v___jp_4144_;
}
}
case 1:
{
lean_object* v_val_4366_; lean_object* v___x_4367_; 
lean_del_object(v___x_4263_);
v_val_4366_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref(v_val_4366_);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4367_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4347_, v_forceExpose_3714_, v___x_4266_, v___x_4345_, v_cls_3908_, v_val_4366_, v_a_3715_, v_a_3716_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4367_;
goto v___jp_4124_;
}
case 5:
{
lean_object* v_defns_4368_; 
lean_del_object(v___x_4263_);
v_defns_4368_ = lean_ctor_get(v_decl_3713_, 0);
if (lean_obj_tag(v_defns_4368_) == 1)
{
lean_object* v_tail_4369_; 
v_tail_4369_ = lean_ctor_get(v_defns_4368_, 1);
if (lean_obj_tag(v_tail_4369_) == 0)
{
lean_object* v_head_4370_; lean_object* v___x_4371_; 
lean_inc_ref(v_defns_4368_);
lean_dec_ref_known(v_decl_3713_, 1);
v_head_4370_ = lean_ctor_get(v_defns_4368_, 0);
lean_inc(v_head_4370_);
lean_dec_ref_known(v_defns_4368_, 2);
v___x_4371_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__10(v___f_4347_, v_forceExpose_3714_, v___x_4266_, v___x_4345_, v_cls_3908_, v_head_4370_, v_a_3715_, v_a_3716_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4371_;
goto v___jp_4124_;
}
else
{
lean_object* v___x_4372_; 
lean_dec_ref(v___f_4347_);
lean_inc_ref(v_decl_3713_);
v___x_4372_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec_ref_known(v_decl_3713_, 1);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4372_;
goto v___jp_4124_;
}
}
else
{
lean_object* v___x_4373_; 
lean_dec_ref(v___f_4347_);
lean_inc_ref(v_decl_3713_);
v___x_4373_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec_ref_known(v_decl_3713_, 1);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4373_;
goto v___jp_4124_;
}
}
case 3:
{
lean_object* v_val_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; lean_object* v_env_4377_; lean_object* v_env_4378_; lean_object* v___f_4379_; 
lean_del_object(v___x_4263_);
v_val_4374_ = lean_ctor_get(v_decl_3713_, 0);
lean_inc_ref_n(v_val_4374_, 2);
lean_dec_ref_known(v_decl_3713_, 1);
v___x_4375_ = lean_st_ref_get(v_a_3716_);
v___x_4376_ = lean_st_ref_get(v_a_3716_);
v_env_4377_ = lean_ctor_get(v___x_4375_, 0);
lean_inc_ref(v_env_4377_);
lean_dec(v___x_4375_);
v_env_4378_ = lean_ctor_get(v___x_4376_, 0);
lean_inc_ref(v_env_4378_);
lean_dec(v___x_4376_);
v___f_4379_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__7___boxed), 7, 2);
lean_closure_set(v___f_4379_, 0, v_val_4374_);
lean_closure_set(v___f_4379_, 1, v___f_4347_);
if (v_forceExpose_3714_ == 0)
{
if (v___x_4266_ == 0)
{
lean_dec_ref(v_env_4378_);
lean_dec_ref(v_env_4377_);
lean_dec_ref(v_val_4374_);
v___y_4152_ = v___f_4379_;
v___y_4153_ = v___x_4345_;
v___y_4154_ = v_a_4261_;
v___y_4155_ = v___x_4326_;
goto v___jp_4151_;
}
else
{
lean_object* v___x_4380_; uint8_t v_isModule_4381_; 
v___x_4380_ = l_Lean_Environment_header(v_env_4377_);
lean_dec_ref(v_env_4377_);
v_isModule_4381_ = lean_ctor_get_uint8(v___x_4380_, sizeof(void*)*7 + 4);
lean_dec_ref(v___x_4380_);
if (v_isModule_4381_ == 0)
{
lean_dec_ref(v_env_4378_);
lean_dec_ref(v_val_4374_);
v___y_4152_ = v___f_4379_;
v___y_4153_ = v___x_4345_;
v___y_4154_ = v_a_4261_;
v___y_4155_ = v___x_4326_;
goto v___jp_4151_;
}
else
{
uint8_t v_isExporting_4382_; 
v_isExporting_4382_ = lean_ctor_get_uint8(v_env_4378_, sizeof(void*)*8);
lean_dec_ref(v_env_4378_);
if (v_isExporting_4382_ == 0)
{
if (v___x_4111_ == 0)
{
lean_object* v___x_4383_; lean_object* v___x_4384_; 
v___x_4383_ = lean_box(0);
v___x_4384_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4374_, v___f_4379_, v___x_4383_, v_a_3715_, v_a_3716_);
lean_dec_ref(v_val_4374_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4384_;
goto v___jp_4124_;
}
else
{
lean_object* v_toConstantVal_4385_; lean_object* v_name_4386_; lean_object* v___x_4387_; lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; lean_object* v___x_4392_; 
v_toConstantVal_4385_ = lean_ctor_get(v_val_4374_, 0);
v_name_4386_ = lean_ctor_get(v_toConstantVal_4385_, 0);
v___x_4387_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2, &l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___closed__2);
lean_inc(v_name_4386_);
v___x_4388_ = l_Lean_MessageData_ofName(v_name_4386_);
v___x_4389_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4387_);
lean_ctor_set(v___x_4389_, 1, v___x_4388_);
v___x_4390_ = lean_obj_once(&l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3, &l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3_once, _init_l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__4___closed__3);
v___x_4391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4389_);
lean_ctor_set(v___x_4391_, 1, v___x_4390_);
v___x_4392_ = l_Lean_addTrace___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__0(v_cls_3908_, v___x_4391_, v_a_3715_, v_a_3716_);
if (lean_obj_tag(v___x_4392_) == 0)
{
lean_object* v_a_4393_; lean_object* v___x_4394_; 
v_a_4393_ = lean_ctor_get(v___x_4392_, 0);
lean_inc(v_a_4393_);
lean_dec_ref_known(v___x_4392_, 1);
v___x_4394_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__9(v_val_4374_, v___f_4379_, v_a_4393_, v_a_3715_, v_a_3716_);
lean_dec_ref(v_val_4374_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4394_;
goto v___jp_4124_;
}
else
{
lean_dec_ref(v___f_4379_);
lean_dec_ref(v_val_4374_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4392_;
goto v___jp_4124_;
}
}
}
else
{
lean_dec_ref(v_val_4374_);
v___y_4152_ = v___f_4379_;
v___y_4153_ = v___x_4345_;
v___y_4154_ = v_a_4261_;
v___y_4155_ = v___x_4326_;
goto v___jp_4151_;
}
}
}
}
else
{
lean_dec_ref(v_env_4378_);
lean_dec_ref(v_env_4377_);
lean_dec_ref(v_val_4374_);
v___y_4152_ = v___f_4379_;
v___y_4153_ = v___x_4345_;
v___y_4154_ = v_a_4261_;
v___y_4155_ = v___x_4326_;
goto v___jp_4151_;
}
}
case 0:
{
lean_object* v_val_4395_; lean_object* v_toConstantVal_4396_; lean_object* v_name_4397_; lean_object* v___x_4399_; 
lean_dec_ref(v___f_4347_);
v_val_4395_ = lean_ctor_get(v_decl_3713_, 0);
v_toConstantVal_4396_ = lean_ctor_get(v_val_4395_, 0);
v_name_4397_ = lean_ctor_get(v_toConstantVal_4396_, 0);
lean_inc_ref(v_val_4395_);
if (v_isShared_4264_ == 0)
{
lean_ctor_set(v___x_4263_, 0, v_val_4395_);
v___x_4399_ = v___x_4263_;
goto v_reusejp_4398_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_val_4395_);
v___x_4399_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4398_;
}
v_reusejp_4398_:
{
uint8_t v___x_4400_; lean_object* v___x_4401_; lean_object* v___x_4402_; lean_object* v___x_4403_; lean_object* v___x_4404_; 
v___x_4400_ = 2;
v___x_4401_ = lean_box(v___x_4400_);
v___x_4402_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4402_, 0, v___x_4399_);
lean_ctor_set(v___x_4402_, 1, v___x_4401_);
lean_inc(v_name_4397_);
v___x_4403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4403_, 0, v_name_4397_);
lean_ctor_set(v___x_4403_, 1, v___x_4402_);
v___x_4404_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__13(v_decl_3713_, v___x_4266_, v_cls_3908_, v___x_4341_, v___x_4345_, v___x_4403_, v___x_4345_, v_a_3715_, v_a_3716_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4404_;
goto v___jp_4124_;
}
}
default: 
{
lean_object* v___x_4406_; 
lean_dec_ref(v___f_4347_);
lean_del_object(v___x_4263_);
lean_inc(v_decl_3713_);
v___x_4406_ = l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__3(v_decl_3713_, v_cls_3908_, v_decl_3713_, v_a_3715_, v_a_3716_);
lean_dec(v_decl_3713_);
v___y_4125_ = v___x_4326_;
v___y_4126_ = v_a_4261_;
v___y_4127_ = v___x_4406_;
goto v___jp_4124_;
}
}
}
}
}
}
}
}
v___jp_3718_:
{
lean_object* v___x_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
v___x_3722_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3719_, v___y_3720_);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3722_);
if (v_isSharedCheck_3729_ == 0)
{
lean_object* v_unused_3730_; 
v_unused_3730_ = lean_ctor_get(v___x_3722_, 0);
lean_dec(v_unused_3730_);
v___x_3724_ = v___x_3722_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_dec(v___x_3722_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set_tag(v___x_3724_, 1);
lean_ctor_set(v___x_3724_, 0, v_a_3721_);
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3721_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
v___jp_3731_:
{
lean_object* v___x_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
v___x_3735_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3732_, v___y_3733_);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3735_);
if (v_isSharedCheck_3742_ == 0)
{
lean_object* v_unused_3743_; 
v_unused_3743_ = lean_ctor_get(v___x_3735_, 0);
lean_dec(v_unused_3743_);
v___x_3737_ = v___x_3735_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_dec(v___x_3735_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_a_3734_);
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3734_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
v___jp_3744_:
{
lean_object* v___x_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v___x_3748_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3745_, v___y_3746_);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3748_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3748_, 0);
lean_dec(v_unused_3756_);
v___x_3750_ = v___x_3748_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_dec(v___x_3748_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_a_3747_);
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3747_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
v___jp_3757_:
{
lean_object* v___x_3761_; lean_object* v___x_3763_; uint8_t v_isShared_3764_; uint8_t v_isSharedCheck_3768_; 
v___x_3761_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3758_, v___y_3759_);
v_isSharedCheck_3768_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3768_ == 0)
{
lean_object* v_unused_3769_; 
v_unused_3769_ = lean_ctor_get(v___x_3761_, 0);
lean_dec(v_unused_3769_);
v___x_3763_ = v___x_3761_;
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
else
{
lean_dec(v___x_3761_);
v___x_3763_ = lean_box(0);
v_isShared_3764_ = v_isSharedCheck_3768_;
goto v_resetjp_3762_;
}
v_resetjp_3762_:
{
lean_object* v___x_3766_; 
if (v_isShared_3764_ == 0)
{
lean_ctor_set_tag(v___x_3763_, 1);
lean_ctor_set(v___x_3763_, 0, v_a_3760_);
v___x_3766_ = v___x_3763_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v_a_3760_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
v___jp_3773_:
{
lean_object* v___x_3785_; 
lean_inc_ref(v___y_3776_);
v___x_3785_ = l_Lean_Environment_AddConstAsyncResult_commitConst(v___y_3782_, v___y_3776_, v___y_3777_, v___y_3784_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v___x_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3832_; 
lean_dec_ref_known(v___x_3785_, 1);
lean_inc_ref(v___y_3778_);
v___x_3786_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3778_, v___y_3780_);
v_isSharedCheck_3832_ = !lean_is_exclusive(v___x_3786_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v___x_3786_, 0);
lean_dec(v_unused_3833_);
v___x_3788_ = v___x_3786_;
v_isShared_3789_ = v_isSharedCheck_3832_;
goto v_resetjp_3787_;
}
else
{
lean_dec(v___x_3786_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3832_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v_options_3790_; lean_object* v___x_3791_; uint8_t v___x_3792_; 
v_options_3790_ = lean_ctor_get(v___y_3779_, 2);
v___x_3791_ = l_Lean_Elab_async;
v___x_3792_ = l_Lean_Option_get___at___00Lean_Kernel_Environment_addDecl_spec__0(v_options_3790_, v___x_3791_);
if (v___x_3792_ == 0)
{
lean_object* v___x_3793_; lean_object* v_r_3794_; 
lean_del_object(v___x_3788_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v___y_3774_);
v___x_3793_ = l_Lean_setEnv___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_addAsAxiom_spec__1___redArg(v___y_3776_, v___y_3780_);
lean_dec_ref(v___x_3793_);
v_r_3794_ = l___private_Lean_AddDecl_0__Lean_addDeclCore_doAdd(v_decl_3713_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v_r_3794_) == 0)
{
lean_object* v_a_3795_; lean_object* v___x_3797_; uint8_t v_isShared_3798_; uint8_t v_isSharedCheck_3804_; 
v_a_3795_ = lean_ctor_get(v_r_3794_, 0);
v_isSharedCheck_3804_ = !lean_is_exclusive(v_r_3794_);
if (v_isSharedCheck_3804_ == 0)
{
v___x_3797_ = v_r_3794_;
v_isShared_3798_ = v_isSharedCheck_3804_;
goto v_resetjp_3796_;
}
else
{
lean_inc(v_a_3795_);
lean_dec(v_r_3794_);
v___x_3797_ = lean_box(0);
v_isShared_3798_ = v_isSharedCheck_3804_;
goto v_resetjp_3796_;
}
v_resetjp_3796_:
{
lean_object* v___x_3800_; 
lean_inc(v_a_3795_);
if (v_isShared_3798_ == 0)
{
lean_ctor_set_tag(v___x_3797_, 1);
v___x_3800_ = v___x_3797_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v_a_3795_);
v___x_3800_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3801_; 
v___x_3801_ = lean_apply_2(v___y_3781_, v___x_3800_, lean_box(0));
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref_known(v___x_3801_, 1);
v___y_3732_ = v___y_3778_;
v___y_3733_ = v___y_3780_;
v_a_3734_ = v_a_3795_;
goto v___jp_3731_;
}
else
{
lean_object* v_a_3802_; 
lean_dec(v_a_3795_);
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___y_3719_ = v___y_3778_;
v___y_3720_ = v___y_3780_;
v_a_3721_ = v_a_3802_;
goto v___jp_3718_;
}
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; 
v_a_3805_ = lean_ctor_get(v_r_3794_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v_r_3794_, 1);
v___x_3806_ = lean_box(0);
v___x_3807_ = lean_apply_2(v___y_3781_, v___x_3806_, lean_box(0));
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_dec_ref_known(v___x_3807_, 1);
v___y_3719_ = v___y_3778_;
v___y_3720_ = v___y_3780_;
v_a_3721_ = v_a_3805_;
goto v___jp_3718_;
}
else
{
lean_object* v_a_3808_; 
lean_dec(v_a_3805_);
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref_known(v___x_3807_, 1);
v___y_3719_ = v___y_3778_;
v___y_3720_ = v___y_3780_;
v_a_3721_ = v_a_3808_;
goto v___jp_3718_;
}
}
}
else
{
lean_object* v___x_3809_; lean_object* v___x_3811_; 
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v___y_3776_);
lean_dec(v_decl_3713_);
v___x_3809_ = l_IO_CancelToken_new();
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 1);
lean_ctor_set(v___x_3788_, 0, v___x_3809_);
v___x_3811_ = v___x_3788_;
goto v_reusejp_3810_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3809_);
v___x_3811_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3810_;
}
v_reusejp_3810_:
{
lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3812_ = lean_unsigned_to_nat(0u);
v___x_3813_ = ((lean_object*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__8___closed__1));
v___x_3814_ = l_Lean_Name_toString(v___x_3813_, v___y_3783_);
lean_inc_ref(v___x_3811_);
v___x_3815_ = l_Lean_Core_wrapAsyncAsSnapshot___redArg(v___y_3775_, v___x_3811_, v___x_3814_, v___y_3779_, v___y_3780_);
if (lean_obj_tag(v___x_3815_) == 0)
{
lean_object* v_a_3816_; lean_object* v_checked_3817_; lean_object* v___x_3818_; lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; lean_object* v___x_3822_; 
v_a_3816_ = lean_ctor_get(v___x_3815_, 0);
lean_inc(v_a_3816_);
lean_dec_ref_known(v___x_3815_, 1);
v_checked_3817_ = lean_ctor_get(v___y_3774_, 2);
lean_inc_ref(v_checked_3817_);
lean_dec_ref(v___y_3774_);
v___x_3818_ = lean_io_map_task(v_a_3816_, v_checked_3817_, v___x_3812_, v_hasTrace_3772_);
v___x_3819_ = lean_box(0);
v___x_3820_ = lean_box(2);
v___x_3821_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3819_);
lean_ctor_set(v___x_3821_, 1, v___x_3820_);
lean_ctor_set(v___x_3821_, 2, v___x_3811_);
lean_ctor_set(v___x_3821_, 3, v___x_3818_);
v___x_3822_ = l_Lean_Core_logSnapshotTask___redArg(v___x_3821_, v___y_3780_);
return v___x_3822_;
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v___x_3811_);
lean_dec_ref(v___y_3774_);
v_a_3823_ = lean_ctor_get(v___x_3815_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3815_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3815_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3815_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3834_; lean_object* v___x_3836_; uint8_t v_isShared_3837_; uint8_t v_isSharedCheck_3846_; 
lean_dec_ref(v___y_3781_);
lean_dec_ref(v___y_3778_);
lean_dec_ref(v___y_3776_);
lean_dec_ref(v___y_3775_);
lean_dec_ref(v___y_3774_);
lean_dec(v_decl_3713_);
v_a_3834_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3836_ = v___x_3785_;
v_isShared_3837_ = v_isSharedCheck_3846_;
goto v_resetjp_3835_;
}
else
{
lean_inc(v_a_3834_);
lean_dec(v___x_3785_);
v___x_3836_ = lean_box(0);
v_isShared_3837_ = v_isSharedCheck_3846_;
goto v_resetjp_3835_;
}
v_resetjp_3835_:
{
lean_object* v_ref_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3844_; 
v_ref_3838_ = lean_ctor_get(v___y_3779_, 5);
v___x_3839_ = lean_io_error_to_string(v_a_3834_);
v___x_3840_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
v___x_3841_ = l_Lean_MessageData_ofFormat(v___x_3840_);
lean_inc(v_ref_3838_);
v___x_3842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3842_, 0, v_ref_3838_);
lean_ctor_set(v___x_3842_, 1, v___x_3841_);
if (v_isShared_3837_ == 0)
{
lean_ctor_set(v___x_3836_, 0, v___x_3842_);
v___x_3844_ = v___x_3836_;
goto v_reusejp_3843_;
}
else
{
lean_object* v_reuseFailAlloc_3845_; 
v_reuseFailAlloc_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3845_, 0, v___x_3842_);
v___x_3844_ = v_reuseFailAlloc_3845_;
goto v_reusejp_3843_;
}
v_reusejp_3843_:
{
return v___x_3844_;
}
}
}
}
v___jp_3847_:
{
uint8_t v___x_3858_; lean_object* v___x_3859_; 
v___x_3858_ = 1;
lean_inc_ref(v___y_3848_);
v___x_3859_ = l_Lean_Environment_addConstAsync(v___y_3848_, v___y_3851_, v___y_3852_, v___y_3857_, v_hasTrace_3772_, v___x_3858_);
if (lean_obj_tag(v___x_3859_) == 0)
{
lean_object* v_a_3860_; lean_object* v_mainEnv_3861_; lean_object* v_asyncEnv_3862_; lean_object* v___f_3863_; lean_object* v___f_3864_; lean_object* v___x_3865_; 
v_a_3860_ = lean_ctor_get(v___x_3859_, 0);
lean_inc_n(v_a_3860_, 3);
lean_dec_ref_known(v___x_3859_, 1);
v_mainEnv_3861_ = lean_ctor_get(v_a_3860_, 0);
lean_inc_ref(v_mainEnv_3861_);
v_asyncEnv_3862_ = lean_ctor_get(v_a_3860_, 1);
lean_inc_ref_n(v_asyncEnv_3862_, 2);
lean_inc_ref(v___y_3849_);
lean_inc(v___y_3850_);
v___f_3863_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__0___boxed), 5, 3);
lean_closure_set(v___f_3863_, 0, v___y_3850_);
lean_closure_set(v___f_3863_, 1, v_a_3860_);
lean_closure_set(v___f_3863_, 2, v___y_3849_);
lean_inc(v_decl_3713_);
v___f_3864_ = lean_alloc_closure((void*)(l___private_Lean_AddDecl_0__Lean_addDeclCore___lam__2___boxed), 7, 3);
lean_closure_set(v___f_3864_, 0, v_asyncEnv_3862_);
lean_closure_set(v___f_3864_, 1, v_a_3860_);
lean_closure_set(v___f_3864_, 2, v_decl_3713_);
v___x_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3865_, 0, v___y_3853_);
if (lean_obj_tag(v___y_3856_) == 0)
{
lean_inc_ref(v___x_3865_);
v___y_3774_ = v___y_3848_;
v___y_3775_ = v___f_3864_;
v___y_3776_ = v_asyncEnv_3862_;
v___y_3777_ = v___x_3865_;
v___y_3778_ = v_mainEnv_3861_;
v___y_3779_ = v___y_3855_;
v___y_3780_ = v___y_3854_;
v___y_3781_ = v___f_3863_;
v___y_3782_ = v_a_3860_;
v___y_3783_ = v___x_3858_;
v___y_3784_ = v___x_3865_;
goto v___jp_3773_;
}
else
{
v___y_3774_ = v___y_3848_;
v___y_3775_ = v___f_3864_;
v___y_3776_ = v_asyncEnv_3862_;
v___y_3777_ = v___x_3865_;
v___y_3778_ = v_mainEnv_3861_;
v___y_3779_ = v___y_3855_;
v___y_3780_ = v___y_3854_;
v___y_3781_ = v___f_3863_;
v___y_3782_ = v_a_3860_;
v___y_3783_ = v___x_3858_;
v___y_3784_ = v___y_3856_;
goto v___jp_3773_;
}
}
else
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3878_; 
lean_dec(v___y_3856_);
lean_dec_ref(v___y_3853_);
lean_dec_ref(v___y_3848_);
lean_dec(v_decl_3713_);
v_a_3866_ = lean_ctor_get(v___x_3859_, 0);
v_isSharedCheck_3878_ = !lean_is_exclusive(v___x_3859_);
if (v_isSharedCheck_3878_ == 0)
{
v___x_3868_ = v___x_3859_;
v_isShared_3869_ = v_isSharedCheck_3878_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3859_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3878_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
lean_object* v_ref_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3876_; 
v_ref_3870_ = lean_ctor_get(v___y_3855_, 5);
v___x_3871_ = lean_io_error_to_string(v_a_3866_);
v___x_3872_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3872_, 0, v___x_3871_);
v___x_3873_ = l_Lean_MessageData_ofFormat(v___x_3872_);
lean_inc(v_ref_3870_);
v___x_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3874_, 0, v_ref_3870_);
lean_ctor_set(v___x_3874_, 1, v___x_3873_);
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3874_);
v___x_3876_ = v___x_3868_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
return v___x_3876_;
}
}
}
}
v___jp_3879_:
{
lean_object* v___x_3886_; 
v___x_3886_ = lean_st_ref_get(v___y_3885_);
if (lean_obj_tag(v_exportedInfo_x3f_3883_) == 0)
{
lean_object* v_env_3887_; lean_object* v___x_3888_; 
v_env_3887_ = lean_ctor_get(v___x_3886_, 0);
lean_inc_ref(v_env_3887_);
lean_dec(v___x_3886_);
v___x_3888_ = lean_box(0);
v___y_3848_ = v_env_3887_;
v___y_3849_ = v___y_3884_;
v___y_3850_ = v___y_3885_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3885_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v_exportedInfo_x3f_3883_;
v___y_3857_ = v___x_3888_;
goto v___jp_3847_;
}
else
{
lean_object* v_env_3889_; lean_object* v_val_3890_; uint8_t v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; 
v_env_3889_ = lean_ctor_get(v___x_3886_, 0);
lean_inc_ref(v_env_3889_);
lean_dec(v___x_3886_);
v_val_3890_ = lean_ctor_get(v_exportedInfo_x3f_3883_, 0);
v___x_3891_ = l_Lean_ConstantKind_ofConstantInfo(v_val_3890_);
v___x_3892_ = lean_box(v___x_3891_);
v___x_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
v___y_3848_ = v_env_3889_;
v___y_3849_ = v___y_3884_;
v___y_3850_ = v___y_3885_;
v___y_3851_ = v___y_3880_;
v___y_3852_ = v___y_3881_;
v___y_3853_ = v___y_3882_;
v___y_3854_ = v___y_3885_;
v___y_3855_ = v___y_3884_;
v___y_3856_ = v_exportedInfo_x3f_3883_;
v___y_3857_ = v___x_3893_;
goto v___jp_3847_;
}
}
v___jp_3894_:
{
lean_object* v___x_3900_; 
lean_inc_ref(v___y_3897_);
v___x_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3900_, 0, v___y_3897_);
v___y_3880_ = v___y_3895_;
v___y_3881_ = v___y_3896_;
v___y_3882_ = v___y_3897_;
v_exportedInfo_x3f_3883_ = v___x_3900_;
v___y_3884_ = v___y_3898_;
v___y_3885_ = v___y_3899_;
goto v___jp_3879_;
}
v___jp_3901_:
{
lean_object* v___x_3907_; 
lean_inc_ref(v___y_3904_);
v___x_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3907_, 0, v___y_3904_);
v___y_3880_ = v___y_3902_;
v___y_3881_ = v___y_3903_;
v___y_3882_ = v___y_3904_;
v_exportedInfo_x3f_3883_ = v___x_3907_;
v___y_3884_ = v___y_3905_;
v___y_3885_ = v___y_3906_;
goto v___jp_3879_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_AddDecl_0__Lean_addDeclCore___boxed(lean_object* v_decl_4792_, lean_object* v_forceExpose_4793_, lean_object* v_a_4794_, lean_object* v_a_4795_, lean_object* v_a_4796_){
_start:
{
uint8_t v_forceExpose_boxed_4797_; lean_object* v_res_4798_; 
v_forceExpose_boxed_4797_ = lean_unbox(v_forceExpose_4793_);
v_res_4798_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4792_, v_forceExpose_boxed_4797_, v_a_4794_, v_a_4795_);
lean_dec(v_a_4795_);
lean_dec_ref(v_a_4794_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(lean_object* v_opt_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v___x_4803_; 
v___x_4803_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___redArg(v_opt_4799_, v___y_4800_);
return v___x_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3___boxed(lean_object* v_opt_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v_res_4808_; 
v_res_4808_ = l_Lean_Option_getM___at___00__private_Lean_AddDecl_0__Lean_addDeclCore_spec__3(v_opt_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec_ref(v_opt_4804_);
return v_res_4808_;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0(lean_object* v_x_4809_, lean_object* v_x_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
if (lean_obj_tag(v_x_4809_) == 0)
{
lean_object* v___x_4814_; lean_object* v___x_4815_; 
v___x_4814_ = l_List_reverse___redArg(v_x_4810_);
v___x_4815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4815_, 0, v___x_4814_);
return v___x_4815_;
}
else
{
lean_object* v_head_4816_; lean_object* v_tail_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4835_; 
v_head_4816_ = lean_ctor_get(v_x_4809_, 0);
v_tail_4817_ = lean_ctor_get(v_x_4809_, 1);
v_isSharedCheck_4835_ = !lean_is_exclusive(v_x_4809_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4819_ = v_x_4809_;
v_isShared_4820_ = v_isSharedCheck_4835_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_tail_4817_);
lean_inc(v_head_4816_);
lean_dec(v_x_4809_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4835_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; 
v___x_4821_ = l_Lean_snapshotEnvLinterOptions(v_head_4816_, v___y_4811_, v___y_4812_);
if (lean_obj_tag(v___x_4821_) == 0)
{
lean_object* v_a_4822_; lean_object* v___x_4824_; 
v_a_4822_ = lean_ctor_get(v___x_4821_, 0);
lean_inc(v_a_4822_);
lean_dec_ref_known(v___x_4821_, 1);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 1, v_x_4810_);
lean_ctor_set(v___x_4819_, 0, v_a_4822_);
v___x_4824_ = v___x_4819_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v_a_4822_);
lean_ctor_set(v_reuseFailAlloc_4826_, 1, v_x_4810_);
v___x_4824_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
v_x_4809_ = v_tail_4817_;
v_x_4810_ = v___x_4824_;
goto _start;
}
}
else
{
lean_object* v_a_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
lean_del_object(v___x_4819_);
lean_dec(v_tail_4817_);
lean_dec(v_x_4810_);
v_a_4827_ = lean_ctor_get(v___x_4821_, 0);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4834_ == 0)
{
v___x_4829_ = v___x_4821_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_inc(v_a_4827_);
lean_dec(v___x_4821_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4827_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___00Lean_addDecl_spec__0___boxed(lean_object* v_x_4836_, lean_object* v_x_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v_x_4836_, v_x_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl(lean_object* v_decl_4842_, uint8_t v_forceExpose_4843_, lean_object* v_a_4844_, lean_object* v_a_4845_){
_start:
{
lean_object* v___x_4847_; 
lean_inc(v_decl_4842_);
v___x_4847_ = l___private_Lean_AddDecl_0__Lean_addDeclCore(v_decl_4842_, v_forceExpose_4843_, v_a_4844_, v_a_4845_);
if (lean_obj_tag(v___x_4847_) == 0)
{
lean_object* v___x_4848_; lean_object* v___x_4849_; lean_object* v___x_4850_; 
lean_dec_ref_known(v___x_4847_, 1);
v___x_4848_ = l_Lean_Declaration_getTopLevelNames(v_decl_4842_);
v___x_4849_ = lean_box(0);
v___x_4850_ = l_List_mapM_loop___at___00Lean_addDecl_spec__0(v___x_4848_, v___x_4849_, v_a_4844_, v_a_4845_);
if (lean_obj_tag(v___x_4850_) == 0)
{
lean_object* v___x_4852_; uint8_t v_isShared_4853_; uint8_t v_isSharedCheck_4858_; 
v_isSharedCheck_4858_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4858_ == 0)
{
lean_object* v_unused_4859_; 
v_unused_4859_ = lean_ctor_get(v___x_4850_, 0);
lean_dec(v_unused_4859_);
v___x_4852_ = v___x_4850_;
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
else
{
lean_dec(v___x_4850_);
v___x_4852_ = lean_box(0);
v_isShared_4853_ = v_isSharedCheck_4858_;
goto v_resetjp_4851_;
}
v_resetjp_4851_:
{
lean_object* v___x_4854_; lean_object* v___x_4856_; 
v___x_4854_ = lean_box(0);
if (v_isShared_4853_ == 0)
{
lean_ctor_set(v___x_4852_, 0, v___x_4854_);
v___x_4856_ = v___x_4852_;
goto v_reusejp_4855_;
}
else
{
lean_object* v_reuseFailAlloc_4857_; 
v_reuseFailAlloc_4857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4857_, 0, v___x_4854_);
v___x_4856_ = v_reuseFailAlloc_4857_;
goto v_reusejp_4855_;
}
v_reusejp_4855_:
{
return v___x_4856_;
}
}
}
else
{
lean_object* v_a_4860_; lean_object* v___x_4862_; uint8_t v_isShared_4863_; uint8_t v_isSharedCheck_4867_; 
v_a_4860_ = lean_ctor_get(v___x_4850_, 0);
v_isSharedCheck_4867_ = !lean_is_exclusive(v___x_4850_);
if (v_isSharedCheck_4867_ == 0)
{
v___x_4862_ = v___x_4850_;
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
else
{
lean_inc(v_a_4860_);
lean_dec(v___x_4850_);
v___x_4862_ = lean_box(0);
v_isShared_4863_ = v_isSharedCheck_4867_;
goto v_resetjp_4861_;
}
v_resetjp_4861_:
{
lean_object* v___x_4865_; 
if (v_isShared_4863_ == 0)
{
v___x_4865_ = v___x_4862_;
goto v_reusejp_4864_;
}
else
{
lean_object* v_reuseFailAlloc_4866_; 
v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_a_4860_);
v___x_4865_ = v_reuseFailAlloc_4866_;
goto v_reusejp_4864_;
}
v_reusejp_4864_:
{
return v___x_4865_;
}
}
}
}
else
{
lean_dec(v_decl_4842_);
return v___x_4847_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addDecl___boxed(lean_object* v_decl_4868_, lean_object* v_forceExpose_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
uint8_t v_forceExpose_boxed_4873_; lean_object* v_res_4874_; 
v_forceExpose_boxed_4873_ = lean_unbox(v_forceExpose_4869_);
v_res_4874_ = l_Lean_addDecl(v_decl_4868_, v_forceExpose_boxed_4873_, v_a_4870_, v_a_4871_);
lean_dec(v_a_4871_);
lean_dec_ref(v_a_4870_);
return v_res_4874_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(lean_object* v_as_x27_4875_, lean_object* v_b_4876_, lean_object* v___y_4877_){
_start:
{
if (lean_obj_tag(v_as_x27_4875_) == 0)
{
lean_object* v___x_4879_; 
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v_b_4876_);
return v___x_4879_;
}
else
{
lean_object* v_head_4880_; lean_object* v_tail_4881_; lean_object* v___x_4882_; lean_object* v_env_4883_; lean_object* v_nextMacroScope_4884_; lean_object* v_ngen_4885_; lean_object* v_auxDeclNGen_4886_; lean_object* v_traceState_4887_; lean_object* v_messages_4888_; lean_object* v_infoState_4889_; lean_object* v_snapshotTasks_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4902_; 
v_head_4880_ = lean_ctor_get(v_as_x27_4875_, 0);
v_tail_4881_ = lean_ctor_get(v_as_x27_4875_, 1);
v___x_4882_ = lean_st_ref_take(v___y_4877_);
v_env_4883_ = lean_ctor_get(v___x_4882_, 0);
v_nextMacroScope_4884_ = lean_ctor_get(v___x_4882_, 1);
v_ngen_4885_ = lean_ctor_get(v___x_4882_, 2);
v_auxDeclNGen_4886_ = lean_ctor_get(v___x_4882_, 3);
v_traceState_4887_ = lean_ctor_get(v___x_4882_, 4);
v_messages_4888_ = lean_ctor_get(v___x_4882_, 6);
v_infoState_4889_ = lean_ctor_get(v___x_4882_, 7);
v_snapshotTasks_4890_ = lean_ctor_get(v___x_4882_, 8);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4902_ == 0)
{
lean_object* v_unused_4903_; 
v_unused_4903_ = lean_ctor_get(v___x_4882_, 5);
lean_dec(v_unused_4903_);
v___x_4892_ = v___x_4882_;
v_isShared_4893_ = v_isSharedCheck_4902_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_snapshotTasks_4890_);
lean_inc(v_infoState_4889_);
lean_inc(v_messages_4888_);
lean_inc(v_traceState_4887_);
lean_inc(v_auxDeclNGen_4886_);
lean_inc(v_ngen_4885_);
lean_inc(v_nextMacroScope_4884_);
lean_inc(v_env_4883_);
lean_dec(v___x_4882_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4902_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4897_; 
lean_inc(v_head_4880_);
v___x_4894_ = l_Lean_markMeta(v_env_4883_, v_head_4880_);
v___x_4895_ = lean_obj_once(&l_Lean_snapshotEnvLinterOptions___closed__2, &l_Lean_snapshotEnvLinterOptions___closed__2_once, _init_l_Lean_snapshotEnvLinterOptions___closed__2);
if (v_isShared_4893_ == 0)
{
lean_ctor_set(v___x_4892_, 5, v___x_4895_);
lean_ctor_set(v___x_4892_, 0, v___x_4894_);
v___x_4897_ = v___x_4892_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4894_);
lean_ctor_set(v_reuseFailAlloc_4901_, 1, v_nextMacroScope_4884_);
lean_ctor_set(v_reuseFailAlloc_4901_, 2, v_ngen_4885_);
lean_ctor_set(v_reuseFailAlloc_4901_, 3, v_auxDeclNGen_4886_);
lean_ctor_set(v_reuseFailAlloc_4901_, 4, v_traceState_4887_);
lean_ctor_set(v_reuseFailAlloc_4901_, 5, v___x_4895_);
lean_ctor_set(v_reuseFailAlloc_4901_, 6, v_messages_4888_);
lean_ctor_set(v_reuseFailAlloc_4901_, 7, v_infoState_4889_);
lean_ctor_set(v_reuseFailAlloc_4901_, 8, v_snapshotTasks_4890_);
v___x_4897_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
lean_object* v___x_4898_; lean_object* v___x_4899_; 
v___x_4898_ = lean_st_ref_set(v___y_4877_, v___x_4897_);
v___x_4899_ = lean_box(0);
v_as_x27_4875_ = v_tail_4881_;
v_b_4876_ = v___x_4899_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg___boxed(lean_object* v_as_x27_4904_, lean_object* v_b_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4904_, v_b_4905_, v___y_4906_);
lean_dec(v___y_4906_);
lean_dec(v_as_x27_4904_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile(lean_object* v_decl_4909_, uint8_t v_logCompileErrors_4910_, uint8_t v_markMeta_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_){
_start:
{
uint8_t v___x_4915_; lean_object* v___x_4916_; 
v___x_4915_ = 0;
lean_inc(v_decl_4909_);
v___x_4916_ = l_Lean_addDecl(v_decl_4909_, v___x_4915_, v_a_4912_, v_a_4913_);
if (lean_obj_tag(v___x_4916_) == 0)
{
lean_dec_ref_known(v___x_4916_, 1);
if (v_markMeta_4911_ == 0)
{
lean_object* v___x_4917_; 
v___x_4917_ = l_Lean_compileDecl(v_decl_4909_, v_logCompileErrors_4910_, v_a_4912_, v_a_4913_);
return v___x_4917_;
}
else
{
lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; 
lean_inc(v_decl_4909_);
v___x_4918_ = l_Lean_Declaration_getNames(v_decl_4909_);
v___x_4919_ = lean_box(0);
v___x_4920_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v___x_4918_, v___x_4919_, v_a_4913_);
lean_dec(v___x_4918_);
lean_dec_ref(v___x_4920_);
v___x_4921_ = l_Lean_compileDecl(v_decl_4909_, v_logCompileErrors_4910_, v_a_4912_, v_a_4913_);
return v___x_4921_;
}
}
else
{
lean_dec(v_decl_4909_);
return v___x_4916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addAndCompile___boxed(lean_object* v_decl_4922_, lean_object* v_logCompileErrors_4923_, lean_object* v_markMeta_4924_, lean_object* v_a_4925_, lean_object* v_a_4926_, lean_object* v_a_4927_){
_start:
{
uint8_t v_logCompileErrors_boxed_4928_; uint8_t v_markMeta_boxed_4929_; lean_object* v_res_4930_; 
v_logCompileErrors_boxed_4928_ = lean_unbox(v_logCompileErrors_4923_);
v_markMeta_boxed_4929_ = lean_unbox(v_markMeta_4924_);
v_res_4930_ = l_Lean_addAndCompile(v_decl_4922_, v_logCompileErrors_boxed_4928_, v_markMeta_boxed_4929_, v_a_4925_, v_a_4926_);
lean_dec(v_a_4926_);
lean_dec_ref(v_a_4925_);
return v_res_4930_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(lean_object* v_as_4931_, lean_object* v_as_x27_4932_, lean_object* v_b_4933_, lean_object* v_a_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
lean_object* v___x_4938_; 
v___x_4938_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___redArg(v_as_x27_4932_, v_b_4933_, v___y_4936_);
return v___x_4938_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0___boxed(lean_object* v_as_4939_, lean_object* v_as_x27_4940_, lean_object* v_b_4941_, lean_object* v_a_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_, lean_object* v___y_4945_){
_start:
{
lean_object* v_res_4946_; 
v_res_4946_ = l_List_forIn_x27_loop___at___00Lean_addAndCompile_spec__0(v_as_4939_, v_as_x27_4940_, v_b_4941_, v_a_4942_, v___y_4943_, v___y_4944_);
lean_dec(v___y_4944_);
lean_dec_ref(v___y_4943_);
lean_dec(v_as_x27_4940_);
lean_dec(v_as_4939_);
return v_res_4946_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sorry(uint8_t builtin);
lean_object* runtime_initialize_Lean_Util_CollectAxioms(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
lean_object* runtime_initialize_Lean_AutoDecl(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_MetaAttr(uint8_t builtin);
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
