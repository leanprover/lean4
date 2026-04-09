// Lean compiler output
// Module: Lean.Meta.WrapInstance
// Imports: public import Lean.Meta.Closure public import Lean.Meta.SynthInstance public import Lean.Meta.CtorRecognizer
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_compileDecls(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_DeclNameGenerator_mkUniqueName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxDefinition(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_markMeta(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Meta_setInlineAttribute(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_trySynthInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAuxTheorem(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_io_get_num_heartbeats();
lean_object* l_Lean_PersistentArray_toArray___redArg(lean_object*);
extern lean_object* l_Lean_trace_profiler;
lean_object* l_Lean_TraceResult_toEmoji(uint8_t);
lean_object* l_Lean_PersistentArray_append___redArg(lean_object*, lean_object*);
double lean_float_sub(double, double);
uint8_t lean_float_decLt(double, double);
extern lean_object* l_Lean_trace_profiler_useHeartbeats;
extern lean_object* l_Lean_trace_profiler_threshold;
double lean_float_div(double, double);
lean_object* lean_io_mono_nanos_now();
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isInstImplicit(uint8_t);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_extract___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "backward"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "inferInstanceAs"};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "wrap"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 77, .m_capacity = 77, .m_length = 76, .m_data = "wrap instance bodies in `inferInstanceAs` and the default `deriving` handler"};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_object* l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "reuseSubInstances"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(10, 196, 243, 125, 230, 240, 101, 207)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 169, .m_capacity = 169, .m_length = 168, .m_data = "when recursing into sub-instances, reuse existing instances for the target type instead of re-wrapping them, which can be important to avoid non-defeq instance diamonds"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(155, 247, 150, 241, 101, 127, 32, 183)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "instances"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(154, 83, 182, 188, 30, 204, 110, 119)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 73, .m_capacity = 73, .m_length = 72, .m_data = "wrap non-reducible instances in auxiliary definitions to fix their types"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(43, 217, 132, 111, 195, 190, 14, 255)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
static const lean_string_object l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "data"};
static const lean_object* l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(77, 196, 98, 49, 58, 220, 29, 220)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(6, 203, 50, 196, 213, 242, 67, 10)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(208, 252, 45, 86, 202, 182, 131, 2)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(170, 208, 243, 158, 154, 215, 49, 58)}};
static const lean_object* l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "wrap data fields in auxiliary definitions to fix their types"};
static const lean_object* l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(32, 38, 242, 87, 165, 12, 140, 145)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(191, 243, 171, 62, 165, 244, 129, 95)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_4 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(221, 185, 124, 149, 229, 249, 47, 175)}};
static const lean_ctor_object l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value_aux_4),((lean_object*)&l_Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(59, 4, 237, 30, 122, 190, 35, 247)}};
static const lean_object* l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_backward_inferInstanceAs_wrap_data;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "wrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(119, 191, 244, 235, 250, 100, 130, 195)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "WrapInstance"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 173, 45, 246, 47, 55, 243, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(185, 135, 228, 210, 15, 68, 162, 204)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(28, 3, 219, 249, 198, 148, 9, 129)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(224, 244, 76, 43, 236, 107, 113, 110)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(173, 218, 192, 96, 244, 90, 226, 106)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 37, 133, 70, 202, 123, 99, 119)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(201, 48, 88, 11, 50, 139, 104, 61)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(89, 200, 58, 34, 117, 240, 39, 228)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(83, 33, 3, 130, 142, 149, 29, 62)}};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static const lean_string_object l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_abstractInstImplicitArgs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_abstractInstImplicitArgs___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "type: "};
static const lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_wrapInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1;
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__2_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(lean_object*);
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23___boxed(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__0 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__0_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1;
static const lean_string_object l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "<exception thrown while producing trace node message>"};
static const lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__2 = (const lean_object*)&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__2_value;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3;
static lean_once_cell_t l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static double l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_wrapInstance___closed__0;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_aux"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__0 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__0_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__0_value),LEAN_SCALAR_PTR_LITERAL(239, 43, 245, 0, 252, 151, 26, 151)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1_value;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__2 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__2_value;
static const lean_ctor_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__3 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__3_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 70, .m_capacity = 70, .m_length = 69, .m_data = "did not reduce to constructor application, returning/wrapping as is: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__5 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__5_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "using existing instance "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "proof field "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__2 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__2_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " does not have expected type "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__4 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__4_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " but "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__6 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__6_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7;
static const lean_string_object l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = ", wrapping in auxiliary theorem: "};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__8 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__8_value;
static lean_once_cell_t l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "wrapInstance: incorrect number of arguments for constructor application `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__7 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__7_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "`: "};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__9 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__9_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "wrapInstance: `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__11 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__11_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12;
static const lean_string_object l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 42, .m_capacity = 42, .m_length = 41, .m_data = "` does not unify with the conclusion of `"};
static const lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__13 = (const lean_object*)&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__13_value;
static lean_once_cell_t l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14;
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_Meta_wrapInstance___closed__1;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_wrapInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "class is "};
static const lean_object* l_Lean_Meta_wrapInstance___closed__2 = (const lean_object*)&l_Lean_Meta_wrapInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_wrapInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_wrapInstance___closed__3;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object**);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___boxed(lean_object**);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_82_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_83_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_84_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_85_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_82_, v___x_83_, v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4____boxed(lean_object* v_a_86_){
_start:
{
lean_object* v_res_87_; 
v_res_87_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_();
return v_res_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_108_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_109_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_110_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_111_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_108_, v___x_109_, v___x_110_);
return v___x_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4____boxed(lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_();
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_134_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_135_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_137_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_134_, v___x_135_, v___x_136_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4____boxed(lean_object* v_a_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_();
return v_res_139_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v___x_184_ = lean_unsigned_to_nat(3246864463u);
v___x_185_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_186_ = l_Lean_Name_num___override(v___x_185_, v___x_184_);
return v___x_186_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_188_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_189_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_190_ = l_Lean_Name_str___override(v___x_189_, v___x_188_);
return v___x_190_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_192_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_193_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_194_ = l_Lean_Name_str___override(v___x_193_, v___x_192_);
return v___x_194_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v___x_197_; 
v___x_195_ = lean_unsigned_to_nat(2u);
v___x_196_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_197_ = l_Lean_Name_num___override(v___x_196_, v___x_195_);
return v___x_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_199_; uint8_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_199_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_200_ = 0;
v___x_201_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_202_ = l_Lean_registerTraceClass(v___x_199_, v___x_200_, v___x_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object* v_a_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(lean_object* v_e_205_, lean_object* v___y_206_){
_start:
{
uint8_t v___x_208_; 
v___x_208_ = l_Lean_Expr_hasMVar(v_e_205_);
if (v___x_208_ == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_209_, 0, v_e_205_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; lean_object* v_mctx_211_; lean_object* v___x_212_; lean_object* v_fst_213_; lean_object* v_snd_214_; lean_object* v___x_215_; lean_object* v_cache_216_; lean_object* v_zetaDeltaFVarIds_217_; lean_object* v_postponed_218_; lean_object* v_diag_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_228_; 
v___x_210_ = lean_st_ref_get(v___y_206_);
v_mctx_211_ = lean_ctor_get(v___x_210_, 0);
lean_inc_ref(v_mctx_211_);
lean_dec(v___x_210_);
v___x_212_ = l_Lean_instantiateMVarsCore(v_mctx_211_, v_e_205_);
v_fst_213_ = lean_ctor_get(v___x_212_, 0);
lean_inc(v_fst_213_);
v_snd_214_ = lean_ctor_get(v___x_212_, 1);
lean_inc(v_snd_214_);
lean_dec_ref(v___x_212_);
v___x_215_ = lean_st_ref_take(v___y_206_);
v_cache_216_ = lean_ctor_get(v___x_215_, 1);
v_zetaDeltaFVarIds_217_ = lean_ctor_get(v___x_215_, 2);
v_postponed_218_ = lean_ctor_get(v___x_215_, 3);
v_diag_219_ = lean_ctor_get(v___x_215_, 4);
v_isSharedCheck_228_ = !lean_is_exclusive(v___x_215_);
if (v_isSharedCheck_228_ == 0)
{
lean_object* v_unused_229_; 
v_unused_229_ = lean_ctor_get(v___x_215_, 0);
lean_dec(v_unused_229_);
v___x_221_ = v___x_215_;
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_diag_219_);
lean_inc(v_postponed_218_);
lean_inc(v_zetaDeltaFVarIds_217_);
lean_inc(v_cache_216_);
lean_dec(v___x_215_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_228_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_224_; 
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v_snd_214_);
v___x_224_ = v___x_221_;
goto v_reusejp_223_;
}
else
{
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_snd_214_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_cache_216_);
lean_ctor_set(v_reuseFailAlloc_227_, 2, v_zetaDeltaFVarIds_217_);
lean_ctor_set(v_reuseFailAlloc_227_, 3, v_postponed_218_);
lean_ctor_set(v_reuseFailAlloc_227_, 4, v_diag_219_);
v___x_224_ = v_reuseFailAlloc_227_;
goto v_reusejp_223_;
}
v_reusejp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; 
v___x_225_ = lean_st_ref_set(v___y_206_, v___x_224_);
v___x_226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_226_, 0, v_fst_213_);
return v___x_226_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg___boxed(lean_object* v_e_230_, lean_object* v___y_231_, lean_object* v___y_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_230_, v___y_231_);
lean_dec(v___y_231_);
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(lean_object* v_e_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___x_240_; 
v___x_240_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_234_, v___y_236_);
return v___x_240_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___boxed(lean_object* v_e_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_){
_start:
{
lean_object* v_res_247_; 
v_res_247_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(v_e_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
lean_dec(v___y_245_);
lean_dec_ref(v___y_244_);
lean_dec(v___y_243_);
lean_dec_ref(v___y_242_);
return v_res_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_){
_start:
{
lean_object* v_ks_252_; lean_object* v_vs_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_277_; 
v_ks_252_ = lean_ctor_get(v_x_248_, 0);
v_vs_253_ = lean_ctor_get(v_x_248_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_x_248_);
if (v_isSharedCheck_277_ == 0)
{
v___x_255_ = v_x_248_;
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_vs_253_);
lean_inc(v_ks_252_);
lean_dec(v_x_248_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_277_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; uint8_t v___x_258_; 
v___x_257_ = lean_array_get_size(v_ks_252_);
v___x_258_ = lean_nat_dec_lt(v_x_249_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
lean_dec(v_x_249_);
v___x_259_ = lean_array_push(v_ks_252_, v_x_250_);
v___x_260_ = lean_array_push(v_vs_253_, v_x_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_260_);
lean_ctor_set(v___x_255_, 0, v___x_259_);
v___x_262_ = v___x_255_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
else
{
lean_object* v_k_x27_264_; uint8_t v___x_265_; 
v_k_x27_264_ = lean_array_fget_borrowed(v_ks_252_, v_x_249_);
v___x_265_ = l_Lean_instBEqMVarId_beq(v_x_250_, v_k_x27_264_);
if (v___x_265_ == 0)
{
lean_object* v___x_267_; 
if (v_isShared_256_ == 0)
{
v___x_267_ = v___x_255_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v_ks_252_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_vs_253_);
v___x_267_ = v_reuseFailAlloc_271_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_add(v_x_249_, v___x_268_);
lean_dec(v_x_249_);
v_x_248_ = v___x_267_;
v_x_249_ = v___x_269_;
goto _start;
}
}
else
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_275_; 
v___x_272_ = lean_array_fset(v_ks_252_, v_x_249_, v_x_250_);
v___x_273_ = lean_array_fset(v_vs_253_, v_x_249_, v_x_251_);
lean_dec(v_x_249_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_273_);
lean_ctor_set(v___x_255_, 0, v___x_272_);
v___x_275_ = v___x_255_;
goto v_reusejp_274_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_273_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_278_, lean_object* v_k_279_, lean_object* v_v_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_278_, v___x_281_, v_k_279_, v_v_280_);
return v___x_282_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_283_; size_t v___x_284_; size_t v___x_285_; 
v___x_283_ = ((size_t)5ULL);
v___x_284_ = ((size_t)1ULL);
v___x_285_ = lean_usize_shift_left(v___x_284_, v___x_283_);
return v___x_285_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_286_; size_t v___x_287_; size_t v___x_288_; 
v___x_286_ = ((size_t)1ULL);
v___x_287_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_288_ = lean_usize_sub(v___x_287_, v___x_286_);
return v___x_288_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(lean_object* v_x_290_, size_t v_x_291_, size_t v_x_292_, lean_object* v_x_293_, lean_object* v_x_294_){
_start:
{
if (lean_obj_tag(v_x_290_) == 0)
{
lean_object* v_es_295_; size_t v___x_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; lean_object* v_j_300_; lean_object* v___x_301_; uint8_t v___x_302_; 
v_es_295_ = lean_ctor_get(v_x_290_, 0);
v___x_296_ = ((size_t)5ULL);
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_299_ = lean_usize_land(v_x_291_, v___x_298_);
v_j_300_ = lean_usize_to_nat(v___x_299_);
v___x_301_ = lean_array_get_size(v_es_295_);
v___x_302_ = lean_nat_dec_lt(v_j_300_, v___x_301_);
if (v___x_302_ == 0)
{
lean_dec(v_j_300_);
lean_dec(v_x_294_);
lean_dec(v_x_293_);
return v_x_290_;
}
else
{
lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_339_; 
lean_inc_ref(v_es_295_);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_339_ == 0)
{
lean_object* v_unused_340_; 
v_unused_340_ = lean_ctor_get(v_x_290_, 0);
lean_dec(v_unused_340_);
v___x_304_ = v_x_290_;
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
else
{
lean_dec(v_x_290_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_339_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v_v_306_; lean_object* v___x_307_; lean_object* v_xs_x27_308_; lean_object* v___y_310_; 
v_v_306_ = lean_array_fget(v_es_295_, v_j_300_);
v___x_307_ = lean_box(0);
v_xs_x27_308_ = lean_array_fset(v_es_295_, v_j_300_, v___x_307_);
switch(lean_obj_tag(v_v_306_))
{
case 0:
{
lean_object* v_key_315_; lean_object* v_val_316_; lean_object* v___x_318_; uint8_t v_isShared_319_; uint8_t v_isSharedCheck_326_; 
v_key_315_ = lean_ctor_get(v_v_306_, 0);
v_val_316_ = lean_ctor_get(v_v_306_, 1);
v_isSharedCheck_326_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_326_ == 0)
{
v___x_318_ = v_v_306_;
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
else
{
lean_inc(v_val_316_);
lean_inc(v_key_315_);
lean_dec(v_v_306_);
v___x_318_ = lean_box(0);
v_isShared_319_ = v_isSharedCheck_326_;
goto v_resetjp_317_;
}
v_resetjp_317_:
{
uint8_t v___x_320_; 
v___x_320_ = l_Lean_instBEqMVarId_beq(v_x_293_, v_key_315_);
if (v___x_320_ == 0)
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_del_object(v___x_318_);
v___x_321_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_315_, v_val_316_, v_x_293_, v_x_294_);
v___x_322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
v___y_310_ = v___x_322_;
goto v___jp_309_;
}
else
{
lean_object* v___x_324_; 
lean_dec(v_val_316_);
lean_dec(v_key_315_);
if (v_isShared_319_ == 0)
{
lean_ctor_set(v___x_318_, 1, v_x_294_);
lean_ctor_set(v___x_318_, 0, v_x_293_);
v___x_324_ = v___x_318_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_x_293_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_x_294_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
v___y_310_ = v___x_324_;
goto v___jp_309_;
}
}
}
}
case 1:
{
lean_object* v_node_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_337_; 
v_node_327_ = lean_ctor_get(v_v_306_, 0);
v_isSharedCheck_337_ = !lean_is_exclusive(v_v_306_);
if (v_isSharedCheck_337_ == 0)
{
v___x_329_ = v_v_306_;
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_node_327_);
lean_dec(v_v_306_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
size_t v___x_331_; size_t v___x_332_; lean_object* v___x_333_; lean_object* v___x_335_; 
v___x_331_ = lean_usize_shift_right(v_x_291_, v___x_296_);
v___x_332_ = lean_usize_add(v_x_292_, v___x_297_);
v___x_333_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_node_327_, v___x_331_, v___x_332_, v_x_293_, v_x_294_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 0, v___x_333_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v___x_333_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v___y_310_ = v___x_335_;
goto v___jp_309_;
}
}
}
default: 
{
lean_object* v___x_338_; 
v___x_338_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_338_, 0, v_x_293_);
lean_ctor_set(v___x_338_, 1, v_x_294_);
v___y_310_ = v___x_338_;
goto v___jp_309_;
}
}
v___jp_309_:
{
lean_object* v___x_311_; lean_object* v___x_313_; 
v___x_311_ = lean_array_fset(v_xs_x27_308_, v_j_300_, v___y_310_);
lean_dec(v_j_300_);
if (v_isShared_305_ == 0)
{
lean_ctor_set(v___x_304_, 0, v___x_311_);
v___x_313_ = v___x_304_;
goto v_reusejp_312_;
}
else
{
lean_object* v_reuseFailAlloc_314_; 
v_reuseFailAlloc_314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_314_, 0, v___x_311_);
v___x_313_ = v_reuseFailAlloc_314_;
goto v_reusejp_312_;
}
v_reusejp_312_:
{
return v___x_313_;
}
}
}
}
}
else
{
lean_object* v_ks_341_; lean_object* v_vs_342_; lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_362_; 
v_ks_341_ = lean_ctor_get(v_x_290_, 0);
v_vs_342_ = lean_ctor_get(v_x_290_, 1);
v_isSharedCheck_362_ = !lean_is_exclusive(v_x_290_);
if (v_isSharedCheck_362_ == 0)
{
v___x_344_ = v_x_290_;
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
else
{
lean_inc(v_vs_342_);
lean_inc(v_ks_341_);
lean_dec(v_x_290_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_362_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v___x_347_; 
if (v_isShared_345_ == 0)
{
v___x_347_ = v___x_344_;
goto v_reusejp_346_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v_ks_341_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v_vs_342_);
v___x_347_ = v_reuseFailAlloc_361_;
goto v_reusejp_346_;
}
v_reusejp_346_:
{
lean_object* v_newNode_348_; uint8_t v___y_350_; size_t v___x_356_; uint8_t v___x_357_; 
v_newNode_348_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v___x_347_, v_x_293_, v_x_294_);
v___x_356_ = ((size_t)7ULL);
v___x_357_ = lean_usize_dec_le(v___x_356_, v_x_292_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_358_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_348_);
v___x_359_ = lean_unsigned_to_nat(4u);
v___x_360_ = lean_nat_dec_lt(v___x_358_, v___x_359_);
lean_dec(v___x_358_);
v___y_350_ = v___x_360_;
goto v___jp_349_;
}
else
{
v___y_350_ = v___x_357_;
goto v___jp_349_;
}
v___jp_349_:
{
if (v___y_350_ == 0)
{
lean_object* v_ks_351_; lean_object* v_vs_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; 
v_ks_351_ = lean_ctor_get(v_newNode_348_, 0);
lean_inc_ref(v_ks_351_);
v_vs_352_ = lean_ctor_get(v_newNode_348_, 1);
lean_inc_ref(v_vs_352_);
lean_dec_ref(v_newNode_348_);
v___x_353_ = lean_unsigned_to_nat(0u);
v___x_354_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_355_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_x_292_, v_ks_351_, v_vs_352_, v___x_353_, v___x_354_);
lean_dec_ref(v_vs_352_);
lean_dec_ref(v_ks_351_);
return v___x_355_;
}
else
{
return v_newNode_348_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_363_, lean_object* v_keys_364_, lean_object* v_vals_365_, lean_object* v_i_366_, lean_object* v_entries_367_){
_start:
{
lean_object* v___x_368_; uint8_t v___x_369_; 
v___x_368_ = lean_array_get_size(v_keys_364_);
v___x_369_ = lean_nat_dec_lt(v_i_366_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_i_366_);
return v_entries_367_;
}
else
{
lean_object* v_k_370_; lean_object* v_v_371_; uint64_t v___x_372_; size_t v_h_373_; size_t v___x_374_; lean_object* v___x_375_; size_t v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v_h_379_; lean_object* v___x_380_; lean_object* v___x_381_; 
v_k_370_ = lean_array_fget_borrowed(v_keys_364_, v_i_366_);
v_v_371_ = lean_array_fget_borrowed(v_vals_365_, v_i_366_);
v___x_372_ = l_Lean_instHashableMVarId_hash(v_k_370_);
v_h_373_ = lean_uint64_to_usize(v___x_372_);
v___x_374_ = ((size_t)5ULL);
v___x_375_ = lean_unsigned_to_nat(1u);
v___x_376_ = ((size_t)1ULL);
v___x_377_ = lean_usize_sub(v_depth_363_, v___x_376_);
v___x_378_ = lean_usize_mul(v___x_374_, v___x_377_);
v_h_379_ = lean_usize_shift_right(v_h_373_, v___x_378_);
v___x_380_ = lean_nat_add(v_i_366_, v___x_375_);
lean_dec(v_i_366_);
lean_inc(v_v_371_);
lean_inc(v_k_370_);
v___x_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_entries_367_, v_h_379_, v_depth_363_, v_k_370_, v_v_371_);
v_i_366_ = v___x_380_;
v_entries_367_ = v___x_381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_383_, lean_object* v_keys_384_, lean_object* v_vals_385_, lean_object* v_i_386_, lean_object* v_entries_387_){
_start:
{
size_t v_depth_boxed_388_; lean_object* v_res_389_; 
v_depth_boxed_388_ = lean_unbox_usize(v_depth_383_);
lean_dec(v_depth_383_);
v_res_389_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_388_, v_keys_384_, v_vals_385_, v_i_386_, v_entries_387_);
lean_dec_ref(v_vals_385_);
lean_dec_ref(v_keys_384_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_390_, lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
size_t v_x_2193__boxed_395_; size_t v_x_2194__boxed_396_; lean_object* v_res_397_; 
v_x_2193__boxed_395_ = lean_unbox_usize(v_x_391_);
lean_dec(v_x_391_);
v_x_2194__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_res_397_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_390_, v_x_2193__boxed_395_, v_x_2194__boxed_396_, v_x_393_, v_x_394_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(lean_object* v_x_398_, lean_object* v_x_399_, lean_object* v_x_400_){
_start:
{
uint64_t v___x_401_; size_t v___x_402_; size_t v___x_403_; lean_object* v___x_404_; 
v___x_401_ = l_Lean_instHashableMVarId_hash(v_x_399_);
v___x_402_ = lean_uint64_to_usize(v___x_401_);
v___x_403_ = ((size_t)1ULL);
v___x_404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_398_, v___x_402_, v___x_403_, v_x_399_, v_x_400_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(lean_object* v_mvarId_405_, lean_object* v_val_406_, lean_object* v___y_407_){
_start:
{
lean_object* v___x_409_; lean_object* v_mctx_410_; lean_object* v_cache_411_; lean_object* v_zetaDeltaFVarIds_412_; lean_object* v_postponed_413_; lean_object* v_diag_414_; lean_object* v___x_416_; uint8_t v_isShared_417_; uint8_t v_isSharedCheck_442_; 
v___x_409_ = lean_st_ref_take(v___y_407_);
v_mctx_410_ = lean_ctor_get(v___x_409_, 0);
v_cache_411_ = lean_ctor_get(v___x_409_, 1);
v_zetaDeltaFVarIds_412_ = lean_ctor_get(v___x_409_, 2);
v_postponed_413_ = lean_ctor_get(v___x_409_, 3);
v_diag_414_ = lean_ctor_get(v___x_409_, 4);
v_isSharedCheck_442_ = !lean_is_exclusive(v___x_409_);
if (v_isSharedCheck_442_ == 0)
{
v___x_416_ = v___x_409_;
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
else
{
lean_inc(v_diag_414_);
lean_inc(v_postponed_413_);
lean_inc(v_zetaDeltaFVarIds_412_);
lean_inc(v_cache_411_);
lean_inc(v_mctx_410_);
lean_dec(v___x_409_);
v___x_416_ = lean_box(0);
v_isShared_417_ = v_isSharedCheck_442_;
goto v_resetjp_415_;
}
v_resetjp_415_:
{
lean_object* v_depth_418_; lean_object* v_levelAssignDepth_419_; lean_object* v_lmvarCounter_420_; lean_object* v_mvarCounter_421_; lean_object* v_lDecls_422_; lean_object* v_decls_423_; lean_object* v_userNames_424_; lean_object* v_lAssignment_425_; lean_object* v_eAssignment_426_; lean_object* v_dAssignment_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_441_; 
v_depth_418_ = lean_ctor_get(v_mctx_410_, 0);
v_levelAssignDepth_419_ = lean_ctor_get(v_mctx_410_, 1);
v_lmvarCounter_420_ = lean_ctor_get(v_mctx_410_, 2);
v_mvarCounter_421_ = lean_ctor_get(v_mctx_410_, 3);
v_lDecls_422_ = lean_ctor_get(v_mctx_410_, 4);
v_decls_423_ = lean_ctor_get(v_mctx_410_, 5);
v_userNames_424_ = lean_ctor_get(v_mctx_410_, 6);
v_lAssignment_425_ = lean_ctor_get(v_mctx_410_, 7);
v_eAssignment_426_ = lean_ctor_get(v_mctx_410_, 8);
v_dAssignment_427_ = lean_ctor_get(v_mctx_410_, 9);
v_isSharedCheck_441_ = !lean_is_exclusive(v_mctx_410_);
if (v_isSharedCheck_441_ == 0)
{
v___x_429_ = v_mctx_410_;
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_dAssignment_427_);
lean_inc(v_eAssignment_426_);
lean_inc(v_lAssignment_425_);
lean_inc(v_userNames_424_);
lean_inc(v_decls_423_);
lean_inc(v_lDecls_422_);
lean_inc(v_mvarCounter_421_);
lean_inc(v_lmvarCounter_420_);
lean_inc(v_levelAssignDepth_419_);
lean_inc(v_depth_418_);
lean_dec(v_mctx_410_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_441_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_431_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_eAssignment_426_, v_mvarId_405_, v_val_406_);
if (v_isShared_430_ == 0)
{
lean_ctor_set(v___x_429_, 8, v___x_431_);
v___x_433_ = v___x_429_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_depth_418_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_levelAssignDepth_419_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_lmvarCounter_420_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_mvarCounter_421_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_lDecls_422_);
lean_ctor_set(v_reuseFailAlloc_440_, 5, v_decls_423_);
lean_ctor_set(v_reuseFailAlloc_440_, 6, v_userNames_424_);
lean_ctor_set(v_reuseFailAlloc_440_, 7, v_lAssignment_425_);
lean_ctor_set(v_reuseFailAlloc_440_, 8, v___x_431_);
lean_ctor_set(v_reuseFailAlloc_440_, 9, v_dAssignment_427_);
v___x_433_ = v_reuseFailAlloc_440_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
lean_object* v___x_435_; 
if (v_isShared_417_ == 0)
{
lean_ctor_set(v___x_416_, 0, v___x_433_);
v___x_435_ = v___x_416_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_439_; 
v_reuseFailAlloc_439_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_439_, 0, v___x_433_);
lean_ctor_set(v_reuseFailAlloc_439_, 1, v_cache_411_);
lean_ctor_set(v_reuseFailAlloc_439_, 2, v_zetaDeltaFVarIds_412_);
lean_ctor_set(v_reuseFailAlloc_439_, 3, v_postponed_413_);
lean_ctor_set(v_reuseFailAlloc_439_, 4, v_diag_414_);
v___x_435_ = v_reuseFailAlloc_439_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_436_ = lean_st_ref_set(v___y_407_, v___x_435_);
v___x_437_ = lean_box(0);
v___x_438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
return v___x_438_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg___boxed(lean_object* v_mvarId_443_, lean_object* v_val_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_443_, v_val_444_, v___y_445_);
lean_dec(v___y_445_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(lean_object* v_fst_448_, lean_object* v_fst_449_, lean_object* v_args_450_, lean_object* v_range_451_, lean_object* v_b_452_, lean_object* v_i_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_stop_459_; lean_object* v_step_460_; uint8_t v___x_461_; 
v_stop_459_ = lean_ctor_get(v_range_451_, 1);
v_step_460_ = lean_ctor_get(v_range_451_, 2);
v___x_461_ = lean_nat_dec_lt(v_i_453_, v_stop_459_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; 
lean_dec(v_i_453_);
v___x_462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_462_, 0, v_b_452_);
return v___x_462_;
}
else
{
uint8_t v___x_463_; lean_object* v___x_464_; lean_object* v___x_468_; lean_object* v___x_469_; uint8_t v___x_470_; uint8_t v___x_471_; 
v___x_463_ = 0;
v___x_464_ = lean_box(0);
v___x_468_ = lean_box(v___x_463_);
v___x_469_ = lean_array_get(v___x_468_, v_fst_448_, v_i_453_);
lean_dec(v___x_468_);
v___x_470_ = lean_unbox(v___x_469_);
lean_dec(v___x_469_);
v___x_471_ = l_Lean_BinderInfo_isInstImplicit(v___x_470_);
if (v___x_471_ == 0)
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_472_ = l_Lean_instInhabitedExpr;
v___x_473_ = lean_array_get_borrowed(v___x_472_, v_fst_449_, v_i_453_);
v___x_474_ = l_Lean_Expr_mvarId_x21(v___x_473_);
v___x_475_ = lean_array_get_borrowed(v___x_472_, v_args_450_, v_i_453_);
lean_inc(v___x_475_);
v___x_476_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_474_, v___x_475_, v___y_455_);
lean_dec_ref(v___x_476_);
goto v___jp_465_;
}
else
{
goto v___jp_465_;
}
v___jp_465_:
{
lean_object* v___x_466_; 
v___x_466_ = lean_nat_add(v_i_453_, v_step_460_);
lean_dec(v_i_453_);
v_b_452_ = v___x_464_;
v_i_453_ = v___x_466_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg___boxed(lean_object* v_fst_477_, lean_object* v_fst_478_, lean_object* v_args_479_, lean_object* v_range_480_, lean_object* v_b_481_, lean_object* v_i_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_477_, v_fst_478_, v_args_479_, v_range_480_, v_b_481_, v_i_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
lean_dec(v___y_486_);
lean_dec_ref(v___y_485_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec_ref(v_range_480_);
lean_dec_ref(v_args_479_);
lean_dec_ref(v_fst_478_);
lean_dec_ref(v_fst_477_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0(void){
_start:
{
lean_object* v___x_489_; lean_object* v_dummy_490_; 
v___x_489_ = lean_box(0);
v_dummy_490_ = l_Lean_Expr_sort___override(v___x_489_);
return v_dummy_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs(lean_object* v_type_491_, lean_object* v_a_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_){
_start:
{
lean_object* v_fn_497_; lean_object* v___x_498_; 
v_fn_497_ = l_Lean_Expr_getAppFn(v_type_491_);
lean_inc(v_a_495_);
lean_inc_ref(v_a_494_);
lean_inc(v_a_493_);
lean_inc_ref(v_a_492_);
lean_inc_ref(v_fn_497_);
v___x_498_ = lean_infer_type(v_fn_497_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_498_) == 0)
{
lean_object* v_a_499_; uint8_t v___x_500_; lean_object* v___x_501_; 
v_a_499_ = lean_ctor_get(v___x_498_, 0);
lean_inc(v_a_499_);
lean_dec_ref(v___x_498_);
v___x_500_ = 0;
v___x_501_ = l_Lean_Meta_forallMetaTelescope(v_a_499_, v___x_500_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v_snd_503_; lean_object* v_fst_504_; lean_object* v_fst_505_; lean_object* v_nargs_506_; lean_object* v_dummy_507_; lean_object* v___x_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v_args_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref(v___x_501_);
v_snd_503_ = lean_ctor_get(v_a_502_, 1);
lean_inc(v_snd_503_);
v_fst_504_ = lean_ctor_get(v_a_502_, 0);
lean_inc(v_fst_504_);
lean_dec(v_a_502_);
v_fst_505_ = lean_ctor_get(v_snd_503_, 0);
lean_inc(v_fst_505_);
lean_dec(v_snd_503_);
v_nargs_506_ = l_Lean_Expr_getAppNumArgs(v_type_491_);
v_dummy_507_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
lean_inc(v_nargs_506_);
v___x_508_ = lean_mk_array(v_nargs_506_, v_dummy_507_);
v___x_509_ = lean_unsigned_to_nat(1u);
v___x_510_ = lean_nat_sub(v_nargs_506_, v___x_509_);
lean_dec(v_nargs_506_);
v_args_511_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_491_, v___x_508_, v___x_510_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = lean_array_get_size(v_fst_504_);
v___x_514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_514_, 0, v___x_512_);
lean_ctor_set(v___x_514_, 1, v___x_513_);
lean_ctor_set(v___x_514_, 2, v___x_509_);
v___x_515_ = lean_box(0);
v___x_516_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_505_, v_fst_504_, v_args_511_, v___x_514_, v___x_515_, v___x_512_, v_a_492_, v_a_493_, v_a_494_, v_a_495_);
lean_dec_ref(v___x_514_);
lean_dec(v_fst_505_);
lean_dec_ref(v___x_516_);
v___x_517_ = lean_array_get_size(v_args_511_);
v___x_518_ = l_Array_extract___redArg(v_args_511_, v___x_513_, v___x_517_);
lean_dec_ref(v_args_511_);
v___x_519_ = l_Array_append___redArg(v_fst_504_, v___x_518_);
lean_dec_ref(v___x_518_);
v___x_520_ = l_Lean_mkAppN(v_fn_497_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v___x_520_, v_a_493_);
return v___x_521_;
}
else
{
lean_object* v_a_522_; lean_object* v___x_524_; uint8_t v_isShared_525_; uint8_t v_isSharedCheck_529_; 
lean_dec_ref(v_fn_497_);
lean_dec_ref(v_type_491_);
v_a_522_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_529_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_529_ == 0)
{
v___x_524_ = v___x_501_;
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
else
{
lean_inc(v_a_522_);
lean_dec(v___x_501_);
v___x_524_ = lean_box(0);
v_isShared_525_ = v_isSharedCheck_529_;
goto v_resetjp_523_;
}
v_resetjp_523_:
{
lean_object* v___x_527_; 
if (v_isShared_525_ == 0)
{
v___x_527_ = v___x_524_;
goto v_reusejp_526_;
}
else
{
lean_object* v_reuseFailAlloc_528_; 
v_reuseFailAlloc_528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_528_, 0, v_a_522_);
v___x_527_ = v_reuseFailAlloc_528_;
goto v_reusejp_526_;
}
v_reusejp_526_:
{
return v___x_527_;
}
}
}
}
else
{
lean_dec_ref(v_fn_497_);
lean_dec_ref(v_type_491_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs___boxed(lean_object* v_type_530_, lean_object* v_a_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l_Lean_Meta_abstractInstImplicitArgs(v_type_530_, v_a_531_, v_a_532_, v_a_533_, v_a_534_);
lean_dec(v_a_534_);
lean_dec_ref(v_a_533_);
lean_dec(v_a_532_);
lean_dec_ref(v_a_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(lean_object* v_mvarId_537_, lean_object* v_val_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_){
_start:
{
lean_object* v___x_544_; 
v___x_544_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_537_, v_val_538_, v___y_540_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___boxed(lean_object* v_mvarId_545_, lean_object* v_val_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(v_mvarId_545_, v_val_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(lean_object* v_fst_553_, lean_object* v_fst_554_, lean_object* v_args_555_, lean_object* v_range_556_, lean_object* v_b_557_, lean_object* v_i_558_, lean_object* v_hs_559_, lean_object* v_hl_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_553_, v_fst_554_, v_args_555_, v_range_556_, v_b_557_, v_i_558_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___boxed(lean_object* v_fst_567_, lean_object* v_fst_568_, lean_object* v_args_569_, lean_object* v_range_570_, lean_object* v_b_571_, lean_object* v_i_572_, lean_object* v_hs_573_, lean_object* v_hl_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_){
_start:
{
lean_object* v_res_580_; 
v_res_580_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(v_fst_567_, v_fst_568_, v_args_569_, v_range_570_, v_b_571_, v_i_572_, v_hs_573_, v_hl_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_);
lean_dec(v___y_578_);
lean_dec_ref(v___y_577_);
lean_dec(v___y_576_);
lean_dec_ref(v___y_575_);
lean_dec_ref(v_range_570_);
lean_dec_ref(v_args_569_);
lean_dec_ref(v_fst_568_);
lean_dec_ref(v_fst_567_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0(lean_object* v_00_u03b2_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_){
_start:
{
lean_object* v___x_585_; 
v___x_585_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_x_582_, v_x_583_, v_x_584_);
return v___x_585_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_586_, lean_object* v_x_587_, size_t v_x_588_, size_t v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_587_, v_x_588_, v_x_589_, v_x_590_, v_x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_593_, lean_object* v_x_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
size_t v_x_2584__boxed_599_; size_t v_x_2585__boxed_600_; lean_object* v_res_601_; 
v_x_2584__boxed_599_ = lean_unbox_usize(v_x_595_);
lean_dec(v_x_595_);
v_x_2585__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_res_601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(v_00_u03b2_593_, v_x_594_, v_x_2584__boxed_599_, v_x_2585__boxed_600_, v_x_597_, v_x_598_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_602_, lean_object* v_n_603_, lean_object* v_k_604_, lean_object* v_v_605_){
_start:
{
lean_object* v___x_606_; 
v___x_606_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v_n_603_, v_k_604_, v_v_605_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_607_, size_t v_depth_608_, lean_object* v_keys_609_, lean_object* v_vals_610_, lean_object* v_heq_611_, lean_object* v_i_612_, lean_object* v_entries_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_608_, v_keys_609_, v_vals_610_, v_i_612_, v_entries_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_615_, lean_object* v_depth_616_, lean_object* v_keys_617_, lean_object* v_vals_618_, lean_object* v_heq_619_, lean_object* v_i_620_, lean_object* v_entries_621_){
_start:
{
size_t v_depth_boxed_622_; lean_object* v_res_623_; 
v_depth_boxed_622_ = lean_unbox_usize(v_depth_616_);
lean_dec(v_depth_616_);
v_res_623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_615_, v_depth_boxed_622_, v_keys_617_, v_vals_618_, v_heq_619_, v_i_620_, v_entries_621_);
lean_dec_ref(v_vals_618_);
lean_dec_ref(v_keys_617_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_624_, lean_object* v_x_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_){
_start:
{
lean_object* v___x_629_; 
v___x_629_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_625_, v_x_626_, v_x_627_, v_x_628_);
return v___x_629_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object* v_opts_630_, lean_object* v_opt_631_){
_start:
{
lean_object* v_name_632_; lean_object* v_defValue_633_; lean_object* v_map_634_; lean_object* v___x_635_; 
v_name_632_ = lean_ctor_get(v_opt_631_, 0);
v_defValue_633_ = lean_ctor_get(v_opt_631_, 1);
v_map_634_ = lean_ctor_get(v_opts_630_, 0);
v___x_635_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_634_, v_name_632_);
if (lean_obj_tag(v___x_635_) == 0)
{
uint8_t v___x_636_; 
v___x_636_ = lean_unbox(v_defValue_633_);
return v___x_636_;
}
else
{
lean_object* v_val_637_; 
v_val_637_ = lean_ctor_get(v___x_635_, 0);
lean_inc(v_val_637_);
lean_dec_ref(v___x_635_);
if (lean_obj_tag(v_val_637_) == 1)
{
uint8_t v_v_638_; 
v_v_638_ = lean_ctor_get_uint8(v_val_637_, 0);
lean_dec_ref(v_val_637_);
return v_v_638_;
}
else
{
uint8_t v___x_639_; 
lean_dec(v_val_637_);
v___x_639_ = lean_unbox(v_defValue_633_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object* v_opts_640_, lean_object* v_opt_641_){
_start:
{
uint8_t v_res_642_; lean_object* v_r_643_; 
v_res_642_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_640_, v_opt_641_);
lean_dec_ref(v_opt_641_);
lean_dec_ref(v_opts_640_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object* v_kind_644_, lean_object* v___y_645_){
_start:
{
lean_object* v___x_647_; lean_object* v_auxDeclNGen_648_; lean_object* v___x_649_; lean_object* v_env_650_; lean_object* v___x_651_; lean_object* v_fst_652_; lean_object* v_snd_653_; lean_object* v___x_654_; lean_object* v_env_655_; lean_object* v_nextMacroScope_656_; lean_object* v_ngen_657_; lean_object* v_traceState_658_; lean_object* v_cache_659_; lean_object* v_messages_660_; lean_object* v_infoState_661_; lean_object* v_snapshotTasks_662_; lean_object* v___x_664_; uint8_t v_isShared_665_; uint8_t v_isSharedCheck_671_; 
v___x_647_ = lean_st_ref_get(v___y_645_);
v_auxDeclNGen_648_ = lean_ctor_get(v___x_647_, 3);
lean_inc_ref(v_auxDeclNGen_648_);
lean_dec(v___x_647_);
v___x_649_ = lean_st_ref_get(v___y_645_);
v_env_650_ = lean_ctor_get(v___x_649_, 0);
lean_inc_ref(v_env_650_);
lean_dec(v___x_649_);
v___x_651_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_650_, v_auxDeclNGen_648_, v_kind_644_);
v_fst_652_ = lean_ctor_get(v___x_651_, 0);
lean_inc(v_fst_652_);
v_snd_653_ = lean_ctor_get(v___x_651_, 1);
lean_inc(v_snd_653_);
lean_dec_ref(v___x_651_);
v___x_654_ = lean_st_ref_take(v___y_645_);
v_env_655_ = lean_ctor_get(v___x_654_, 0);
v_nextMacroScope_656_ = lean_ctor_get(v___x_654_, 1);
v_ngen_657_ = lean_ctor_get(v___x_654_, 2);
v_traceState_658_ = lean_ctor_get(v___x_654_, 4);
v_cache_659_ = lean_ctor_get(v___x_654_, 5);
v_messages_660_ = lean_ctor_get(v___x_654_, 6);
v_infoState_661_ = lean_ctor_get(v___x_654_, 7);
v_snapshotTasks_662_ = lean_ctor_get(v___x_654_, 8);
v_isSharedCheck_671_ = !lean_is_exclusive(v___x_654_);
if (v_isSharedCheck_671_ == 0)
{
lean_object* v_unused_672_; 
v_unused_672_ = lean_ctor_get(v___x_654_, 3);
lean_dec(v_unused_672_);
v___x_664_ = v___x_654_;
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
else
{
lean_inc(v_snapshotTasks_662_);
lean_inc(v_infoState_661_);
lean_inc(v_messages_660_);
lean_inc(v_cache_659_);
lean_inc(v_traceState_658_);
lean_inc(v_ngen_657_);
lean_inc(v_nextMacroScope_656_);
lean_inc(v_env_655_);
lean_dec(v___x_654_);
v___x_664_ = lean_box(0);
v_isShared_665_ = v_isSharedCheck_671_;
goto v_resetjp_663_;
}
v_resetjp_663_:
{
lean_object* v___x_667_; 
if (v_isShared_665_ == 0)
{
lean_ctor_set(v___x_664_, 3, v_snd_653_);
v___x_667_ = v___x_664_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_670_; 
v_reuseFailAlloc_670_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_670_, 0, v_env_655_);
lean_ctor_set(v_reuseFailAlloc_670_, 1, v_nextMacroScope_656_);
lean_ctor_set(v_reuseFailAlloc_670_, 2, v_ngen_657_);
lean_ctor_set(v_reuseFailAlloc_670_, 3, v_snd_653_);
lean_ctor_set(v_reuseFailAlloc_670_, 4, v_traceState_658_);
lean_ctor_set(v_reuseFailAlloc_670_, 5, v_cache_659_);
lean_ctor_set(v_reuseFailAlloc_670_, 6, v_messages_660_);
lean_ctor_set(v_reuseFailAlloc_670_, 7, v_infoState_661_);
lean_ctor_set(v_reuseFailAlloc_670_, 8, v_snapshotTasks_662_);
v___x_667_ = v_reuseFailAlloc_670_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = lean_st_ref_set(v___y_645_, v___x_667_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v_fst_652_);
return v___x_669_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object* v_kind_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object* v_kind_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_677_, v___y_681_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object* v_kind_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(v_kind_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
return v_res_690_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_691_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v___x_694_);
return v___x_695_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_697_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_697_, 0, v___x_696_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_ctor_set(v___x_697_, 2, v___x_696_);
lean_ctor_set(v___x_697_, 3, v___x_696_);
lean_ctor_set(v___x_697_, 4, v___x_696_);
lean_ctor_set(v___x_697_, 5, v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object* v_declName_698_, uint8_t v_s_699_, lean_object* v___y_700_, lean_object* v___y_701_){
_start:
{
lean_object* v___x_703_; lean_object* v_env_704_; lean_object* v_nextMacroScope_705_; lean_object* v_ngen_706_; lean_object* v_auxDeclNGen_707_; lean_object* v_traceState_708_; lean_object* v_messages_709_; lean_object* v_infoState_710_; lean_object* v_snapshotTasks_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_740_; 
v___x_703_ = lean_st_ref_take(v___y_701_);
v_env_704_ = lean_ctor_get(v___x_703_, 0);
v_nextMacroScope_705_ = lean_ctor_get(v___x_703_, 1);
v_ngen_706_ = lean_ctor_get(v___x_703_, 2);
v_auxDeclNGen_707_ = lean_ctor_get(v___x_703_, 3);
v_traceState_708_ = lean_ctor_get(v___x_703_, 4);
v_messages_709_ = lean_ctor_get(v___x_703_, 6);
v_infoState_710_ = lean_ctor_get(v___x_703_, 7);
v_snapshotTasks_711_ = lean_ctor_get(v___x_703_, 8);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_703_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v___x_703_, 5);
lean_dec(v_unused_741_);
v___x_713_ = v___x_703_;
v_isShared_714_ = v_isSharedCheck_740_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_snapshotTasks_711_);
lean_inc(v_infoState_710_);
lean_inc(v_messages_709_);
lean_inc(v_traceState_708_);
lean_inc(v_auxDeclNGen_707_);
lean_inc(v_ngen_706_);
lean_inc(v_nextMacroScope_705_);
lean_inc(v_env_704_);
lean_dec(v___x_703_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_740_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
uint8_t v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_715_ = 0;
v___x_716_ = lean_box(0);
v___x_717_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_704_, v_declName_698_, v_s_699_, v___x_715_, v___x_716_);
v___x_718_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 5, v___x_718_);
lean_ctor_set(v___x_713_, 0, v___x_717_);
v___x_720_ = v___x_713_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v_nextMacroScope_705_);
lean_ctor_set(v_reuseFailAlloc_739_, 2, v_ngen_706_);
lean_ctor_set(v_reuseFailAlloc_739_, 3, v_auxDeclNGen_707_);
lean_ctor_set(v_reuseFailAlloc_739_, 4, v_traceState_708_);
lean_ctor_set(v_reuseFailAlloc_739_, 5, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_739_, 6, v_messages_709_);
lean_ctor_set(v_reuseFailAlloc_739_, 7, v_infoState_710_);
lean_ctor_set(v_reuseFailAlloc_739_, 8, v_snapshotTasks_711_);
v___x_720_ = v_reuseFailAlloc_739_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v_mctx_723_; lean_object* v_zetaDeltaFVarIds_724_; lean_object* v_postponed_725_; lean_object* v_diag_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_737_; 
v___x_721_ = lean_st_ref_set(v___y_701_, v___x_720_);
v___x_722_ = lean_st_ref_take(v___y_700_);
v_mctx_723_ = lean_ctor_get(v___x_722_, 0);
v_zetaDeltaFVarIds_724_ = lean_ctor_get(v___x_722_, 2);
v_postponed_725_ = lean_ctor_get(v___x_722_, 3);
v_diag_726_ = lean_ctor_get(v___x_722_, 4);
v_isSharedCheck_737_ = !lean_is_exclusive(v___x_722_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v___x_722_, 1);
lean_dec(v_unused_738_);
v___x_728_ = v___x_722_;
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_diag_726_);
lean_inc(v_postponed_725_);
lean_inc(v_zetaDeltaFVarIds_724_);
lean_inc(v_mctx_723_);
lean_dec(v___x_722_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_737_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_730_; lean_object* v___x_732_; 
v___x_730_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_729_ == 0)
{
lean_ctor_set(v___x_728_, 1, v___x_730_);
v___x_732_ = v___x_728_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v_mctx_723_);
lean_ctor_set(v_reuseFailAlloc_736_, 1, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_736_, 2, v_zetaDeltaFVarIds_724_);
lean_ctor_set(v_reuseFailAlloc_736_, 3, v_postponed_725_);
lean_ctor_set(v_reuseFailAlloc_736_, 4, v_diag_726_);
v___x_732_ = v_reuseFailAlloc_736_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_733_ = lean_st_ref_set(v___y_700_, v___x_732_);
v___x_734_ = lean_box(0);
v___x_735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_735_, 0, v___x_734_);
return v___x_735_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object* v_declName_742_, lean_object* v_s_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_){
_start:
{
uint8_t v_s_boxed_747_; lean_object* v_res_748_; 
v_s_boxed_747_ = lean_unbox(v_s_743_);
v_res_748_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_742_, v_s_boxed_747_, v___y_744_, v___y_745_);
lean_dec(v___y_745_);
lean_dec(v___y_744_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_declName_749_, uint8_t v_s_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_){
_start:
{
lean_object* v___x_756_; 
v___x_756_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_749_, v_s_750_, v___y_752_, v___y_754_);
return v___x_756_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_declName_757_, lean_object* v_s_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
uint8_t v_s_boxed_764_; lean_object* v_res_765_; 
v_s_boxed_764_ = lean_unbox(v_s_758_);
v_res_765_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(v_declName_757_, v_s_boxed_764_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec_ref(v___y_759_);
return v_res_765_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; 
v___x_766_ = lean_unsigned_to_nat(32u);
v___x_767_ = lean_mk_empty_array_with_capacity(v___x_766_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
return v___x_768_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; 
v___x_769_ = ((size_t)5ULL);
v___x_770_ = lean_unsigned_to_nat(0u);
v___x_771_ = lean_unsigned_to_nat(32u);
v___x_772_ = lean_mk_empty_array_with_capacity(v___x_771_);
v___x_773_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0);
v___x_774_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_774_, 0, v___x_773_);
lean_ctor_set(v___x_774_, 1, v___x_772_);
lean_ctor_set(v___x_774_, 2, v___x_770_);
lean_ctor_set(v___x_774_, 3, v___x_770_);
lean_ctor_set_usize(v___x_774_, 4, v___x_769_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(lean_object* v___y_775_){
_start:
{
lean_object* v___x_777_; lean_object* v_traceState_778_; lean_object* v_traces_779_; lean_object* v___x_780_; lean_object* v_traceState_781_; lean_object* v_env_782_; lean_object* v_nextMacroScope_783_; lean_object* v_ngen_784_; lean_object* v_auxDeclNGen_785_; lean_object* v_cache_786_; lean_object* v_messages_787_; lean_object* v_infoState_788_; lean_object* v_snapshotTasks_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_808_; 
v___x_777_ = lean_st_ref_get(v___y_775_);
v_traceState_778_ = lean_ctor_get(v___x_777_, 4);
lean_inc_ref(v_traceState_778_);
lean_dec(v___x_777_);
v_traces_779_ = lean_ctor_get(v_traceState_778_, 0);
lean_inc_ref(v_traces_779_);
lean_dec_ref(v_traceState_778_);
v___x_780_ = lean_st_ref_take(v___y_775_);
v_traceState_781_ = lean_ctor_get(v___x_780_, 4);
v_env_782_ = lean_ctor_get(v___x_780_, 0);
v_nextMacroScope_783_ = lean_ctor_get(v___x_780_, 1);
v_ngen_784_ = lean_ctor_get(v___x_780_, 2);
v_auxDeclNGen_785_ = lean_ctor_get(v___x_780_, 3);
v_cache_786_ = lean_ctor_get(v___x_780_, 5);
v_messages_787_ = lean_ctor_get(v___x_780_, 6);
v_infoState_788_ = lean_ctor_get(v___x_780_, 7);
v_snapshotTasks_789_ = lean_ctor_get(v___x_780_, 8);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_808_ == 0)
{
v___x_791_ = v___x_780_;
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_snapshotTasks_789_);
lean_inc(v_infoState_788_);
lean_inc(v_messages_787_);
lean_inc(v_cache_786_);
lean_inc(v_traceState_781_);
lean_inc(v_auxDeclNGen_785_);
lean_inc(v_ngen_784_);
lean_inc(v_nextMacroScope_783_);
lean_inc(v_env_782_);
lean_dec(v___x_780_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_808_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
uint64_t v_tid_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_806_; 
v_tid_793_ = lean_ctor_get_uint64(v_traceState_781_, sizeof(void*)*1);
v_isSharedCheck_806_ = !lean_is_exclusive(v_traceState_781_);
if (v_isSharedCheck_806_ == 0)
{
lean_object* v_unused_807_; 
v_unused_807_ = lean_ctor_get(v_traceState_781_, 0);
lean_dec(v_unused_807_);
v___x_795_ = v_traceState_781_;
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
else
{
lean_dec(v_traceState_781_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_806_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_797_; lean_object* v___x_799_; 
v___x_797_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1);
if (v_isShared_796_ == 0)
{
lean_ctor_set(v___x_795_, 0, v___x_797_);
v___x_799_ = v___x_795_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v___x_797_);
lean_ctor_set_uint64(v_reuseFailAlloc_805_, sizeof(void*)*1, v_tid_793_);
v___x_799_ = v_reuseFailAlloc_805_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
lean_object* v___x_801_; 
if (v_isShared_792_ == 0)
{
lean_ctor_set(v___x_791_, 4, v___x_799_);
v___x_801_ = v___x_791_;
goto v_reusejp_800_;
}
else
{
lean_object* v_reuseFailAlloc_804_; 
v_reuseFailAlloc_804_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_804_, 0, v_env_782_);
lean_ctor_set(v_reuseFailAlloc_804_, 1, v_nextMacroScope_783_);
lean_ctor_set(v_reuseFailAlloc_804_, 2, v_ngen_784_);
lean_ctor_set(v_reuseFailAlloc_804_, 3, v_auxDeclNGen_785_);
lean_ctor_set(v_reuseFailAlloc_804_, 4, v___x_799_);
lean_ctor_set(v_reuseFailAlloc_804_, 5, v_cache_786_);
lean_ctor_set(v_reuseFailAlloc_804_, 6, v_messages_787_);
lean_ctor_set(v_reuseFailAlloc_804_, 7, v_infoState_788_);
lean_ctor_set(v_reuseFailAlloc_804_, 8, v_snapshotTasks_789_);
v___x_801_ = v_reuseFailAlloc_804_;
goto v_reusejp_800_;
}
v_reusejp_800_:
{
lean_object* v___x_802_; lean_object* v___x_803_; 
v___x_802_ = lean_st_ref_set(v___y_775_, v___x_801_);
v___x_803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_803_, 0, v_traces_779_);
return v___x_803_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___boxed(lean_object* v___y_809_, lean_object* v___y_810_){
_start:
{
lean_object* v_res_811_; 
v_res_811_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_809_);
lean_dec(v___y_809_);
return v_res_811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
lean_object* v___x_817_; 
v___x_817_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_815_);
return v___x_817_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_){
_start:
{
lean_object* v_res_823_; 
v_res_823_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(v___y_818_, v___y_819_, v___y_820_, v___y_821_);
lean_dec(v___y_821_);
lean_dec_ref(v___y_820_);
lean_dec(v___y_819_);
lean_dec_ref(v___y_818_);
return v_res_823_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_826_ = l_Lean_stringToMessageData(v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_827_, lean_object* v_x_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; 
v___x_834_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_835_ = l_Lean_MessageData_ofExpr(v_expectedType_827_);
v___x_836_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_834_);
lean_ctor_set(v___x_836_, 1, v___x_835_);
v___x_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
return v___x_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_838_, lean_object* v_x_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_){
_start:
{
lean_object* v_res_845_; 
v_res_845_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_838_, v_x_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_x_839_);
return v_res_845_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0);
v___x_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1);
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_851_, 0, v___x_850_);
lean_ctor_set(v___x_851_, 1, v___x_850_);
lean_ctor_set(v___x_851_, 2, v___x_850_);
lean_ctor_set(v___x_851_, 3, v___x_850_);
lean_ctor_set(v___x_851_, 4, v___x_849_);
lean_ctor_set(v___x_851_, 5, v___x_849_);
lean_ctor_set(v___x_851_, 6, v___x_849_);
lean_ctor_set(v___x_851_, 7, v___x_849_);
lean_ctor_set(v___x_851_, 8, v___x_849_);
lean_ctor_set(v___x_851_, 9, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = lean_unsigned_to_nat(32u);
v___x_853_ = lean_mk_empty_array_with_capacity(v___x_852_);
v___x_854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_854_, 0, v___x_853_);
return v___x_854_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_855_ = ((size_t)5ULL);
v___x_856_ = lean_unsigned_to_nat(0u);
v___x_857_ = lean_unsigned_to_nat(32u);
v___x_858_ = lean_mk_empty_array_with_capacity(v___x_857_);
v___x_859_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3);
v___x_860_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v___x_858_);
lean_ctor_set(v___x_860_, 2, v___x_856_);
lean_ctor_set(v___x_860_, 3, v___x_856_);
lean_ctor_set_usize(v___x_860_, 4, v___x_855_);
return v___x_860_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_861_ = lean_box(1);
v___x_862_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4);
v___x_863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1);
v___x_864_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_861_);
return v___x_864_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_866_; lean_object* v___x_867_; 
v___x_866_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__6));
v___x_867_ = l_Lean_stringToMessageData(v___x_866_);
return v___x_867_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_869_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__8));
v___x_870_ = l_Lean_stringToMessageData(v___x_869_);
return v___x_870_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_872_; lean_object* v___x_873_; 
v___x_872_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__10));
v___x_873_ = l_Lean_stringToMessageData(v___x_872_);
return v___x_873_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__12));
v___x_876_ = l_Lean_stringToMessageData(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__14));
v___x_879_ = l_Lean_stringToMessageData(v___x_878_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__16));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__18));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(lean_object* v_msg_886_, lean_object* v_declHint_887_, lean_object* v___y_888_){
_start:
{
lean_object* v___x_890_; lean_object* v_env_891_; uint8_t v___x_892_; 
v___x_890_ = lean_st_ref_get(v___y_888_);
v_env_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc_ref(v_env_891_);
lean_dec(v___x_890_);
v___x_892_ = l_Lean_Name_isAnonymous(v_declHint_887_);
if (v___x_892_ == 0)
{
uint8_t v_isExporting_893_; 
v_isExporting_893_ = lean_ctor_get_uint8(v_env_891_, sizeof(void*)*8);
if (v_isExporting_893_ == 0)
{
lean_object* v___x_894_; 
lean_dec_ref(v_env_891_);
lean_dec(v_declHint_887_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v_msg_886_);
return v___x_894_;
}
else
{
lean_object* v___x_895_; uint8_t v___x_896_; 
lean_inc_ref(v_env_891_);
v___x_895_ = l_Lean_Environment_setExporting(v_env_891_, v___x_892_);
lean_inc(v_declHint_887_);
lean_inc_ref(v___x_895_);
v___x_896_ = l_Lean_Environment_contains(v___x_895_, v_declHint_887_, v_isExporting_893_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; 
lean_dec_ref(v___x_895_);
lean_dec_ref(v_env_891_);
lean_dec(v_declHint_887_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v_msg_886_);
return v___x_897_;
}
else
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v_c_903_; lean_object* v___x_904_; 
v___x_898_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2);
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5);
v___x_900_ = l_Lean_Options_empty;
v___x_901_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_901_, 0, v___x_895_);
lean_ctor_set(v___x_901_, 1, v___x_898_);
lean_ctor_set(v___x_901_, 2, v___x_899_);
lean_ctor_set(v___x_901_, 3, v___x_900_);
lean_inc(v_declHint_887_);
v___x_902_ = l_Lean_MessageData_ofConstName(v_declHint_887_, v___x_892_);
v_c_903_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_903_, 0, v___x_901_);
lean_ctor_set(v_c_903_, 1, v___x_902_);
v___x_904_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_891_, v_declHint_887_);
if (lean_obj_tag(v___x_904_) == 0)
{
lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
lean_dec_ref(v_env_891_);
lean_dec(v_declHint_887_);
v___x_905_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7);
v___x_906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_906_, 0, v___x_905_);
lean_ctor_set(v___x_906_, 1, v_c_903_);
v___x_907_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9);
v___x_908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_908_, 0, v___x_906_);
lean_ctor_set(v___x_908_, 1, v___x_907_);
v___x_909_ = l_Lean_MessageData_note(v___x_908_);
v___x_910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_910_, 0, v_msg_886_);
lean_ctor_set(v___x_910_, 1, v___x_909_);
v___x_911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_911_, 0, v___x_910_);
return v___x_911_;
}
else
{
lean_object* v_val_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_947_; 
v_val_912_ = lean_ctor_get(v___x_904_, 0);
v_isSharedCheck_947_ = !lean_is_exclusive(v___x_904_);
if (v_isSharedCheck_947_ == 0)
{
v___x_914_ = v___x_904_;
v_isShared_915_ = v_isSharedCheck_947_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_val_912_);
lean_dec(v___x_904_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_947_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v_mod_919_; uint8_t v___x_920_; 
v___x_916_ = lean_box(0);
v___x_917_ = l_Lean_Environment_header(v_env_891_);
lean_dec_ref(v_env_891_);
v___x_918_ = l_Lean_EnvironmentHeader_moduleNames(v___x_917_);
v_mod_919_ = lean_array_get(v___x_916_, v___x_918_, v_val_912_);
lean_dec(v_val_912_);
lean_dec_ref(v___x_918_);
v___x_920_ = l_Lean_isPrivateName(v_declHint_887_);
lean_dec(v_declHint_887_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_932_; 
v___x_921_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11);
v___x_922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_922_, 0, v___x_921_);
lean_ctor_set(v___x_922_, 1, v_c_903_);
v___x_923_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13);
v___x_924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_924_, 0, v___x_922_);
lean_ctor_set(v___x_924_, 1, v___x_923_);
v___x_925_ = l_Lean_MessageData_ofName(v_mod_919_);
v___x_926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_926_, 0, v___x_924_);
lean_ctor_set(v___x_926_, 1, v___x_925_);
v___x_927_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15);
v___x_928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_928_, 0, v___x_926_);
lean_ctor_set(v___x_928_, 1, v___x_927_);
v___x_929_ = l_Lean_MessageData_note(v___x_928_);
v___x_930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_930_, 0, v_msg_886_);
lean_ctor_set(v___x_930_, 1, v___x_929_);
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 0);
lean_ctor_set(v___x_914_, 0, v___x_930_);
v___x_932_ = v___x_914_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v___x_930_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
else
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
v___x_934_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7);
v___x_935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
lean_ctor_set(v___x_935_, 1, v_c_903_);
v___x_936_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17);
v___x_937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_937_, 0, v___x_935_);
lean_ctor_set(v___x_937_, 1, v___x_936_);
v___x_938_ = l_Lean_MessageData_ofName(v_mod_919_);
v___x_939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_937_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19);
v___x_941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_941_, 0, v___x_939_);
lean_ctor_set(v___x_941_, 1, v___x_940_);
v___x_942_ = l_Lean_MessageData_note(v___x_941_);
v___x_943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_943_, 0, v_msg_886_);
lean_ctor_set(v___x_943_, 1, v___x_942_);
if (v_isShared_915_ == 0)
{
lean_ctor_set_tag(v___x_914_, 0);
lean_ctor_set(v___x_914_, 0, v___x_943_);
v___x_945_ = v___x_914_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_948_; 
lean_dec_ref(v_env_891_);
lean_dec(v_declHint_887_);
v___x_948_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_948_, 0, v_msg_886_);
return v___x_948_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___boxed(lean_object* v_msg_949_, lean_object* v_declHint_950_, lean_object* v___y_951_, lean_object* v___y_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_949_, v_declHint_950_, v___y_951_);
lean_dec(v___y_951_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(lean_object* v_msg_954_, lean_object* v_declHint_955_, lean_object* v___y_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_971_; 
v___x_961_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_954_, v_declHint_955_, v___y_959_);
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_971_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_971_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_971_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_969_; 
v___x_966_ = l_Lean_unknownIdentifierMessageTag;
v___x_967_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
lean_ctor_set(v___x_967_, 1, v_a_962_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_967_);
v___x_969_ = v___x_964_;
goto v_reusejp_968_;
}
else
{
lean_object* v_reuseFailAlloc_970_; 
v_reuseFailAlloc_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_970_, 0, v___x_967_);
v___x_969_ = v_reuseFailAlloc_970_;
goto v_reusejp_968_;
}
v_reusejp_968_:
{
return v___x_969_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29___boxed(lean_object* v_msg_972_, lean_object* v_declHint_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(v_msg_972_, v_declHint_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(lean_object* v_msgData_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v___x_986_; lean_object* v_env_987_; lean_object* v___x_988_; lean_object* v_mctx_989_; lean_object* v_lctx_990_; lean_object* v_options_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_986_ = lean_st_ref_get(v___y_984_);
v_env_987_ = lean_ctor_get(v___x_986_, 0);
lean_inc_ref(v_env_987_);
lean_dec(v___x_986_);
v___x_988_ = lean_st_ref_get(v___y_982_);
v_mctx_989_ = lean_ctor_get(v___x_988_, 0);
lean_inc_ref(v_mctx_989_);
lean_dec(v___x_988_);
v_lctx_990_ = lean_ctor_get(v___y_981_, 2);
v_options_991_ = lean_ctor_get(v___y_983_, 2);
lean_inc_ref(v_options_991_);
lean_inc_ref(v_lctx_990_);
v___x_992_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_992_, 0, v_env_987_);
lean_ctor_set(v___x_992_, 1, v_mctx_989_);
lean_ctor_set(v___x_992_, 2, v_lctx_990_);
lean_ctor_set(v___x_992_, 3, v_options_991_);
v___x_993_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_993_, 0, v___x_992_);
lean_ctor_set(v___x_993_, 1, v_msgData_980_);
v___x_994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3___boxed(lean_object* v_msgData_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v_res_1001_; 
v_res_1001_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msgData_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
lean_dec(v___y_999_);
lean_dec_ref(v___y_998_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
return v_res_1001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object* v_msg_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
lean_object* v_ref_1008_; lean_object* v___x_1009_; lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1018_; 
v_ref_1008_ = lean_ctor_get(v___y_1005_, 5);
v___x_1009_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1002_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
v_a_1010_ = lean_ctor_get(v___x_1009_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_1009_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1012_ = v___x_1009_;
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1009_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1018_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1014_; lean_object* v___x_1016_; 
lean_inc(v_ref_1008_);
v___x_1014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1014_, 0, v_ref_1008_);
lean_ctor_set(v___x_1014_, 1, v_a_1010_);
if (v_isShared_1013_ == 0)
{
lean_ctor_set_tag(v___x_1012_, 1);
lean_ctor_set(v___x_1012_, 0, v___x_1014_);
v___x_1016_ = v___x_1012_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1014_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object* v_msg_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(lean_object* v_ref_1026_, lean_object* v_msg_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_){
_start:
{
lean_object* v_fileName_1033_; lean_object* v_fileMap_1034_; lean_object* v_options_1035_; lean_object* v_currRecDepth_1036_; lean_object* v_maxRecDepth_1037_; lean_object* v_ref_1038_; lean_object* v_currNamespace_1039_; lean_object* v_openDecls_1040_; lean_object* v_initHeartbeats_1041_; lean_object* v_maxHeartbeats_1042_; lean_object* v_quotContext_1043_; lean_object* v_currMacroScope_1044_; uint8_t v_diag_1045_; lean_object* v_cancelTk_x3f_1046_; uint8_t v_suppressElabErrors_1047_; lean_object* v_inheritedTraceOptions_1048_; lean_object* v_ref_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_fileName_1033_ = lean_ctor_get(v___y_1030_, 0);
v_fileMap_1034_ = lean_ctor_get(v___y_1030_, 1);
v_options_1035_ = lean_ctor_get(v___y_1030_, 2);
v_currRecDepth_1036_ = lean_ctor_get(v___y_1030_, 3);
v_maxRecDepth_1037_ = lean_ctor_get(v___y_1030_, 4);
v_ref_1038_ = lean_ctor_get(v___y_1030_, 5);
v_currNamespace_1039_ = lean_ctor_get(v___y_1030_, 6);
v_openDecls_1040_ = lean_ctor_get(v___y_1030_, 7);
v_initHeartbeats_1041_ = lean_ctor_get(v___y_1030_, 8);
v_maxHeartbeats_1042_ = lean_ctor_get(v___y_1030_, 9);
v_quotContext_1043_ = lean_ctor_get(v___y_1030_, 10);
v_currMacroScope_1044_ = lean_ctor_get(v___y_1030_, 11);
v_diag_1045_ = lean_ctor_get_uint8(v___y_1030_, sizeof(void*)*14);
v_cancelTk_x3f_1046_ = lean_ctor_get(v___y_1030_, 12);
v_suppressElabErrors_1047_ = lean_ctor_get_uint8(v___y_1030_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1048_ = lean_ctor_get(v___y_1030_, 13);
v_ref_1049_ = l_Lean_replaceRef(v_ref_1026_, v_ref_1038_);
lean_inc_ref(v_inheritedTraceOptions_1048_);
lean_inc(v_cancelTk_x3f_1046_);
lean_inc(v_currMacroScope_1044_);
lean_inc(v_quotContext_1043_);
lean_inc(v_maxHeartbeats_1042_);
lean_inc(v_initHeartbeats_1041_);
lean_inc(v_openDecls_1040_);
lean_inc(v_currNamespace_1039_);
lean_inc(v_maxRecDepth_1037_);
lean_inc(v_currRecDepth_1036_);
lean_inc_ref(v_options_1035_);
lean_inc_ref(v_fileMap_1034_);
lean_inc_ref(v_fileName_1033_);
v___x_1050_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1050_, 0, v_fileName_1033_);
lean_ctor_set(v___x_1050_, 1, v_fileMap_1034_);
lean_ctor_set(v___x_1050_, 2, v_options_1035_);
lean_ctor_set(v___x_1050_, 3, v_currRecDepth_1036_);
lean_ctor_set(v___x_1050_, 4, v_maxRecDepth_1037_);
lean_ctor_set(v___x_1050_, 5, v_ref_1049_);
lean_ctor_set(v___x_1050_, 6, v_currNamespace_1039_);
lean_ctor_set(v___x_1050_, 7, v_openDecls_1040_);
lean_ctor_set(v___x_1050_, 8, v_initHeartbeats_1041_);
lean_ctor_set(v___x_1050_, 9, v_maxHeartbeats_1042_);
lean_ctor_set(v___x_1050_, 10, v_quotContext_1043_);
lean_ctor_set(v___x_1050_, 11, v_currMacroScope_1044_);
lean_ctor_set(v___x_1050_, 12, v_cancelTk_x3f_1046_);
lean_ctor_set(v___x_1050_, 13, v_inheritedTraceOptions_1048_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*14, v_diag_1045_);
lean_ctor_set_uint8(v___x_1050_, sizeof(void*)*14 + 1, v_suppressElabErrors_1047_);
v___x_1051_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_1027_, v___y_1028_, v___y_1029_, v___x_1050_, v___y_1031_);
lean_dec_ref(v___x_1050_);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg___boxed(lean_object* v_ref_1052_, lean_object* v_msg_1053_, lean_object* v___y_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_1052_, v_msg_1053_, v___y_1054_, v___y_1055_, v___y_1056_, v___y_1057_);
lean_dec(v___y_1057_);
lean_dec_ref(v___y_1056_);
lean_dec(v___y_1055_);
lean_dec_ref(v___y_1054_);
lean_dec(v_ref_1052_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(lean_object* v_ref_1060_, lean_object* v_msg_1061_, lean_object* v_declHint_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; lean_object* v_a_1069_; lean_object* v___x_1070_; 
v___x_1068_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(v_msg_1061_, v_declHint_1062_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
v_a_1069_ = lean_ctor_get(v___x_1068_, 0);
lean_inc(v_a_1069_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_1060_, v_a_1069_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1071_, lean_object* v_msg_1072_, lean_object* v_declHint_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v_res_1079_; 
v_res_1079_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_1071_, v_msg_1072_, v_declHint_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v_ref_1071_);
return v_res_1079_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__0));
v___x_1082_ = l_Lean_stringToMessageData(v___x_1081_);
return v___x_1082_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
v___x_1084_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__2));
v___x_1085_ = l_Lean_stringToMessageData(v___x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_1086_, lean_object* v_constName_1087_, lean_object* v___y_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
lean_object* v___x_1093_; uint8_t v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1093_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1);
v___x_1094_ = 0;
lean_inc(v_constName_1087_);
v___x_1095_ = l_Lean_MessageData_ofConstName(v_constName_1087_, v___x_1094_);
v___x_1096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1093_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_1098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1098_, 0, v___x_1096_);
lean_ctor_set(v___x_1098_, 1, v___x_1097_);
v___x_1099_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_1086_, v___x_1098_, v_constName_1087_, v___y_1088_, v___y_1089_, v___y_1090_, v___y_1091_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1100_, lean_object* v_constName_1101_, lean_object* v___y_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_){
_start:
{
lean_object* v_res_1107_; 
v_res_1107_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_1100_, v_constName_1101_, v___y_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
lean_dec(v___y_1105_);
lean_dec_ref(v___y_1104_);
lean_dec(v___y_1103_);
lean_dec_ref(v___y_1102_);
lean_dec(v_ref_1100_);
return v_res_1107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(lean_object* v_constName_1108_, lean_object* v___y_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_){
_start:
{
lean_object* v_ref_1114_; lean_object* v___x_1115_; 
v_ref_1114_ = lean_ctor_get(v___y_1111_, 5);
v___x_1115_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_1114_, v_constName_1108_, v___y_1109_, v___y_1110_, v___y_1111_, v___y_1112_);
return v___x_1115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg___boxed(lean_object* v_constName_1116_, lean_object* v___y_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_1116_, v___y_1117_, v___y_1118_, v___y_1119_, v___y_1120_);
lean_dec(v___y_1120_);
lean_dec_ref(v___y_1119_);
lean_dec(v___y_1118_);
lean_dec_ref(v___y_1117_);
return v_res_1122_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_constName_1123_, lean_object* v___y_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_){
_start:
{
lean_object* v___x_1129_; lean_object* v_env_1130_; uint8_t v___x_1131_; lean_object* v___x_1132_; 
v___x_1129_ = lean_st_ref_get(v___y_1127_);
v_env_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc_ref(v_env_1130_);
lean_dec(v___x_1129_);
v___x_1131_ = 0;
lean_inc(v_constName_1123_);
v___x_1132_ = l_Lean_Environment_find_x3f(v_env_1130_, v_constName_1123_, v___x_1131_);
if (lean_obj_tag(v___x_1132_) == 0)
{
lean_object* v___x_1133_; 
v___x_1133_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_1123_, v___y_1124_, v___y_1125_, v___y_1126_, v___y_1127_);
return v___x_1133_;
}
else
{
lean_object* v_val_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1141_; 
lean_dec(v_constName_1123_);
v_val_1134_ = lean_ctor_get(v___x_1132_, 0);
v_isSharedCheck_1141_ = !lean_is_exclusive(v___x_1132_);
if (v_isSharedCheck_1141_ == 0)
{
v___x_1136_ = v___x_1132_;
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_val_1134_);
lean_dec(v___x_1132_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1141_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1139_; 
if (v_isShared_1137_ == 0)
{
lean_ctor_set_tag(v___x_1136_, 0);
v___x_1139_ = v___x_1136_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1140_; 
v_reuseFailAlloc_1140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1140_, 0, v_val_1134_);
v___x_1139_ = v_reuseFailAlloc_1140_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
return v___x_1139_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_constName_1142_, lean_object* v___y_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_){
_start:
{
lean_object* v_res_1148_; 
v_res_1148_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_constName_1142_, v___y_1143_, v___y_1144_, v___y_1145_, v___y_1146_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
lean_dec(v___y_1144_);
lean_dec_ref(v___y_1143_);
return v_res_1148_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1149_; double v___x_1150_; 
v___x_1149_ = lean_unsigned_to_nat(0u);
v___x_1150_ = lean_float_of_nat(v___x_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_cls_1154_, lean_object* v_msg_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_){
_start:
{
lean_object* v_ref_1161_; lean_object* v___x_1162_; lean_object* v_a_1163_; lean_object* v___x_1165_; uint8_t v_isShared_1166_; uint8_t v_isSharedCheck_1207_; 
v_ref_1161_ = lean_ctor_get(v___y_1158_, 5);
v___x_1162_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1155_, v___y_1156_, v___y_1157_, v___y_1158_, v___y_1159_);
v_a_1163_ = lean_ctor_get(v___x_1162_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1162_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1165_ = v___x_1162_;
v_isShared_1166_ = v_isSharedCheck_1207_;
goto v_resetjp_1164_;
}
else
{
lean_inc(v_a_1163_);
lean_dec(v___x_1162_);
v___x_1165_ = lean_box(0);
v_isShared_1166_ = v_isSharedCheck_1207_;
goto v_resetjp_1164_;
}
v_resetjp_1164_:
{
lean_object* v___x_1167_; lean_object* v_traceState_1168_; lean_object* v_env_1169_; lean_object* v_nextMacroScope_1170_; lean_object* v_ngen_1171_; lean_object* v_auxDeclNGen_1172_; lean_object* v_cache_1173_; lean_object* v_messages_1174_; lean_object* v_infoState_1175_; lean_object* v_snapshotTasks_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1206_; 
v___x_1167_ = lean_st_ref_take(v___y_1159_);
v_traceState_1168_ = lean_ctor_get(v___x_1167_, 4);
v_env_1169_ = lean_ctor_get(v___x_1167_, 0);
v_nextMacroScope_1170_ = lean_ctor_get(v___x_1167_, 1);
v_ngen_1171_ = lean_ctor_get(v___x_1167_, 2);
v_auxDeclNGen_1172_ = lean_ctor_get(v___x_1167_, 3);
v_cache_1173_ = lean_ctor_get(v___x_1167_, 5);
v_messages_1174_ = lean_ctor_get(v___x_1167_, 6);
v_infoState_1175_ = lean_ctor_get(v___x_1167_, 7);
v_snapshotTasks_1176_ = lean_ctor_get(v___x_1167_, 8);
v_isSharedCheck_1206_ = !lean_is_exclusive(v___x_1167_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1178_ = v___x_1167_;
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_snapshotTasks_1176_);
lean_inc(v_infoState_1175_);
lean_inc(v_messages_1174_);
lean_inc(v_cache_1173_);
lean_inc(v_traceState_1168_);
lean_inc(v_auxDeclNGen_1172_);
lean_inc(v_ngen_1171_);
lean_inc(v_nextMacroScope_1170_);
lean_inc(v_env_1169_);
lean_dec(v___x_1167_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1206_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
uint64_t v_tid_1180_; lean_object* v_traces_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1205_; 
v_tid_1180_ = lean_ctor_get_uint64(v_traceState_1168_, sizeof(void*)*1);
v_traces_1181_ = lean_ctor_get(v_traceState_1168_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v_traceState_1168_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1183_ = v_traceState_1168_;
v_isShared_1184_ = v_isSharedCheck_1205_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_traces_1181_);
lean_dec(v_traceState_1168_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1205_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1185_; double v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1195_; 
v___x_1185_ = lean_box(0);
v___x_1186_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0);
v___x_1187_ = 0;
v___x_1188_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1));
v___x_1189_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1189_, 0, v_cls_1154_);
lean_ctor_set(v___x_1189_, 1, v___x_1185_);
lean_ctor_set(v___x_1189_, 2, v___x_1188_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3, v___x_1186_);
lean_ctor_set_float(v___x_1189_, sizeof(void*)*3 + 8, v___x_1186_);
lean_ctor_set_uint8(v___x_1189_, sizeof(void*)*3 + 16, v___x_1187_);
v___x_1190_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__2));
v___x_1191_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1191_, 0, v___x_1189_);
lean_ctor_set(v___x_1191_, 1, v_a_1163_);
lean_ctor_set(v___x_1191_, 2, v___x_1190_);
lean_inc(v_ref_1161_);
v___x_1192_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1192_, 0, v_ref_1161_);
lean_ctor_set(v___x_1192_, 1, v___x_1191_);
v___x_1193_ = l_Lean_PersistentArray_push___redArg(v_traces_1181_, v___x_1192_);
if (v_isShared_1184_ == 0)
{
lean_ctor_set(v___x_1183_, 0, v___x_1193_);
v___x_1195_ = v___x_1183_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v___x_1193_);
lean_ctor_set_uint64(v_reuseFailAlloc_1204_, sizeof(void*)*1, v_tid_1180_);
v___x_1195_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1197_; 
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 4, v___x_1195_);
v___x_1197_ = v___x_1178_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v_env_1169_);
lean_ctor_set(v_reuseFailAlloc_1203_, 1, v_nextMacroScope_1170_);
lean_ctor_set(v_reuseFailAlloc_1203_, 2, v_ngen_1171_);
lean_ctor_set(v_reuseFailAlloc_1203_, 3, v_auxDeclNGen_1172_);
lean_ctor_set(v_reuseFailAlloc_1203_, 4, v___x_1195_);
lean_ctor_set(v_reuseFailAlloc_1203_, 5, v_cache_1173_);
lean_ctor_set(v_reuseFailAlloc_1203_, 6, v_messages_1174_);
lean_ctor_set(v_reuseFailAlloc_1203_, 7, v_infoState_1175_);
lean_ctor_set(v_reuseFailAlloc_1203_, 8, v_snapshotTasks_1176_);
v___x_1197_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1201_; 
v___x_1198_ = lean_st_ref_set(v___y_1159_, v___x_1197_);
v___x_1199_ = lean_box(0);
if (v_isShared_1166_ == 0)
{
lean_ctor_set(v___x_1165_, 0, v___x_1199_);
v___x_1201_ = v___x_1165_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v___x_1199_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_cls_1208_, lean_object* v_msg_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_res_1215_; 
v_res_1215_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1208_, v_msg_1209_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(size_t v_sz_1216_, size_t v_i_1217_, lean_object* v_bs_1218_, lean_object* v___y_1219_){
_start:
{
uint8_t v___x_1221_; 
v___x_1221_ = lean_usize_dec_lt(v_i_1217_, v_sz_1216_);
if (v___x_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1222_, 0, v_bs_1218_);
return v___x_1222_;
}
else
{
lean_object* v_v_1223_; lean_object* v___x_1224_; 
v_v_1223_ = lean_array_uget_borrowed(v_bs_1218_, v_i_1217_);
lean_inc(v_v_1223_);
v___x_1224_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_v_1223_, v___y_1219_);
if (lean_obj_tag(v___x_1224_) == 0)
{
lean_object* v_a_1225_; lean_object* v___x_1226_; lean_object* v_bs_x27_1227_; size_t v___x_1228_; size_t v___x_1229_; lean_object* v___x_1230_; 
v_a_1225_ = lean_ctor_get(v___x_1224_, 0);
lean_inc(v_a_1225_);
lean_dec_ref(v___x_1224_);
v___x_1226_ = lean_unsigned_to_nat(0u);
v_bs_x27_1227_ = lean_array_uset(v_bs_1218_, v_i_1217_, v___x_1226_);
v___x_1228_ = ((size_t)1ULL);
v___x_1229_ = lean_usize_add(v_i_1217_, v___x_1228_);
v___x_1230_ = lean_array_uset(v_bs_x27_1227_, v_i_1217_, v_a_1225_);
v_i_1217_ = v___x_1229_;
v_bs_1218_ = v___x_1230_;
goto _start;
}
else
{
lean_object* v_a_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1239_; 
lean_dec_ref(v_bs_1218_);
v_a_1232_ = lean_ctor_get(v___x_1224_, 0);
v_isSharedCheck_1239_ = !lean_is_exclusive(v___x_1224_);
if (v_isSharedCheck_1239_ == 0)
{
v___x_1234_ = v___x_1224_;
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_a_1232_);
lean_dec(v___x_1224_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1239_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v___x_1237_; 
if (v_isShared_1235_ == 0)
{
v___x_1237_ = v___x_1234_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1238_; 
v_reuseFailAlloc_1238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1238_, 0, v_a_1232_);
v___x_1237_ = v_reuseFailAlloc_1238_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
return v___x_1237_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object* v_sz_1240_, lean_object* v_i_1241_, lean_object* v_bs_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
size_t v_sz_boxed_1245_; size_t v_i_boxed_1246_; lean_object* v_res_1247_; 
v_sz_boxed_1245_ = lean_unbox_usize(v_sz_1240_);
lean_dec(v_sz_1240_);
v_i_boxed_1246_ = lean_unbox_usize(v_i_1241_);
lean_dec(v_i_1241_);
v_res_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_boxed_1245_, v_i_boxed_1246_, v_bs_1242_, v___y_1243_);
lean_dec(v___y_1243_);
return v_res_1247_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_a_1248_, lean_object* v_a_1249_){
_start:
{
if (lean_obj_tag(v_a_1248_) == 0)
{
lean_object* v___x_1250_; 
v___x_1250_ = l_List_reverse___redArg(v_a_1249_);
return v___x_1250_;
}
else
{
lean_object* v_head_1251_; lean_object* v_tail_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1261_; 
v_head_1251_ = lean_ctor_get(v_a_1248_, 0);
v_tail_1252_ = lean_ctor_get(v_a_1248_, 1);
v_isSharedCheck_1261_ = !lean_is_exclusive(v_a_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1254_ = v_a_1248_;
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_tail_1252_);
lean_inc(v_head_1251_);
lean_dec(v_a_1248_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1261_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1256_; lean_object* v___x_1258_; 
v___x_1256_ = l_Lean_MessageData_ofExpr(v_head_1251_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v_a_1249_);
lean_ctor_set(v___x_1254_, 0, v___x_1256_);
v___x_1258_ = v___x_1254_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1256_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v_a_1249_);
v___x_1258_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
v_a_1248_ = v_tail_1252_;
v_a_1249_ = v___x_1258_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(lean_object* v___x_1262_, lean_object* v_a_1263_, lean_object* v_____r_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_){
_start:
{
lean_object* v___x_1270_; 
v___x_1270_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1262_, v_a_1263_, v___y_1266_);
if (lean_obj_tag(v___x_1270_) == 0)
{
lean_object* v___x_1272_; uint8_t v_isShared_1273_; uint8_t v_isSharedCheck_1278_; 
v_isSharedCheck_1278_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1278_ == 0)
{
lean_object* v_unused_1279_; 
v_unused_1279_ = lean_ctor_get(v___x_1270_, 0);
lean_dec(v_unused_1279_);
v___x_1272_ = v___x_1270_;
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
else
{
lean_dec(v___x_1270_);
v___x_1272_ = lean_box(0);
v_isShared_1273_ = v_isSharedCheck_1278_;
goto v_resetjp_1271_;
}
v_resetjp_1271_:
{
lean_object* v___x_1274_; lean_object* v___x_1276_; 
v___x_1274_ = lean_box(0);
if (v_isShared_1273_ == 0)
{
lean_ctor_set(v___x_1272_, 0, v___x_1274_);
v___x_1276_ = v___x_1272_;
goto v_reusejp_1275_;
}
else
{
lean_object* v_reuseFailAlloc_1277_; 
v_reuseFailAlloc_1277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1277_, 0, v___x_1274_);
v___x_1276_ = v_reuseFailAlloc_1277_;
goto v_reusejp_1275_;
}
v_reusejp_1275_:
{
return v___x_1276_;
}
}
}
else
{
lean_object* v_a_1280_; lean_object* v___x_1282_; uint8_t v_isShared_1283_; uint8_t v_isSharedCheck_1287_; 
v_a_1280_ = lean_ctor_get(v___x_1270_, 0);
v_isSharedCheck_1287_ = !lean_is_exclusive(v___x_1270_);
if (v_isSharedCheck_1287_ == 0)
{
v___x_1282_ = v___x_1270_;
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
else
{
lean_inc(v_a_1280_);
lean_dec(v___x_1270_);
v___x_1282_ = lean_box(0);
v_isShared_1283_ = v_isSharedCheck_1287_;
goto v_resetjp_1281_;
}
v_resetjp_1281_:
{
lean_object* v___x_1285_; 
if (v_isShared_1283_ == 0)
{
v___x_1285_ = v___x_1282_;
goto v_reusejp_1284_;
}
else
{
lean_object* v_reuseFailAlloc_1286_; 
v_reuseFailAlloc_1286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1286_, 0, v_a_1280_);
v___x_1285_ = v_reuseFailAlloc_1286_;
goto v_reusejp_1284_;
}
v_reusejp_1284_:
{
return v___x_1285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed(lean_object* v___x_1288_, lean_object* v_a_1289_, lean_object* v_____r_1290_, lean_object* v___y_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1288_, v_a_1289_, v_____r_1290_, v___y_1291_, v___y_1292_, v___y_1293_, v___y_1294_);
lean_dec(v___y_1294_);
lean_dec_ref(v___y_1293_);
lean_dec(v___y_1292_);
lean_dec_ref(v___y_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(lean_object* v_a_1297_, lean_object* v___x_1298_, uint8_t v_compile_1299_, uint8_t v_logCompileErrors_1300_, lean_object* v_____r_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
if (v_compile_1299_ == 0)
{
goto v___jp_1307_;
}
else
{
lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; 
v___x_1326_ = lean_unsigned_to_nat(1u);
v___x_1327_ = lean_mk_empty_array_with_capacity(v___x_1326_);
lean_inc(v_a_1297_);
v___x_1328_ = lean_array_push(v___x_1327_, v_a_1297_);
v___x_1329_ = l_Lean_compileDecls(v___x_1328_, v_logCompileErrors_1300_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_dec_ref(v___x_1329_);
goto v___jp_1307_;
}
else
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
lean_dec(v_a_1297_);
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
}
v___jp_1307_:
{
lean_object* v___x_1308_; 
v___x_1308_ = l_Lean_enableRealizationsForConst(v_a_1297_, v___y_1304_, v___y_1305_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1316_; 
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1316_ == 0)
{
lean_object* v_unused_1317_; 
v_unused_1317_ = lean_ctor_get(v___x_1308_, 0);
lean_dec(v_unused_1317_);
v___x_1310_ = v___x_1308_;
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
else
{
lean_dec(v___x_1308_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1316_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1312_; lean_object* v___x_1314_; 
v___x_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1312_, 0, v___x_1298_);
if (v_isShared_1311_ == 0)
{
lean_ctor_set(v___x_1310_, 0, v___x_1312_);
v___x_1314_ = v___x_1310_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1312_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
v_a_1318_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1308_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1308_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed(lean_object* v_a_1338_, lean_object* v___x_1339_, lean_object* v_compile_1340_, lean_object* v_logCompileErrors_1341_, lean_object* v_____r_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_){
_start:
{
uint8_t v_compile_boxed_1348_; uint8_t v_logCompileErrors_boxed_1349_; lean_object* v_res_1350_; 
v_compile_boxed_1348_ = lean_unbox(v_compile_1340_);
v_logCompileErrors_boxed_1349_ = lean_unbox(v_logCompileErrors_1341_);
v_res_1350_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1338_, v___x_1339_, v_compile_boxed_1348_, v_logCompileErrors_boxed_1349_, v_____r_1342_, v___y_1343_, v___y_1344_, v___y_1345_, v___y_1346_);
lean_dec(v___y_1346_);
lean_dec_ref(v___y_1345_);
lean_dec(v___y_1344_);
lean_dec_ref(v___y_1343_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(lean_object* v_a_1351_, lean_object* v___x_1352_, uint8_t v___x_1353_, lean_object* v___x_1354_, lean_object* v___x_1355_, lean_object* v_____r_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_){
_start:
{
lean_object* v___x_1362_; lean_object* v___x_1363_; 
v___x_1362_ = lean_box(0);
v___x_1363_ = l_Lean_Meta_mkAuxTheorem(v_a_1351_, v___x_1352_, v___x_1353_, v___x_1362_, v___x_1353_, v___y_1357_, v___y_1358_, v___y_1359_, v___y_1360_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_object* v_a_1364_; lean_object* v___x_1365_; 
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
lean_inc(v_a_1364_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1354_, v_a_1364_, v___y_1358_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1373_; 
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1373_ == 0)
{
lean_object* v_unused_1374_; 
v_unused_1374_ = lean_ctor_get(v___x_1365_, 0);
lean_dec(v_unused_1374_);
v___x_1367_ = v___x_1365_;
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
else
{
lean_dec(v___x_1365_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1373_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1369_; lean_object* v___x_1371_; 
v___x_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1355_);
if (v_isShared_1368_ == 0)
{
lean_ctor_set(v___x_1367_, 0, v___x_1369_);
v___x_1371_ = v___x_1367_;
goto v_reusejp_1370_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1369_);
v___x_1371_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1370_;
}
v_reusejp_1370_:
{
return v___x_1371_;
}
}
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1365_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1365_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
lean_dec(v___x_1354_);
v_a_1383_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1363_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1363_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3___boxed(lean_object* v_a_1391_, lean_object* v___x_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v_____r_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_){
_start:
{
uint8_t v___x_120984__boxed_1402_; lean_object* v_res_1403_; 
v___x_120984__boxed_1402_ = lean_unbox(v___x_1393_);
v_res_1403_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1391_, v___x_1392_, v___x_120984__boxed_1402_, v___x_1394_, v___x_1395_, v_____r_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
lean_dec(v___y_1400_);
lean_dec_ref(v___y_1399_);
lean_dec(v___y_1398_);
lean_dec_ref(v___y_1397_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(size_t v_sz_1404_, size_t v_i_1405_, lean_object* v_bs_1406_){
_start:
{
uint8_t v___x_1407_; 
v___x_1407_ = lean_usize_dec_lt(v_i_1405_, v_sz_1404_);
if (v___x_1407_ == 0)
{
return v_bs_1406_;
}
else
{
lean_object* v_v_1408_; lean_object* v_msg_1409_; lean_object* v___x_1410_; lean_object* v_bs_x27_1411_; size_t v___x_1412_; size_t v___x_1413_; lean_object* v___x_1414_; 
v_v_1408_ = lean_array_uget_borrowed(v_bs_1406_, v_i_1405_);
v_msg_1409_ = lean_ctor_get(v_v_1408_, 1);
lean_inc_ref(v_msg_1409_);
v___x_1410_ = lean_unsigned_to_nat(0u);
v_bs_x27_1411_ = lean_array_uset(v_bs_1406_, v_i_1405_, v___x_1410_);
v___x_1412_ = ((size_t)1ULL);
v___x_1413_ = lean_usize_add(v_i_1405_, v___x_1412_);
v___x_1414_ = lean_array_uset(v_bs_x27_1411_, v_i_1405_, v_msg_1409_);
v_i_1405_ = v___x_1413_;
v_bs_1406_ = v___x_1414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26___boxed(lean_object* v_sz_1416_, lean_object* v_i_1417_, lean_object* v_bs_1418_){
_start:
{
size_t v_sz_boxed_1419_; size_t v_i_boxed_1420_; lean_object* v_res_1421_; 
v_sz_boxed_1419_ = lean_unbox_usize(v_sz_1416_);
lean_dec(v_sz_1416_);
v_i_boxed_1420_ = lean_unbox_usize(v_i_1417_);
lean_dec(v_i_1417_);
v_res_1421_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(v_sz_boxed_1419_, v_i_boxed_1420_, v_bs_1418_);
return v_res_1421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(lean_object* v_oldTraces_1422_, lean_object* v_data_1423_, lean_object* v_ref_1424_, lean_object* v_msg_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_fileName_1431_; lean_object* v_fileMap_1432_; lean_object* v_options_1433_; lean_object* v_currRecDepth_1434_; lean_object* v_maxRecDepth_1435_; lean_object* v_ref_1436_; lean_object* v_currNamespace_1437_; lean_object* v_openDecls_1438_; lean_object* v_initHeartbeats_1439_; lean_object* v_maxHeartbeats_1440_; lean_object* v_quotContext_1441_; lean_object* v_currMacroScope_1442_; uint8_t v_diag_1443_; lean_object* v_cancelTk_x3f_1444_; uint8_t v_suppressElabErrors_1445_; lean_object* v_inheritedTraceOptions_1446_; lean_object* v___x_1447_; lean_object* v_traceState_1448_; lean_object* v_traces_1449_; lean_object* v_ref_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; size_t v_sz_1453_; size_t v___x_1454_; lean_object* v___x_1455_; lean_object* v_msg_1456_; lean_object* v___x_1457_; lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1495_; 
v_fileName_1431_ = lean_ctor_get(v___y_1428_, 0);
v_fileMap_1432_ = lean_ctor_get(v___y_1428_, 1);
v_options_1433_ = lean_ctor_get(v___y_1428_, 2);
v_currRecDepth_1434_ = lean_ctor_get(v___y_1428_, 3);
v_maxRecDepth_1435_ = lean_ctor_get(v___y_1428_, 4);
v_ref_1436_ = lean_ctor_get(v___y_1428_, 5);
v_currNamespace_1437_ = lean_ctor_get(v___y_1428_, 6);
v_openDecls_1438_ = lean_ctor_get(v___y_1428_, 7);
v_initHeartbeats_1439_ = lean_ctor_get(v___y_1428_, 8);
v_maxHeartbeats_1440_ = lean_ctor_get(v___y_1428_, 9);
v_quotContext_1441_ = lean_ctor_get(v___y_1428_, 10);
v_currMacroScope_1442_ = lean_ctor_get(v___y_1428_, 11);
v_diag_1443_ = lean_ctor_get_uint8(v___y_1428_, sizeof(void*)*14);
v_cancelTk_x3f_1444_ = lean_ctor_get(v___y_1428_, 12);
v_suppressElabErrors_1445_ = lean_ctor_get_uint8(v___y_1428_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1446_ = lean_ctor_get(v___y_1428_, 13);
v___x_1447_ = lean_st_ref_get(v___y_1429_);
v_traceState_1448_ = lean_ctor_get(v___x_1447_, 4);
lean_inc_ref(v_traceState_1448_);
lean_dec(v___x_1447_);
v_traces_1449_ = lean_ctor_get(v_traceState_1448_, 0);
lean_inc_ref(v_traces_1449_);
lean_dec_ref(v_traceState_1448_);
v_ref_1450_ = l_Lean_replaceRef(v_ref_1424_, v_ref_1436_);
lean_inc_ref(v_inheritedTraceOptions_1446_);
lean_inc(v_cancelTk_x3f_1444_);
lean_inc(v_currMacroScope_1442_);
lean_inc(v_quotContext_1441_);
lean_inc(v_maxHeartbeats_1440_);
lean_inc(v_initHeartbeats_1439_);
lean_inc(v_openDecls_1438_);
lean_inc(v_currNamespace_1437_);
lean_inc(v_maxRecDepth_1435_);
lean_inc(v_currRecDepth_1434_);
lean_inc_ref(v_options_1433_);
lean_inc_ref(v_fileMap_1432_);
lean_inc_ref(v_fileName_1431_);
v___x_1451_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1451_, 0, v_fileName_1431_);
lean_ctor_set(v___x_1451_, 1, v_fileMap_1432_);
lean_ctor_set(v___x_1451_, 2, v_options_1433_);
lean_ctor_set(v___x_1451_, 3, v_currRecDepth_1434_);
lean_ctor_set(v___x_1451_, 4, v_maxRecDepth_1435_);
lean_ctor_set(v___x_1451_, 5, v_ref_1450_);
lean_ctor_set(v___x_1451_, 6, v_currNamespace_1437_);
lean_ctor_set(v___x_1451_, 7, v_openDecls_1438_);
lean_ctor_set(v___x_1451_, 8, v_initHeartbeats_1439_);
lean_ctor_set(v___x_1451_, 9, v_maxHeartbeats_1440_);
lean_ctor_set(v___x_1451_, 10, v_quotContext_1441_);
lean_ctor_set(v___x_1451_, 11, v_currMacroScope_1442_);
lean_ctor_set(v___x_1451_, 12, v_cancelTk_x3f_1444_);
lean_ctor_set(v___x_1451_, 13, v_inheritedTraceOptions_1446_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*14, v_diag_1443_);
lean_ctor_set_uint8(v___x_1451_, sizeof(void*)*14 + 1, v_suppressElabErrors_1445_);
v___x_1452_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1449_);
lean_dec_ref(v_traces_1449_);
v_sz_1453_ = lean_array_size(v___x_1452_);
v___x_1454_ = ((size_t)0ULL);
v___x_1455_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(v_sz_1453_, v___x_1454_, v___x_1452_);
v_msg_1456_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1456_, 0, v_data_1423_);
lean_ctor_set(v_msg_1456_, 1, v_msg_1425_);
lean_ctor_set(v_msg_1456_, 2, v___x_1455_);
v___x_1457_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1456_, v___y_1426_, v___y_1427_, v___x_1451_, v___y_1429_);
lean_dec_ref(v___x_1451_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1457_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1460_ = v___x_1457_;
v_isShared_1461_ = v_isSharedCheck_1495_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1457_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1495_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1462_; lean_object* v_traceState_1463_; lean_object* v_env_1464_; lean_object* v_nextMacroScope_1465_; lean_object* v_ngen_1466_; lean_object* v_auxDeclNGen_1467_; lean_object* v_cache_1468_; lean_object* v_messages_1469_; lean_object* v_infoState_1470_; lean_object* v_snapshotTasks_1471_; lean_object* v___x_1473_; uint8_t v_isShared_1474_; uint8_t v_isSharedCheck_1494_; 
v___x_1462_ = lean_st_ref_take(v___y_1429_);
v_traceState_1463_ = lean_ctor_get(v___x_1462_, 4);
v_env_1464_ = lean_ctor_get(v___x_1462_, 0);
v_nextMacroScope_1465_ = lean_ctor_get(v___x_1462_, 1);
v_ngen_1466_ = lean_ctor_get(v___x_1462_, 2);
v_auxDeclNGen_1467_ = lean_ctor_get(v___x_1462_, 3);
v_cache_1468_ = lean_ctor_get(v___x_1462_, 5);
v_messages_1469_ = lean_ctor_get(v___x_1462_, 6);
v_infoState_1470_ = lean_ctor_get(v___x_1462_, 7);
v_snapshotTasks_1471_ = lean_ctor_get(v___x_1462_, 8);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1473_ = v___x_1462_;
v_isShared_1474_ = v_isSharedCheck_1494_;
goto v_resetjp_1472_;
}
else
{
lean_inc(v_snapshotTasks_1471_);
lean_inc(v_infoState_1470_);
lean_inc(v_messages_1469_);
lean_inc(v_cache_1468_);
lean_inc(v_traceState_1463_);
lean_inc(v_auxDeclNGen_1467_);
lean_inc(v_ngen_1466_);
lean_inc(v_nextMacroScope_1465_);
lean_inc(v_env_1464_);
lean_dec(v___x_1462_);
v___x_1473_ = lean_box(0);
v_isShared_1474_ = v_isSharedCheck_1494_;
goto v_resetjp_1472_;
}
v_resetjp_1472_:
{
uint64_t v_tid_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1492_; 
v_tid_1475_ = lean_ctor_get_uint64(v_traceState_1463_, sizeof(void*)*1);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_traceState_1463_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; 
v_unused_1493_ = lean_ctor_get(v_traceState_1463_, 0);
lean_dec(v_unused_1493_);
v___x_1477_ = v_traceState_1463_;
v_isShared_1478_ = v_isSharedCheck_1492_;
goto v_resetjp_1476_;
}
else
{
lean_dec(v_traceState_1463_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1492_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v_ref_1424_);
lean_ctor_set(v___x_1479_, 1, v_a_1458_);
v___x_1480_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1422_, v___x_1479_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1480_);
v___x_1482_ = v___x_1477_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1480_);
lean_ctor_set_uint64(v_reuseFailAlloc_1491_, sizeof(void*)*1, v_tid_1475_);
v___x_1482_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1474_ == 0)
{
lean_ctor_set(v___x_1473_, 4, v___x_1482_);
v___x_1484_ = v___x_1473_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_env_1464_);
lean_ctor_set(v_reuseFailAlloc_1490_, 1, v_nextMacroScope_1465_);
lean_ctor_set(v_reuseFailAlloc_1490_, 2, v_ngen_1466_);
lean_ctor_set(v_reuseFailAlloc_1490_, 3, v_auxDeclNGen_1467_);
lean_ctor_set(v_reuseFailAlloc_1490_, 4, v___x_1482_);
lean_ctor_set(v_reuseFailAlloc_1490_, 5, v_cache_1468_);
lean_ctor_set(v_reuseFailAlloc_1490_, 6, v_messages_1469_);
lean_ctor_set(v_reuseFailAlloc_1490_, 7, v_infoState_1470_);
lean_ctor_set(v_reuseFailAlloc_1490_, 8, v_snapshotTasks_1471_);
v___x_1484_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1485_ = lean_st_ref_set(v___y_1429_, v___x_1484_);
v___x_1486_ = lean_box(0);
if (v_isShared_1461_ == 0)
{
lean_ctor_set(v___x_1460_, 0, v___x_1486_);
v___x_1488_ = v___x_1460_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1486_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24___boxed(lean_object* v_oldTraces_1496_, lean_object* v_data_1497_, lean_object* v_ref_1498_, lean_object* v_msg_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_oldTraces_1496_, v_data_1497_, v_ref_1498_, v_msg_1499_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(lean_object* v_opts_1506_, lean_object* v_opt_1507_){
_start:
{
lean_object* v_name_1508_; lean_object* v_defValue_1509_; lean_object* v_map_1510_; lean_object* v___x_1511_; 
v_name_1508_ = lean_ctor_get(v_opt_1507_, 0);
v_defValue_1509_ = lean_ctor_get(v_opt_1507_, 1);
v_map_1510_ = lean_ctor_get(v_opts_1506_, 0);
v___x_1511_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1510_, v_name_1508_);
if (lean_obj_tag(v___x_1511_) == 0)
{
lean_inc(v_defValue_1509_);
return v_defValue_1509_;
}
else
{
lean_object* v_val_1512_; 
v_val_1512_ = lean_ctor_get(v___x_1511_, 0);
lean_inc(v_val_1512_);
lean_dec_ref(v___x_1511_);
if (lean_obj_tag(v_val_1512_) == 3)
{
lean_object* v_v_1513_; 
v_v_1513_ = lean_ctor_get(v_val_1512_, 0);
lean_inc(v_v_1513_);
lean_dec_ref(v_val_1512_);
return v_v_1513_;
}
else
{
lean_dec(v_val_1512_);
lean_inc(v_defValue_1509_);
return v_defValue_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26___boxed(lean_object* v_opts_1514_, lean_object* v_opt_1515_){
_start:
{
lean_object* v_res_1516_; 
v_res_1516_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1514_, v_opt_1515_);
lean_dec_ref(v_opt_1515_);
lean_dec_ref(v_opts_1514_);
return v_res_1516_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(lean_object* v_e_1517_){
_start:
{
if (lean_obj_tag(v_e_1517_) == 0)
{
uint8_t v___x_1518_; 
v___x_1518_ = 2;
return v___x_1518_;
}
else
{
uint8_t v___x_1519_; 
v___x_1519_ = 0;
return v___x_1519_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23___boxed(lean_object* v_e_1520_){
_start:
{
uint8_t v_res_1521_; lean_object* v_r_1522_; 
v_res_1521_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(v_e_1520_);
lean_dec_ref(v_e_1520_);
v_r_1522_ = lean_box(v_res_1521_);
return v_r_1522_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(lean_object* v_x_1523_){
_start:
{
if (lean_obj_tag(v_x_1523_) == 0)
{
lean_object* v_a_1525_; lean_object* v___x_1527_; uint8_t v_isShared_1528_; uint8_t v_isSharedCheck_1532_; 
v_a_1525_ = lean_ctor_get(v_x_1523_, 0);
v_isSharedCheck_1532_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1532_ == 0)
{
v___x_1527_ = v_x_1523_;
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
else
{
lean_inc(v_a_1525_);
lean_dec(v_x_1523_);
v___x_1527_ = lean_box(0);
v_isShared_1528_ = v_isSharedCheck_1532_;
goto v_resetjp_1526_;
}
v_resetjp_1526_:
{
lean_object* v___x_1530_; 
if (v_isShared_1528_ == 0)
{
lean_ctor_set_tag(v___x_1527_, 1);
v___x_1530_ = v___x_1527_;
goto v_reusejp_1529_;
}
else
{
lean_object* v_reuseFailAlloc_1531_; 
v_reuseFailAlloc_1531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1531_, 0, v_a_1525_);
v___x_1530_ = v_reuseFailAlloc_1531_;
goto v_reusejp_1529_;
}
v_reusejp_1529_:
{
return v___x_1530_;
}
}
}
else
{
lean_object* v_a_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1540_; 
v_a_1533_ = lean_ctor_get(v_x_1523_, 0);
v_isSharedCheck_1540_ = !lean_is_exclusive(v_x_1523_);
if (v_isSharedCheck_1540_ == 0)
{
v___x_1535_ = v_x_1523_;
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_a_1533_);
lean_dec(v_x_1523_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1540_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1538_; 
if (v_isShared_1536_ == 0)
{
lean_ctor_set_tag(v___x_1535_, 0);
v___x_1538_ = v___x_1535_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1539_; 
v_reuseFailAlloc_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1539_, 0, v_a_1533_);
v___x_1538_ = v_reuseFailAlloc_1539_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
return v___x_1538_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg___boxed(lean_object* v_x_1541_, lean_object* v___y_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_x_1541_);
return v_res_1543_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; 
v___x_1545_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__0));
v___x_1546_ = l_Lean_stringToMessageData(v___x_1545_);
return v___x_1546_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; 
v___x_1548_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__2));
v___x_1549_ = l_Lean_stringToMessageData(v___x_1548_);
return v___x_1549_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4(void){
_start:
{
lean_object* v___x_1550_; double v___x_1551_; 
v___x_1550_ = lean_unsigned_to_nat(1000u);
v___x_1551_ = lean_float_of_nat(v___x_1550_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(lean_object* v_cls_1552_, uint8_t v_collapsed_1553_, lean_object* v_tag_1554_, lean_object* v_opts_1555_, uint8_t v_clsEnabled_1556_, lean_object* v_oldTraces_1557_, lean_object* v_msg_1558_, lean_object* v_resStartStop_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_){
_start:
{
lean_object* v_fst_1565_; lean_object* v_snd_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1664_; 
v_fst_1565_ = lean_ctor_get(v_resStartStop_1559_, 0);
v_snd_1566_ = lean_ctor_get(v_resStartStop_1559_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_resStartStop_1559_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1568_ = v_resStartStop_1559_;
v_isShared_1569_ = v_isSharedCheck_1664_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_snd_1566_);
lean_inc(v_fst_1565_);
lean_dec(v_resStartStop_1559_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1664_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___y_1571_; lean_object* v___y_1572_; lean_object* v_data_1573_; lean_object* v_fst_1584_; lean_object* v_snd_1585_; lean_object* v___x_1587_; uint8_t v_isShared_1588_; uint8_t v_isSharedCheck_1663_; 
v_fst_1584_ = lean_ctor_get(v_snd_1566_, 0);
v_snd_1585_ = lean_ctor_get(v_snd_1566_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v_snd_1566_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1587_ = v_snd_1566_;
v_isShared_1588_ = v_isSharedCheck_1663_;
goto v_resetjp_1586_;
}
else
{
lean_inc(v_snd_1585_);
lean_inc(v_fst_1584_);
lean_dec(v_snd_1566_);
v___x_1587_ = lean_box(0);
v_isShared_1588_ = v_isSharedCheck_1663_;
goto v_resetjp_1586_;
}
v___jp_1570_:
{
lean_object* v___x_1574_; 
lean_inc(v___y_1572_);
v___x_1574_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_oldTraces_1557_, v_data_1573_, v___y_1572_, v___y_1571_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
if (lean_obj_tag(v___x_1574_) == 0)
{
lean_object* v___x_1575_; 
lean_dec_ref(v___x_1574_);
v___x_1575_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_fst_1565_);
return v___x_1575_;
}
else
{
lean_object* v_a_1576_; lean_object* v___x_1578_; uint8_t v_isShared_1579_; uint8_t v_isSharedCheck_1583_; 
lean_dec(v_fst_1565_);
v_a_1576_ = lean_ctor_get(v___x_1574_, 0);
v_isSharedCheck_1583_ = !lean_is_exclusive(v___x_1574_);
if (v_isSharedCheck_1583_ == 0)
{
v___x_1578_ = v___x_1574_;
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
else
{
lean_inc(v_a_1576_);
lean_dec(v___x_1574_);
v___x_1578_ = lean_box(0);
v_isShared_1579_ = v_isSharedCheck_1583_;
goto v_resetjp_1577_;
}
v_resetjp_1577_:
{
lean_object* v___x_1581_; 
if (v_isShared_1579_ == 0)
{
v___x_1581_ = v___x_1578_;
goto v_reusejp_1580_;
}
else
{
lean_object* v_reuseFailAlloc_1582_; 
v_reuseFailAlloc_1582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1582_, 0, v_a_1576_);
v___x_1581_ = v_reuseFailAlloc_1582_;
goto v_reusejp_1580_;
}
v_reusejp_1580_:
{
return v___x_1581_;
}
}
}
}
v_resetjp_1586_:
{
lean_object* v___x_1589_; uint8_t v___x_1590_; lean_object* v___y_1592_; lean_object* v_a_1593_; uint8_t v___y_1617_; double v___y_1648_; 
v___x_1589_ = l_Lean_trace_profiler;
v___x_1590_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_1555_, v___x_1589_);
if (v___x_1590_ == 0)
{
v___y_1617_ = v___x_1590_;
goto v___jp_1616_;
}
else
{
lean_object* v___x_1653_; uint8_t v___x_1654_; 
v___x_1653_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1654_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_1555_, v___x_1653_);
if (v___x_1654_ == 0)
{
lean_object* v___x_1655_; lean_object* v___x_1656_; double v___x_1657_; double v___x_1658_; double v___x_1659_; 
v___x_1655_ = l_Lean_trace_profiler_threshold;
v___x_1656_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1555_, v___x_1655_);
v___x_1657_ = lean_float_of_nat(v___x_1656_);
v___x_1658_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4);
v___x_1659_ = lean_float_div(v___x_1657_, v___x_1658_);
v___y_1648_ = v___x_1659_;
goto v___jp_1647_;
}
else
{
lean_object* v___x_1660_; lean_object* v___x_1661_; double v___x_1662_; 
v___x_1660_ = l_Lean_trace_profiler_threshold;
v___x_1661_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1555_, v___x_1660_);
v___x_1662_ = lean_float_of_nat(v___x_1661_);
v___y_1648_ = v___x_1662_;
goto v___jp_1647_;
}
}
v___jp_1591_:
{
uint8_t v_result_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1599_; 
v_result_1594_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(v_fst_1565_);
v___x_1595_ = l_Lean_TraceResult_toEmoji(v_result_1594_);
v___x_1596_ = l_Lean_stringToMessageData(v___x_1595_);
v___x_1597_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1);
if (v_isShared_1588_ == 0)
{
lean_ctor_set_tag(v___x_1587_, 7);
lean_ctor_set(v___x_1587_, 1, v___x_1597_);
lean_ctor_set(v___x_1587_, 0, v___x_1596_);
v___x_1599_ = v___x_1587_;
goto v_reusejp_1598_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1596_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v___x_1597_);
v___x_1599_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1598_;
}
v_reusejp_1598_:
{
lean_object* v_m_1601_; 
if (v_isShared_1569_ == 0)
{
lean_ctor_set_tag(v___x_1568_, 7);
lean_ctor_set(v___x_1568_, 1, v_a_1593_);
lean_ctor_set(v___x_1568_, 0, v___x_1599_);
v_m_1601_ = v___x_1568_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1609_; 
v_reuseFailAlloc_1609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1609_, 0, v___x_1599_);
lean_ctor_set(v_reuseFailAlloc_1609_, 1, v_a_1593_);
v_m_1601_ = v_reuseFailAlloc_1609_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; double v___x_1604_; lean_object* v_data_1605_; 
v___x_1602_ = lean_box(v_result_1594_);
v___x_1603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1603_, 0, v___x_1602_);
v___x_1604_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0);
lean_inc_ref(v_tag_1554_);
lean_inc_ref(v___x_1603_);
lean_inc(v_cls_1552_);
v_data_1605_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1605_, 0, v_cls_1552_);
lean_ctor_set(v_data_1605_, 1, v___x_1603_);
lean_ctor_set(v_data_1605_, 2, v_tag_1554_);
lean_ctor_set_float(v_data_1605_, sizeof(void*)*3, v___x_1604_);
lean_ctor_set_float(v_data_1605_, sizeof(void*)*3 + 8, v___x_1604_);
lean_ctor_set_uint8(v_data_1605_, sizeof(void*)*3 + 16, v_collapsed_1553_);
if (v___x_1590_ == 0)
{
lean_dec_ref(v___x_1603_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_dec_ref(v_tag_1554_);
lean_dec(v_cls_1552_);
v___y_1571_ = v_m_1601_;
v___y_1572_ = v___y_1592_;
v_data_1573_ = v_data_1605_;
goto v___jp_1570_;
}
else
{
lean_object* v_data_1606_; double v___x_1607_; double v___x_1608_; 
lean_dec_ref(v_data_1605_);
v_data_1606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1606_, 0, v_cls_1552_);
lean_ctor_set(v_data_1606_, 1, v___x_1603_);
lean_ctor_set(v_data_1606_, 2, v_tag_1554_);
v___x_1607_ = lean_unbox_float(v_fst_1584_);
lean_dec(v_fst_1584_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3, v___x_1607_);
v___x_1608_ = lean_unbox_float(v_snd_1585_);
lean_dec(v_snd_1585_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3 + 8, v___x_1608_);
lean_ctor_set_uint8(v_data_1606_, sizeof(void*)*3 + 16, v_collapsed_1553_);
v___y_1571_ = v_m_1601_;
v___y_1572_ = v___y_1592_;
v_data_1573_ = v_data_1606_;
goto v___jp_1570_;
}
}
}
}
v___jp_1611_:
{
lean_object* v_ref_1612_; lean_object* v___x_1613_; 
v_ref_1612_ = lean_ctor_get(v___y_1562_, 5);
lean_inc(v___y_1563_);
lean_inc_ref(v___y_1562_);
lean_inc(v___y_1561_);
lean_inc_ref(v___y_1560_);
lean_inc(v_fst_1565_);
v___x_1613_ = lean_apply_6(v_msg_1558_, v_fst_1565_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_, lean_box(0));
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v_a_1614_; 
v_a_1614_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_a_1614_);
lean_dec_ref(v___x_1613_);
v___y_1592_ = v_ref_1612_;
v_a_1593_ = v_a_1614_;
goto v___jp_1591_;
}
else
{
lean_object* v___x_1615_; 
lean_dec_ref(v___x_1613_);
v___x_1615_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3);
v___y_1592_ = v_ref_1612_;
v_a_1593_ = v___x_1615_;
goto v___jp_1591_;
}
}
v___jp_1616_:
{
if (v_clsEnabled_1556_ == 0)
{
if (v___y_1617_ == 0)
{
lean_object* v___x_1618_; lean_object* v_traceState_1619_; lean_object* v_env_1620_; lean_object* v_nextMacroScope_1621_; lean_object* v_ngen_1622_; lean_object* v_auxDeclNGen_1623_; lean_object* v_cache_1624_; lean_object* v_messages_1625_; lean_object* v_infoState_1626_; lean_object* v_snapshotTasks_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1646_; 
lean_del_object(v___x_1587_);
lean_dec(v_snd_1585_);
lean_dec(v_fst_1584_);
lean_del_object(v___x_1568_);
lean_dec_ref(v_msg_1558_);
lean_dec_ref(v_tag_1554_);
lean_dec(v_cls_1552_);
v___x_1618_ = lean_st_ref_take(v___y_1563_);
v_traceState_1619_ = lean_ctor_get(v___x_1618_, 4);
v_env_1620_ = lean_ctor_get(v___x_1618_, 0);
v_nextMacroScope_1621_ = lean_ctor_get(v___x_1618_, 1);
v_ngen_1622_ = lean_ctor_get(v___x_1618_, 2);
v_auxDeclNGen_1623_ = lean_ctor_get(v___x_1618_, 3);
v_cache_1624_ = lean_ctor_get(v___x_1618_, 5);
v_messages_1625_ = lean_ctor_get(v___x_1618_, 6);
v_infoState_1626_ = lean_ctor_get(v___x_1618_, 7);
v_snapshotTasks_1627_ = lean_ctor_get(v___x_1618_, 8);
v_isSharedCheck_1646_ = !lean_is_exclusive(v___x_1618_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1629_ = v___x_1618_;
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_snapshotTasks_1627_);
lean_inc(v_infoState_1626_);
lean_inc(v_messages_1625_);
lean_inc(v_cache_1624_);
lean_inc(v_traceState_1619_);
lean_inc(v_auxDeclNGen_1623_);
lean_inc(v_ngen_1622_);
lean_inc(v_nextMacroScope_1621_);
lean_inc(v_env_1620_);
lean_dec(v___x_1618_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1646_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
uint64_t v_tid_1631_; lean_object* v_traces_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1645_; 
v_tid_1631_ = lean_ctor_get_uint64(v_traceState_1619_, sizeof(void*)*1);
v_traces_1632_ = lean_ctor_get(v_traceState_1619_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_traceState_1619_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1634_ = v_traceState_1619_;
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_traces_1632_);
lean_dec(v_traceState_1619_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1645_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1557_, v_traces_1632_);
lean_dec_ref(v_traces_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v___x_1636_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1636_);
lean_ctor_set_uint64(v_reuseFailAlloc_1644_, sizeof(void*)*1, v_tid_1631_);
v___x_1638_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
lean_object* v___x_1640_; 
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 4, v___x_1638_);
v___x_1640_ = v___x_1629_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_env_1620_);
lean_ctor_set(v_reuseFailAlloc_1643_, 1, v_nextMacroScope_1621_);
lean_ctor_set(v_reuseFailAlloc_1643_, 2, v_ngen_1622_);
lean_ctor_set(v_reuseFailAlloc_1643_, 3, v_auxDeclNGen_1623_);
lean_ctor_set(v_reuseFailAlloc_1643_, 4, v___x_1638_);
lean_ctor_set(v_reuseFailAlloc_1643_, 5, v_cache_1624_);
lean_ctor_set(v_reuseFailAlloc_1643_, 6, v_messages_1625_);
lean_ctor_set(v_reuseFailAlloc_1643_, 7, v_infoState_1626_);
lean_ctor_set(v_reuseFailAlloc_1643_, 8, v_snapshotTasks_1627_);
v___x_1640_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; 
v___x_1641_ = lean_st_ref_set(v___y_1563_, v___x_1640_);
v___x_1642_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_fst_1565_);
return v___x_1642_;
}
}
}
}
}
else
{
goto v___jp_1611_;
}
}
else
{
goto v___jp_1611_;
}
}
v___jp_1647_:
{
double v___x_1649_; double v___x_1650_; double v___x_1651_; uint8_t v___x_1652_; 
v___x_1649_ = lean_unbox_float(v_snd_1585_);
v___x_1650_ = lean_unbox_float(v_fst_1584_);
v___x_1651_ = lean_float_sub(v___x_1649_, v___x_1650_);
v___x_1652_ = lean_float_decLt(v___y_1648_, v___x_1651_);
v___y_1617_ = v___x_1652_;
goto v___jp_1616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object* v_cls_1665_, lean_object* v_collapsed_1666_, lean_object* v_tag_1667_, lean_object* v_opts_1668_, lean_object* v_clsEnabled_1669_, lean_object* v_oldTraces_1670_, lean_object* v_msg_1671_, lean_object* v_resStartStop_1672_, lean_object* v___y_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_){
_start:
{
uint8_t v_collapsed_boxed_1678_; uint8_t v_clsEnabled_boxed_1679_; lean_object* v_res_1680_; 
v_collapsed_boxed_1678_ = lean_unbox(v_collapsed_1666_);
v_clsEnabled_boxed_1679_ = lean_unbox(v_clsEnabled_1669_);
v_res_1680_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_1665_, v_collapsed_boxed_1678_, v_tag_1667_, v_opts_1668_, v_clsEnabled_boxed_1679_, v_oldTraces_1670_, v_msg_1671_, v_resStartStop_1672_, v___y_1673_, v___y_1674_, v___y_1675_, v___y_1676_);
lean_dec(v___y_1676_);
lean_dec_ref(v___y_1675_);
lean_dec(v___y_1674_);
lean_dec_ref(v___y_1673_);
lean_dec_ref(v_opts_1668_);
return v_res_1680_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_1681_; uint64_t v___x_1682_; 
v___x_1681_ = 3;
v___x_1682_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1681_);
return v___x_1682_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4(void){
_start:
{
lean_object* v_cls_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_cls_1689_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_1690_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__3));
v___x_1691_ = l_Lean_Name_append(v___x_1690_, v_cls_1689_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; 
v___x_1693_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__5));
v___x_1694_ = l_Lean_stringToMessageData(v___x_1693_);
return v___x_1694_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; 
v___x_1696_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__0));
v___x_1697_ = l_Lean_stringToMessageData(v___x_1696_);
return v___x_1697_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1699_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__2));
v___x_1700_ = l_Lean_stringToMessageData(v___x_1699_);
return v___x_1700_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__4));
v___x_1703_ = l_Lean_stringToMessageData(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__6));
v___x_1706_ = l_Lean_stringToMessageData(v___x_1705_);
return v___x_1706_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; 
v___x_1708_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__8));
v___x_1709_ = l_Lean_stringToMessageData(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(lean_object* v_upperBound_1710_, lean_object* v_fst_1711_, lean_object* v_args_1712_, uint8_t v_compile_1713_, uint8_t v_logCompileErrors_1714_, uint8_t v_isMeta_1715_, uint8_t v___x_1716_, lean_object* v_a_1717_, lean_object* v_b_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_){
_start:
{
lean_object* v_a_1725_; lean_object* v___y_1730_; uint8_t v___x_1749_; 
v___x_1749_ = lean_nat_dec_lt(v_a_1717_, v_upperBound_1710_);
if (v___x_1749_ == 0)
{
lean_object* v___x_1750_; 
lean_dec(v_a_1717_);
v___x_1750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1750_, 0, v_b_1718_);
return v___x_1750_;
}
else
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_array_fget_borrowed(v_fst_1711_, v_a_1717_);
v___x_1752_ = l_Lean_Expr_mvarId_x21(v___x_1751_);
lean_inc(v___x_1752_);
v___x_1753_ = l_Lean_MVarId_getDecl(v___x_1752_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1753_) == 0)
{
lean_object* v_a_1754_; lean_object* v_type_1755_; lean_object* v___x_1756_; 
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref(v___x_1753_);
v_type_1755_ = lean_ctor_get(v_a_1754_, 2);
lean_inc_ref(v_type_1755_);
lean_dec(v_a_1754_);
v___x_1756_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_1755_, v___y_1720_);
if (lean_obj_tag(v___x_1756_) == 0)
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1756_, 0);
lean_inc_n(v_a_1757_, 2);
lean_dec_ref(v___x_1756_);
v___x_1758_ = l_Lean_Meta_isProp(v_a_1757_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1760_; lean_object* v_cls_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref(v___x_1758_);
v___x_1760_ = lean_box(0);
v_cls_1761_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_1762_ = lean_array_fget_borrowed(v_args_1712_, v_a_1717_);
v___x_1763_ = lean_unbox(v_a_1759_);
lean_dec(v_a_1759_);
if (v___x_1763_ == 0)
{
lean_object* v___x_1764_; 
lean_inc(v_a_1757_);
v___x_1764_ = l_Lean_Meta_isClass_x3f(v_a_1757_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1764_) == 0)
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1896_; 
v_a_1765_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1767_ = v___x_1764_;
v_isShared_1768_ = v_isSharedCheck_1896_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1764_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1896_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
if (lean_obj_tag(v_a_1765_) == 0)
{
lean_object* v_options_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; 
lean_del_object(v___x_1767_);
v_options_1769_ = lean_ctor_get(v___y_1721_, 2);
v___x_1770_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1771_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1769_, v___x_1770_);
if (v___x_1771_ == 0)
{
lean_object* v___x_1772_; 
lean_dec(v_a_1757_);
lean_inc(v___x_1762_);
v___x_1772_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1752_, v___x_1762_, v___y_1720_);
if (lean_obj_tag(v___x_1772_) == 0)
{
lean_dec_ref(v___x_1772_);
v_a_1725_ = v___x_1760_;
goto v___jp_1724_;
}
else
{
lean_dec(v_a_1717_);
return v___x_1772_;
}
}
else
{
lean_object* v___x_1773_; 
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc(v___x_1762_);
v___x_1773_ = lean_infer_type(v___x_1762_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_object* v_a_1774_; lean_object* v___x_1775_; 
v_a_1774_ = lean_ctor_get(v___x_1773_, 0);
lean_inc(v_a_1774_);
lean_dec_ref(v___x_1773_);
lean_inc(v_a_1757_);
v___x_1775_ = l_Lean_Meta_isExprDefEq(v_a_1757_, v_a_1774_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; uint8_t v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref(v___x_1775_);
v___x_1777_ = lean_unbox(v_a_1776_);
lean_dec(v_a_1776_);
if (v___x_1777_ == 0)
{
lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1778_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_1779_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_1778_, v___y_1722_);
if (lean_obj_tag(v___x_1779_) == 0)
{
lean_object* v_a_1780_; lean_object* v___x_1781_; 
v_a_1780_ = lean_ctor_get(v___x_1779_, 0);
lean_inc_n(v_a_1780_, 2);
lean_dec_ref(v___x_1779_);
lean_inc(v___x_1762_);
v___x_1781_ = l_Lean_Meta_mkAuxDefinition(v_a_1780_, v_a_1757_, v___x_1762_, v___x_1716_, v___x_1716_, v___x_1749_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1781_) == 0)
{
lean_object* v_a_1782_; lean_object* v___x_1783_; 
v_a_1782_ = lean_ctor_get(v___x_1781_, 0);
lean_inc(v_a_1782_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1752_, v_a_1782_, v___y_1720_);
if (lean_obj_tag(v___x_1783_) == 0)
{
uint8_t v___x_1784_; lean_object* v___x_1785_; 
lean_dec_ref(v___x_1783_);
v___x_1784_ = 0;
lean_inc(v_a_1780_);
v___x_1785_ = l_Lean_Meta_setInlineAttribute(v_a_1780_, v___x_1784_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1785_) == 0)
{
lean_dec_ref(v___x_1785_);
if (v_isMeta_1715_ == 0)
{
lean_object* v___x_1786_; 
v___x_1786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1780_, v___x_1760_, v_compile_1713_, v_logCompileErrors_1714_, v___x_1760_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1786_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1787_; lean_object* v_env_1788_; lean_object* v_nextMacroScope_1789_; lean_object* v_ngen_1790_; lean_object* v_auxDeclNGen_1791_; lean_object* v_traceState_1792_; lean_object* v_messages_1793_; lean_object* v_infoState_1794_; lean_object* v_snapshotTasks_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1821_; 
v___x_1787_ = lean_st_ref_take(v___y_1722_);
v_env_1788_ = lean_ctor_get(v___x_1787_, 0);
v_nextMacroScope_1789_ = lean_ctor_get(v___x_1787_, 1);
v_ngen_1790_ = lean_ctor_get(v___x_1787_, 2);
v_auxDeclNGen_1791_ = lean_ctor_get(v___x_1787_, 3);
v_traceState_1792_ = lean_ctor_get(v___x_1787_, 4);
v_messages_1793_ = lean_ctor_get(v___x_1787_, 6);
v_infoState_1794_ = lean_ctor_get(v___x_1787_, 7);
v_snapshotTasks_1795_ = lean_ctor_get(v___x_1787_, 8);
v_isSharedCheck_1821_ = !lean_is_exclusive(v___x_1787_);
if (v_isSharedCheck_1821_ == 0)
{
lean_object* v_unused_1822_; 
v_unused_1822_ = lean_ctor_get(v___x_1787_, 5);
lean_dec(v_unused_1822_);
v___x_1797_ = v___x_1787_;
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_snapshotTasks_1795_);
lean_inc(v_infoState_1794_);
lean_inc(v_messages_1793_);
lean_inc(v_traceState_1792_);
lean_inc(v_auxDeclNGen_1791_);
lean_inc(v_ngen_1790_);
lean_inc(v_nextMacroScope_1789_);
lean_inc(v_env_1788_);
lean_dec(v___x_1787_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1821_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1802_; 
lean_inc(v_a_1780_);
v___x_1799_ = l_Lean_markMeta(v_env_1788_, v_a_1780_);
v___x_1800_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_1798_ == 0)
{
lean_ctor_set(v___x_1797_, 5, v___x_1800_);
lean_ctor_set(v___x_1797_, 0, v___x_1799_);
v___x_1802_ = v___x_1797_;
goto v_reusejp_1801_;
}
else
{
lean_object* v_reuseFailAlloc_1820_; 
v_reuseFailAlloc_1820_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1799_);
lean_ctor_set(v_reuseFailAlloc_1820_, 1, v_nextMacroScope_1789_);
lean_ctor_set(v_reuseFailAlloc_1820_, 2, v_ngen_1790_);
lean_ctor_set(v_reuseFailAlloc_1820_, 3, v_auxDeclNGen_1791_);
lean_ctor_set(v_reuseFailAlloc_1820_, 4, v_traceState_1792_);
lean_ctor_set(v_reuseFailAlloc_1820_, 5, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1820_, 6, v_messages_1793_);
lean_ctor_set(v_reuseFailAlloc_1820_, 7, v_infoState_1794_);
lean_ctor_set(v_reuseFailAlloc_1820_, 8, v_snapshotTasks_1795_);
v___x_1802_ = v_reuseFailAlloc_1820_;
goto v_reusejp_1801_;
}
v_reusejp_1801_:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; lean_object* v_mctx_1805_; lean_object* v_zetaDeltaFVarIds_1806_; lean_object* v_postponed_1807_; lean_object* v_diag_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1818_; 
v___x_1803_ = lean_st_ref_set(v___y_1722_, v___x_1802_);
v___x_1804_ = lean_st_ref_take(v___y_1720_);
v_mctx_1805_ = lean_ctor_get(v___x_1804_, 0);
v_zetaDeltaFVarIds_1806_ = lean_ctor_get(v___x_1804_, 2);
v_postponed_1807_ = lean_ctor_get(v___x_1804_, 3);
v_diag_1808_ = lean_ctor_get(v___x_1804_, 4);
v_isSharedCheck_1818_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1818_ == 0)
{
lean_object* v_unused_1819_; 
v_unused_1819_ = lean_ctor_get(v___x_1804_, 1);
lean_dec(v_unused_1819_);
v___x_1810_ = v___x_1804_;
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_diag_1808_);
lean_inc(v_postponed_1807_);
lean_inc(v_zetaDeltaFVarIds_1806_);
lean_inc(v_mctx_1805_);
lean_dec(v___x_1804_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1818_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1812_; lean_object* v___x_1814_; 
v___x_1812_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 1, v___x_1812_);
v___x_1814_ = v___x_1810_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_mctx_1805_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1812_);
lean_ctor_set(v_reuseFailAlloc_1817_, 2, v_zetaDeltaFVarIds_1806_);
lean_ctor_set(v_reuseFailAlloc_1817_, 3, v_postponed_1807_);
lean_ctor_set(v_reuseFailAlloc_1817_, 4, v_diag_1808_);
v___x_1814_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = lean_st_ref_set(v___y_1720_, v___x_1814_);
v___x_1816_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1780_, v___x_1760_, v_compile_1713_, v_logCompileErrors_1714_, v___x_1760_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1816_;
goto v___jp_1729_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1780_);
lean_dec(v_a_1717_);
return v___x_1785_;
}
}
else
{
lean_dec(v_a_1780_);
lean_dec(v_a_1717_);
return v___x_1783_;
}
}
else
{
lean_object* v_a_1823_; lean_object* v___x_1825_; uint8_t v_isShared_1826_; uint8_t v_isSharedCheck_1830_; 
lean_dec(v_a_1780_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1823_ = lean_ctor_get(v___x_1781_, 0);
v_isSharedCheck_1830_ = !lean_is_exclusive(v___x_1781_);
if (v_isSharedCheck_1830_ == 0)
{
v___x_1825_ = v___x_1781_;
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
else
{
lean_inc(v_a_1823_);
lean_dec(v___x_1781_);
v___x_1825_ = lean_box(0);
v_isShared_1826_ = v_isSharedCheck_1830_;
goto v_resetjp_1824_;
}
v_resetjp_1824_:
{
lean_object* v___x_1828_; 
if (v_isShared_1826_ == 0)
{
v___x_1828_ = v___x_1825_;
goto v_reusejp_1827_;
}
else
{
lean_object* v_reuseFailAlloc_1829_; 
v_reuseFailAlloc_1829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1829_, 0, v_a_1823_);
v___x_1828_ = v_reuseFailAlloc_1829_;
goto v_reusejp_1827_;
}
v_reusejp_1827_:
{
return v___x_1828_;
}
}
}
}
else
{
lean_object* v_a_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1838_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1831_ = lean_ctor_get(v___x_1779_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1779_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1833_ = v___x_1779_;
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
else
{
lean_inc(v_a_1831_);
lean_dec(v___x_1779_);
v___x_1833_ = lean_box(0);
v_isShared_1834_ = v_isSharedCheck_1838_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v___x_1836_; 
if (v_isShared_1834_ == 0)
{
v___x_1836_ = v___x_1833_;
goto v_reusejp_1835_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_a_1831_);
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
else
{
lean_object* v___x_1839_; 
lean_dec(v_a_1757_);
lean_inc(v___x_1762_);
v___x_1839_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1752_, v___x_1762_, v___y_1720_);
if (lean_obj_tag(v___x_1839_) == 0)
{
lean_dec_ref(v___x_1839_);
v_a_1725_ = v___x_1760_;
goto v___jp_1724_;
}
else
{
lean_dec(v_a_1717_);
return v___x_1839_;
}
}
}
else
{
lean_object* v_a_1840_; lean_object* v___x_1842_; uint8_t v_isShared_1843_; uint8_t v_isSharedCheck_1847_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1840_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1847_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1847_ == 0)
{
v___x_1842_ = v___x_1775_;
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
else
{
lean_inc(v_a_1840_);
lean_dec(v___x_1775_);
v___x_1842_ = lean_box(0);
v_isShared_1843_ = v_isSharedCheck_1847_;
goto v_resetjp_1841_;
}
v_resetjp_1841_:
{
lean_object* v___x_1845_; 
if (v_isShared_1843_ == 0)
{
v___x_1845_ = v___x_1842_;
goto v_reusejp_1844_;
}
else
{
lean_object* v_reuseFailAlloc_1846_; 
v_reuseFailAlloc_1846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1846_, 0, v_a_1840_);
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
else
{
lean_object* v_a_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1855_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1848_ = lean_ctor_get(v___x_1773_, 0);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1773_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1850_ = v___x_1773_;
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_a_1848_);
lean_dec(v___x_1773_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1855_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
lean_object* v___x_1853_; 
if (v_isShared_1851_ == 0)
{
v___x_1853_ = v___x_1850_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1848_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
}
}
else
{
lean_object* v_options_1856_; lean_object* v_inheritedTraceOptions_1857_; lean_object* v_a_1859_; lean_object* v___y_1862_; uint8_t v___y_1863_; lean_object* v_a_1868_; lean_object* v___y_1872_; lean_object* v___x_1876_; uint8_t v___x_1877_; 
lean_dec_ref(v_a_1765_);
v_options_1856_ = lean_ctor_get(v___y_1721_, 2);
v_inheritedTraceOptions_1857_ = lean_ctor_get(v___y_1721_, 13);
v___x_1876_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_1877_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1856_, v___x_1876_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
lean_del_object(v___x_1767_);
lean_inc(v___x_1762_);
v___x_1878_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_1762_, v_a_1757_, v_compile_1713_, v_logCompileErrors_1714_, v_isMeta_1715_, v___x_1752_, v___x_1760_, v___x_1760_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1878_;
goto v___jp_1729_;
}
else
{
lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1879_ = lean_box(0);
lean_inc(v_a_1757_);
v___x_1880_ = l_Lean_Meta_trySynthInstance(v_a_1757_, v___x_1879_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
if (lean_obj_tag(v_a_1881_) == 1)
{
lean_object* v_a_1882_; uint8_t v_hasTrace_1883_; 
v_a_1882_ = lean_ctor_get(v_a_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v_a_1881_);
v_hasTrace_1883_ = lean_ctor_get_uint8(v_options_1856_, sizeof(void*)*1);
if (v_hasTrace_1883_ == 0)
{
goto v___jp_1884_;
}
else
{
lean_object* v___x_1886_; uint8_t v___x_1887_; 
v___x_1886_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_1887_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1857_, v_options_1856_, v___x_1886_);
if (v___x_1887_ == 0)
{
goto v___jp_1884_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1888_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_1882_);
v___x_1889_ = l_Lean_MessageData_ofExpr(v_a_1882_);
v___x_1890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1888_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1761_, v___x_1890_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1891_) == 0)
{
lean_object* v_a_1892_; lean_object* v___x_1893_; 
v_a_1892_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1892_);
lean_dec_ref(v___x_1891_);
lean_inc(v___x_1752_);
v___x_1893_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1752_, v_a_1882_, v_a_1892_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1872_ = v___x_1893_;
goto v___jp_1871_;
}
else
{
lean_object* v_a_1894_; 
lean_dec(v_a_1882_);
v_a_1894_ = lean_ctor_get(v___x_1891_, 0);
lean_inc(v_a_1894_);
lean_dec_ref(v___x_1891_);
v_a_1868_ = v_a_1894_;
goto v___jp_1867_;
}
}
}
v___jp_1884_:
{
lean_object* v___x_1885_; 
lean_inc(v___x_1752_);
v___x_1885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1752_, v_a_1882_, v___x_1760_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1872_ = v___x_1885_;
goto v___jp_1871_;
}
}
else
{
lean_dec(v_a_1881_);
lean_del_object(v___x_1767_);
v_a_1859_ = v___x_1760_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1895_; 
v_a_1895_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1880_);
v_a_1868_ = v_a_1895_;
goto v___jp_1867_;
}
}
v___jp_1858_:
{
lean_object* v___x_1860_; 
lean_inc(v___x_1762_);
v___x_1860_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_1762_, v_a_1757_, v_compile_1713_, v_logCompileErrors_1714_, v_isMeta_1715_, v___x_1752_, v___x_1760_, v_a_1859_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1860_;
goto v___jp_1729_;
}
v___jp_1861_:
{
if (v___y_1863_ == 0)
{
lean_dec_ref(v___y_1862_);
lean_del_object(v___x_1767_);
v_a_1859_ = v___x_1760_;
goto v___jp_1858_;
}
else
{
lean_object* v___x_1865_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set_tag(v___x_1767_, 1);
lean_ctor_set(v___x_1767_, 0, v___y_1862_);
v___x_1865_ = v___x_1767_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___y_1862_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
v___jp_1867_:
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_Exception_isInterrupt(v_a_1868_);
if (v___x_1869_ == 0)
{
uint8_t v___x_1870_; 
lean_inc_ref(v_a_1868_);
v___x_1870_ = l_Lean_Exception_isRuntime(v_a_1868_);
v___y_1862_ = v_a_1868_;
v___y_1863_ = v___x_1870_;
goto v___jp_1861_;
}
else
{
v___y_1862_ = v_a_1868_;
v___y_1863_ = v___x_1869_;
goto v___jp_1861_;
}
}
v___jp_1871_:
{
if (lean_obj_tag(v___y_1872_) == 0)
{
lean_object* v_a_1873_; 
lean_del_object(v___x_1767_);
v_a_1873_ = lean_ctor_get(v___y_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___y_1872_);
if (lean_obj_tag(v_a_1873_) == 0)
{
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
v_a_1725_ = v___x_1760_;
goto v___jp_1724_;
}
else
{
lean_object* v_a_1874_; 
v_a_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v_a_1873_);
v_a_1859_ = v_a_1874_;
goto v___jp_1858_;
}
}
else
{
lean_object* v_a_1875_; 
v_a_1875_ = lean_ctor_get(v___y_1872_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___y_1872_);
v_a_1868_ = v_a_1875_;
goto v___jp_1867_;
}
}
}
}
}
else
{
lean_object* v_a_1897_; lean_object* v___x_1899_; uint8_t v_isShared_1900_; uint8_t v_isSharedCheck_1904_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1897_ = lean_ctor_get(v___x_1764_, 0);
v_isSharedCheck_1904_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1904_ == 0)
{
v___x_1899_ = v___x_1764_;
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
else
{
lean_inc(v_a_1897_);
lean_dec(v___x_1764_);
v___x_1899_ = lean_box(0);
v_isShared_1900_ = v_isSharedCheck_1904_;
goto v_resetjp_1898_;
}
v_resetjp_1898_:
{
lean_object* v___x_1902_; 
if (v_isShared_1900_ == 0)
{
v___x_1902_ = v___x_1899_;
goto v_reusejp_1901_;
}
else
{
lean_object* v_reuseFailAlloc_1903_; 
v_reuseFailAlloc_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1903_, 0, v_a_1897_);
v___x_1902_ = v_reuseFailAlloc_1903_;
goto v_reusejp_1901_;
}
v_reusejp_1901_:
{
return v___x_1902_;
}
}
}
}
else
{
lean_object* v___x_1905_; 
lean_inc(v___y_1722_);
lean_inc_ref(v___y_1721_);
lean_inc(v___y_1720_);
lean_inc_ref(v___y_1719_);
lean_inc(v___x_1762_);
v___x_1905_ = lean_infer_type(v___x_1762_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc_n(v_a_1906_, 2);
lean_dec_ref(v___x_1905_);
lean_inc(v_a_1757_);
v___x_1907_ = l_Lean_Meta_isExprDefEq(v_a_1757_, v_a_1906_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; uint8_t v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
v___x_1909_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1909_ == 0)
{
lean_object* v_options_1910_; lean_object* v_inheritedTraceOptions_1911_; uint8_t v_hasTrace_1912_; 
v_options_1910_ = lean_ctor_get(v___y_1721_, 2);
v_inheritedTraceOptions_1911_ = lean_ctor_get(v___y_1721_, 13);
v_hasTrace_1912_ = lean_ctor_get_uint8(v_options_1910_, sizeof(void*)*1);
if (v_hasTrace_1912_ == 0)
{
lean_dec(v_a_1906_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_1916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1911_, v_options_1910_, v___x_1915_);
if (v___x_1916_ == 0)
{
lean_dec(v_a_1906_);
goto v___jp_1913_;
}
else
{
lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1917_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_1717_);
v___x_1918_ = l_Nat_reprFast(v_a_1717_);
v___x_1919_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1919_, 0, v___x_1918_);
v___x_1920_ = l_Lean_MessageData_ofFormat(v___x_1919_);
v___x_1921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1917_);
lean_ctor_set(v___x_1921_, 1, v___x_1920_);
v___x_1922_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_1923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1921_);
lean_ctor_set(v___x_1923_, 1, v___x_1922_);
lean_inc(v_a_1757_);
v___x_1924_ = l_Lean_MessageData_ofExpr(v_a_1757_);
v___x_1925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1923_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
v___x_1926_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_1927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1925_);
lean_ctor_set(v___x_1927_, 1, v___x_1926_);
v___x_1928_ = l_Lean_MessageData_ofExpr(v_a_1906_);
v___x_1929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1927_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_1931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1931_, 0, v___x_1929_);
lean_ctor_set(v___x_1931_, 1, v___x_1930_);
lean_inc(v___x_1762_);
v___x_1932_ = l_Lean_MessageData_ofExpr(v___x_1762_);
v___x_1933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1933_, 0, v___x_1931_);
lean_ctor_set(v___x_1933_, 1, v___x_1932_);
v___x_1934_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1761_, v___x_1933_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v_a_1935_; lean_object* v___x_1936_; 
v_a_1935_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1935_);
lean_dec_ref(v___x_1934_);
lean_inc(v___x_1762_);
v___x_1936_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1757_, v___x_1762_, v___x_1749_, v___x_1752_, v___x_1760_, v_a_1935_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1936_;
goto v___jp_1729_;
}
else
{
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
return v___x_1934_;
}
}
}
v___jp_1913_:
{
lean_object* v___x_1914_; 
lean_inc(v___x_1762_);
v___x_1914_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1757_, v___x_1762_, v___x_1749_, v___x_1752_, v___x_1760_, v___x_1760_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
v___y_1730_ = v___x_1914_;
goto v___jp_1729_;
}
}
else
{
lean_object* v___x_1937_; 
lean_dec(v_a_1906_);
lean_dec(v_a_1757_);
lean_inc(v___x_1762_);
v___x_1937_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1752_, v___x_1762_, v___y_1720_);
if (lean_obj_tag(v___x_1937_) == 0)
{
lean_dec_ref(v___x_1937_);
v_a_1725_ = v___x_1760_;
goto v___jp_1724_;
}
else
{
lean_dec(v_a_1717_);
return v___x_1937_;
}
}
}
else
{
lean_object* v_a_1938_; lean_object* v___x_1940_; uint8_t v_isShared_1941_; uint8_t v_isSharedCheck_1945_; 
lean_dec(v_a_1906_);
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1938_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1940_ = v___x_1907_;
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
else
{
lean_inc(v_a_1938_);
lean_dec(v___x_1907_);
v___x_1940_ = lean_box(0);
v_isShared_1941_ = v_isSharedCheck_1945_;
goto v_resetjp_1939_;
}
v_resetjp_1939_:
{
lean_object* v___x_1943_; 
if (v_isShared_1941_ == 0)
{
v___x_1943_ = v___x_1940_;
goto v_reusejp_1942_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_a_1938_);
v___x_1943_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1942_;
}
v_reusejp_1942_:
{
return v___x_1943_;
}
}
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1946_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1905_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1905_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
}
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_dec(v_a_1757_);
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1954_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1758_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1758_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
}
}
}
}
else
{
lean_object* v_a_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1969_; 
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1962_ = lean_ctor_get(v___x_1756_, 0);
v_isSharedCheck_1969_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1969_ == 0)
{
v___x_1964_ = v___x_1756_;
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_a_1962_);
lean_dec(v___x_1756_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1969_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1967_; 
if (v_isShared_1965_ == 0)
{
v___x_1967_ = v___x_1964_;
goto v_reusejp_1966_;
}
else
{
lean_object* v_reuseFailAlloc_1968_; 
v_reuseFailAlloc_1968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1968_, 0, v_a_1962_);
v___x_1967_ = v_reuseFailAlloc_1968_;
goto v_reusejp_1966_;
}
v_reusejp_1966_:
{
return v___x_1967_;
}
}
}
}
else
{
lean_object* v_a_1970_; lean_object* v___x_1972_; uint8_t v_isShared_1973_; uint8_t v_isSharedCheck_1977_; 
lean_dec(v___x_1752_);
lean_dec(v_a_1717_);
v_a_1970_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1977_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1972_ = v___x_1753_;
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
else
{
lean_inc(v_a_1970_);
lean_dec(v___x_1753_);
v___x_1972_ = lean_box(0);
v_isShared_1973_ = v_isSharedCheck_1977_;
goto v_resetjp_1971_;
}
v_resetjp_1971_:
{
lean_object* v___x_1975_; 
if (v_isShared_1973_ == 0)
{
v___x_1975_ = v___x_1972_;
goto v_reusejp_1974_;
}
else
{
lean_object* v_reuseFailAlloc_1976_; 
v_reuseFailAlloc_1976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1976_, 0, v_a_1970_);
v___x_1975_ = v_reuseFailAlloc_1976_;
goto v_reusejp_1974_;
}
v_reusejp_1974_:
{
return v___x_1975_;
}
}
}
}
v___jp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1727_; 
v___x_1726_ = lean_unsigned_to_nat(1u);
v___x_1727_ = lean_nat_add(v_a_1717_, v___x_1726_);
lean_dec(v_a_1717_);
v_a_1717_ = v___x_1727_;
v_b_1718_ = v_a_1725_;
goto _start;
}
v___jp_1729_:
{
if (lean_obj_tag(v___y_1730_) == 0)
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1740_; 
v_a_1731_ = lean_ctor_get(v___y_1730_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___y_1730_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1733_ = v___y_1730_;
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___y_1730_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1740_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
if (lean_obj_tag(v_a_1731_) == 0)
{
lean_object* v_a_1735_; lean_object* v___x_1737_; 
lean_dec(v_a_1717_);
v_a_1735_ = lean_ctor_get(v_a_1731_, 0);
lean_inc(v_a_1735_);
lean_dec_ref(v_a_1731_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 0, v_a_1735_);
v___x_1737_ = v___x_1733_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1735_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
else
{
lean_object* v_a_1739_; 
lean_del_object(v___x_1733_);
v_a_1739_ = lean_ctor_get(v_a_1731_, 0);
lean_inc(v_a_1739_);
lean_dec_ref(v_a_1731_);
v_a_1725_ = v_a_1739_;
goto v___jp_1724_;
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1717_);
v_a_1741_ = lean_ctor_get(v___y_1730_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___y_1730_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___y_1730_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___y_1730_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object* v_upperBound_1978_, lean_object* v_fst_1979_, lean_object* v_args_1980_, uint8_t v_compile_1981_, uint8_t v_logCompileErrors_1982_, uint8_t v_isMeta_1983_, uint8_t v___x_1984_, lean_object* v_a_1985_, lean_object* v_b_1986_, lean_object* v___y_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_){
_start:
{
lean_object* v_a_1993_; lean_object* v___y_1998_; uint8_t v___x_2017_; 
v___x_2017_ = lean_nat_dec_lt(v_a_1985_, v_upperBound_1978_);
if (v___x_2017_ == 0)
{
lean_object* v___x_2018_; 
lean_dec(v_a_1985_);
v___x_2018_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2018_, 0, v_b_1986_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_array_fget_borrowed(v_fst_1979_, v_a_1985_);
v___x_2020_ = l_Lean_Expr_mvarId_x21(v___x_2019_);
lean_inc(v___x_2020_);
v___x_2021_ = l_Lean_MVarId_getDecl(v___x_2020_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v_type_2023_; lean_object* v___x_2024_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
v_type_2023_ = lean_ctor_get(v_a_2022_, 2);
lean_inc_ref(v_type_2023_);
lean_dec(v_a_2022_);
v___x_2024_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2023_, v___y_1988_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc_n(v_a_2025_, 2);
lean_dec_ref(v___x_2024_);
v___x_2026_ = l_Lean_Meta_isProp(v_a_2025_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; lean_object* v___x_2028_; lean_object* v_cls_2029_; lean_object* v___x_2030_; uint8_t v___x_2031_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref(v___x_2026_);
v___x_2028_ = lean_box(0);
v_cls_2029_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2030_ = lean_array_fget_borrowed(v_args_1980_, v_a_1985_);
v___x_2031_ = lean_unbox(v_a_2027_);
lean_dec(v_a_2027_);
if (v___x_2031_ == 0)
{
lean_object* v___x_2032_; 
lean_inc(v_a_2025_);
v___x_2032_ = l_Lean_Meta_isClass_x3f(v_a_2025_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2164_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2035_ = v___x_2032_;
v_isShared_2036_ = v_isSharedCheck_2164_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_a_2033_);
lean_dec(v___x_2032_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2164_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
if (lean_obj_tag(v_a_2033_) == 0)
{
lean_object* v_options_2037_; lean_object* v___x_2038_; uint8_t v___x_2039_; 
lean_del_object(v___x_2035_);
v_options_2037_ = lean_ctor_get(v___y_1989_, 2);
v___x_2038_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2039_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2037_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v___x_2040_; 
lean_dec(v_a_2025_);
lean_inc(v___x_2030_);
v___x_2040_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2020_, v___x_2030_, v___y_1988_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref(v___x_2040_);
v_a_1993_ = v___x_2028_;
goto v___jp_1992_;
}
else
{
lean_dec(v_a_1985_);
return v___x_2040_;
}
}
else
{
lean_object* v___x_2041_; 
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___x_2030_);
v___x_2041_ = lean_infer_type(v___x_2030_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref(v___x_2041_);
lean_inc(v_a_2025_);
v___x_2043_ = l_Lean_Meta_isExprDefEq(v_a_2025_, v_a_2042_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2043_) == 0)
{
lean_object* v_a_2044_; uint8_t v___x_2045_; 
v_a_2044_ = lean_ctor_get(v___x_2043_, 0);
lean_inc(v_a_2044_);
lean_dec_ref(v___x_2043_);
v___x_2045_ = lean_unbox(v_a_2044_);
lean_dec(v_a_2044_);
if (v___x_2045_ == 0)
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2046_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2047_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2046_, v___y_1990_);
if (lean_obj_tag(v___x_2047_) == 0)
{
lean_object* v_a_2048_; lean_object* v___x_2049_; 
v_a_2048_ = lean_ctor_get(v___x_2047_, 0);
lean_inc_n(v_a_2048_, 2);
lean_dec_ref(v___x_2047_);
lean_inc(v___x_2030_);
v___x_2049_ = l_Lean_Meta_mkAuxDefinition(v_a_2048_, v_a_2025_, v___x_2030_, v___x_1984_, v___x_1984_, v___x_2017_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2049_) == 0)
{
lean_object* v_a_2050_; lean_object* v___x_2051_; 
v_a_2050_ = lean_ctor_get(v___x_2049_, 0);
lean_inc(v_a_2050_);
lean_dec_ref(v___x_2049_);
v___x_2051_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2020_, v_a_2050_, v___y_1988_);
if (lean_obj_tag(v___x_2051_) == 0)
{
uint8_t v___x_2052_; lean_object* v___x_2053_; 
lean_dec_ref(v___x_2051_);
v___x_2052_ = 0;
lean_inc(v_a_2048_);
v___x_2053_ = l_Lean_Meta_setInlineAttribute(v_a_2048_, v___x_2052_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2053_) == 0)
{
lean_dec_ref(v___x_2053_);
if (v_isMeta_1983_ == 0)
{
lean_object* v___x_2054_; 
v___x_2054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2048_, v___x_2028_, v_compile_1981_, v_logCompileErrors_1982_, v___x_2028_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2054_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2055_; lean_object* v_env_2056_; lean_object* v_nextMacroScope_2057_; lean_object* v_ngen_2058_; lean_object* v_auxDeclNGen_2059_; lean_object* v_traceState_2060_; lean_object* v_messages_2061_; lean_object* v_infoState_2062_; lean_object* v_snapshotTasks_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2089_; 
v___x_2055_ = lean_st_ref_take(v___y_1990_);
v_env_2056_ = lean_ctor_get(v___x_2055_, 0);
v_nextMacroScope_2057_ = lean_ctor_get(v___x_2055_, 1);
v_ngen_2058_ = lean_ctor_get(v___x_2055_, 2);
v_auxDeclNGen_2059_ = lean_ctor_get(v___x_2055_, 3);
v_traceState_2060_ = lean_ctor_get(v___x_2055_, 4);
v_messages_2061_ = lean_ctor_get(v___x_2055_, 6);
v_infoState_2062_ = lean_ctor_get(v___x_2055_, 7);
v_snapshotTasks_2063_ = lean_ctor_get(v___x_2055_, 8);
v_isSharedCheck_2089_ = !lean_is_exclusive(v___x_2055_);
if (v_isSharedCheck_2089_ == 0)
{
lean_object* v_unused_2090_; 
v_unused_2090_ = lean_ctor_get(v___x_2055_, 5);
lean_dec(v_unused_2090_);
v___x_2065_ = v___x_2055_;
v_isShared_2066_ = v_isSharedCheck_2089_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_snapshotTasks_2063_);
lean_inc(v_infoState_2062_);
lean_inc(v_messages_2061_);
lean_inc(v_traceState_2060_);
lean_inc(v_auxDeclNGen_2059_);
lean_inc(v_ngen_2058_);
lean_inc(v_nextMacroScope_2057_);
lean_inc(v_env_2056_);
lean_dec(v___x_2055_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2089_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2070_; 
lean_inc(v_a_2048_);
v___x_2067_ = l_Lean_markMeta(v_env_2056_, v_a_2048_);
v___x_2068_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2066_ == 0)
{
lean_ctor_set(v___x_2065_, 5, v___x_2068_);
lean_ctor_set(v___x_2065_, 0, v___x_2067_);
v___x_2070_ = v___x_2065_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2088_; 
v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2067_);
lean_ctor_set(v_reuseFailAlloc_2088_, 1, v_nextMacroScope_2057_);
lean_ctor_set(v_reuseFailAlloc_2088_, 2, v_ngen_2058_);
lean_ctor_set(v_reuseFailAlloc_2088_, 3, v_auxDeclNGen_2059_);
lean_ctor_set(v_reuseFailAlloc_2088_, 4, v_traceState_2060_);
lean_ctor_set(v_reuseFailAlloc_2088_, 5, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2088_, 6, v_messages_2061_);
lean_ctor_set(v_reuseFailAlloc_2088_, 7, v_infoState_2062_);
lean_ctor_set(v_reuseFailAlloc_2088_, 8, v_snapshotTasks_2063_);
v___x_2070_ = v_reuseFailAlloc_2088_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v_mctx_2073_; lean_object* v_zetaDeltaFVarIds_2074_; lean_object* v_postponed_2075_; lean_object* v_diag_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2086_; 
v___x_2071_ = lean_st_ref_set(v___y_1990_, v___x_2070_);
v___x_2072_ = lean_st_ref_take(v___y_1988_);
v_mctx_2073_ = lean_ctor_get(v___x_2072_, 0);
v_zetaDeltaFVarIds_2074_ = lean_ctor_get(v___x_2072_, 2);
v_postponed_2075_ = lean_ctor_get(v___x_2072_, 3);
v_diag_2076_ = lean_ctor_get(v___x_2072_, 4);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2086_ == 0)
{
lean_object* v_unused_2087_; 
v_unused_2087_ = lean_ctor_get(v___x_2072_, 1);
lean_dec(v_unused_2087_);
v___x_2078_ = v___x_2072_;
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_diag_2076_);
lean_inc(v_postponed_2075_);
lean_inc(v_zetaDeltaFVarIds_2074_);
lean_inc(v_mctx_2073_);
lean_dec(v___x_2072_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2086_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v___x_2082_; 
v___x_2080_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 1, v___x_2080_);
v___x_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_mctx_2073_);
lean_ctor_set(v_reuseFailAlloc_2085_, 1, v___x_2080_);
lean_ctor_set(v_reuseFailAlloc_2085_, 2, v_zetaDeltaFVarIds_2074_);
lean_ctor_set(v_reuseFailAlloc_2085_, 3, v_postponed_2075_);
lean_ctor_set(v_reuseFailAlloc_2085_, 4, v_diag_2076_);
v___x_2082_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = lean_st_ref_set(v___y_1988_, v___x_2082_);
v___x_2084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2048_, v___x_2028_, v_compile_1981_, v_logCompileErrors_1982_, v___x_2028_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2084_;
goto v___jp_1997_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2048_);
lean_dec(v_a_1985_);
return v___x_2053_;
}
}
else
{
lean_dec(v_a_2048_);
lean_dec(v_a_1985_);
return v___x_2051_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_dec(v_a_2048_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2091_ = lean_ctor_get(v___x_2049_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2049_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2049_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2049_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2099_ = lean_ctor_get(v___x_2047_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2047_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2047_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2047_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v___x_2107_; 
lean_dec(v_a_2025_);
lean_inc(v___x_2030_);
v___x_2107_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2020_, v___x_2030_, v___y_1988_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_dec_ref(v___x_2107_);
v_a_1993_ = v___x_2028_;
goto v___jp_1992_;
}
else
{
lean_dec(v_a_1985_);
return v___x_2107_;
}
}
}
else
{
lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2108_ = lean_ctor_get(v___x_2043_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2043_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2043_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_dec(v___x_2043_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2116_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2041_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2041_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
v___x_2121_ = v___x_2118_;
goto v_reusejp_2120_;
}
else
{
lean_object* v_reuseFailAlloc_2122_; 
v_reuseFailAlloc_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2122_, 0, v_a_2116_);
v___x_2121_ = v_reuseFailAlloc_2122_;
goto v_reusejp_2120_;
}
v_reusejp_2120_:
{
return v___x_2121_;
}
}
}
}
}
else
{
lean_object* v_options_2124_; lean_object* v_inheritedTraceOptions_2125_; lean_object* v_a_2127_; lean_object* v___y_2130_; uint8_t v___y_2131_; lean_object* v_a_2136_; lean_object* v___y_2140_; lean_object* v___x_2144_; uint8_t v___x_2145_; 
lean_dec_ref(v_a_2033_);
v_options_2124_ = lean_ctor_get(v___y_1989_, 2);
v_inheritedTraceOptions_2125_ = lean_ctor_get(v___y_1989_, 13);
v___x_2144_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2145_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2124_, v___x_2144_);
if (v___x_2145_ == 0)
{
lean_object* v___x_2146_; 
lean_del_object(v___x_2035_);
lean_inc(v___x_2030_);
v___x_2146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2030_, v_a_2025_, v_compile_1981_, v_logCompileErrors_1982_, v_isMeta_1983_, v___x_2020_, v___x_2028_, v___x_2028_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2146_;
goto v___jp_1997_;
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = lean_box(0);
lean_inc(v_a_2025_);
v___x_2148_ = l_Lean_Meta_trySynthInstance(v_a_2025_, v___x_2147_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2148_) == 0)
{
lean_object* v_a_2149_; 
v_a_2149_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2149_);
lean_dec_ref(v___x_2148_);
if (lean_obj_tag(v_a_2149_) == 1)
{
lean_object* v_a_2150_; uint8_t v_hasTrace_2151_; 
v_a_2150_ = lean_ctor_get(v_a_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v_a_2149_);
v_hasTrace_2151_ = lean_ctor_get_uint8(v_options_2124_, sizeof(void*)*1);
if (v_hasTrace_2151_ == 0)
{
goto v___jp_2152_;
}
else
{
lean_object* v___x_2154_; uint8_t v___x_2155_; 
v___x_2154_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2125_, v_options_2124_, v___x_2154_);
if (v___x_2155_ == 0)
{
goto v___jp_2152_;
}
else
{
lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2156_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_2150_);
v___x_2157_ = l_Lean_MessageData_ofExpr(v_a_2150_);
v___x_2158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2156_);
lean_ctor_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2029_, v___x_2158_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2161_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2160_);
lean_dec_ref(v___x_2159_);
lean_inc(v___x_2020_);
v___x_2161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2020_, v_a_2150_, v_a_2160_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_2140_ = v___x_2161_;
goto v___jp_2139_;
}
else
{
lean_object* v_a_2162_; 
lean_dec(v_a_2150_);
v_a_2162_ = lean_ctor_get(v___x_2159_, 0);
lean_inc(v_a_2162_);
lean_dec_ref(v___x_2159_);
v_a_2136_ = v_a_2162_;
goto v___jp_2135_;
}
}
}
v___jp_2152_:
{
lean_object* v___x_2153_; 
lean_inc(v___x_2020_);
v___x_2153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2020_, v_a_2150_, v___x_2028_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_2140_ = v___x_2153_;
goto v___jp_2139_;
}
}
else
{
lean_dec(v_a_2149_);
lean_del_object(v___x_2035_);
v_a_2127_ = v___x_2028_;
goto v___jp_2126_;
}
}
else
{
lean_object* v_a_2163_; 
v_a_2163_ = lean_ctor_get(v___x_2148_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2148_);
v_a_2136_ = v_a_2163_;
goto v___jp_2135_;
}
}
v___jp_2126_:
{
lean_object* v___x_2128_; 
lean_inc(v___x_2030_);
v___x_2128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2030_, v_a_2025_, v_compile_1981_, v_logCompileErrors_1982_, v_isMeta_1983_, v___x_2020_, v___x_2028_, v_a_2127_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2128_;
goto v___jp_1997_;
}
v___jp_2129_:
{
if (v___y_2131_ == 0)
{
lean_dec_ref(v___y_2130_);
lean_del_object(v___x_2035_);
v_a_2127_ = v___x_2028_;
goto v___jp_2126_;
}
else
{
lean_object* v___x_2133_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set_tag(v___x_2035_, 1);
lean_ctor_set(v___x_2035_, 0, v___y_2130_);
v___x_2133_ = v___x_2035_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v___y_2130_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
v___jp_2135_:
{
uint8_t v___x_2137_; 
v___x_2137_ = l_Lean_Exception_isInterrupt(v_a_2136_);
if (v___x_2137_ == 0)
{
uint8_t v___x_2138_; 
lean_inc_ref(v_a_2136_);
v___x_2138_ = l_Lean_Exception_isRuntime(v_a_2136_);
v___y_2130_ = v_a_2136_;
v___y_2131_ = v___x_2138_;
goto v___jp_2129_;
}
else
{
v___y_2130_ = v_a_2136_;
v___y_2131_ = v___x_2137_;
goto v___jp_2129_;
}
}
v___jp_2139_:
{
if (lean_obj_tag(v___y_2140_) == 0)
{
lean_object* v_a_2141_; 
lean_del_object(v___x_2035_);
v_a_2141_ = lean_ctor_get(v___y_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref(v___y_2140_);
if (lean_obj_tag(v_a_2141_) == 0)
{
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
v_a_1993_ = v___x_2028_;
goto v___jp_1992_;
}
else
{
lean_object* v_a_2142_; 
v_a_2142_ = lean_ctor_get(v_a_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v_a_2141_);
v_a_2127_ = v_a_2142_;
goto v___jp_2126_;
}
}
else
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v___y_2140_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v___y_2140_);
v_a_2136_ = v_a_2143_;
goto v___jp_2135_;
}
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2165_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2032_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2032_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_object* v___x_2173_; 
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1989_);
lean_inc(v___y_1988_);
lean_inc_ref(v___y_1987_);
lean_inc(v___x_2030_);
v___x_2173_ = lean_infer_type(v___x_2030_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; lean_object* v___x_2175_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc_n(v_a_2174_, 2);
lean_dec_ref(v___x_2173_);
lean_inc(v_a_2025_);
v___x_2175_ = l_Lean_Meta_isExprDefEq(v_a_2025_, v_a_2174_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; uint8_t v___x_2177_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = lean_unbox(v_a_2176_);
lean_dec(v_a_2176_);
if (v___x_2177_ == 0)
{
lean_object* v_options_2178_; lean_object* v_inheritedTraceOptions_2179_; uint8_t v_hasTrace_2180_; 
v_options_2178_ = lean_ctor_get(v___y_1989_, 2);
v_inheritedTraceOptions_2179_ = lean_ctor_get(v___y_1989_, 13);
v_hasTrace_2180_ = lean_ctor_get_uint8(v_options_2178_, sizeof(void*)*1);
if (v_hasTrace_2180_ == 0)
{
lean_dec(v_a_2174_);
goto v___jp_2181_;
}
else
{
lean_object* v___x_2183_; uint8_t v___x_2184_; 
v___x_2183_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2179_, v_options_2178_, v___x_2183_);
if (v___x_2184_ == 0)
{
lean_dec(v_a_2174_);
goto v___jp_2181_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2185_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_1985_);
v___x_2186_ = l_Nat_reprFast(v_a_1985_);
v___x_2187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
v___x_2188_ = l_Lean_MessageData_ofFormat(v___x_2187_);
v___x_2189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2185_);
lean_ctor_set(v___x_2189_, 1, v___x_2188_);
v___x_2190_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_2191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2191_, 0, v___x_2189_);
lean_ctor_set(v___x_2191_, 1, v___x_2190_);
lean_inc(v_a_2025_);
v___x_2192_ = l_Lean_MessageData_ofExpr(v_a_2025_);
v___x_2193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2191_);
lean_ctor_set(v___x_2193_, 1, v___x_2192_);
v___x_2194_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_2195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2193_);
lean_ctor_set(v___x_2195_, 1, v___x_2194_);
v___x_2196_ = l_Lean_MessageData_ofExpr(v_a_2174_);
v___x_2197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2197_, 0, v___x_2195_);
lean_ctor_set(v___x_2197_, 1, v___x_2196_);
v___x_2198_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_2199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2197_);
lean_ctor_set(v___x_2199_, 1, v___x_2198_);
lean_inc(v___x_2030_);
v___x_2200_ = l_Lean_MessageData_ofExpr(v___x_2030_);
v___x_2201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2199_);
lean_ctor_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2029_, v___x_2201_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
if (lean_obj_tag(v___x_2202_) == 0)
{
lean_object* v_a_2203_; lean_object* v___x_2204_; 
v_a_2203_ = lean_ctor_get(v___x_2202_, 0);
lean_inc(v_a_2203_);
lean_dec_ref(v___x_2202_);
lean_inc(v___x_2030_);
v___x_2204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2025_, v___x_2030_, v___x_2017_, v___x_2020_, v___x_2028_, v_a_2203_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2204_;
goto v___jp_1997_;
}
else
{
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
return v___x_2202_;
}
}
}
v___jp_2181_:
{
lean_object* v___x_2182_; 
lean_inc(v___x_2030_);
v___x_2182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2025_, v___x_2030_, v___x_2017_, v___x_2020_, v___x_2028_, v___x_2028_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
v___y_1998_ = v___x_2182_;
goto v___jp_1997_;
}
}
else
{
lean_object* v___x_2205_; 
lean_dec(v_a_2174_);
lean_dec(v_a_2025_);
lean_inc(v___x_2030_);
v___x_2205_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2020_, v___x_2030_, v___y_1988_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_dec_ref(v___x_2205_);
v_a_1993_ = v___x_2028_;
goto v___jp_1992_;
}
else
{
lean_dec(v_a_1985_);
return v___x_2205_;
}
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_a_2174_);
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2206_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2175_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2175_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2214_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2173_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2173_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec(v_a_2025_);
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2222_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2026_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2026_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2230_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2024_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2024_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v___x_2020_);
lean_dec(v_a_1985_);
v_a_2238_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2021_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2021_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
v___jp_1992_:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_unsigned_to_nat(1u);
v___x_1995_ = lean_nat_add(v_a_1985_, v___x_1994_);
lean_dec(v_a_1985_);
v___x_1996_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_1978_, v_fst_1979_, v_args_1980_, v_compile_1981_, v_logCompileErrors_1982_, v_isMeta_1983_, v___x_1984_, v___x_1995_, v_a_1993_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_);
return v___x_1996_;
}
v___jp_1997_:
{
if (lean_obj_tag(v___y_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2008_; 
v_a_1999_ = lean_ctor_get(v___y_1998_, 0);
v_isSharedCheck_2008_ = !lean_is_exclusive(v___y_1998_);
if (v_isSharedCheck_2008_ == 0)
{
v___x_2001_ = v___y_1998_;
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_a_1999_);
lean_dec(v___y_1998_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2008_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
if (lean_obj_tag(v_a_1999_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2005_; 
lean_dec(v_a_1985_);
v_a_2003_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v_a_1999_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 0, v_a_2003_);
v___x_2005_ = v___x_2001_;
goto v_reusejp_2004_;
}
else
{
lean_object* v_reuseFailAlloc_2006_; 
v_reuseFailAlloc_2006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2006_, 0, v_a_2003_);
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
lean_object* v_a_2007_; 
lean_del_object(v___x_2001_);
v_a_2007_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v_a_1999_);
v_a_1993_ = v_a_2007_;
goto v___jp_1992_;
}
}
}
else
{
lean_object* v_a_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2016_; 
lean_dec(v_a_1985_);
v_a_2009_ = lean_ctor_get(v___y_1998_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___y_1998_);
if (v_isSharedCheck_2016_ == 0)
{
v___x_2011_ = v___y_1998_;
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_a_2009_);
lean_dec(v___y_1998_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2016_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v___x_2014_; 
if (v_isShared_2012_ == 0)
{
v___x_2014_ = v___x_2011_;
goto v_reusejp_2013_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_a_2009_);
v___x_2014_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2013_;
}
v_reusejp_2013_:
{
return v___x_2014_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8(void){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; 
v___x_2247_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__7));
v___x_2248_ = l_Lean_stringToMessageData(v___x_2247_);
return v___x_2248_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2250_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__9));
v___x_2251_ = l_Lean_stringToMessageData(v___x_2250_);
return v___x_2251_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; 
v___x_2253_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__11));
v___x_2254_ = l_Lean_stringToMessageData(v___x_2253_);
return v___x_2254_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14(void){
_start:
{
lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2256_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__13));
v___x_2257_ = l_Lean_stringToMessageData(v___x_2256_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(lean_object* v_a_2258_, lean_object* v_expectedType_2259_, uint8_t v___x_2260_, uint8_t v_compile_2261_, uint8_t v_logCompileErrors_2262_, uint8_t v_isMeta_2263_, lean_object* v_x_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_){
_start:
{
lean_object* v___y_2273_; lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2295_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; 
if (lean_obj_tag(v_x_2264_) == 5)
{
lean_object* v_fn_2311_; lean_object* v_arg_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
v_fn_2311_ = lean_ctor_get(v_x_2264_, 0);
lean_inc_ref(v_fn_2311_);
v_arg_2312_ = lean_ctor_get(v_x_2264_, 1);
lean_inc_ref(v_arg_2312_);
lean_dec_ref(v_x_2264_);
v___x_2313_ = lean_array_set(v_x_2265_, v_x_2266_, v_arg_2312_);
v___x_2314_ = lean_unsigned_to_nat(1u);
v___x_2315_ = lean_nat_sub(v_x_2266_, v___x_2314_);
lean_dec(v_x_2266_);
v_x_2264_ = v_fn_2311_;
v_x_2265_ = v___x_2313_;
v_x_2266_ = v___x_2315_;
goto _start;
}
else
{
uint8_t v___x_2317_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v_options_2322_; lean_object* v___y_2323_; lean_object* v_cls_2389_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___x_2412_; 
lean_dec(v_x_2266_);
v___x_2317_ = 1;
v_cls_2389_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2412_ = l_Lean_Expr_constName_x3f(v_x_2264_);
if (lean_obj_tag(v___x_2412_) == 0)
{
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
v___y_2391_ = v___y_2267_;
v___y_2392_ = v___y_2268_;
v___y_2393_ = v___y_2269_;
v___y_2394_ = v___y_2270_;
goto v___jp_2390_;
}
else
{
lean_object* v_val_2413_; lean_object* v___x_2414_; 
v_val_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc(v_val_2413_);
lean_dec_ref(v___x_2412_);
v___x_2414_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_2413_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref(v___x_2414_);
if (lean_obj_tag(v_a_2415_) == 6)
{
lean_object* v_val_2416_; lean_object* v___x_2417_; 
lean_dec_ref(v_a_2258_);
v_val_2416_ = lean_ctor_get(v_a_2415_, 0);
lean_inc_ref(v_val_2416_);
lean_dec_ref(v_a_2415_);
lean_inc(v___y_2270_);
lean_inc_ref(v___y_2269_);
lean_inc(v___y_2268_);
lean_inc_ref(v___y_2267_);
lean_inc_ref(v_x_2264_);
v___x_2417_ = lean_infer_type(v_x_2264_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; uint8_t v___x_2419_; lean_object* v___x_2420_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = 0;
v___x_2420_ = l_Lean_Meta_forallMetaTelescope(v_a_2418_, v___x_2419_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v_snd_2422_; lean_object* v_fst_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2522_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref(v___x_2420_);
v_snd_2422_ = lean_ctor_get(v_a_2421_, 1);
v_fst_2423_ = lean_ctor_get(v_a_2421_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_a_2421_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2425_ = v_a_2421_;
v_isShared_2426_ = v_isSharedCheck_2522_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_snd_2422_);
lean_inc(v_fst_2423_);
lean_dec(v_a_2421_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2522_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v_snd_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2520_; 
v_snd_2427_ = lean_ctor_get(v_snd_2422_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_snd_2422_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v_snd_2422_, 0);
lean_dec(v_unused_2521_);
v___x_2429_ = v_snd_2422_;
v_isShared_2430_ = v_isSharedCheck_2520_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snd_2427_);
lean_dec(v_snd_2422_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2520_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2431_; lean_object* v___y_2433_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___x_2468_; uint8_t v___x_2469_; 
v___x_2431_ = lean_array_get_size(v_x_2265_);
v___x_2468_ = lean_array_get_size(v_fst_2423_);
v___x_2469_ = lean_nat_dec_eq(v___x_2431_, v___x_2468_);
if (v___x_2469_ == 0)
{
lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2473_; 
lean_dec(v_snd_2427_);
lean_dec(v_fst_2423_);
lean_dec_ref(v_val_2416_);
lean_dec_ref(v_expectedType_2259_);
v___x_2470_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_2471_ = l_Lean_MessageData_ofExpr(v_x_2264_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 7);
lean_ctor_set(v___x_2429_, 1, v___x_2471_);
lean_ctor_set(v___x_2429_, 0, v___x_2470_);
v___x_2473_ = v___x_2429_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2470_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2471_);
v___x_2473_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
lean_object* v___x_2474_; lean_object* v___x_2476_; 
v___x_2474_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_2426_ == 0)
{
lean_ctor_set_tag(v___x_2425_, 7);
lean_ctor_set(v___x_2425_, 1, v___x_2474_);
lean_ctor_set(v___x_2425_, 0, v___x_2473_);
v___x_2476_ = v___x_2425_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v___x_2473_);
lean_ctor_set(v_reuseFailAlloc_2483_, 1, v___x_2474_);
v___x_2476_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2477_ = lean_array_to_list(v_x_2265_);
v___x_2478_ = lean_box(0);
v___x_2479_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_2477_, v___x_2478_);
v___x_2480_ = l_Lean_MessageData_ofList(v___x_2479_);
v___x_2481_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2481_, 0, v___x_2476_);
lean_ctor_set(v___x_2481_, 1, v___x_2480_);
v___x_2482_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2481_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
return v___x_2482_;
}
}
}
else
{
lean_object* v___x_2485_; 
lean_inc_ref(v_expectedType_2259_);
v___x_2485_ = l_Lean_Meta_isExprDefEq(v_expectedType_2259_, v_snd_2427_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; uint8_t v___x_2487_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref(v___x_2485_);
v___x_2487_ = lean_unbox(v_a_2486_);
lean_dec(v_a_2486_);
if (v___x_2487_ == 0)
{
lean_object* v_toConstantVal_2488_; lean_object* v_name_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2493_; 
lean_dec(v_fst_2423_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
v_toConstantVal_2488_ = lean_ctor_get(v_val_2416_, 0);
lean_inc_ref(v_toConstantVal_2488_);
lean_dec_ref(v_val_2416_);
v_name_2489_ = lean_ctor_get(v_toConstantVal_2488_, 0);
lean_inc(v_name_2489_);
lean_dec_ref(v_toConstantVal_2488_);
v___x_2490_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_2491_ = l_Lean_MessageData_ofExpr(v_expectedType_2259_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set_tag(v___x_2429_, 7);
lean_ctor_set(v___x_2429_, 1, v___x_2491_);
lean_ctor_set(v___x_2429_, 0, v___x_2490_);
v___x_2493_ = v___x_2429_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2491_);
v___x_2493_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
lean_object* v___x_2494_; lean_object* v___x_2496_; 
v___x_2494_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_2426_ == 0)
{
lean_ctor_set_tag(v___x_2425_, 7);
lean_ctor_set(v___x_2425_, 1, v___x_2494_);
lean_ctor_set(v___x_2425_, 0, v___x_2493_);
v___x_2496_ = v___x_2425_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2493_);
lean_ctor_set(v_reuseFailAlloc_2510_, 1, v___x_2494_);
v___x_2496_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
v___x_2497_ = l_Lean_MessageData_ofConstName(v_name_2489_, v___x_2260_);
v___x_2498_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2496_);
lean_ctor_set(v___x_2498_, 1, v___x_2497_);
v___x_2499_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_2500_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2500_, 0, v___x_2498_);
lean_ctor_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2500_, v___y_2267_, v___y_2268_, v___y_2269_, v___y_2270_);
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2501_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2501_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
}
}
else
{
lean_del_object(v___x_2429_);
lean_del_object(v___x_2425_);
lean_dec_ref(v_expectedType_2259_);
v___y_2433_ = v___y_2267_;
v___y_2434_ = v___y_2268_;
v___y_2435_ = v___y_2269_;
v___y_2436_ = v___y_2270_;
goto v___jp_2432_;
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_del_object(v___x_2429_);
lean_del_object(v___x_2425_);
lean_dec(v_fst_2423_);
lean_dec_ref(v_val_2416_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
lean_dec_ref(v_expectedType_2259_);
v_a_2512_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2485_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2485_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
v___jp_2432_:
{
lean_object* v_numParams_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; 
v_numParams_2437_ = lean_ctor_get(v_val_2416_, 3);
lean_inc(v_numParams_2437_);
lean_dec_ref(v_val_2416_);
v___x_2438_ = lean_box(0);
v___x_2439_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2431_, v_fst_2423_, v_x_2265_, v_compile_2261_, v_logCompileErrors_2262_, v_isMeta_2263_, v___x_2260_, v_numParams_2437_, v___x_2438_, v___y_2433_, v___y_2434_, v___y_2435_, v___y_2436_);
lean_dec_ref(v_x_2265_);
if (lean_obj_tag(v___x_2439_) == 0)
{
size_t v_sz_2440_; size_t v___x_2441_; lean_object* v___x_2442_; 
lean_dec_ref(v___x_2439_);
v_sz_2440_ = lean_array_size(v_fst_2423_);
v___x_2441_ = ((size_t)0ULL);
v___x_2442_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_2440_, v___x_2441_, v_fst_2423_, v___y_2434_);
if (lean_obj_tag(v___x_2442_) == 0)
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2451_; 
v_a_2443_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2445_ = v___x_2442_;
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2442_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2451_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2447_; lean_object* v___x_2449_; 
v___x_2447_ = l_Lean_mkAppN(v_x_2264_, v_a_2443_);
lean_dec(v_a_2443_);
if (v_isShared_2446_ == 0)
{
lean_ctor_set(v___x_2445_, 0, v___x_2447_);
v___x_2449_ = v___x_2445_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v___x_2447_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec_ref(v_x_2264_);
v_a_2452_ = lean_ctor_get(v___x_2442_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2442_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2442_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2442_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v_fst_2423_);
lean_dec_ref(v_x_2264_);
v_a_2460_ = lean_ctor_get(v___x_2439_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2439_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2439_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2439_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec_ref(v_val_2416_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
lean_dec_ref(v_expectedType_2259_);
v_a_2523_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2420_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2420_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
v___x_2528_ = v_reuseFailAlloc_2529_;
goto v_reusejp_2527_;
}
v_reusejp_2527_:
{
return v___x_2528_;
}
}
}
}
else
{
lean_dec_ref(v_val_2416_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
lean_dec_ref(v_expectedType_2259_);
return v___x_2417_;
}
}
else
{
lean_dec(v_a_2415_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
v___y_2391_ = v___y_2267_;
v___y_2392_ = v___y_2268_;
v___y_2393_ = v___y_2269_;
v___y_2394_ = v___y_2270_;
goto v___jp_2390_;
}
}
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_x_2264_);
lean_dec_ref(v_expectedType_2259_);
lean_dec_ref(v_a_2258_);
v_a_2531_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2414_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2414_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
v___jp_2318_:
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2325_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2322_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; 
lean_dec_ref(v_expectedType_2259_);
v___x_2326_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2326_, 0, v_a_2258_);
return v___x_2326_;
}
else
{
lean_object* v___x_2327_; 
lean_inc(v___y_2323_);
lean_inc_ref(v___y_2321_);
lean_inc(v___y_2320_);
lean_inc_ref(v___y_2319_);
lean_inc_ref(v_a_2258_);
v___x_2327_ = lean_infer_type(v_a_2258_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2323_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2329_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_a_2328_);
lean_dec_ref(v___x_2327_);
lean_inc_ref(v_expectedType_2259_);
v___x_2329_ = l_Lean_Meta_isExprDefEq(v_expectedType_2259_, v_a_2328_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2323_);
if (lean_obj_tag(v___x_2329_) == 0)
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2380_; 
v_a_2330_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2332_ = v___x_2329_;
v_isShared_2333_ = v_isSharedCheck_2380_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2329_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2380_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
uint8_t v___x_2334_; 
v___x_2334_ = lean_unbox(v_a_2330_);
lean_dec(v_a_2330_);
if (v___x_2334_ == 0)
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v_a_2337_; lean_object* v___x_2338_; 
lean_del_object(v___x_2332_);
v___x_2335_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2336_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2335_, v___y_2323_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
lean_inc_n(v_a_2337_, 2);
lean_dec_ref(v___x_2336_);
v___x_2338_ = l_Lean_Meta_mkAuxDefinition(v_a_2337_, v_expectedType_2259_, v_a_2258_, v___x_2260_, v___x_2260_, v___x_2317_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2323_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; uint8_t v___x_2340_; lean_object* v___x_2341_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = 3;
lean_inc(v_a_2337_);
v___x_2341_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_2337_, v___x_2340_, v___y_2320_, v___y_2323_);
lean_dec_ref(v___x_2341_);
if (v_isMeta_2263_ == 0)
{
v___y_2295_ = v_a_2339_;
v___y_2296_ = v_a_2337_;
v___y_2297_ = v___y_2321_;
v___y_2298_ = v___y_2323_;
goto v___jp_2294_;
}
else
{
lean_object* v___x_2342_; lean_object* v_env_2343_; lean_object* v_nextMacroScope_2344_; lean_object* v_ngen_2345_; lean_object* v_auxDeclNGen_2346_; lean_object* v_traceState_2347_; lean_object* v_messages_2348_; lean_object* v_infoState_2349_; lean_object* v_snapshotTasks_2350_; lean_object* v___x_2352_; uint8_t v_isShared_2353_; uint8_t v_isSharedCheck_2375_; 
v___x_2342_ = lean_st_ref_take(v___y_2323_);
v_env_2343_ = lean_ctor_get(v___x_2342_, 0);
v_nextMacroScope_2344_ = lean_ctor_get(v___x_2342_, 1);
v_ngen_2345_ = lean_ctor_get(v___x_2342_, 2);
v_auxDeclNGen_2346_ = lean_ctor_get(v___x_2342_, 3);
v_traceState_2347_ = lean_ctor_get(v___x_2342_, 4);
v_messages_2348_ = lean_ctor_get(v___x_2342_, 6);
v_infoState_2349_ = lean_ctor_get(v___x_2342_, 7);
v_snapshotTasks_2350_ = lean_ctor_get(v___x_2342_, 8);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2375_ == 0)
{
lean_object* v_unused_2376_; 
v_unused_2376_ = lean_ctor_get(v___x_2342_, 5);
lean_dec(v_unused_2376_);
v___x_2352_ = v___x_2342_;
v_isShared_2353_ = v_isSharedCheck_2375_;
goto v_resetjp_2351_;
}
else
{
lean_inc(v_snapshotTasks_2350_);
lean_inc(v_infoState_2349_);
lean_inc(v_messages_2348_);
lean_inc(v_traceState_2347_);
lean_inc(v_auxDeclNGen_2346_);
lean_inc(v_ngen_2345_);
lean_inc(v_nextMacroScope_2344_);
lean_inc(v_env_2343_);
lean_dec(v___x_2342_);
v___x_2352_ = lean_box(0);
v_isShared_2353_ = v_isSharedCheck_2375_;
goto v_resetjp_2351_;
}
v_resetjp_2351_:
{
lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2357_; 
lean_inc(v_a_2337_);
v___x_2354_ = l_Lean_markMeta(v_env_2343_, v_a_2337_);
v___x_2355_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2353_ == 0)
{
lean_ctor_set(v___x_2352_, 5, v___x_2355_);
lean_ctor_set(v___x_2352_, 0, v___x_2354_);
v___x_2357_ = v___x_2352_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v___x_2354_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_nextMacroScope_2344_);
lean_ctor_set(v_reuseFailAlloc_2374_, 2, v_ngen_2345_);
lean_ctor_set(v_reuseFailAlloc_2374_, 3, v_auxDeclNGen_2346_);
lean_ctor_set(v_reuseFailAlloc_2374_, 4, v_traceState_2347_);
lean_ctor_set(v_reuseFailAlloc_2374_, 5, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2374_, 6, v_messages_2348_);
lean_ctor_set(v_reuseFailAlloc_2374_, 7, v_infoState_2349_);
lean_ctor_set(v_reuseFailAlloc_2374_, 8, v_snapshotTasks_2350_);
v___x_2357_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v_mctx_2360_; lean_object* v_zetaDeltaFVarIds_2361_; lean_object* v_postponed_2362_; lean_object* v_diag_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2372_; 
v___x_2358_ = lean_st_ref_set(v___y_2323_, v___x_2357_);
v___x_2359_ = lean_st_ref_take(v___y_2320_);
v_mctx_2360_ = lean_ctor_get(v___x_2359_, 0);
v_zetaDeltaFVarIds_2361_ = lean_ctor_get(v___x_2359_, 2);
v_postponed_2362_ = lean_ctor_get(v___x_2359_, 3);
v_diag_2363_ = lean_ctor_get(v___x_2359_, 4);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2372_ == 0)
{
lean_object* v_unused_2373_; 
v_unused_2373_ = lean_ctor_get(v___x_2359_, 1);
lean_dec(v_unused_2373_);
v___x_2365_ = v___x_2359_;
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_diag_2363_);
lean_inc(v_postponed_2362_);
lean_inc(v_zetaDeltaFVarIds_2361_);
lean_inc(v_mctx_2360_);
lean_dec(v___x_2359_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2372_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2367_; lean_object* v___x_2369_; 
v___x_2367_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 1, v___x_2367_);
v___x_2369_ = v___x_2365_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_mctx_2360_);
lean_ctor_set(v_reuseFailAlloc_2371_, 1, v___x_2367_);
lean_ctor_set(v_reuseFailAlloc_2371_, 2, v_zetaDeltaFVarIds_2361_);
lean_ctor_set(v_reuseFailAlloc_2371_, 3, v_postponed_2362_);
lean_ctor_set(v_reuseFailAlloc_2371_, 4, v_diag_2363_);
v___x_2369_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
lean_object* v___x_2370_; 
v___x_2370_ = lean_st_ref_set(v___y_2320_, v___x_2369_);
v___y_2295_ = v_a_2339_;
v___y_2296_ = v_a_2337_;
v___y_2297_ = v___y_2321_;
v___y_2298_ = v___y_2323_;
goto v___jp_2294_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2337_);
return v___x_2338_;
}
}
else
{
lean_object* v___x_2378_; 
lean_dec_ref(v_expectedType_2259_);
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 0, v_a_2258_);
v___x_2378_ = v___x_2332_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2258_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v_expectedType_2259_);
lean_dec_ref(v_a_2258_);
v_a_2381_ = lean_ctor_get(v___x_2329_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2329_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2329_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2329_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2259_);
lean_dec_ref(v_a_2258_);
return v___x_2327_;
}
}
}
v___jp_2390_:
{
lean_object* v_options_2395_; uint8_t v_hasTrace_2396_; 
v_options_2395_ = lean_ctor_get(v___y_2393_, 2);
v_hasTrace_2396_ = lean_ctor_get_uint8(v_options_2395_, sizeof(void*)*1);
if (v_hasTrace_2396_ == 0)
{
v___y_2319_ = v___y_2391_;
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v_options_2322_ = v_options_2395_;
v___y_2323_ = v___y_2394_;
goto v___jp_2318_;
}
else
{
lean_object* v_inheritedTraceOptions_2397_; lean_object* v___x_2398_; uint8_t v___x_2399_; 
v_inheritedTraceOptions_2397_ = lean_ctor_get(v___y_2393_, 13);
v___x_2398_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2399_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2397_, v_options_2395_, v___x_2398_);
if (v___x_2399_ == 0)
{
v___y_2319_ = v___y_2391_;
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v_options_2322_ = v_options_2395_;
v___y_2323_ = v___y_2394_;
goto v___jp_2318_;
}
else
{
lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2400_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_2258_);
v___x_2401_ = l_Lean_MessageData_ofExpr(v_a_2258_);
v___x_2402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2400_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2389_, v___x_2402_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_dec_ref(v___x_2403_);
v___y_2319_ = v___y_2391_;
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v_options_2322_ = v_options_2395_;
v___y_2323_ = v___y_2394_;
goto v___jp_2318_;
}
else
{
lean_object* v_a_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2411_; 
lean_dec_ref(v_expectedType_2259_);
lean_dec_ref(v_a_2258_);
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2411_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2411_ == 0)
{
v___x_2406_ = v___x_2403_;
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_a_2404_);
lean_dec(v___x_2403_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2411_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2409_; 
if (v_isShared_2407_ == 0)
{
v___x_2409_ = v___x_2406_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v_a_2404_);
v___x_2409_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
return v___x_2409_;
}
}
}
}
}
}
}
v___jp_2272_:
{
lean_object* v___x_2277_; 
v___x_2277_ = l_Lean_enableRealizationsForConst(v___y_2274_, v___y_2275_, v___y_2276_);
if (lean_obj_tag(v___x_2277_) == 0)
{
lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2284_ == 0)
{
lean_object* v_unused_2285_; 
v_unused_2285_ = lean_ctor_get(v___x_2277_, 0);
lean_dec(v_unused_2285_);
v___x_2279_ = v___x_2277_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_dec(v___x_2277_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
lean_ctor_set(v___x_2279_, 0, v___y_2273_);
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v___y_2273_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec_ref(v___y_2273_);
v_a_2286_ = lean_ctor_get(v___x_2277_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2277_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2277_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2277_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
v___jp_2294_:
{
if (v_compile_2261_ == 0)
{
v___y_2273_ = v___y_2295_;
v___y_2274_ = v___y_2296_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2298_;
goto v___jp_2272_;
}
else
{
lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2299_ = lean_unsigned_to_nat(1u);
v___x_2300_ = lean_mk_empty_array_with_capacity(v___x_2299_);
lean_inc(v___y_2296_);
v___x_2301_ = lean_array_push(v___x_2300_, v___y_2296_);
v___x_2302_ = l_Lean_compileDecls(v___x_2301_, v_logCompileErrors_2262_, v___y_2297_, v___y_2298_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_dec_ref(v___x_2302_);
v___y_2273_ = v___y_2295_;
v___y_2274_ = v___y_2296_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2298_;
goto v___jp_2272_;
}
else
{
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2302_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v_a_2539_, lean_object* v_expectedType_2540_, uint8_t v___x_2541_, uint8_t v_compile_2542_, uint8_t v_logCompileErrors_2543_, uint8_t v_isMeta_2544_, lean_object* v_x_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v___y_2554_; lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2576_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; 
if (lean_obj_tag(v_x_2545_) == 5)
{
lean_object* v_fn_2592_; lean_object* v_arg_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v_fn_2592_ = lean_ctor_get(v_x_2545_, 0);
lean_inc_ref(v_fn_2592_);
v_arg_2593_ = lean_ctor_get(v_x_2545_, 1);
lean_inc_ref(v_arg_2593_);
lean_dec_ref(v_x_2545_);
v___x_2594_ = lean_array_set(v_x_2546_, v_x_2547_, v_arg_2593_);
v___x_2595_ = lean_unsigned_to_nat(1u);
v___x_2596_ = lean_nat_sub(v_x_2547_, v___x_2595_);
v___x_2597_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(v_a_2539_, v_expectedType_2540_, v___x_2541_, v_compile_2542_, v_logCompileErrors_2543_, v_isMeta_2544_, v_fn_2592_, v___x_2594_, v___x_2596_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2597_;
}
else
{
uint8_t v___x_2598_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v_options_2603_; lean_object* v___y_2604_; lean_object* v_cls_2670_; lean_object* v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___x_2693_; 
v___x_2598_ = 1;
v_cls_2670_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2693_ = l_Lean_Expr_constName_x3f(v_x_2545_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
v___y_2672_ = v___y_2548_;
v___y_2673_ = v___y_2549_;
v___y_2674_ = v___y_2550_;
v___y_2675_ = v___y_2551_;
goto v___jp_2671_;
}
else
{
lean_object* v_val_2694_; lean_object* v___x_2695_; 
v_val_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_val_2694_);
lean_dec_ref(v___x_2693_);
v___x_2695_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_2694_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref(v___x_2695_);
if (lean_obj_tag(v_a_2696_) == 6)
{
lean_object* v_val_2697_; lean_object* v___x_2698_; 
lean_dec_ref(v_a_2539_);
v_val_2697_ = lean_ctor_get(v_a_2696_, 0);
lean_inc_ref(v_val_2697_);
lean_dec_ref(v_a_2696_);
lean_inc(v___y_2551_);
lean_inc_ref(v___y_2550_);
lean_inc(v___y_2549_);
lean_inc_ref(v___y_2548_);
lean_inc_ref(v_x_2545_);
v___x_2698_ = lean_infer_type(v_x_2545_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; uint8_t v___x_2700_; lean_object* v___x_2701_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref(v___x_2698_);
v___x_2700_ = 0;
v___x_2701_ = l_Lean_Meta_forallMetaTelescope(v_a_2699_, v___x_2700_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v_snd_2703_; lean_object* v_fst_2704_; lean_object* v___x_2706_; uint8_t v_isShared_2707_; uint8_t v_isSharedCheck_2803_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref(v___x_2701_);
v_snd_2703_ = lean_ctor_get(v_a_2702_, 1);
v_fst_2704_ = lean_ctor_get(v_a_2702_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v_a_2702_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2706_ = v_a_2702_;
v_isShared_2707_ = v_isSharedCheck_2803_;
goto v_resetjp_2705_;
}
else
{
lean_inc(v_snd_2703_);
lean_inc(v_fst_2704_);
lean_dec(v_a_2702_);
v___x_2706_ = lean_box(0);
v_isShared_2707_ = v_isSharedCheck_2803_;
goto v_resetjp_2705_;
}
v_resetjp_2705_:
{
lean_object* v_snd_2708_; lean_object* v___x_2710_; uint8_t v_isShared_2711_; uint8_t v_isSharedCheck_2801_; 
v_snd_2708_ = lean_ctor_get(v_snd_2703_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_snd_2703_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; 
v_unused_2802_ = lean_ctor_get(v_snd_2703_, 0);
lean_dec(v_unused_2802_);
v___x_2710_ = v_snd_2703_;
v_isShared_2711_ = v_isSharedCheck_2801_;
goto v_resetjp_2709_;
}
else
{
lean_inc(v_snd_2708_);
lean_dec(v_snd_2703_);
v___x_2710_ = lean_box(0);
v_isShared_2711_ = v_isSharedCheck_2801_;
goto v_resetjp_2709_;
}
v_resetjp_2709_:
{
lean_object* v___x_2712_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___x_2749_; uint8_t v___x_2750_; 
v___x_2712_ = lean_array_get_size(v_x_2546_);
v___x_2749_ = lean_array_get_size(v_fst_2704_);
v___x_2750_ = lean_nat_dec_eq(v___x_2712_, v___x_2749_);
if (v___x_2750_ == 0)
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec(v_snd_2708_);
lean_dec(v_fst_2704_);
lean_dec_ref(v_val_2697_);
lean_dec_ref(v_expectedType_2540_);
v___x_2751_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_2752_ = l_Lean_MessageData_ofExpr(v_x_2545_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 7);
lean_ctor_set(v___x_2710_, 1, v___x_2752_);
lean_ctor_set(v___x_2710_, 0, v___x_2751_);
v___x_2754_ = v___x_2710_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2751_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2755_; lean_object* v___x_2757_; 
v___x_2755_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 7);
lean_ctor_set(v___x_2706_, 1, v___x_2755_);
lean_ctor_set(v___x_2706_, 0, v___x_2754_);
v___x_2757_ = v___x_2706_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2764_; 
v_reuseFailAlloc_2764_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2764_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2764_, 1, v___x_2755_);
v___x_2757_ = v_reuseFailAlloc_2764_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2758_ = lean_array_to_list(v_x_2546_);
v___x_2759_ = lean_box(0);
v___x_2760_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_2758_, v___x_2759_);
v___x_2761_ = l_Lean_MessageData_ofList(v___x_2760_);
v___x_2762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2762_, 0, v___x_2757_);
lean_ctor_set(v___x_2762_, 1, v___x_2761_);
v___x_2763_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2762_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
return v___x_2763_;
}
}
}
else
{
lean_object* v___x_2766_; 
lean_inc_ref(v_expectedType_2540_);
v___x_2766_ = l_Lean_Meta_isExprDefEq(v_expectedType_2540_, v_snd_2708_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
if (lean_obj_tag(v___x_2766_) == 0)
{
lean_object* v_a_2767_; uint8_t v___x_2768_; 
v_a_2767_ = lean_ctor_get(v___x_2766_, 0);
lean_inc(v_a_2767_);
lean_dec_ref(v___x_2766_);
v___x_2768_ = lean_unbox(v_a_2767_);
lean_dec(v_a_2767_);
if (v___x_2768_ == 0)
{
lean_object* v_toConstantVal_2769_; lean_object* v_name_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
lean_dec(v_fst_2704_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
v_toConstantVal_2769_ = lean_ctor_get(v_val_2697_, 0);
lean_inc_ref(v_toConstantVal_2769_);
lean_dec_ref(v_val_2697_);
v_name_2770_ = lean_ctor_get(v_toConstantVal_2769_, 0);
lean_inc(v_name_2770_);
lean_dec_ref(v_toConstantVal_2769_);
v___x_2771_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_2772_ = l_Lean_MessageData_ofExpr(v_expectedType_2540_);
if (v_isShared_2711_ == 0)
{
lean_ctor_set_tag(v___x_2710_, 7);
lean_ctor_set(v___x_2710_, 1, v___x_2772_);
lean_ctor_set(v___x_2710_, 0, v___x_2771_);
v___x_2774_ = v___x_2710_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2771_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
v___x_2775_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_2707_ == 0)
{
lean_ctor_set_tag(v___x_2706_, 7);
lean_ctor_set(v___x_2706_, 1, v___x_2775_);
lean_ctor_set(v___x_2706_, 0, v___x_2774_);
v___x_2777_ = v___x_2706_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2791_, 1, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
lean_object* v___x_2778_; lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v_a_2783_; lean_object* v___x_2785_; uint8_t v_isShared_2786_; uint8_t v_isSharedCheck_2790_; 
v___x_2778_ = l_Lean_MessageData_ofConstName(v_name_2770_, v___x_2541_);
v___x_2779_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2777_);
lean_ctor_set(v___x_2779_, 1, v___x_2778_);
v___x_2780_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_2781_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2781_, 0, v___x_2779_);
lean_ctor_set(v___x_2781_, 1, v___x_2780_);
v___x_2782_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2781_, v___y_2548_, v___y_2549_, v___y_2550_, v___y_2551_);
v_a_2783_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2790_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2790_ == 0)
{
v___x_2785_ = v___x_2782_;
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
else
{
lean_inc(v_a_2783_);
lean_dec(v___x_2782_);
v___x_2785_ = lean_box(0);
v_isShared_2786_ = v_isSharedCheck_2790_;
goto v_resetjp_2784_;
}
v_resetjp_2784_:
{
lean_object* v___x_2788_; 
if (v_isShared_2786_ == 0)
{
v___x_2788_ = v___x_2785_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_a_2783_);
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
else
{
lean_del_object(v___x_2710_);
lean_del_object(v___x_2706_);
lean_dec_ref(v_expectedType_2540_);
v___y_2714_ = v___y_2548_;
v___y_2715_ = v___y_2549_;
v___y_2716_ = v___y_2550_;
v___y_2717_ = v___y_2551_;
goto v___jp_2713_;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2710_);
lean_del_object(v___x_2706_);
lean_dec(v_fst_2704_);
lean_dec_ref(v_val_2697_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
lean_dec_ref(v_expectedType_2540_);
v_a_2793_ = lean_ctor_get(v___x_2766_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2766_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2766_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2766_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
v___jp_2713_:
{
lean_object* v_numParams_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; 
v_numParams_2718_ = lean_ctor_get(v_val_2697_, 3);
lean_inc(v_numParams_2718_);
lean_dec_ref(v_val_2697_);
v___x_2719_ = lean_box(0);
v___x_2720_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2712_, v_fst_2704_, v_x_2546_, v_compile_2542_, v_logCompileErrors_2543_, v_isMeta_2544_, v___x_2541_, v_numParams_2718_, v___x_2719_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec_ref(v_x_2546_);
if (lean_obj_tag(v___x_2720_) == 0)
{
size_t v_sz_2721_; size_t v___x_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v___x_2720_);
v_sz_2721_ = lean_array_size(v_fst_2704_);
v___x_2722_ = ((size_t)0ULL);
v___x_2723_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_2721_, v___x_2722_, v_fst_2704_, v___y_2715_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2732_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2728_ = l_Lean_mkAppN(v_x_2545_, v_a_2724_);
lean_dec(v_a_2724_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set(v___x_2726_, 0, v___x_2728_);
v___x_2730_ = v___x_2726_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
else
{
lean_object* v_a_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2740_; 
lean_dec_ref(v_x_2545_);
v_a_2733_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2735_ = v___x_2723_;
v_isShared_2736_ = v_isSharedCheck_2740_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_a_2733_);
lean_dec(v___x_2723_);
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
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec(v_fst_2704_);
lean_dec_ref(v_x_2545_);
v_a_2741_ = lean_ctor_get(v___x_2720_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2720_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2720_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2720_);
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
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
else
{
lean_object* v_a_2804_; lean_object* v___x_2806_; uint8_t v_isShared_2807_; uint8_t v_isSharedCheck_2811_; 
lean_dec_ref(v_val_2697_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
lean_dec_ref(v_expectedType_2540_);
v_a_2804_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2811_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2811_ == 0)
{
v___x_2806_ = v___x_2701_;
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
else
{
lean_inc(v_a_2804_);
lean_dec(v___x_2701_);
v___x_2806_ = lean_box(0);
v_isShared_2807_ = v_isSharedCheck_2811_;
goto v_resetjp_2805_;
}
v_resetjp_2805_:
{
lean_object* v___x_2809_; 
if (v_isShared_2807_ == 0)
{
v___x_2809_ = v___x_2806_;
goto v_reusejp_2808_;
}
else
{
lean_object* v_reuseFailAlloc_2810_; 
v_reuseFailAlloc_2810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2810_, 0, v_a_2804_);
v___x_2809_ = v_reuseFailAlloc_2810_;
goto v_reusejp_2808_;
}
v_reusejp_2808_:
{
return v___x_2809_;
}
}
}
}
else
{
lean_dec_ref(v_val_2697_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
lean_dec_ref(v_expectedType_2540_);
return v___x_2698_;
}
}
else
{
lean_dec(v_a_2696_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
v___y_2672_ = v___y_2548_;
v___y_2673_ = v___y_2549_;
v___y_2674_ = v___y_2550_;
v___y_2675_ = v___y_2551_;
goto v___jp_2671_;
}
}
else
{
lean_object* v_a_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2819_; 
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_x_2545_);
lean_dec_ref(v_expectedType_2540_);
lean_dec_ref(v_a_2539_);
v_a_2812_ = lean_ctor_get(v___x_2695_, 0);
v_isSharedCheck_2819_ = !lean_is_exclusive(v___x_2695_);
if (v_isSharedCheck_2819_ == 0)
{
v___x_2814_ = v___x_2695_;
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
else
{
lean_inc(v_a_2812_);
lean_dec(v___x_2695_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2819_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2817_; 
if (v_isShared_2815_ == 0)
{
v___x_2817_ = v___x_2814_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_a_2812_);
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
v___jp_2599_:
{
lean_object* v___x_2605_; uint8_t v___x_2606_; 
v___x_2605_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2606_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2603_, v___x_2605_);
if (v___x_2606_ == 0)
{
lean_object* v___x_2607_; 
lean_dec_ref(v_expectedType_2540_);
v___x_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2607_, 0, v_a_2539_);
return v___x_2607_;
}
else
{
lean_object* v___x_2608_; 
lean_inc(v___y_2604_);
lean_inc_ref(v___y_2602_);
lean_inc(v___y_2601_);
lean_inc_ref(v___y_2600_);
lean_inc_ref(v_a_2539_);
v___x_2608_ = lean_infer_type(v_a_2539_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2604_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; lean_object* v___x_2610_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref(v___x_2608_);
lean_inc_ref(v_expectedType_2540_);
v___x_2610_ = l_Lean_Meta_isExprDefEq(v_expectedType_2540_, v_a_2609_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2604_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2661_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2613_ = v___x_2610_;
v_isShared_2614_ = v_isSharedCheck_2661_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2610_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2661_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
uint8_t v___x_2615_; 
v___x_2615_ = lean_unbox(v_a_2611_);
lean_dec(v_a_2611_);
if (v___x_2615_ == 0)
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v_a_2618_; lean_object* v___x_2619_; 
lean_del_object(v___x_2613_);
v___x_2616_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2617_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2616_, v___y_2604_);
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
lean_inc_n(v_a_2618_, 2);
lean_dec_ref(v___x_2617_);
v___x_2619_ = l_Lean_Meta_mkAuxDefinition(v_a_2618_, v_expectedType_2540_, v_a_2539_, v___x_2541_, v___x_2541_, v___x_2598_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2604_);
if (lean_obj_tag(v___x_2619_) == 0)
{
lean_object* v_a_2620_; uint8_t v___x_2621_; lean_object* v___x_2622_; 
v_a_2620_ = lean_ctor_get(v___x_2619_, 0);
lean_inc(v_a_2620_);
lean_dec_ref(v___x_2619_);
v___x_2621_ = 3;
lean_inc(v_a_2618_);
v___x_2622_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_2618_, v___x_2621_, v___y_2601_, v___y_2604_);
lean_dec_ref(v___x_2622_);
if (v_isMeta_2544_ == 0)
{
v___y_2576_ = v_a_2618_;
v___y_2577_ = v_a_2620_;
v___y_2578_ = v___y_2602_;
v___y_2579_ = v___y_2604_;
goto v___jp_2575_;
}
else
{
lean_object* v___x_2623_; lean_object* v_env_2624_; lean_object* v_nextMacroScope_2625_; lean_object* v_ngen_2626_; lean_object* v_auxDeclNGen_2627_; lean_object* v_traceState_2628_; lean_object* v_messages_2629_; lean_object* v_infoState_2630_; lean_object* v_snapshotTasks_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2656_; 
v___x_2623_ = lean_st_ref_take(v___y_2604_);
v_env_2624_ = lean_ctor_get(v___x_2623_, 0);
v_nextMacroScope_2625_ = lean_ctor_get(v___x_2623_, 1);
v_ngen_2626_ = lean_ctor_get(v___x_2623_, 2);
v_auxDeclNGen_2627_ = lean_ctor_get(v___x_2623_, 3);
v_traceState_2628_ = lean_ctor_get(v___x_2623_, 4);
v_messages_2629_ = lean_ctor_get(v___x_2623_, 6);
v_infoState_2630_ = lean_ctor_get(v___x_2623_, 7);
v_snapshotTasks_2631_ = lean_ctor_get(v___x_2623_, 8);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; 
v_unused_2657_ = lean_ctor_get(v___x_2623_, 5);
lean_dec(v_unused_2657_);
v___x_2633_ = v___x_2623_;
v_isShared_2634_ = v_isSharedCheck_2656_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_snapshotTasks_2631_);
lean_inc(v_infoState_2630_);
lean_inc(v_messages_2629_);
lean_inc(v_traceState_2628_);
lean_inc(v_auxDeclNGen_2627_);
lean_inc(v_ngen_2626_);
lean_inc(v_nextMacroScope_2625_);
lean_inc(v_env_2624_);
lean_dec(v___x_2623_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2656_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
lean_inc(v_a_2618_);
v___x_2635_ = l_Lean_markMeta(v_env_2624_, v_a_2618_);
v___x_2636_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2634_ == 0)
{
lean_ctor_set(v___x_2633_, 5, v___x_2636_);
lean_ctor_set(v___x_2633_, 0, v___x_2635_);
v___x_2638_ = v___x_2633_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v_nextMacroScope_2625_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_ngen_2626_);
lean_ctor_set(v_reuseFailAlloc_2655_, 3, v_auxDeclNGen_2627_);
lean_ctor_set(v_reuseFailAlloc_2655_, 4, v_traceState_2628_);
lean_ctor_set(v_reuseFailAlloc_2655_, 5, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2655_, 6, v_messages_2629_);
lean_ctor_set(v_reuseFailAlloc_2655_, 7, v_infoState_2630_);
lean_ctor_set(v_reuseFailAlloc_2655_, 8, v_snapshotTasks_2631_);
v___x_2638_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v_mctx_2641_; lean_object* v_zetaDeltaFVarIds_2642_; lean_object* v_postponed_2643_; lean_object* v_diag_2644_; lean_object* v___x_2646_; uint8_t v_isShared_2647_; uint8_t v_isSharedCheck_2653_; 
v___x_2639_ = lean_st_ref_set(v___y_2604_, v___x_2638_);
v___x_2640_ = lean_st_ref_take(v___y_2601_);
v_mctx_2641_ = lean_ctor_get(v___x_2640_, 0);
v_zetaDeltaFVarIds_2642_ = lean_ctor_get(v___x_2640_, 2);
v_postponed_2643_ = lean_ctor_get(v___x_2640_, 3);
v_diag_2644_ = lean_ctor_get(v___x_2640_, 4);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2653_ == 0)
{
lean_object* v_unused_2654_; 
v_unused_2654_ = lean_ctor_get(v___x_2640_, 1);
lean_dec(v_unused_2654_);
v___x_2646_ = v___x_2640_;
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
else
{
lean_inc(v_diag_2644_);
lean_inc(v_postponed_2643_);
lean_inc(v_zetaDeltaFVarIds_2642_);
lean_inc(v_mctx_2641_);
lean_dec(v___x_2640_);
v___x_2646_ = lean_box(0);
v_isShared_2647_ = v_isSharedCheck_2653_;
goto v_resetjp_2645_;
}
v_resetjp_2645_:
{
lean_object* v___x_2648_; lean_object* v___x_2650_; 
v___x_2648_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2647_ == 0)
{
lean_ctor_set(v___x_2646_, 1, v___x_2648_);
v___x_2650_ = v___x_2646_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_mctx_2641_);
lean_ctor_set(v_reuseFailAlloc_2652_, 1, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2652_, 2, v_zetaDeltaFVarIds_2642_);
lean_ctor_set(v_reuseFailAlloc_2652_, 3, v_postponed_2643_);
lean_ctor_set(v_reuseFailAlloc_2652_, 4, v_diag_2644_);
v___x_2650_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
lean_object* v___x_2651_; 
v___x_2651_ = lean_st_ref_set(v___y_2601_, v___x_2650_);
v___y_2576_ = v_a_2618_;
v___y_2577_ = v_a_2620_;
v___y_2578_ = v___y_2602_;
v___y_2579_ = v___y_2604_;
goto v___jp_2575_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2618_);
return v___x_2619_;
}
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v_expectedType_2540_);
if (v_isShared_2614_ == 0)
{
lean_ctor_set(v___x_2613_, 0, v_a_2539_);
v___x_2659_ = v___x_2613_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2539_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec_ref(v_expectedType_2540_);
lean_dec_ref(v_a_2539_);
v_a_2662_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2610_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2610_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2540_);
lean_dec_ref(v_a_2539_);
return v___x_2608_;
}
}
}
v___jp_2671_:
{
lean_object* v_options_2676_; uint8_t v_hasTrace_2677_; 
v_options_2676_ = lean_ctor_get(v___y_2674_, 2);
v_hasTrace_2677_ = lean_ctor_get_uint8(v_options_2676_, sizeof(void*)*1);
if (v_hasTrace_2677_ == 0)
{
v___y_2600_ = v___y_2672_;
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v_options_2603_ = v_options_2676_;
v___y_2604_ = v___y_2675_;
goto v___jp_2599_;
}
else
{
lean_object* v_inheritedTraceOptions_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_inheritedTraceOptions_2678_ = lean_ctor_get(v___y_2674_, 13);
v___x_2679_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2680_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2678_, v_options_2676_, v___x_2679_);
if (v___x_2680_ == 0)
{
v___y_2600_ = v___y_2672_;
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v_options_2603_ = v_options_2676_;
v___y_2604_ = v___y_2675_;
goto v___jp_2599_;
}
else
{
lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v___x_2681_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_2539_);
v___x_2682_ = l_Lean_MessageData_ofExpr(v_a_2539_);
v___x_2683_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2681_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2670_, v___x_2683_, v___y_2672_, v___y_2673_, v___y_2674_, v___y_2675_);
if (lean_obj_tag(v___x_2684_) == 0)
{
lean_dec_ref(v___x_2684_);
v___y_2600_ = v___y_2672_;
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v_options_2603_ = v_options_2676_;
v___y_2604_ = v___y_2675_;
goto v___jp_2599_;
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec_ref(v_expectedType_2540_);
lean_dec_ref(v_a_2539_);
v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2684_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2684_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2684_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
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
return v___x_2690_;
}
}
}
}
}
}
}
v___jp_2553_:
{
lean_object* v___x_2558_; 
v___x_2558_ = l_Lean_enableRealizationsForConst(v___y_2554_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2558_) == 0)
{
lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2565_ == 0)
{
lean_object* v_unused_2566_; 
v_unused_2566_ = lean_ctor_get(v___x_2558_, 0);
lean_dec(v_unused_2566_);
v___x_2560_ = v___x_2558_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_dec(v___x_2558_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
lean_ctor_set(v___x_2560_, 0, v___y_2555_);
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v___y_2555_);
v___x_2563_ = v_reuseFailAlloc_2564_;
goto v_reusejp_2562_;
}
v_reusejp_2562_:
{
return v___x_2563_;
}
}
}
else
{
lean_object* v_a_2567_; lean_object* v___x_2569_; uint8_t v_isShared_2570_; uint8_t v_isSharedCheck_2574_; 
lean_dec_ref(v___y_2555_);
v_a_2567_ = lean_ctor_get(v___x_2558_, 0);
v_isSharedCheck_2574_ = !lean_is_exclusive(v___x_2558_);
if (v_isSharedCheck_2574_ == 0)
{
v___x_2569_ = v___x_2558_;
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
else
{
lean_inc(v_a_2567_);
lean_dec(v___x_2558_);
v___x_2569_ = lean_box(0);
v_isShared_2570_ = v_isSharedCheck_2574_;
goto v_resetjp_2568_;
}
v_resetjp_2568_:
{
lean_object* v___x_2572_; 
if (v_isShared_2570_ == 0)
{
v___x_2572_ = v___x_2569_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v_a_2567_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
v___jp_2575_:
{
if (v_compile_2542_ == 0)
{
v___y_2554_ = v___y_2576_;
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
goto v___jp_2553_;
}
else
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2580_ = lean_unsigned_to_nat(1u);
v___x_2581_ = lean_mk_empty_array_with_capacity(v___x_2580_);
lean_inc(v___y_2576_);
v___x_2582_ = lean_array_push(v___x_2581_, v___y_2576_);
v___x_2583_ = l_Lean_compileDecls(v___x_2582_, v_logCompileErrors_2543_, v___y_2578_, v___y_2579_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_dec_ref(v___x_2583_);
v___y_2554_ = v___y_2576_;
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
goto v___jp_2553_;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v___y_2577_);
lean_dec(v___y_2576_);
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2583_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2583_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
}
}
static double _init_l_Lean_Meta_wrapInstance___closed__1(void){
_start:
{
lean_object* v___x_2820_; double v___x_2821_; 
v___x_2820_ = lean_unsigned_to_nat(1000000000u);
v___x_2821_ = lean_float_of_nat(v___x_2820_);
return v___x_2821_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(lean_object* v_upperBound_2822_, lean_object* v_fst_2823_, lean_object* v_args_2824_, uint8_t v___x_2825_, uint8_t v_compile_2826_, uint8_t v_logCompileErrors_2827_, uint8_t v_isMeta_2828_, uint8_t v___x_2829_, lean_object* v_a_2830_, lean_object* v_b_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_){
_start:
{
lean_object* v_a_2838_; lean_object* v___y_2843_; uint8_t v___x_2862_; 
v___x_2862_ = lean_nat_dec_lt(v_a_2830_, v_upperBound_2822_);
if (v___x_2862_ == 0)
{
lean_object* v___x_2863_; 
lean_dec(v_a_2830_);
v___x_2863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2863_, 0, v_b_2831_);
return v___x_2863_;
}
else
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_array_fget_borrowed(v_fst_2823_, v_a_2830_);
v___x_2865_ = l_Lean_Expr_mvarId_x21(v___x_2864_);
lean_inc(v___x_2865_);
v___x_2866_ = l_Lean_MVarId_getDecl(v___x_2865_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2866_) == 0)
{
lean_object* v_a_2867_; lean_object* v_type_2868_; lean_object* v___x_2869_; 
v_a_2867_ = lean_ctor_get(v___x_2866_, 0);
lean_inc(v_a_2867_);
lean_dec_ref(v___x_2866_);
v_type_2868_ = lean_ctor_get(v_a_2867_, 2);
lean_inc_ref(v_type_2868_);
lean_dec(v_a_2867_);
v___x_2869_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2868_, v___y_2833_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2871_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc_n(v_a_2870_, 2);
lean_dec_ref(v___x_2869_);
v___x_2871_ = l_Lean_Meta_isProp(v_a_2870_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; lean_object* v_cls_2874_; lean_object* v___x_2875_; uint8_t v___x_2876_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref(v___x_2871_);
v___x_2873_ = lean_box(0);
v_cls_2874_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2875_ = lean_array_fget_borrowed(v_args_2824_, v_a_2830_);
v___x_2876_ = lean_unbox(v_a_2872_);
lean_dec(v_a_2872_);
if (v___x_2876_ == 0)
{
lean_object* v___x_2877_; 
lean_inc(v_a_2870_);
v___x_2877_ = l_Lean_Meta_isClass_x3f(v_a_2870_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_3012_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_2880_ = v___x_2877_;
v_isShared_2881_ = v_isSharedCheck_3012_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2877_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_3012_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v_a_2883_; lean_object* v___y_2886_; uint8_t v___y_2887_; lean_object* v_a_2892_; lean_object* v___y_2896_; lean_object* v___y_2901_; 
if (lean_obj_tag(v_a_2878_) == 0)
{
if (v___x_2829_ == 0)
{
lean_object* v_options_2925_; lean_object* v___x_2926_; uint8_t v___x_2927_; 
lean_del_object(v___x_2880_);
v_options_2925_ = lean_ctor_get(v___y_2834_, 2);
v___x_2926_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2927_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2925_, v___x_2926_);
if (v___x_2927_ == 0)
{
lean_object* v___x_2928_; 
lean_dec(v_a_2870_);
lean_inc(v___x_2875_);
v___x_2928_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2865_, v___x_2875_, v___y_2833_);
if (lean_obj_tag(v___x_2928_) == 0)
{
lean_dec_ref(v___x_2928_);
v_a_2838_ = v___x_2873_;
goto v___jp_2837_;
}
else
{
lean_dec(v_a_2830_);
return v___x_2928_;
}
}
else
{
lean_object* v___x_2929_; 
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___x_2875_);
v___x_2929_ = lean_infer_type(v___x_2875_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_object* v_a_2930_; lean_object* v___x_2931_; 
v_a_2930_ = lean_ctor_get(v___x_2929_, 0);
lean_inc(v_a_2930_);
lean_dec_ref(v___x_2929_);
lean_inc(v_a_2870_);
v___x_2931_ = l_Lean_Meta_isExprDefEq(v_a_2870_, v_a_2930_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; uint8_t v___x_2933_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref(v___x_2931_);
v___x_2933_ = lean_unbox(v_a_2932_);
lean_dec(v_a_2932_);
if (v___x_2933_ == 0)
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2935_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2934_, v___y_2835_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc_n(v_a_2936_, 2);
lean_dec_ref(v___x_2935_);
lean_inc(v___x_2875_);
v___x_2937_ = l_Lean_Meta_mkAuxDefinition(v_a_2936_, v_a_2870_, v___x_2875_, v___x_2829_, v___x_2829_, v___x_2825_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v___x_2939_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref(v___x_2937_);
v___x_2939_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2865_, v_a_2938_, v___y_2833_);
if (lean_obj_tag(v___x_2939_) == 0)
{
uint8_t v___x_2940_; lean_object* v___x_2941_; 
lean_dec_ref(v___x_2939_);
v___x_2940_ = 0;
lean_inc(v_a_2936_);
v___x_2941_ = l_Lean_Meta_setInlineAttribute(v_a_2936_, v___x_2940_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2941_) == 0)
{
lean_dec_ref(v___x_2941_);
if (v_isMeta_2828_ == 0)
{
lean_object* v___x_2942_; 
v___x_2942_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2936_, v___x_2873_, v_compile_2826_, v_logCompileErrors_2827_, v___x_2873_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_2942_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2943_; lean_object* v_env_2944_; lean_object* v_nextMacroScope_2945_; lean_object* v_ngen_2946_; lean_object* v_auxDeclNGen_2947_; lean_object* v_traceState_2948_; lean_object* v_messages_2949_; lean_object* v_infoState_2950_; lean_object* v_snapshotTasks_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2977_; 
v___x_2943_ = lean_st_ref_take(v___y_2835_);
v_env_2944_ = lean_ctor_get(v___x_2943_, 0);
v_nextMacroScope_2945_ = lean_ctor_get(v___x_2943_, 1);
v_ngen_2946_ = lean_ctor_get(v___x_2943_, 2);
v_auxDeclNGen_2947_ = lean_ctor_get(v___x_2943_, 3);
v_traceState_2948_ = lean_ctor_get(v___x_2943_, 4);
v_messages_2949_ = lean_ctor_get(v___x_2943_, 6);
v_infoState_2950_ = lean_ctor_get(v___x_2943_, 7);
v_snapshotTasks_2951_ = lean_ctor_get(v___x_2943_, 8);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2977_ == 0)
{
lean_object* v_unused_2978_; 
v_unused_2978_ = lean_ctor_get(v___x_2943_, 5);
lean_dec(v_unused_2978_);
v___x_2953_ = v___x_2943_;
v_isShared_2954_ = v_isSharedCheck_2977_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_snapshotTasks_2951_);
lean_inc(v_infoState_2950_);
lean_inc(v_messages_2949_);
lean_inc(v_traceState_2948_);
lean_inc(v_auxDeclNGen_2947_);
lean_inc(v_ngen_2946_);
lean_inc(v_nextMacroScope_2945_);
lean_inc(v_env_2944_);
lean_dec(v___x_2943_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2977_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2958_; 
lean_inc(v_a_2936_);
v___x_2955_ = l_Lean_markMeta(v_env_2944_, v_a_2936_);
v___x_2956_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2954_ == 0)
{
lean_ctor_set(v___x_2953_, 5, v___x_2956_);
lean_ctor_set(v___x_2953_, 0, v___x_2955_);
v___x_2958_ = v___x_2953_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2955_);
lean_ctor_set(v_reuseFailAlloc_2976_, 1, v_nextMacroScope_2945_);
lean_ctor_set(v_reuseFailAlloc_2976_, 2, v_ngen_2946_);
lean_ctor_set(v_reuseFailAlloc_2976_, 3, v_auxDeclNGen_2947_);
lean_ctor_set(v_reuseFailAlloc_2976_, 4, v_traceState_2948_);
lean_ctor_set(v_reuseFailAlloc_2976_, 5, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2976_, 6, v_messages_2949_);
lean_ctor_set(v_reuseFailAlloc_2976_, 7, v_infoState_2950_);
lean_ctor_set(v_reuseFailAlloc_2976_, 8, v_snapshotTasks_2951_);
v___x_2958_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v_mctx_2961_; lean_object* v_zetaDeltaFVarIds_2962_; lean_object* v_postponed_2963_; lean_object* v_diag_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2974_; 
v___x_2959_ = lean_st_ref_set(v___y_2835_, v___x_2958_);
v___x_2960_ = lean_st_ref_take(v___y_2833_);
v_mctx_2961_ = lean_ctor_get(v___x_2960_, 0);
v_zetaDeltaFVarIds_2962_ = lean_ctor_get(v___x_2960_, 2);
v_postponed_2963_ = lean_ctor_get(v___x_2960_, 3);
v_diag_2964_ = lean_ctor_get(v___x_2960_, 4);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2974_ == 0)
{
lean_object* v_unused_2975_; 
v_unused_2975_ = lean_ctor_get(v___x_2960_, 1);
lean_dec(v_unused_2975_);
v___x_2966_ = v___x_2960_;
v_isShared_2967_ = v_isSharedCheck_2974_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_diag_2964_);
lean_inc(v_postponed_2963_);
lean_inc(v_zetaDeltaFVarIds_2962_);
lean_inc(v_mctx_2961_);
lean_dec(v___x_2960_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2974_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2968_; lean_object* v___x_2970_; 
v___x_2968_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2967_ == 0)
{
lean_ctor_set(v___x_2966_, 1, v___x_2968_);
v___x_2970_ = v___x_2966_;
goto v_reusejp_2969_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_mctx_2961_);
lean_ctor_set(v_reuseFailAlloc_2973_, 1, v___x_2968_);
lean_ctor_set(v_reuseFailAlloc_2973_, 2, v_zetaDeltaFVarIds_2962_);
lean_ctor_set(v_reuseFailAlloc_2973_, 3, v_postponed_2963_);
lean_ctor_set(v_reuseFailAlloc_2973_, 4, v_diag_2964_);
v___x_2970_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2969_;
}
v_reusejp_2969_:
{
lean_object* v___x_2971_; lean_object* v___x_2972_; 
v___x_2971_ = lean_st_ref_set(v___y_2833_, v___x_2970_);
v___x_2972_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2936_, v___x_2873_, v_compile_2826_, v_logCompileErrors_2827_, v___x_2873_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_2972_;
goto v___jp_2842_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2936_);
lean_dec(v_a_2830_);
return v___x_2941_;
}
}
else
{
lean_dec(v_a_2936_);
lean_dec(v_a_2830_);
return v___x_2939_;
}
}
else
{
lean_object* v_a_2979_; lean_object* v___x_2981_; uint8_t v_isShared_2982_; uint8_t v_isSharedCheck_2986_; 
lean_dec(v_a_2936_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_2979_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2986_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2986_ == 0)
{
v___x_2981_ = v___x_2937_;
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
else
{
lean_inc(v_a_2979_);
lean_dec(v___x_2937_);
v___x_2981_ = lean_box(0);
v_isShared_2982_ = v_isSharedCheck_2986_;
goto v_resetjp_2980_;
}
v_resetjp_2980_:
{
lean_object* v___x_2984_; 
if (v_isShared_2982_ == 0)
{
v___x_2984_ = v___x_2981_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_2985_; 
v_reuseFailAlloc_2985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2985_, 0, v_a_2979_);
v___x_2984_ = v_reuseFailAlloc_2985_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
return v___x_2984_;
}
}
}
}
else
{
lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_2987_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2935_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2935_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
}
else
{
lean_object* v___x_2995_; 
lean_dec(v_a_2870_);
lean_inc(v___x_2875_);
v___x_2995_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2865_, v___x_2875_, v___y_2833_);
if (lean_obj_tag(v___x_2995_) == 0)
{
lean_dec_ref(v___x_2995_);
v_a_2838_ = v___x_2873_;
goto v___jp_2837_;
}
else
{
lean_dec(v_a_2830_);
return v___x_2995_;
}
}
}
else
{
lean_object* v_a_2996_; lean_object* v___x_2998_; uint8_t v_isShared_2999_; uint8_t v_isSharedCheck_3003_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_2996_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_3003_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_3003_ == 0)
{
v___x_2998_ = v___x_2931_;
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
else
{
lean_inc(v_a_2996_);
lean_dec(v___x_2931_);
v___x_2998_ = lean_box(0);
v_isShared_2999_ = v_isSharedCheck_3003_;
goto v_resetjp_2997_;
}
v_resetjp_2997_:
{
lean_object* v___x_3001_; 
if (v_isShared_2999_ == 0)
{
v___x_3001_ = v___x_2998_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3002_; 
v_reuseFailAlloc_3002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3002_, 0, v_a_2996_);
v___x_3001_ = v_reuseFailAlloc_3002_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
return v___x_3001_;
}
}
}
}
else
{
lean_object* v_a_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3011_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3004_ = lean_ctor_get(v___x_2929_, 0);
v_isSharedCheck_3011_ = !lean_is_exclusive(v___x_2929_);
if (v_isSharedCheck_3011_ == 0)
{
v___x_3006_ = v___x_2929_;
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_a_3004_);
lean_dec(v___x_2929_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3011_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v___x_3009_; 
if (v_isShared_3007_ == 0)
{
v___x_3009_ = v___x_3006_;
goto v_reusejp_3008_;
}
else
{
lean_object* v_reuseFailAlloc_3010_; 
v_reuseFailAlloc_3010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3010_, 0, v_a_3004_);
v___x_3009_ = v_reuseFailAlloc_3010_;
goto v_reusejp_3008_;
}
v_reusejp_3008_:
{
return v___x_3009_;
}
}
}
}
}
else
{
goto v___jp_2903_;
}
}
else
{
lean_dec_ref(v_a_2878_);
goto v___jp_2903_;
}
v___jp_2882_:
{
lean_object* v___x_2884_; 
lean_inc(v___x_2875_);
v___x_2884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2875_, v_a_2870_, v_compile_2826_, v_logCompileErrors_2827_, v_isMeta_2828_, v___x_2865_, v___x_2873_, v_a_2883_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_2884_;
goto v___jp_2842_;
}
v___jp_2885_:
{
if (v___y_2887_ == 0)
{
lean_dec_ref(v___y_2886_);
lean_del_object(v___x_2880_);
v_a_2883_ = v___x_2873_;
goto v___jp_2882_;
}
else
{
lean_object* v___x_2889_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
if (v_isShared_2881_ == 0)
{
lean_ctor_set_tag(v___x_2880_, 1);
lean_ctor_set(v___x_2880_, 0, v___y_2886_);
v___x_2889_ = v___x_2880_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v___y_2886_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
v___jp_2891_:
{
uint8_t v___x_2893_; 
v___x_2893_ = l_Lean_Exception_isInterrupt(v_a_2892_);
if (v___x_2893_ == 0)
{
uint8_t v___x_2894_; 
lean_inc_ref(v_a_2892_);
v___x_2894_ = l_Lean_Exception_isRuntime(v_a_2892_);
v___y_2886_ = v_a_2892_;
v___y_2887_ = v___x_2894_;
goto v___jp_2885_;
}
else
{
v___y_2886_ = v_a_2892_;
v___y_2887_ = v___x_2893_;
goto v___jp_2885_;
}
}
v___jp_2895_:
{
if (lean_obj_tag(v___y_2896_) == 0)
{
lean_object* v_a_2897_; 
lean_del_object(v___x_2880_);
v_a_2897_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref(v___y_2896_);
if (lean_obj_tag(v_a_2897_) == 0)
{
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
v_a_2838_ = v___x_2873_;
goto v___jp_2837_;
}
else
{
lean_object* v_a_2898_; 
v_a_2898_ = lean_ctor_get(v_a_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v_a_2897_);
v_a_2883_ = v_a_2898_;
goto v___jp_2882_;
}
}
else
{
lean_object* v_a_2899_; 
v_a_2899_ = lean_ctor_get(v___y_2896_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v___y_2896_);
v_a_2892_ = v_a_2899_;
goto v___jp_2891_;
}
}
v___jp_2900_:
{
lean_object* v___x_2902_; 
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
v___x_2902_ = lean_apply_6(v___y_2901_, v___x_2873_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_, lean_box(0));
v___y_2896_ = v___x_2902_;
goto v___jp_2895_;
}
v___jp_2903_:
{
lean_object* v_options_2904_; lean_object* v_inheritedTraceOptions_2905_; lean_object* v___x_2906_; uint8_t v___x_2907_; 
v_options_2904_ = lean_ctor_get(v___y_2834_, 2);
v_inheritedTraceOptions_2905_ = lean_ctor_get(v___y_2834_, 13);
v___x_2906_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2907_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2904_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; 
lean_del_object(v___x_2880_);
lean_inc(v___x_2875_);
v___x_2908_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2875_, v_a_2870_, v_compile_2826_, v_logCompileErrors_2827_, v_isMeta_2828_, v___x_2865_, v___x_2873_, v___x_2873_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_2908_;
goto v___jp_2842_;
}
else
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_box(0);
lean_inc(v_a_2870_);
v___x_2910_ = l_Lean_Meta_trySynthInstance(v_a_2870_, v___x_2909_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2910_) == 0)
{
lean_object* v_a_2911_; 
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2911_);
lean_dec_ref(v___x_2910_);
if (lean_obj_tag(v_a_2911_) == 1)
{
lean_object* v_a_2912_; uint8_t v_hasTrace_2913_; lean_object* v___f_2914_; 
v_a_2912_ = lean_ctor_get(v_a_2911_, 0);
lean_inc_n(v_a_2912_, 2);
lean_dec_ref(v_a_2911_);
v_hasTrace_2913_ = lean_ctor_get_uint8(v_options_2904_, sizeof(void*)*1);
lean_inc(v___x_2865_);
v___f_2914_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed), 8, 2);
lean_closure_set(v___f_2914_, 0, v___x_2865_);
lean_closure_set(v___f_2914_, 1, v_a_2912_);
if (v_hasTrace_2913_ == 0)
{
lean_dec(v_a_2912_);
v___y_2901_ = v___f_2914_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2916_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2905_, v_options_2904_, v___x_2915_);
if (v___x_2916_ == 0)
{
lean_dec(v_a_2912_);
v___y_2901_ = v___f_2914_;
goto v___jp_2900_;
}
else
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; 
lean_dec_ref(v___f_2914_);
v___x_2917_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_2912_);
v___x_2918_ = l_Lean_MessageData_ofExpr(v_a_2912_);
v___x_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2919_, 0, v___x_2917_);
lean_ctor_set(v___x_2919_, 1, v___x_2918_);
v___x_2920_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2874_, v___x_2919_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; lean_object* v___x_2922_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref(v___x_2920_);
lean_inc(v___x_2865_);
v___x_2922_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2865_, v_a_2912_, v_a_2921_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2896_ = v___x_2922_;
goto v___jp_2895_;
}
else
{
lean_object* v_a_2923_; 
lean_dec(v_a_2912_);
v_a_2923_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2923_);
lean_dec_ref(v___x_2920_);
v_a_2892_ = v_a_2923_;
goto v___jp_2891_;
}
}
}
}
else
{
lean_dec(v_a_2911_);
lean_del_object(v___x_2880_);
v_a_2883_ = v___x_2873_;
goto v___jp_2882_;
}
}
else
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___x_2910_, 0);
lean_inc(v_a_2924_);
lean_dec_ref(v___x_2910_);
v_a_2892_ = v_a_2924_;
goto v___jp_2891_;
}
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3013_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2877_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2877_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
else
{
lean_object* v___x_3021_; 
lean_inc(v___y_2835_);
lean_inc_ref(v___y_2834_);
lean_inc(v___y_2833_);
lean_inc_ref(v___y_2832_);
lean_inc(v___x_2875_);
v___x_3021_ = lean_infer_type(v___x_2875_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc_n(v_a_3022_, 2);
lean_dec_ref(v___x_3021_);
lean_inc(v_a_2870_);
v___x_3023_ = l_Lean_Meta_isExprDefEq(v_a_2870_, v_a_3022_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; uint8_t v___x_3025_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref(v___x_3023_);
v___x_3025_ = lean_unbox(v_a_3024_);
lean_dec(v_a_3024_);
if (v___x_3025_ == 0)
{
lean_object* v_options_3026_; lean_object* v_inheritedTraceOptions_3027_; uint8_t v_hasTrace_3028_; 
v_options_3026_ = lean_ctor_get(v___y_2834_, 2);
v_inheritedTraceOptions_3027_ = lean_ctor_get(v___y_2834_, 13);
v_hasTrace_3028_ = lean_ctor_get_uint8(v_options_3026_, sizeof(void*)*1);
if (v_hasTrace_3028_ == 0)
{
lean_dec(v_a_3022_);
goto v___jp_3029_;
}
else
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3032_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3027_, v_options_3026_, v___x_3031_);
if (v___x_3032_ == 0)
{
lean_dec(v_a_3022_);
goto v___jp_3029_;
}
else
{
lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3033_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_2830_);
v___x_3034_ = l_Nat_reprFast(v_a_2830_);
v___x_3035_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
v___x_3036_ = l_Lean_MessageData_ofFormat(v___x_3035_);
v___x_3037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3033_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_3039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3039_, 0, v___x_3037_);
lean_ctor_set(v___x_3039_, 1, v___x_3038_);
lean_inc(v_a_2870_);
v___x_3040_ = l_Lean_MessageData_ofExpr(v_a_2870_);
v___x_3041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3041_, 0, v___x_3039_);
lean_ctor_set(v___x_3041_, 1, v___x_3040_);
v___x_3042_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_3043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3043_, 0, v___x_3041_);
lean_ctor_set(v___x_3043_, 1, v___x_3042_);
v___x_3044_ = l_Lean_MessageData_ofExpr(v_a_3022_);
v___x_3045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3045_, 0, v___x_3043_);
lean_ctor_set(v___x_3045_, 1, v___x_3044_);
v___x_3046_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_3047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3047_, 0, v___x_3045_);
lean_ctor_set(v___x_3047_, 1, v___x_3046_);
lean_inc(v___x_2875_);
v___x_3048_ = l_Lean_MessageData_ofExpr(v___x_2875_);
v___x_3049_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3047_);
lean_ctor_set(v___x_3049_, 1, v___x_3048_);
v___x_3050_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2874_, v___x_3049_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
if (lean_obj_tag(v___x_3050_) == 0)
{
lean_object* v_a_3051_; lean_object* v___x_3052_; 
v_a_3051_ = lean_ctor_get(v___x_3050_, 0);
lean_inc(v_a_3051_);
lean_dec_ref(v___x_3050_);
lean_inc(v___x_2875_);
v___x_3052_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2870_, v___x_2875_, v___x_2825_, v___x_2865_, v___x_2873_, v_a_3051_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_3052_;
goto v___jp_2842_;
}
else
{
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
return v___x_3050_;
}
}
}
v___jp_3029_:
{
lean_object* v___x_3030_; 
lean_inc(v___x_2875_);
v___x_3030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2870_, v___x_2875_, v___x_2825_, v___x_2865_, v___x_2873_, v___x_2873_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
v___y_2843_ = v___x_3030_;
goto v___jp_2842_;
}
}
else
{
lean_object* v___x_3053_; 
lean_dec(v_a_3022_);
lean_dec(v_a_2870_);
lean_inc(v___x_2875_);
v___x_3053_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2865_, v___x_2875_, v___y_2833_);
if (lean_obj_tag(v___x_3053_) == 0)
{
lean_dec_ref(v___x_3053_);
v_a_2838_ = v___x_2873_;
goto v___jp_2837_;
}
else
{
lean_dec(v_a_2830_);
return v___x_3053_;
}
}
}
else
{
lean_object* v_a_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3061_; 
lean_dec(v_a_3022_);
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3054_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3061_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3061_ == 0)
{
v___x_3056_ = v___x_3023_;
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_a_3054_);
lean_dec(v___x_3023_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3061_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3059_; 
if (v_isShared_3057_ == 0)
{
v___x_3059_ = v___x_3056_;
goto v_reusejp_3058_;
}
else
{
lean_object* v_reuseFailAlloc_3060_; 
v_reuseFailAlloc_3060_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3060_, 0, v_a_3054_);
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
else
{
lean_object* v_a_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3069_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3062_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3069_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3069_ == 0)
{
v___x_3064_ = v___x_3021_;
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_a_3062_);
lean_dec(v___x_3021_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3069_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3067_; 
if (v_isShared_3065_ == 0)
{
v___x_3067_ = v___x_3064_;
goto v_reusejp_3066_;
}
else
{
lean_object* v_reuseFailAlloc_3068_; 
v_reuseFailAlloc_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3068_, 0, v_a_3062_);
v___x_3067_ = v_reuseFailAlloc_3068_;
goto v_reusejp_3066_;
}
v_reusejp_3066_:
{
return v___x_3067_;
}
}
}
}
}
else
{
lean_object* v_a_3070_; lean_object* v___x_3072_; uint8_t v_isShared_3073_; uint8_t v_isSharedCheck_3077_; 
lean_dec(v_a_2870_);
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3070_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_3077_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_3077_ == 0)
{
v___x_3072_ = v___x_2871_;
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
else
{
lean_inc(v_a_3070_);
lean_dec(v___x_2871_);
v___x_3072_ = lean_box(0);
v_isShared_3073_ = v_isSharedCheck_3077_;
goto v_resetjp_3071_;
}
v_resetjp_3071_:
{
lean_object* v___x_3075_; 
if (v_isShared_3073_ == 0)
{
v___x_3075_ = v___x_3072_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_a_3070_);
v___x_3075_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
return v___x_3075_;
}
}
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3078_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_2869_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_2869_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_dec(v___x_2865_);
lean_dec(v_a_2830_);
v_a_3086_ = lean_ctor_get(v___x_2866_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_2866_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_2866_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
v___jp_2837_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; 
v___x_2839_ = lean_unsigned_to_nat(1u);
v___x_2840_ = lean_nat_add(v_a_2830_, v___x_2839_);
lean_dec(v_a_2830_);
v_a_2830_ = v___x_2840_;
v_b_2831_ = v_a_2838_;
goto _start;
}
v___jp_2842_:
{
if (lean_obj_tag(v___y_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2853_; 
v_a_2844_ = lean_ctor_get(v___y_2843_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___y_2843_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2846_ = v___y_2843_;
v_isShared_2847_ = v_isSharedCheck_2853_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___y_2843_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2853_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
if (lean_obj_tag(v_a_2844_) == 0)
{
lean_object* v_a_2848_; lean_object* v___x_2850_; 
lean_dec(v_a_2830_);
v_a_2848_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_a_2848_);
lean_dec_ref(v_a_2844_);
if (v_isShared_2847_ == 0)
{
lean_ctor_set(v___x_2846_, 0, v_a_2848_);
v___x_2850_ = v___x_2846_;
goto v_reusejp_2849_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2848_);
v___x_2850_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2849_;
}
v_reusejp_2849_:
{
return v___x_2850_;
}
}
else
{
lean_object* v_a_2852_; 
lean_del_object(v___x_2846_);
v_a_2852_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_a_2852_);
lean_dec_ref(v_a_2844_);
v_a_2838_ = v_a_2852_;
goto v___jp_2837_;
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec(v_a_2830_);
v_a_2854_ = lean_ctor_get(v___y_2843_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___y_2843_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___y_2843_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___y_2843_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object* v_upperBound_3094_, lean_object* v_fst_3095_, lean_object* v_args_3096_, uint8_t v___x_3097_, uint8_t v_compile_3098_, uint8_t v_logCompileErrors_3099_, uint8_t v_isMeta_3100_, uint8_t v___x_3101_, lean_object* v_a_3102_, lean_object* v_b_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_a_3110_; lean_object* v___y_3115_; uint8_t v___x_3134_; 
v___x_3134_ = lean_nat_dec_lt(v_a_3102_, v_upperBound_3094_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; 
lean_dec(v_a_3102_);
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_b_3103_);
return v___x_3135_;
}
else
{
lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3136_ = lean_array_fget_borrowed(v_fst_3095_, v_a_3102_);
v___x_3137_ = l_Lean_Expr_mvarId_x21(v___x_3136_);
lean_inc(v___x_3137_);
v___x_3138_ = l_Lean_MVarId_getDecl(v___x_3137_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v_type_3140_; lean_object* v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___x_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref(v___x_3138_);
v_type_3140_ = lean_ctor_get(v_a_3139_, 2);
lean_inc_ref(v_type_3140_);
lean_dec(v_a_3139_);
v___x_3141_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_3140_, v___y_3105_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3143_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
lean_inc_n(v_a_3142_, 2);
lean_dec_ref(v___x_3141_);
v___x_3143_ = l_Lean_Meta_isProp(v_a_3142_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3145_; lean_object* v_cls_3146_; lean_object* v___x_3147_; uint8_t v___x_3148_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
v___x_3145_ = lean_box(0);
v_cls_3146_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3147_ = lean_array_fget_borrowed(v_args_3096_, v_a_3102_);
v___x_3148_ = lean_unbox(v_a_3144_);
lean_dec(v_a_3144_);
if (v___x_3148_ == 0)
{
lean_object* v___x_3149_; 
lean_inc(v_a_3142_);
v___x_3149_ = l_Lean_Meta_isClass_x3f(v_a_3142_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3149_) == 0)
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3284_; 
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3152_ = v___x_3149_;
v_isShared_3153_ = v_isSharedCheck_3284_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3149_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3284_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v_a_3155_; lean_object* v___y_3158_; uint8_t v___y_3159_; lean_object* v_a_3164_; lean_object* v___y_3168_; lean_object* v___y_3173_; 
if (lean_obj_tag(v_a_3150_) == 0)
{
if (v___x_3101_ == 0)
{
lean_object* v_options_3197_; lean_object* v___x_3198_; uint8_t v___x_3199_; 
lean_del_object(v___x_3152_);
v_options_3197_ = lean_ctor_get(v___y_3106_, 2);
v___x_3198_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_3199_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v___x_3200_; 
lean_dec(v_a_3142_);
lean_inc(v___x_3147_);
v___x_3200_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3137_, v___x_3147_, v___y_3105_);
if (lean_obj_tag(v___x_3200_) == 0)
{
lean_dec_ref(v___x_3200_);
v_a_3110_ = v___x_3145_;
goto v___jp_3109_;
}
else
{
lean_dec(v_a_3102_);
return v___x_3200_;
}
}
else
{
lean_object* v___x_3201_; 
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3106_);
lean_inc(v___y_3105_);
lean_inc_ref(v___y_3104_);
lean_inc(v___x_3147_);
v___x_3201_ = lean_infer_type(v___x_3147_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_object* v_a_3202_; lean_object* v___x_3203_; 
v_a_3202_ = lean_ctor_get(v___x_3201_, 0);
lean_inc(v_a_3202_);
lean_dec_ref(v___x_3201_);
lean_inc(v_a_3142_);
v___x_3203_ = l_Lean_Meta_isExprDefEq(v_a_3142_, v_a_3202_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v_a_3204_; uint8_t v___x_3205_; 
v_a_3204_ = lean_ctor_get(v___x_3203_, 0);
lean_inc(v_a_3204_);
lean_dec_ref(v___x_3203_);
v___x_3205_ = lean_unbox(v_a_3204_);
lean_dec(v_a_3204_);
if (v___x_3205_ == 0)
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3207_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3206_, v___y_3107_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc_n(v_a_3208_, 2);
lean_dec_ref(v___x_3207_);
lean_inc(v___x_3147_);
v___x_3209_ = l_Lean_Meta_mkAuxDefinition(v_a_3208_, v_a_3142_, v___x_3147_, v___x_3101_, v___x_3101_, v___x_3097_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v_a_3210_; lean_object* v___x_3211_; 
v_a_3210_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_a_3210_);
lean_dec_ref(v___x_3209_);
v___x_3211_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3137_, v_a_3210_, v___y_3105_);
if (lean_obj_tag(v___x_3211_) == 0)
{
uint8_t v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref(v___x_3211_);
v___x_3212_ = 0;
lean_inc(v_a_3208_);
v___x_3213_ = l_Lean_Meta_setInlineAttribute(v_a_3208_, v___x_3212_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec_ref(v___x_3213_);
if (v_isMeta_3100_ == 0)
{
lean_object* v___x_3214_; 
v___x_3214_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_3208_, v___x_3145_, v_compile_3098_, v_logCompileErrors_3099_, v___x_3145_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3214_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3215_; lean_object* v_env_3216_; lean_object* v_nextMacroScope_3217_; lean_object* v_ngen_3218_; lean_object* v_auxDeclNGen_3219_; lean_object* v_traceState_3220_; lean_object* v_messages_3221_; lean_object* v_infoState_3222_; lean_object* v_snapshotTasks_3223_; lean_object* v___x_3225_; uint8_t v_isShared_3226_; uint8_t v_isSharedCheck_3249_; 
v___x_3215_ = lean_st_ref_take(v___y_3107_);
v_env_3216_ = lean_ctor_get(v___x_3215_, 0);
v_nextMacroScope_3217_ = lean_ctor_get(v___x_3215_, 1);
v_ngen_3218_ = lean_ctor_get(v___x_3215_, 2);
v_auxDeclNGen_3219_ = lean_ctor_get(v___x_3215_, 3);
v_traceState_3220_ = lean_ctor_get(v___x_3215_, 4);
v_messages_3221_ = lean_ctor_get(v___x_3215_, 6);
v_infoState_3222_ = lean_ctor_get(v___x_3215_, 7);
v_snapshotTasks_3223_ = lean_ctor_get(v___x_3215_, 8);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3249_ == 0)
{
lean_object* v_unused_3250_; 
v_unused_3250_ = lean_ctor_get(v___x_3215_, 5);
lean_dec(v_unused_3250_);
v___x_3225_ = v___x_3215_;
v_isShared_3226_ = v_isSharedCheck_3249_;
goto v_resetjp_3224_;
}
else
{
lean_inc(v_snapshotTasks_3223_);
lean_inc(v_infoState_3222_);
lean_inc(v_messages_3221_);
lean_inc(v_traceState_3220_);
lean_inc(v_auxDeclNGen_3219_);
lean_inc(v_ngen_3218_);
lean_inc(v_nextMacroScope_3217_);
lean_inc(v_env_3216_);
lean_dec(v___x_3215_);
v___x_3225_ = lean_box(0);
v_isShared_3226_ = v_isSharedCheck_3249_;
goto v_resetjp_3224_;
}
v_resetjp_3224_:
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3230_; 
lean_inc(v_a_3208_);
v___x_3227_ = l_Lean_markMeta(v_env_3216_, v_a_3208_);
v___x_3228_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3226_ == 0)
{
lean_ctor_set(v___x_3225_, 5, v___x_3228_);
lean_ctor_set(v___x_3225_, 0, v___x_3227_);
v___x_3230_ = v___x_3225_;
goto v_reusejp_3229_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3248_, 1, v_nextMacroScope_3217_);
lean_ctor_set(v_reuseFailAlloc_3248_, 2, v_ngen_3218_);
lean_ctor_set(v_reuseFailAlloc_3248_, 3, v_auxDeclNGen_3219_);
lean_ctor_set(v_reuseFailAlloc_3248_, 4, v_traceState_3220_);
lean_ctor_set(v_reuseFailAlloc_3248_, 5, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3248_, 6, v_messages_3221_);
lean_ctor_set(v_reuseFailAlloc_3248_, 7, v_infoState_3222_);
lean_ctor_set(v_reuseFailAlloc_3248_, 8, v_snapshotTasks_3223_);
v___x_3230_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3229_;
}
v_reusejp_3229_:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v_mctx_3233_; lean_object* v_zetaDeltaFVarIds_3234_; lean_object* v_postponed_3235_; lean_object* v_diag_3236_; lean_object* v___x_3238_; uint8_t v_isShared_3239_; uint8_t v_isSharedCheck_3246_; 
v___x_3231_ = lean_st_ref_set(v___y_3107_, v___x_3230_);
v___x_3232_ = lean_st_ref_take(v___y_3105_);
v_mctx_3233_ = lean_ctor_get(v___x_3232_, 0);
v_zetaDeltaFVarIds_3234_ = lean_ctor_get(v___x_3232_, 2);
v_postponed_3235_ = lean_ctor_get(v___x_3232_, 3);
v_diag_3236_ = lean_ctor_get(v___x_3232_, 4);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3232_);
if (v_isSharedCheck_3246_ == 0)
{
lean_object* v_unused_3247_; 
v_unused_3247_ = lean_ctor_get(v___x_3232_, 1);
lean_dec(v_unused_3247_);
v___x_3238_ = v___x_3232_;
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
else
{
lean_inc(v_diag_3236_);
lean_inc(v_postponed_3235_);
lean_inc(v_zetaDeltaFVarIds_3234_);
lean_inc(v_mctx_3233_);
lean_dec(v___x_3232_);
v___x_3238_ = lean_box(0);
v_isShared_3239_ = v_isSharedCheck_3246_;
goto v_resetjp_3237_;
}
v_resetjp_3237_:
{
lean_object* v___x_3240_; lean_object* v___x_3242_; 
v___x_3240_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3239_ == 0)
{
lean_ctor_set(v___x_3238_, 1, v___x_3240_);
v___x_3242_ = v___x_3238_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_mctx_3233_);
lean_ctor_set(v_reuseFailAlloc_3245_, 1, v___x_3240_);
lean_ctor_set(v_reuseFailAlloc_3245_, 2, v_zetaDeltaFVarIds_3234_);
lean_ctor_set(v_reuseFailAlloc_3245_, 3, v_postponed_3235_);
lean_ctor_set(v_reuseFailAlloc_3245_, 4, v_diag_3236_);
v___x_3242_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_st_ref_set(v___y_3105_, v___x_3242_);
v___x_3244_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_3208_, v___x_3145_, v_compile_3098_, v_logCompileErrors_3099_, v___x_3145_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3244_;
goto v___jp_3114_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3208_);
lean_dec(v_a_3102_);
return v___x_3213_;
}
}
else
{
lean_dec(v_a_3208_);
lean_dec(v_a_3102_);
return v___x_3211_;
}
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_a_3208_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3251_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3209_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3209_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3259_; lean_object* v___x_3261_; uint8_t v_isShared_3262_; uint8_t v_isSharedCheck_3266_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3259_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3266_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3266_ == 0)
{
v___x_3261_ = v___x_3207_;
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
else
{
lean_inc(v_a_3259_);
lean_dec(v___x_3207_);
v___x_3261_ = lean_box(0);
v_isShared_3262_ = v_isSharedCheck_3266_;
goto v_resetjp_3260_;
}
v_resetjp_3260_:
{
lean_object* v___x_3264_; 
if (v_isShared_3262_ == 0)
{
v___x_3264_ = v___x_3261_;
goto v_reusejp_3263_;
}
else
{
lean_object* v_reuseFailAlloc_3265_; 
v_reuseFailAlloc_3265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3265_, 0, v_a_3259_);
v___x_3264_ = v_reuseFailAlloc_3265_;
goto v_reusejp_3263_;
}
v_reusejp_3263_:
{
return v___x_3264_;
}
}
}
}
else
{
lean_object* v___x_3267_; 
lean_dec(v_a_3142_);
lean_inc(v___x_3147_);
v___x_3267_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3137_, v___x_3147_, v___y_3105_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_dec_ref(v___x_3267_);
v_a_3110_ = v___x_3145_;
goto v___jp_3109_;
}
else
{
lean_dec(v_a_3102_);
return v___x_3267_;
}
}
}
else
{
lean_object* v_a_3268_; lean_object* v___x_3270_; uint8_t v_isShared_3271_; uint8_t v_isSharedCheck_3275_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3268_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3275_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3275_ == 0)
{
v___x_3270_ = v___x_3203_;
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
else
{
lean_inc(v_a_3268_);
lean_dec(v___x_3203_);
v___x_3270_ = lean_box(0);
v_isShared_3271_ = v_isSharedCheck_3275_;
goto v_resetjp_3269_;
}
v_resetjp_3269_:
{
lean_object* v___x_3273_; 
if (v_isShared_3271_ == 0)
{
v___x_3273_ = v___x_3270_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3274_; 
v_reuseFailAlloc_3274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3274_, 0, v_a_3268_);
v___x_3273_ = v_reuseFailAlloc_3274_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
return v___x_3273_;
}
}
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3276_ = lean_ctor_get(v___x_3201_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3201_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3201_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3201_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
else
{
goto v___jp_3175_;
}
}
else
{
lean_dec_ref(v_a_3150_);
goto v___jp_3175_;
}
v___jp_3154_:
{
lean_object* v___x_3156_; 
lean_inc(v___x_3147_);
v___x_3156_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3147_, v_a_3142_, v_compile_3098_, v_logCompileErrors_3099_, v_isMeta_3100_, v___x_3137_, v___x_3145_, v_a_3155_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3156_;
goto v___jp_3114_;
}
v___jp_3157_:
{
if (v___y_3159_ == 0)
{
lean_dec_ref(v___y_3158_);
lean_del_object(v___x_3152_);
v_a_3155_ = v___x_3145_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3161_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 1);
lean_ctor_set(v___x_3152_, 0, v___y_3158_);
v___x_3161_ = v___x_3152_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___y_3158_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
v___jp_3163_:
{
uint8_t v___x_3165_; 
v___x_3165_ = l_Lean_Exception_isInterrupt(v_a_3164_);
if (v___x_3165_ == 0)
{
uint8_t v___x_3166_; 
lean_inc_ref(v_a_3164_);
v___x_3166_ = l_Lean_Exception_isRuntime(v_a_3164_);
v___y_3158_ = v_a_3164_;
v___y_3159_ = v___x_3166_;
goto v___jp_3157_;
}
else
{
v___y_3158_ = v_a_3164_;
v___y_3159_ = v___x_3165_;
goto v___jp_3157_;
}
}
v___jp_3167_:
{
if (lean_obj_tag(v___y_3168_) == 0)
{
lean_object* v_a_3169_; 
lean_del_object(v___x_3152_);
v_a_3169_ = lean_ctor_get(v___y_3168_, 0);
lean_inc(v_a_3169_);
lean_dec_ref(v___y_3168_);
if (lean_obj_tag(v_a_3169_) == 0)
{
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
v_a_3110_ = v___x_3145_;
goto v___jp_3109_;
}
else
{
lean_object* v_a_3170_; 
v_a_3170_ = lean_ctor_get(v_a_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v_a_3169_);
v_a_3155_ = v_a_3170_;
goto v___jp_3154_;
}
}
else
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v___y_3168_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v___y_3168_);
v_a_3164_ = v_a_3171_;
goto v___jp_3163_;
}
}
v___jp_3172_:
{
lean_object* v___x_3174_; 
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3106_);
lean_inc(v___y_3105_);
lean_inc_ref(v___y_3104_);
v___x_3174_ = lean_apply_6(v___y_3173_, v___x_3145_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_, lean_box(0));
v___y_3168_ = v___x_3174_;
goto v___jp_3167_;
}
v___jp_3175_:
{
lean_object* v_options_3176_; lean_object* v_inheritedTraceOptions_3177_; lean_object* v___x_3178_; uint8_t v___x_3179_; 
v_options_3176_ = lean_ctor_get(v___y_3106_, 2);
v_inheritedTraceOptions_3177_ = lean_ctor_get(v___y_3106_, 13);
v___x_3178_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3179_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3176_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v___x_3180_; 
lean_del_object(v___x_3152_);
lean_inc(v___x_3147_);
v___x_3180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3147_, v_a_3142_, v_compile_3098_, v_logCompileErrors_3099_, v_isMeta_3100_, v___x_3137_, v___x_3145_, v___x_3145_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3180_;
goto v___jp_3114_;
}
else
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = lean_box(0);
lean_inc(v_a_3142_);
v___x_3182_ = l_Lean_Meta_trySynthInstance(v_a_3142_, v___x_3181_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref(v___x_3182_);
if (lean_obj_tag(v_a_3183_) == 1)
{
lean_object* v_a_3184_; uint8_t v_hasTrace_3185_; lean_object* v___f_3186_; 
v_a_3184_ = lean_ctor_get(v_a_3183_, 0);
lean_inc_n(v_a_3184_, 2);
lean_dec_ref(v_a_3183_);
v_hasTrace_3185_ = lean_ctor_get_uint8(v_options_3176_, sizeof(void*)*1);
lean_inc(v___x_3137_);
v___f_3186_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3186_, 0, v___x_3137_);
lean_closure_set(v___f_3186_, 1, v_a_3184_);
if (v_hasTrace_3185_ == 0)
{
lean_dec(v_a_3184_);
v___y_3173_ = v___f_3186_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3187_; uint8_t v___x_3188_; 
v___x_3187_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3188_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3177_, v_options_3176_, v___x_3187_);
if (v___x_3188_ == 0)
{
lean_dec(v_a_3184_);
v___y_3173_ = v___f_3186_;
goto v___jp_3172_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
lean_dec_ref(v___f_3186_);
v___x_3189_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_3184_);
v___x_3190_ = l_Lean_MessageData_ofExpr(v_a_3184_);
v___x_3191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3189_);
lean_ctor_set(v___x_3191_, 1, v___x_3190_);
v___x_3192_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3146_, v___x_3191_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3194_; 
v_a_3193_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3193_);
lean_dec_ref(v___x_3192_);
lean_inc(v___x_3137_);
v___x_3194_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_3137_, v_a_3184_, v_a_3193_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3168_ = v___x_3194_;
goto v___jp_3167_;
}
else
{
lean_object* v_a_3195_; 
lean_dec(v_a_3184_);
v_a_3195_ = lean_ctor_get(v___x_3192_, 0);
lean_inc(v_a_3195_);
lean_dec_ref(v___x_3192_);
v_a_3164_ = v_a_3195_;
goto v___jp_3163_;
}
}
}
}
else
{
lean_dec(v_a_3183_);
lean_del_object(v___x_3152_);
v_a_3155_ = v___x_3145_;
goto v___jp_3154_;
}
}
else
{
lean_object* v_a_3196_; 
v_a_3196_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3196_);
lean_dec_ref(v___x_3182_);
v_a_3164_ = v_a_3196_;
goto v___jp_3163_;
}
}
}
}
}
else
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3285_ = lean_ctor_get(v___x_3149_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3149_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3149_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3149_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
}
else
{
lean_object* v___x_3293_; 
lean_inc(v___y_3107_);
lean_inc_ref(v___y_3106_);
lean_inc(v___y_3105_);
lean_inc_ref(v___y_3104_);
lean_inc(v___x_3147_);
v___x_3293_ = lean_infer_type(v___x_3147_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v_a_3294_; lean_object* v___x_3295_; 
v_a_3294_ = lean_ctor_get(v___x_3293_, 0);
lean_inc_n(v_a_3294_, 2);
lean_dec_ref(v___x_3293_);
lean_inc(v_a_3142_);
v___x_3295_ = l_Lean_Meta_isExprDefEq(v_a_3142_, v_a_3294_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3295_) == 0)
{
lean_object* v_a_3296_; uint8_t v___x_3297_; 
v_a_3296_ = lean_ctor_get(v___x_3295_, 0);
lean_inc(v_a_3296_);
lean_dec_ref(v___x_3295_);
v___x_3297_ = lean_unbox(v_a_3296_);
lean_dec(v_a_3296_);
if (v___x_3297_ == 0)
{
lean_object* v_options_3298_; lean_object* v_inheritedTraceOptions_3299_; uint8_t v_hasTrace_3300_; 
v_options_3298_ = lean_ctor_get(v___y_3106_, 2);
v_inheritedTraceOptions_3299_ = lean_ctor_get(v___y_3106_, 13);
v_hasTrace_3300_ = lean_ctor_get_uint8(v_options_3298_, sizeof(void*)*1);
if (v_hasTrace_3300_ == 0)
{
lean_dec(v_a_3294_);
goto v___jp_3301_;
}
else
{
lean_object* v___x_3303_; uint8_t v___x_3304_; 
v___x_3303_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3304_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3299_, v_options_3298_, v___x_3303_);
if (v___x_3304_ == 0)
{
lean_dec(v_a_3294_);
goto v___jp_3301_;
}
else
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3305_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_3102_);
v___x_3306_ = l_Nat_reprFast(v_a_3102_);
v___x_3307_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3307_, 0, v___x_3306_);
v___x_3308_ = l_Lean_MessageData_ofFormat(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3305_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
lean_inc(v_a_3142_);
v___x_3312_ = l_Lean_MessageData_ofExpr(v_a_3142_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_MessageData_ofExpr(v_a_3294_);
v___x_3317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3317_, 0, v___x_3315_);
lean_ctor_set(v___x_3317_, 1, v___x_3316_);
v___x_3318_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_3319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3317_);
lean_ctor_set(v___x_3319_, 1, v___x_3318_);
lean_inc(v___x_3147_);
v___x_3320_ = l_Lean_MessageData_ofExpr(v___x_3147_);
v___x_3321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3321_, 0, v___x_3319_);
lean_ctor_set(v___x_3321_, 1, v___x_3320_);
v___x_3322_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3146_, v___x_3321_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
if (lean_obj_tag(v___x_3322_) == 0)
{
lean_object* v_a_3323_; lean_object* v___x_3324_; 
v_a_3323_ = lean_ctor_get(v___x_3322_, 0);
lean_inc(v_a_3323_);
lean_dec_ref(v___x_3322_);
lean_inc(v___x_3147_);
v___x_3324_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_3142_, v___x_3147_, v___x_3097_, v___x_3137_, v___x_3145_, v_a_3323_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3324_;
goto v___jp_3114_;
}
else
{
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
return v___x_3322_;
}
}
}
v___jp_3301_:
{
lean_object* v___x_3302_; 
lean_inc(v___x_3147_);
v___x_3302_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_3142_, v___x_3147_, v___x_3097_, v___x_3137_, v___x_3145_, v___x_3145_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
v___y_3115_ = v___x_3302_;
goto v___jp_3114_;
}
}
else
{
lean_object* v___x_3325_; 
lean_dec(v_a_3294_);
lean_dec(v_a_3142_);
lean_inc(v___x_3147_);
v___x_3325_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3137_, v___x_3147_, v___y_3105_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_dec_ref(v___x_3325_);
v_a_3110_ = v___x_3145_;
goto v___jp_3109_;
}
else
{
lean_dec(v_a_3102_);
return v___x_3325_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec(v_a_3294_);
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3326_ = lean_ctor_get(v___x_3295_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3295_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3295_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3295_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3341_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3334_ = lean_ctor_get(v___x_3293_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v___x_3293_);
if (v_isSharedCheck_3341_ == 0)
{
v___x_3336_ = v___x_3293_;
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3293_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3341_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3339_; 
if (v_isShared_3337_ == 0)
{
v___x_3339_ = v___x_3336_;
goto v_reusejp_3338_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_a_3334_);
v___x_3339_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3338_;
}
v_reusejp_3338_:
{
return v___x_3339_;
}
}
}
}
}
else
{
lean_object* v_a_3342_; lean_object* v___x_3344_; uint8_t v_isShared_3345_; uint8_t v_isSharedCheck_3349_; 
lean_dec(v_a_3142_);
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3342_ = lean_ctor_get(v___x_3143_, 0);
v_isSharedCheck_3349_ = !lean_is_exclusive(v___x_3143_);
if (v_isSharedCheck_3349_ == 0)
{
v___x_3344_ = v___x_3143_;
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
else
{
lean_inc(v_a_3342_);
lean_dec(v___x_3143_);
v___x_3344_ = lean_box(0);
v_isShared_3345_ = v_isSharedCheck_3349_;
goto v_resetjp_3343_;
}
v_resetjp_3343_:
{
lean_object* v___x_3347_; 
if (v_isShared_3345_ == 0)
{
v___x_3347_ = v___x_3344_;
goto v_reusejp_3346_;
}
else
{
lean_object* v_reuseFailAlloc_3348_; 
v_reuseFailAlloc_3348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3348_, 0, v_a_3342_);
v___x_3347_ = v_reuseFailAlloc_3348_;
goto v_reusejp_3346_;
}
v_reusejp_3346_:
{
return v___x_3347_;
}
}
}
}
else
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3357_; 
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3350_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3357_ == 0)
{
v___x_3352_ = v___x_3141_;
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3141_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3357_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3355_; 
if (v_isShared_3353_ == 0)
{
v___x_3355_ = v___x_3352_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v_a_3350_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v___x_3137_);
lean_dec(v_a_3102_);
v_a_3358_ = lean_ctor_get(v___x_3138_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3138_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3138_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3138_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
v___jp_3109_:
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; 
v___x_3111_ = lean_unsigned_to_nat(1u);
v___x_3112_ = lean_nat_add(v_a_3102_, v___x_3111_);
lean_dec(v_a_3102_);
v___x_3113_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_3094_, v_fst_3095_, v_args_3096_, v___x_3097_, v_compile_3098_, v_logCompileErrors_3099_, v_isMeta_3100_, v___x_3101_, v___x_3112_, v_a_3110_, v___y_3104_, v___y_3105_, v___y_3106_, v___y_3107_);
return v___x_3113_;
}
v___jp_3114_:
{
if (lean_obj_tag(v___y_3115_) == 0)
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3125_; 
v_a_3116_ = lean_ctor_get(v___y_3115_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___y_3115_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3118_ = v___y_3115_;
v_isShared_3119_ = v_isSharedCheck_3125_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___y_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3125_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
if (lean_obj_tag(v_a_3116_) == 0)
{
lean_object* v_a_3120_; lean_object* v___x_3122_; 
lean_dec(v_a_3102_);
v_a_3120_ = lean_ctor_get(v_a_3116_, 0);
lean_inc(v_a_3120_);
lean_dec_ref(v_a_3116_);
if (v_isShared_3119_ == 0)
{
lean_ctor_set(v___x_3118_, 0, v_a_3120_);
v___x_3122_ = v___x_3118_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v_a_3120_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
else
{
lean_object* v_a_3124_; 
lean_del_object(v___x_3118_);
v_a_3124_ = lean_ctor_get(v_a_3116_, 0);
lean_inc(v_a_3124_);
lean_dec_ref(v_a_3116_);
v_a_3110_ = v_a_3124_;
goto v___jp_3109_;
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_a_3102_);
v_a_3126_ = lean_ctor_get(v___y_3115_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___y_3115_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___y_3115_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___y_3115_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object* v_a_3366_, lean_object* v_expectedType_3367_, uint8_t v___x_3368_, uint8_t v___x_3369_, uint8_t v_compile_3370_, uint8_t v_logCompileErrors_3371_, uint8_t v_isMeta_3372_, lean_object* v_x_3373_, lean_object* v_x_3374_, lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_){
_start:
{
lean_object* v___y_3382_; lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3404_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3421_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v_options_3424_; lean_object* v___y_3425_; 
if (lean_obj_tag(v_x_3373_) == 5)
{
lean_object* v_fn_3491_; lean_object* v_arg_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; 
v_fn_3491_ = lean_ctor_get(v_x_3373_, 0);
lean_inc_ref(v_fn_3491_);
v_arg_3492_ = lean_ctor_get(v_x_3373_, 1);
lean_inc_ref(v_arg_3492_);
lean_dec_ref(v_x_3373_);
v___x_3493_ = lean_array_set(v_x_3374_, v_x_3375_, v_arg_3492_);
v___x_3494_ = lean_unsigned_to_nat(1u);
v___x_3495_ = lean_nat_sub(v_x_3375_, v___x_3494_);
lean_dec(v_x_3375_);
v_x_3373_ = v_fn_3491_;
v_x_3374_ = v___x_3493_;
v_x_3375_ = v___x_3495_;
goto _start;
}
else
{
lean_object* v_cls_3497_; lean_object* v___y_3499_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___x_3520_; 
lean_dec(v_x_3375_);
v_cls_3497_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3520_ = l_Lean_Expr_constName_x3f(v_x_3373_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
v___y_3499_ = v___y_3376_;
v___y_3500_ = v___y_3377_;
v___y_3501_ = v___y_3378_;
v___y_3502_ = v___y_3379_;
goto v___jp_3498_;
}
else
{
lean_object* v_val_3521_; lean_object* v___x_3522_; 
v_val_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_val_3521_);
lean_dec_ref(v___x_3520_);
v___x_3522_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3521_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref(v___x_3522_);
if (lean_obj_tag(v_a_3523_) == 6)
{
lean_object* v_val_3524_; lean_object* v___x_3525_; 
lean_dec_ref(v_a_3366_);
v_val_3524_ = lean_ctor_get(v_a_3523_, 0);
lean_inc_ref(v_val_3524_);
lean_dec_ref(v_a_3523_);
lean_inc(v___y_3379_);
lean_inc_ref(v___y_3378_);
lean_inc(v___y_3377_);
lean_inc_ref(v___y_3376_);
lean_inc_ref(v_x_3373_);
v___x_3525_ = lean_infer_type(v_x_3373_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; uint8_t v___x_3527_; lean_object* v___x_3528_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
lean_inc(v_a_3526_);
lean_dec_ref(v___x_3525_);
v___x_3527_ = 0;
v___x_3528_ = l_Lean_Meta_forallMetaTelescope(v_a_3526_, v___x_3527_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v_snd_3530_; lean_object* v_fst_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3630_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
lean_inc(v_a_3529_);
lean_dec_ref(v___x_3528_);
v_snd_3530_ = lean_ctor_get(v_a_3529_, 1);
v_fst_3531_ = lean_ctor_get(v_a_3529_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_a_3529_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3533_ = v_a_3529_;
v_isShared_3534_ = v_isSharedCheck_3630_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_snd_3530_);
lean_inc(v_fst_3531_);
lean_dec(v_a_3529_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3630_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v_snd_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3628_; 
v_snd_3535_ = lean_ctor_get(v_snd_3530_, 1);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_snd_3530_);
if (v_isSharedCheck_3628_ == 0)
{
lean_object* v_unused_3629_; 
v_unused_3629_ = lean_ctor_get(v_snd_3530_, 0);
lean_dec(v_unused_3629_);
v___x_3537_ = v_snd_3530_;
v_isShared_3538_ = v_isSharedCheck_3628_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_snd_3535_);
lean_dec(v_snd_3530_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3628_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3539_; lean_object* v___y_3541_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___x_3576_; uint8_t v___x_3577_; 
v___x_3539_ = lean_array_get_size(v_x_3374_);
v___x_3576_ = lean_array_get_size(v_fst_3531_);
v___x_3577_ = lean_nat_dec_eq(v___x_3539_, v___x_3576_);
if (v___x_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3581_; 
lean_dec(v_snd_3535_);
lean_dec(v_fst_3531_);
lean_dec_ref(v_val_3524_);
lean_dec_ref(v_expectedType_3367_);
v___x_3578_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_3579_ = l_Lean_MessageData_ofExpr(v_x_3373_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 7);
lean_ctor_set(v___x_3537_, 1, v___x_3579_);
lean_ctor_set(v___x_3537_, 0, v___x_3578_);
v___x_3581_ = v___x_3537_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3579_);
v___x_3581_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
lean_object* v___x_3582_; lean_object* v___x_3584_; 
v___x_3582_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 7);
lean_ctor_set(v___x_3533_, 1, v___x_3582_);
lean_ctor_set(v___x_3533_, 0, v___x_3581_);
v___x_3584_ = v___x_3533_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3591_, 1, v___x_3582_);
v___x_3584_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
lean_object* v___x_3585_; lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3585_ = lean_array_to_list(v_x_3374_);
v___x_3586_ = lean_box(0);
v___x_3587_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3585_, v___x_3586_);
v___x_3588_ = l_Lean_MessageData_ofList(v___x_3587_);
v___x_3589_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3584_);
lean_ctor_set(v___x_3589_, 1, v___x_3588_);
v___x_3590_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3589_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
return v___x_3590_;
}
}
}
else
{
lean_object* v___x_3593_; 
lean_inc_ref(v_expectedType_3367_);
v___x_3593_ = l_Lean_Meta_isExprDefEq(v_expectedType_3367_, v_snd_3535_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; uint8_t v___x_3595_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
lean_inc(v_a_3594_);
lean_dec_ref(v___x_3593_);
v___x_3595_ = lean_unbox(v_a_3594_);
lean_dec(v_a_3594_);
if (v___x_3595_ == 0)
{
lean_object* v_toConstantVal_3596_; lean_object* v_name_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3601_; 
lean_dec(v_fst_3531_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
v_toConstantVal_3596_ = lean_ctor_get(v_val_3524_, 0);
lean_inc_ref(v_toConstantVal_3596_);
lean_dec_ref(v_val_3524_);
v_name_3597_ = lean_ctor_get(v_toConstantVal_3596_, 0);
lean_inc(v_name_3597_);
lean_dec_ref(v_toConstantVal_3596_);
v___x_3598_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_3599_ = l_Lean_MessageData_ofExpr(v_expectedType_3367_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set_tag(v___x_3537_, 7);
lean_ctor_set(v___x_3537_, 1, v___x_3599_);
lean_ctor_set(v___x_3537_, 0, v___x_3598_);
v___x_3601_ = v___x_3537_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3598_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___x_3599_);
v___x_3601_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_3534_ == 0)
{
lean_ctor_set_tag(v___x_3533_, 7);
lean_ctor_set(v___x_3533_, 1, v___x_3602_);
lean_ctor_set(v___x_3533_, 0, v___x_3601_);
v___x_3604_ = v___x_3533_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v___x_3601_);
lean_ctor_set(v_reuseFailAlloc_3618_, 1, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
v___x_3605_ = l_Lean_MessageData_ofConstName(v_name_3597_, v___x_3368_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3604_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3608_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_);
v_a_3610_ = lean_ctor_get(v___x_3609_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3609_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3609_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3609_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
}
else
{
lean_del_object(v___x_3537_);
lean_del_object(v___x_3533_);
lean_dec_ref(v_expectedType_3367_);
v___y_3541_ = v___y_3376_;
v___y_3542_ = v___y_3377_;
v___y_3543_ = v___y_3378_;
v___y_3544_ = v___y_3379_;
goto v___jp_3540_;
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3537_);
lean_del_object(v___x_3533_);
lean_dec(v_fst_3531_);
lean_dec_ref(v_val_3524_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
lean_dec_ref(v_expectedType_3367_);
v_a_3620_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3593_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3593_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
v___jp_3540_:
{
lean_object* v_numParams_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; 
v_numParams_3545_ = lean_ctor_get(v_val_3524_, 3);
lean_inc(v_numParams_3545_);
lean_dec_ref(v_val_3524_);
v___x_3546_ = lean_box(0);
v___x_3547_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_3539_, v_fst_3531_, v_x_3374_, v___x_3369_, v_compile_3370_, v_logCompileErrors_3371_, v_isMeta_3372_, v___x_3368_, v_numParams_3545_, v___x_3546_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec_ref(v_x_3374_);
if (lean_obj_tag(v___x_3547_) == 0)
{
size_t v_sz_3548_; size_t v___x_3549_; lean_object* v___x_3550_; 
lean_dec_ref(v___x_3547_);
v_sz_3548_ = lean_array_size(v_fst_3531_);
v___x_3549_ = ((size_t)0ULL);
v___x_3550_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3548_, v___x_3549_, v_fst_3531_, v___y_3542_);
if (lean_obj_tag(v___x_3550_) == 0)
{
lean_object* v_a_3551_; lean_object* v___x_3553_; uint8_t v_isShared_3554_; uint8_t v_isSharedCheck_3559_; 
v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3559_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3559_ == 0)
{
v___x_3553_ = v___x_3550_;
v_isShared_3554_ = v_isSharedCheck_3559_;
goto v_resetjp_3552_;
}
else
{
lean_inc(v_a_3551_);
lean_dec(v___x_3550_);
v___x_3553_ = lean_box(0);
v_isShared_3554_ = v_isSharedCheck_3559_;
goto v_resetjp_3552_;
}
v_resetjp_3552_:
{
lean_object* v___x_3555_; lean_object* v___x_3557_; 
v___x_3555_ = l_Lean_mkAppN(v_x_3373_, v_a_3551_);
lean_dec(v_a_3551_);
if (v_isShared_3554_ == 0)
{
lean_ctor_set(v___x_3553_, 0, v___x_3555_);
v___x_3557_ = v___x_3553_;
goto v_reusejp_3556_;
}
else
{
lean_object* v_reuseFailAlloc_3558_; 
v_reuseFailAlloc_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3558_, 0, v___x_3555_);
v___x_3557_ = v_reuseFailAlloc_3558_;
goto v_reusejp_3556_;
}
v_reusejp_3556_:
{
return v___x_3557_;
}
}
}
else
{
lean_object* v_a_3560_; lean_object* v___x_3562_; uint8_t v_isShared_3563_; uint8_t v_isSharedCheck_3567_; 
lean_dec_ref(v_x_3373_);
v_a_3560_ = lean_ctor_get(v___x_3550_, 0);
v_isSharedCheck_3567_ = !lean_is_exclusive(v___x_3550_);
if (v_isSharedCheck_3567_ == 0)
{
v___x_3562_ = v___x_3550_;
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
else
{
lean_inc(v_a_3560_);
lean_dec(v___x_3550_);
v___x_3562_ = lean_box(0);
v_isShared_3563_ = v_isSharedCheck_3567_;
goto v_resetjp_3561_;
}
v_resetjp_3561_:
{
lean_object* v___x_3565_; 
if (v_isShared_3563_ == 0)
{
v___x_3565_ = v___x_3562_;
goto v_reusejp_3564_;
}
else
{
lean_object* v_reuseFailAlloc_3566_; 
v_reuseFailAlloc_3566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3566_, 0, v_a_3560_);
v___x_3565_ = v_reuseFailAlloc_3566_;
goto v_reusejp_3564_;
}
v_reusejp_3564_:
{
return v___x_3565_;
}
}
}
}
else
{
lean_object* v_a_3568_; lean_object* v___x_3570_; uint8_t v_isShared_3571_; uint8_t v_isSharedCheck_3575_; 
lean_dec(v_fst_3531_);
lean_dec_ref(v_x_3373_);
v_a_3568_ = lean_ctor_get(v___x_3547_, 0);
v_isSharedCheck_3575_ = !lean_is_exclusive(v___x_3547_);
if (v_isSharedCheck_3575_ == 0)
{
v___x_3570_ = v___x_3547_;
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
else
{
lean_inc(v_a_3568_);
lean_dec(v___x_3547_);
v___x_3570_ = lean_box(0);
v_isShared_3571_ = v_isSharedCheck_3575_;
goto v_resetjp_3569_;
}
v_resetjp_3569_:
{
lean_object* v___x_3573_; 
if (v_isShared_3571_ == 0)
{
v___x_3573_ = v___x_3570_;
goto v_reusejp_3572_;
}
else
{
lean_object* v_reuseFailAlloc_3574_; 
v_reuseFailAlloc_3574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3574_, 0, v_a_3568_);
v___x_3573_ = v_reuseFailAlloc_3574_;
goto v_reusejp_3572_;
}
v_reusejp_3572_:
{
return v___x_3573_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec_ref(v_val_3524_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
lean_dec_ref(v_expectedType_3367_);
v_a_3631_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3528_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3528_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_dec_ref(v_val_3524_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
lean_dec_ref(v_expectedType_3367_);
return v___x_3525_;
}
}
else
{
lean_dec(v_a_3523_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
v___y_3499_ = v___y_3376_;
v___y_3500_ = v___y_3377_;
v___y_3501_ = v___y_3378_;
v___y_3502_ = v___y_3379_;
goto v___jp_3498_;
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_x_3373_);
lean_dec_ref(v_expectedType_3367_);
lean_dec_ref(v_a_3366_);
v_a_3639_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3522_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3522_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
v___jp_3498_:
{
lean_object* v_options_3503_; uint8_t v_hasTrace_3504_; 
v_options_3503_ = lean_ctor_get(v___y_3501_, 2);
v_hasTrace_3504_ = lean_ctor_get_uint8(v_options_3503_, sizeof(void*)*1);
if (v_hasTrace_3504_ == 0)
{
v___y_3421_ = v___y_3499_;
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v_options_3424_ = v_options_3503_;
v___y_3425_ = v___y_3502_;
goto v___jp_3420_;
}
else
{
lean_object* v_inheritedTraceOptions_3505_; lean_object* v___x_3506_; uint8_t v___x_3507_; 
v_inheritedTraceOptions_3505_ = lean_ctor_get(v___y_3501_, 13);
v___x_3506_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3507_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3505_, v_options_3503_, v___x_3506_);
if (v___x_3507_ == 0)
{
v___y_3421_ = v___y_3499_;
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v_options_3424_ = v_options_3503_;
v___y_3425_ = v___y_3502_;
goto v___jp_3420_;
}
else
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
v___x_3508_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_3366_);
v___x_3509_ = l_Lean_MessageData_ofExpr(v_a_3366_);
v___x_3510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3508_);
lean_ctor_set(v___x_3510_, 1, v___x_3509_);
v___x_3511_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3497_, v___x_3510_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_dec_ref(v___x_3511_);
v___y_3421_ = v___y_3499_;
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v_options_3424_ = v_options_3503_;
v___y_3425_ = v___y_3502_;
goto v___jp_3420_;
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_dec_ref(v_expectedType_3367_);
lean_dec_ref(v_a_3366_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
}
}
}
v___jp_3381_:
{
lean_object* v___x_3386_; 
v___x_3386_ = l_Lean_enableRealizationsForConst(v___y_3382_, v___y_3384_, v___y_3385_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3393_; 
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
lean_ctor_set(v___x_3388_, 0, v___y_3383_);
v___x_3391_ = v___x_3388_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___y_3383_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec_ref(v___y_3383_);
v_a_3395_ = lean_ctor_get(v___x_3386_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3386_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3386_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
v___jp_3403_:
{
if (v_compile_3370_ == 0)
{
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
goto v___jp_3381_;
}
else
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3408_ = lean_unsigned_to_nat(1u);
v___x_3409_ = lean_mk_empty_array_with_capacity(v___x_3408_);
lean_inc(v___y_3404_);
v___x_3410_ = lean_array_push(v___x_3409_, v___y_3404_);
v___x_3411_ = l_Lean_compileDecls(v___x_3410_, v_logCompileErrors_3371_, v___y_3406_, v___y_3407_);
if (lean_obj_tag(v___x_3411_) == 0)
{
lean_dec_ref(v___x_3411_);
v___y_3382_ = v___y_3404_;
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
goto v___jp_3381_;
}
else
{
lean_object* v_a_3412_; lean_object* v___x_3414_; uint8_t v_isShared_3415_; uint8_t v_isSharedCheck_3419_; 
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
v_a_3412_ = lean_ctor_get(v___x_3411_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v___x_3411_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3414_ = v___x_3411_;
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
else
{
lean_inc(v_a_3412_);
lean_dec(v___x_3411_);
v___x_3414_ = lean_box(0);
v_isShared_3415_ = v_isSharedCheck_3419_;
goto v_resetjp_3413_;
}
v_resetjp_3413_:
{
lean_object* v___x_3417_; 
if (v_isShared_3415_ == 0)
{
v___x_3417_ = v___x_3414_;
goto v_reusejp_3416_;
}
else
{
lean_object* v_reuseFailAlloc_3418_; 
v_reuseFailAlloc_3418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3418_, 0, v_a_3412_);
v___x_3417_ = v_reuseFailAlloc_3418_;
goto v_reusejp_3416_;
}
v_reusejp_3416_:
{
return v___x_3417_;
}
}
}
}
}
v___jp_3420_:
{
lean_object* v___x_3426_; uint8_t v___x_3427_; 
v___x_3426_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3427_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3424_, v___x_3426_);
if (v___x_3427_ == 0)
{
lean_object* v___x_3428_; 
lean_dec_ref(v_expectedType_3367_);
v___x_3428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3428_, 0, v_a_3366_);
return v___x_3428_;
}
else
{
lean_object* v___x_3429_; 
lean_inc(v___y_3425_);
lean_inc_ref(v___y_3423_);
lean_inc(v___y_3422_);
lean_inc_ref(v___y_3421_);
lean_inc_ref(v_a_3366_);
v___x_3429_ = lean_infer_type(v_a_3366_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3425_);
if (lean_obj_tag(v___x_3429_) == 0)
{
lean_object* v_a_3430_; lean_object* v___x_3431_; 
v_a_3430_ = lean_ctor_get(v___x_3429_, 0);
lean_inc(v_a_3430_);
lean_dec_ref(v___x_3429_);
lean_inc_ref(v_expectedType_3367_);
v___x_3431_ = l_Lean_Meta_isExprDefEq(v_expectedType_3367_, v_a_3430_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3425_);
if (lean_obj_tag(v___x_3431_) == 0)
{
lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3482_; 
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3482_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3482_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3482_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3482_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
uint8_t v___x_3436_; 
v___x_3436_ = lean_unbox(v_a_3432_);
lean_dec(v_a_3432_);
if (v___x_3436_ == 0)
{
lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v_a_3439_; lean_object* v___x_3440_; 
lean_del_object(v___x_3434_);
v___x_3437_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3438_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3437_, v___y_3425_);
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
lean_inc_n(v_a_3439_, 2);
lean_dec_ref(v___x_3438_);
v___x_3440_ = l_Lean_Meta_mkAuxDefinition(v_a_3439_, v_expectedType_3367_, v_a_3366_, v___x_3368_, v___x_3368_, v___x_3369_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3425_);
if (lean_obj_tag(v___x_3440_) == 0)
{
lean_object* v_a_3441_; uint8_t v___x_3442_; lean_object* v___x_3443_; 
v_a_3441_ = lean_ctor_get(v___x_3440_, 0);
lean_inc(v_a_3441_);
lean_dec_ref(v___x_3440_);
v___x_3442_ = 3;
lean_inc(v_a_3439_);
v___x_3443_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3439_, v___x_3442_, v___y_3422_, v___y_3425_);
lean_dec_ref(v___x_3443_);
if (v_isMeta_3372_ == 0)
{
v___y_3404_ = v_a_3439_;
v___y_3405_ = v_a_3441_;
v___y_3406_ = v___y_3423_;
v___y_3407_ = v___y_3425_;
goto v___jp_3403_;
}
else
{
lean_object* v___x_3444_; lean_object* v_env_3445_; lean_object* v_nextMacroScope_3446_; lean_object* v_ngen_3447_; lean_object* v_auxDeclNGen_3448_; lean_object* v_traceState_3449_; lean_object* v_messages_3450_; lean_object* v_infoState_3451_; lean_object* v_snapshotTasks_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3477_; 
v___x_3444_ = lean_st_ref_take(v___y_3425_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
v_nextMacroScope_3446_ = lean_ctor_get(v___x_3444_, 1);
v_ngen_3447_ = lean_ctor_get(v___x_3444_, 2);
v_auxDeclNGen_3448_ = lean_ctor_get(v___x_3444_, 3);
v_traceState_3449_ = lean_ctor_get(v___x_3444_, 4);
v_messages_3450_ = lean_ctor_get(v___x_3444_, 6);
v_infoState_3451_ = lean_ctor_get(v___x_3444_, 7);
v_snapshotTasks_3452_ = lean_ctor_get(v___x_3444_, 8);
v_isSharedCheck_3477_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3477_ == 0)
{
lean_object* v_unused_3478_; 
v_unused_3478_ = lean_ctor_get(v___x_3444_, 5);
lean_dec(v_unused_3478_);
v___x_3454_ = v___x_3444_;
v_isShared_3455_ = v_isSharedCheck_3477_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_snapshotTasks_3452_);
lean_inc(v_infoState_3451_);
lean_inc(v_messages_3450_);
lean_inc(v_traceState_3449_);
lean_inc(v_auxDeclNGen_3448_);
lean_inc(v_ngen_3447_);
lean_inc(v_nextMacroScope_3446_);
lean_inc(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3477_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3459_; 
lean_inc(v_a_3439_);
v___x_3456_ = l_Lean_markMeta(v_env_3445_, v_a_3439_);
v___x_3457_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 5, v___x_3457_);
lean_ctor_set(v___x_3454_, 0, v___x_3456_);
v___x_3459_ = v___x_3454_;
goto v_reusejp_3458_;
}
else
{
lean_object* v_reuseFailAlloc_3476_; 
v_reuseFailAlloc_3476_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3476_, 0, v___x_3456_);
lean_ctor_set(v_reuseFailAlloc_3476_, 1, v_nextMacroScope_3446_);
lean_ctor_set(v_reuseFailAlloc_3476_, 2, v_ngen_3447_);
lean_ctor_set(v_reuseFailAlloc_3476_, 3, v_auxDeclNGen_3448_);
lean_ctor_set(v_reuseFailAlloc_3476_, 4, v_traceState_3449_);
lean_ctor_set(v_reuseFailAlloc_3476_, 5, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3476_, 6, v_messages_3450_);
lean_ctor_set(v_reuseFailAlloc_3476_, 7, v_infoState_3451_);
lean_ctor_set(v_reuseFailAlloc_3476_, 8, v_snapshotTasks_3452_);
v___x_3459_ = v_reuseFailAlloc_3476_;
goto v_reusejp_3458_;
}
v_reusejp_3458_:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v_mctx_3462_; lean_object* v_zetaDeltaFVarIds_3463_; lean_object* v_postponed_3464_; lean_object* v_diag_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3474_; 
v___x_3460_ = lean_st_ref_set(v___y_3425_, v___x_3459_);
v___x_3461_ = lean_st_ref_take(v___y_3422_);
v_mctx_3462_ = lean_ctor_get(v___x_3461_, 0);
v_zetaDeltaFVarIds_3463_ = lean_ctor_get(v___x_3461_, 2);
v_postponed_3464_ = lean_ctor_get(v___x_3461_, 3);
v_diag_3465_ = lean_ctor_get(v___x_3461_, 4);
v_isSharedCheck_3474_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3474_ == 0)
{
lean_object* v_unused_3475_; 
v_unused_3475_ = lean_ctor_get(v___x_3461_, 1);
lean_dec(v_unused_3475_);
v___x_3467_ = v___x_3461_;
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_diag_3465_);
lean_inc(v_postponed_3464_);
lean_inc(v_zetaDeltaFVarIds_3463_);
lean_inc(v_mctx_3462_);
lean_dec(v___x_3461_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3474_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3469_; lean_object* v___x_3471_; 
v___x_3469_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3468_ == 0)
{
lean_ctor_set(v___x_3467_, 1, v___x_3469_);
v___x_3471_ = v___x_3467_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3473_; 
v_reuseFailAlloc_3473_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3473_, 0, v_mctx_3462_);
lean_ctor_set(v_reuseFailAlloc_3473_, 1, v___x_3469_);
lean_ctor_set(v_reuseFailAlloc_3473_, 2, v_zetaDeltaFVarIds_3463_);
lean_ctor_set(v_reuseFailAlloc_3473_, 3, v_postponed_3464_);
lean_ctor_set(v_reuseFailAlloc_3473_, 4, v_diag_3465_);
v___x_3471_ = v_reuseFailAlloc_3473_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
lean_object* v___x_3472_; 
v___x_3472_ = lean_st_ref_set(v___y_3422_, v___x_3471_);
v___y_3404_ = v_a_3439_;
v___y_3405_ = v_a_3441_;
v___y_3406_ = v___y_3423_;
v___y_3407_ = v___y_3425_;
goto v___jp_3403_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3439_);
return v___x_3440_;
}
}
else
{
lean_object* v___x_3480_; 
lean_dec_ref(v_expectedType_3367_);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v_a_3366_);
v___x_3480_ = v___x_3434_;
goto v_reusejp_3479_;
}
else
{
lean_object* v_reuseFailAlloc_3481_; 
v_reuseFailAlloc_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3481_, 0, v_a_3366_);
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
else
{
lean_object* v_a_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3490_; 
lean_dec_ref(v_expectedType_3367_);
lean_dec_ref(v_a_3366_);
v_a_3483_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3490_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3490_ == 0)
{
v___x_3485_ = v___x_3431_;
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_a_3483_);
lean_dec(v___x_3431_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3490_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3489_; 
v_reuseFailAlloc_3489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_a_3483_);
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
else
{
lean_dec_ref(v_expectedType_3367_);
lean_dec_ref(v_a_3366_);
return v___x_3429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_a_3647_, lean_object* v_expectedType_3648_, uint8_t v___x_3649_, uint8_t v___x_3650_, uint8_t v_compile_3651_, uint8_t v_logCompileErrors_3652_, uint8_t v_isMeta_3653_, lean_object* v_x_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_, lean_object* v___y_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_){
_start:
{
lean_object* v___y_3663_; lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3685_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3702_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v_options_3705_; lean_object* v___y_3706_; 
if (lean_obj_tag(v_x_3654_) == 5)
{
lean_object* v_fn_3772_; lean_object* v_arg_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; 
v_fn_3772_ = lean_ctor_get(v_x_3654_, 0);
lean_inc_ref(v_fn_3772_);
v_arg_3773_ = lean_ctor_get(v_x_3654_, 1);
lean_inc_ref(v_arg_3773_);
lean_dec_ref(v_x_3654_);
v___x_3774_ = lean_array_set(v_x_3655_, v_x_3656_, v_arg_3773_);
v___x_3775_ = lean_unsigned_to_nat(1u);
v___x_3776_ = lean_nat_sub(v_x_3656_, v___x_3775_);
v___x_3777_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_a_3647_, v_expectedType_3648_, v___x_3649_, v___x_3650_, v_compile_3651_, v_logCompileErrors_3652_, v_isMeta_3653_, v_fn_3772_, v___x_3774_, v___x_3776_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3777_;
}
else
{
lean_object* v_cls_3778_; lean_object* v___y_3780_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___x_3801_; 
v_cls_3778_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3801_ = l_Lean_Expr_constName_x3f(v_x_3654_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
v___y_3780_ = v___y_3657_;
v___y_3781_ = v___y_3658_;
v___y_3782_ = v___y_3659_;
v___y_3783_ = v___y_3660_;
goto v___jp_3779_;
}
else
{
lean_object* v_val_3802_; lean_object* v___x_3803_; 
v_val_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_val_3802_);
lean_dec_ref(v___x_3801_);
v___x_3803_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3802_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3804_);
lean_dec_ref(v___x_3803_);
if (lean_obj_tag(v_a_3804_) == 6)
{
lean_object* v_val_3805_; lean_object* v___x_3806_; 
lean_dec_ref(v_a_3647_);
v_val_3805_ = lean_ctor_get(v_a_3804_, 0);
lean_inc_ref(v_val_3805_);
lean_dec_ref(v_a_3804_);
lean_inc(v___y_3660_);
lean_inc_ref(v___y_3659_);
lean_inc(v___y_3658_);
lean_inc_ref(v___y_3657_);
lean_inc_ref(v_x_3654_);
v___x_3806_ = lean_infer_type(v_x_3654_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3806_) == 0)
{
lean_object* v_a_3807_; uint8_t v___x_3808_; lean_object* v___x_3809_; 
v_a_3807_ = lean_ctor_get(v___x_3806_, 0);
lean_inc(v_a_3807_);
lean_dec_ref(v___x_3806_);
v___x_3808_ = 0;
v___x_3809_ = l_Lean_Meta_forallMetaTelescope(v_a_3807_, v___x_3808_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3809_) == 0)
{
lean_object* v_a_3810_; lean_object* v_snd_3811_; lean_object* v_fst_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3911_; 
v_a_3810_ = lean_ctor_get(v___x_3809_, 0);
lean_inc(v_a_3810_);
lean_dec_ref(v___x_3809_);
v_snd_3811_ = lean_ctor_get(v_a_3810_, 1);
v_fst_3812_ = lean_ctor_get(v_a_3810_, 0);
v_isSharedCheck_3911_ = !lean_is_exclusive(v_a_3810_);
if (v_isSharedCheck_3911_ == 0)
{
v___x_3814_ = v_a_3810_;
v_isShared_3815_ = v_isSharedCheck_3911_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_snd_3811_);
lean_inc(v_fst_3812_);
lean_dec(v_a_3810_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3911_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v_snd_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3909_; 
v_snd_3816_ = lean_ctor_get(v_snd_3811_, 1);
v_isSharedCheck_3909_ = !lean_is_exclusive(v_snd_3811_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v_snd_3811_, 0);
lean_dec(v_unused_3910_);
v___x_3818_ = v_snd_3811_;
v_isShared_3819_ = v_isSharedCheck_3909_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_snd_3816_);
lean_dec(v_snd_3811_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3909_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v___x_3820_; lean_object* v___y_3822_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___x_3857_; uint8_t v___x_3858_; 
v___x_3820_ = lean_array_get_size(v_x_3655_);
v___x_3857_ = lean_array_get_size(v_fst_3812_);
v___x_3858_ = lean_nat_dec_eq(v___x_3820_, v___x_3857_);
if (v___x_3858_ == 0)
{
lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___x_3862_; 
lean_dec(v_snd_3816_);
lean_dec(v_fst_3812_);
lean_dec_ref(v_val_3805_);
lean_dec_ref(v_expectedType_3648_);
v___x_3859_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_3860_ = l_Lean_MessageData_ofExpr(v_x_3654_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set_tag(v___x_3818_, 7);
lean_ctor_set(v___x_3818_, 1, v___x_3860_);
lean_ctor_set(v___x_3818_, 0, v___x_3859_);
v___x_3862_ = v___x_3818_;
goto v_reusejp_3861_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___x_3860_);
v___x_3862_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3861_;
}
v_reusejp_3861_:
{
lean_object* v___x_3863_; lean_object* v___x_3865_; 
v___x_3863_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 7);
lean_ctor_set(v___x_3814_, 1, v___x_3863_);
lean_ctor_set(v___x_3814_, 0, v___x_3862_);
v___x_3865_ = v___x_3814_;
goto v_reusejp_3864_;
}
else
{
lean_object* v_reuseFailAlloc_3872_; 
v_reuseFailAlloc_3872_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3872_, 0, v___x_3862_);
lean_ctor_set(v_reuseFailAlloc_3872_, 1, v___x_3863_);
v___x_3865_ = v_reuseFailAlloc_3872_;
goto v_reusejp_3864_;
}
v_reusejp_3864_:
{
lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3866_ = lean_array_to_list(v_x_3655_);
v___x_3867_ = lean_box(0);
v___x_3868_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3866_, v___x_3867_);
v___x_3869_ = l_Lean_MessageData_ofList(v___x_3868_);
v___x_3870_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3870_, 0, v___x_3865_);
lean_ctor_set(v___x_3870_, 1, v___x_3869_);
v___x_3871_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3870_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
return v___x_3871_;
}
}
}
else
{
lean_object* v___x_3874_; 
lean_inc_ref(v_expectedType_3648_);
v___x_3874_ = l_Lean_Meta_isExprDefEq(v_expectedType_3648_, v_snd_3816_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
if (lean_obj_tag(v___x_3874_) == 0)
{
lean_object* v_a_3875_; uint8_t v___x_3876_; 
v_a_3875_ = lean_ctor_get(v___x_3874_, 0);
lean_inc(v_a_3875_);
lean_dec_ref(v___x_3874_);
v___x_3876_ = lean_unbox(v_a_3875_);
lean_dec(v_a_3875_);
if (v___x_3876_ == 0)
{
lean_object* v_toConstantVal_3877_; lean_object* v_name_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3882_; 
lean_dec(v_fst_3812_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
v_toConstantVal_3877_ = lean_ctor_get(v_val_3805_, 0);
lean_inc_ref(v_toConstantVal_3877_);
lean_dec_ref(v_val_3805_);
v_name_3878_ = lean_ctor_get(v_toConstantVal_3877_, 0);
lean_inc(v_name_3878_);
lean_dec_ref(v_toConstantVal_3877_);
v___x_3879_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_3880_ = l_Lean_MessageData_ofExpr(v_expectedType_3648_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set_tag(v___x_3818_, 7);
lean_ctor_set(v___x_3818_, 1, v___x_3880_);
lean_ctor_set(v___x_3818_, 0, v___x_3879_);
v___x_3882_ = v___x_3818_;
goto v_reusejp_3881_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___x_3880_);
v___x_3882_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3881_;
}
v_reusejp_3881_:
{
lean_object* v___x_3883_; lean_object* v___x_3885_; 
v___x_3883_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_3815_ == 0)
{
lean_ctor_set_tag(v___x_3814_, 7);
lean_ctor_set(v___x_3814_, 1, v___x_3883_);
lean_ctor_set(v___x_3814_, 0, v___x_3882_);
v___x_3885_ = v___x_3814_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3882_);
lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___x_3883_);
v___x_3885_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3898_; 
v___x_3886_ = l_Lean_MessageData_ofConstName(v_name_3878_, v___x_3649_);
v___x_3887_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3887_, 0, v___x_3885_);
lean_ctor_set(v___x_3887_, 1, v___x_3886_);
v___x_3888_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_3889_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3887_);
lean_ctor_set(v___x_3889_, 1, v___x_3888_);
v___x_3890_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3889_, v___y_3657_, v___y_3658_, v___y_3659_, v___y_3660_);
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3898_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3896_; 
if (v_isShared_3894_ == 0)
{
v___x_3896_ = v___x_3893_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v_a_3891_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
}
}
else
{
lean_del_object(v___x_3818_);
lean_del_object(v___x_3814_);
lean_dec_ref(v_expectedType_3648_);
v___y_3822_ = v___y_3657_;
v___y_3823_ = v___y_3658_;
v___y_3824_ = v___y_3659_;
v___y_3825_ = v___y_3660_;
goto v___jp_3821_;
}
}
else
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3908_; 
lean_del_object(v___x_3818_);
lean_del_object(v___x_3814_);
lean_dec(v_fst_3812_);
lean_dec_ref(v_val_3805_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
lean_dec_ref(v_expectedType_3648_);
v_a_3901_ = lean_ctor_get(v___x_3874_, 0);
v_isSharedCheck_3908_ = !lean_is_exclusive(v___x_3874_);
if (v_isSharedCheck_3908_ == 0)
{
v___x_3903_ = v___x_3874_;
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3874_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3908_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3906_; 
if (v_isShared_3904_ == 0)
{
v___x_3906_ = v___x_3903_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
v___jp_3821_:
{
lean_object* v_numParams_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; 
v_numParams_3826_ = lean_ctor_get(v_val_3805_, 3);
lean_inc(v_numParams_3826_);
lean_dec_ref(v_val_3805_);
v___x_3827_ = lean_box(0);
v___x_3828_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_3820_, v_fst_3812_, v_x_3655_, v___x_3650_, v_compile_3651_, v_logCompileErrors_3652_, v_isMeta_3653_, v___x_3649_, v_numParams_3826_, v___x_3827_, v___y_3822_, v___y_3823_, v___y_3824_, v___y_3825_);
lean_dec_ref(v_x_3655_);
if (lean_obj_tag(v___x_3828_) == 0)
{
size_t v_sz_3829_; size_t v___x_3830_; lean_object* v___x_3831_; 
lean_dec_ref(v___x_3828_);
v_sz_3829_ = lean_array_size(v_fst_3812_);
v___x_3830_ = ((size_t)0ULL);
v___x_3831_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3829_, v___x_3830_, v_fst_3812_, v___y_3823_);
if (lean_obj_tag(v___x_3831_) == 0)
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3840_; 
v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3840_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3840_ == 0)
{
v___x_3834_ = v___x_3831_;
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3831_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3840_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3836_; lean_object* v___x_3838_; 
v___x_3836_ = l_Lean_mkAppN(v_x_3654_, v_a_3832_);
lean_dec(v_a_3832_);
if (v_isShared_3835_ == 0)
{
lean_ctor_set(v___x_3834_, 0, v___x_3836_);
v___x_3838_ = v___x_3834_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v___x_3836_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
return v___x_3838_;
}
}
}
else
{
lean_object* v_a_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3848_; 
lean_dec_ref(v_x_3654_);
v_a_3841_ = lean_ctor_get(v___x_3831_, 0);
v_isSharedCheck_3848_ = !lean_is_exclusive(v___x_3831_);
if (v_isSharedCheck_3848_ == 0)
{
v___x_3843_ = v___x_3831_;
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_a_3841_);
lean_dec(v___x_3831_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3848_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v___x_3846_; 
if (v_isShared_3844_ == 0)
{
v___x_3846_ = v___x_3843_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v_a_3841_);
v___x_3846_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
return v___x_3846_;
}
}
}
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec(v_fst_3812_);
lean_dec_ref(v_x_3654_);
v_a_3849_ = lean_ctor_get(v___x_3828_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3828_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3828_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3828_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_val_3805_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
lean_dec_ref(v_expectedType_3648_);
v_a_3912_ = lean_ctor_get(v___x_3809_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3809_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3809_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3809_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
else
{
lean_dec_ref(v_val_3805_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
lean_dec_ref(v_expectedType_3648_);
return v___x_3806_;
}
}
else
{
lean_dec(v_a_3804_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
v___y_3780_ = v___y_3657_;
v___y_3781_ = v___y_3658_;
v___y_3782_ = v___y_3659_;
v___y_3783_ = v___y_3660_;
goto v___jp_3779_;
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_x_3654_);
lean_dec_ref(v_expectedType_3648_);
lean_dec_ref(v_a_3647_);
v_a_3920_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3803_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3803_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
v___jp_3779_:
{
lean_object* v_options_3784_; uint8_t v_hasTrace_3785_; 
v_options_3784_ = lean_ctor_get(v___y_3782_, 2);
v_hasTrace_3785_ = lean_ctor_get_uint8(v_options_3784_, sizeof(void*)*1);
if (v_hasTrace_3785_ == 0)
{
v___y_3702_ = v___y_3780_;
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v_options_3705_ = v_options_3784_;
v___y_3706_ = v___y_3783_;
goto v___jp_3701_;
}
else
{
lean_object* v_inheritedTraceOptions_3786_; lean_object* v___x_3787_; uint8_t v___x_3788_; 
v_inheritedTraceOptions_3786_ = lean_ctor_get(v___y_3782_, 13);
v___x_3787_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3788_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3786_, v_options_3784_, v___x_3787_);
if (v___x_3788_ == 0)
{
v___y_3702_ = v___y_3780_;
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v_options_3705_ = v_options_3784_;
v___y_3706_ = v___y_3783_;
goto v___jp_3701_;
}
else
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3789_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_3647_);
v___x_3790_ = l_Lean_MessageData_ofExpr(v_a_3647_);
v___x_3791_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3791_, 0, v___x_3789_);
lean_ctor_set(v___x_3791_, 1, v___x_3790_);
v___x_3792_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3778_, v___x_3791_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_dec_ref(v___x_3792_);
v___y_3702_ = v___y_3780_;
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v_options_3705_ = v_options_3784_;
v___y_3706_ = v___y_3783_;
goto v___jp_3701_;
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_dec_ref(v_expectedType_3648_);
lean_dec_ref(v_a_3647_);
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
}
}
}
v___jp_3662_:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_enableRealizationsForConst(v___y_3664_, v___y_3665_, v___y_3666_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3674_ == 0)
{
lean_object* v_unused_3675_; 
v_unused_3675_ = lean_ctor_get(v___x_3667_, 0);
lean_dec(v_unused_3675_);
v___x_3669_ = v___x_3667_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_dec(v___x_3667_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
lean_ctor_set(v___x_3669_, 0, v___y_3663_);
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___y_3663_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
else
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3683_; 
lean_dec_ref(v___y_3663_);
v_a_3676_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3683_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3683_ == 0)
{
v___x_3678_ = v___x_3667_;
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3667_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3683_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3681_; 
if (v_isShared_3679_ == 0)
{
v___x_3681_ = v___x_3678_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
return v___x_3681_;
}
}
}
}
v___jp_3684_:
{
if (v_compile_3651_ == 0)
{
v___y_3663_ = v___y_3685_;
v___y_3664_ = v___y_3686_;
v___y_3665_ = v___y_3687_;
v___y_3666_ = v___y_3688_;
goto v___jp_3662_;
}
else
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; 
v___x_3689_ = lean_unsigned_to_nat(1u);
v___x_3690_ = lean_mk_empty_array_with_capacity(v___x_3689_);
lean_inc(v___y_3686_);
v___x_3691_ = lean_array_push(v___x_3690_, v___y_3686_);
v___x_3692_ = l_Lean_compileDecls(v___x_3691_, v_logCompileErrors_3652_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3692_) == 0)
{
lean_dec_ref(v___x_3692_);
v___y_3663_ = v___y_3685_;
v___y_3664_ = v___y_3686_;
v___y_3665_ = v___y_3687_;
v___y_3666_ = v___y_3688_;
goto v___jp_3662_;
}
else
{
lean_object* v_a_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3700_; 
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
v_a_3693_ = lean_ctor_get(v___x_3692_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3692_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3695_ = v___x_3692_;
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_a_3693_);
lean_dec(v___x_3692_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3700_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3698_; 
if (v_isShared_3696_ == 0)
{
v___x_3698_ = v___x_3695_;
goto v_reusejp_3697_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
v___x_3698_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3697_;
}
v_reusejp_3697_:
{
return v___x_3698_;
}
}
}
}
}
v___jp_3701_:
{
lean_object* v___x_3707_; uint8_t v___x_3708_; 
v___x_3707_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3708_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3705_, v___x_3707_);
if (v___x_3708_ == 0)
{
lean_object* v___x_3709_; 
lean_dec_ref(v_expectedType_3648_);
v___x_3709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3709_, 0, v_a_3647_);
return v___x_3709_;
}
else
{
lean_object* v___x_3710_; 
lean_inc(v___y_3706_);
lean_inc_ref(v___y_3704_);
lean_inc(v___y_3703_);
lean_inc_ref(v___y_3702_);
lean_inc_ref(v_a_3647_);
v___x_3710_ = lean_infer_type(v_a_3647_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3706_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref(v___x_3710_);
lean_inc_ref(v_expectedType_3648_);
v___x_3712_ = l_Lean_Meta_isExprDefEq(v_expectedType_3648_, v_a_3711_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3706_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3763_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3763_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3763_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
uint8_t v___x_3717_; 
v___x_3717_ = lean_unbox(v_a_3713_);
lean_dec(v_a_3713_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v_a_3720_; lean_object* v___x_3721_; 
lean_del_object(v___x_3715_);
v___x_3718_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3719_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3718_, v___y_3706_);
v_a_3720_ = lean_ctor_get(v___x_3719_, 0);
lean_inc_n(v_a_3720_, 2);
lean_dec_ref(v___x_3719_);
v___x_3721_ = l_Lean_Meta_mkAuxDefinition(v_a_3720_, v_expectedType_3648_, v_a_3647_, v___x_3649_, v___x_3649_, v___x_3650_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3706_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; uint8_t v___x_3723_; lean_object* v___x_3724_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
lean_inc(v_a_3722_);
lean_dec_ref(v___x_3721_);
v___x_3723_ = 3;
lean_inc(v_a_3720_);
v___x_3724_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3720_, v___x_3723_, v___y_3703_, v___y_3706_);
lean_dec_ref(v___x_3724_);
if (v_isMeta_3653_ == 0)
{
v___y_3685_ = v_a_3722_;
v___y_3686_ = v_a_3720_;
v___y_3687_ = v___y_3704_;
v___y_3688_ = v___y_3706_;
goto v___jp_3684_;
}
else
{
lean_object* v___x_3725_; lean_object* v_env_3726_; lean_object* v_nextMacroScope_3727_; lean_object* v_ngen_3728_; lean_object* v_auxDeclNGen_3729_; lean_object* v_traceState_3730_; lean_object* v_messages_3731_; lean_object* v_infoState_3732_; lean_object* v_snapshotTasks_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3758_; 
v___x_3725_ = lean_st_ref_take(v___y_3706_);
v_env_3726_ = lean_ctor_get(v___x_3725_, 0);
v_nextMacroScope_3727_ = lean_ctor_get(v___x_3725_, 1);
v_ngen_3728_ = lean_ctor_get(v___x_3725_, 2);
v_auxDeclNGen_3729_ = lean_ctor_get(v___x_3725_, 3);
v_traceState_3730_ = lean_ctor_get(v___x_3725_, 4);
v_messages_3731_ = lean_ctor_get(v___x_3725_, 6);
v_infoState_3732_ = lean_ctor_get(v___x_3725_, 7);
v_snapshotTasks_3733_ = lean_ctor_get(v___x_3725_, 8);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3725_);
if (v_isSharedCheck_3758_ == 0)
{
lean_object* v_unused_3759_; 
v_unused_3759_ = lean_ctor_get(v___x_3725_, 5);
lean_dec(v_unused_3759_);
v___x_3735_ = v___x_3725_;
v_isShared_3736_ = v_isSharedCheck_3758_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_snapshotTasks_3733_);
lean_inc(v_infoState_3732_);
lean_inc(v_messages_3731_);
lean_inc(v_traceState_3730_);
lean_inc(v_auxDeclNGen_3729_);
lean_inc(v_ngen_3728_);
lean_inc(v_nextMacroScope_3727_);
lean_inc(v_env_3726_);
lean_dec(v___x_3725_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3758_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; lean_object* v___x_3740_; 
lean_inc(v_a_3720_);
v___x_3737_ = l_Lean_markMeta(v_env_3726_, v_a_3720_);
v___x_3738_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 5, v___x_3738_);
lean_ctor_set(v___x_3735_, 0, v___x_3737_);
v___x_3740_ = v___x_3735_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v___x_3737_);
lean_ctor_set(v_reuseFailAlloc_3757_, 1, v_nextMacroScope_3727_);
lean_ctor_set(v_reuseFailAlloc_3757_, 2, v_ngen_3728_);
lean_ctor_set(v_reuseFailAlloc_3757_, 3, v_auxDeclNGen_3729_);
lean_ctor_set(v_reuseFailAlloc_3757_, 4, v_traceState_3730_);
lean_ctor_set(v_reuseFailAlloc_3757_, 5, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3757_, 6, v_messages_3731_);
lean_ctor_set(v_reuseFailAlloc_3757_, 7, v_infoState_3732_);
lean_ctor_set(v_reuseFailAlloc_3757_, 8, v_snapshotTasks_3733_);
v___x_3740_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v_mctx_3743_; lean_object* v_zetaDeltaFVarIds_3744_; lean_object* v_postponed_3745_; lean_object* v_diag_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3755_; 
v___x_3741_ = lean_st_ref_set(v___y_3706_, v___x_3740_);
v___x_3742_ = lean_st_ref_take(v___y_3703_);
v_mctx_3743_ = lean_ctor_get(v___x_3742_, 0);
v_zetaDeltaFVarIds_3744_ = lean_ctor_get(v___x_3742_, 2);
v_postponed_3745_ = lean_ctor_get(v___x_3742_, 3);
v_diag_3746_ = lean_ctor_get(v___x_3742_, 4);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3755_ == 0)
{
lean_object* v_unused_3756_; 
v_unused_3756_ = lean_ctor_get(v___x_3742_, 1);
lean_dec(v_unused_3756_);
v___x_3748_ = v___x_3742_;
v_isShared_3749_ = v_isSharedCheck_3755_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_diag_3746_);
lean_inc(v_postponed_3745_);
lean_inc(v_zetaDeltaFVarIds_3744_);
lean_inc(v_mctx_3743_);
lean_dec(v___x_3742_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3755_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; lean_object* v___x_3752_; 
v___x_3750_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 1, v___x_3750_);
v___x_3752_ = v___x_3748_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_mctx_3743_);
lean_ctor_set(v_reuseFailAlloc_3754_, 1, v___x_3750_);
lean_ctor_set(v_reuseFailAlloc_3754_, 2, v_zetaDeltaFVarIds_3744_);
lean_ctor_set(v_reuseFailAlloc_3754_, 3, v_postponed_3745_);
lean_ctor_set(v_reuseFailAlloc_3754_, 4, v_diag_3746_);
v___x_3752_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
lean_object* v___x_3753_; 
v___x_3753_ = lean_st_ref_set(v___y_3703_, v___x_3752_);
v___y_3685_ = v_a_3722_;
v___y_3686_ = v_a_3720_;
v___y_3687_ = v___y_3704_;
v___y_3688_ = v___y_3706_;
goto v___jp_3684_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3720_);
return v___x_3721_;
}
}
else
{
lean_object* v___x_3761_; 
lean_dec_ref(v_expectedType_3648_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v_a_3647_);
v___x_3761_ = v___x_3715_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3647_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3771_; 
lean_dec_ref(v_expectedType_3648_);
lean_dec_ref(v_a_3647_);
v_a_3764_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3771_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3771_ == 0)
{
v___x_3766_ = v___x_3712_;
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3712_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3771_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v___x_3769_; 
if (v_isShared_3767_ == 0)
{
v___x_3769_ = v___x_3766_;
goto v_reusejp_3768_;
}
else
{
lean_object* v_reuseFailAlloc_3770_; 
v_reuseFailAlloc_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3770_, 0, v_a_3764_);
v___x_3769_ = v_reuseFailAlloc_3770_;
goto v_reusejp_3768_;
}
v_reusejp_3768_:
{
return v___x_3769_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3648_);
lean_dec_ref(v_a_3647_);
return v___x_3710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_3928_, lean_object* v_inst_3929_, uint8_t v___x_3930_, uint8_t v_hasTrace_3931_, uint8_t v_compile_3932_, uint8_t v_logCompileErrors_3933_, uint8_t v_isMeta_3934_, lean_object* v_____r_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_){
_start:
{
lean_object* v___x_3941_; 
lean_inc_ref(v_expectedType_3928_);
v___x_3941_ = l_Lean_Meta_isProp(v_expectedType_3928_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
if (lean_obj_tag(v___x_3941_) == 0)
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3963_; 
v_a_3942_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3944_ = v___x_3941_;
v_isShared_3945_ = v_isSharedCheck_3963_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3941_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3963_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
uint8_t v___x_3946_; 
v___x_3946_ = lean_unbox(v_a_3942_);
lean_dec(v_a_3942_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
lean_del_object(v___x_3944_);
lean_inc(v___y_3939_);
lean_inc_ref(v___y_3938_);
lean_inc(v___y_3937_);
lean_inc_ref(v___y_3936_);
v___x_3947_ = lean_whnf(v_inst_3929_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
if (lean_obj_tag(v___x_3947_) == 0)
{
lean_object* v_a_3948_; lean_object* v_dummy_3949_; lean_object* v_nargs_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; 
v_a_3948_ = lean_ctor_get(v___x_3947_, 0);
lean_inc_n(v_a_3948_, 2);
lean_dec_ref(v___x_3947_);
v_dummy_3949_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3950_ = l_Lean_Expr_getAppNumArgs(v_a_3948_);
lean_inc(v_nargs_3950_);
v___x_3951_ = lean_mk_array(v_nargs_3950_, v_dummy_3949_);
v___x_3952_ = lean_unsigned_to_nat(1u);
v___x_3953_ = lean_nat_sub(v_nargs_3950_, v___x_3952_);
lean_dec(v_nargs_3950_);
v___x_3954_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_3948_, v_expectedType_3928_, v___x_3930_, v_hasTrace_3931_, v_compile_3932_, v_logCompileErrors_3933_, v_isMeta_3934_, v_a_3948_, v___x_3951_, v___x_3953_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___x_3953_);
return v___x_3954_;
}
else
{
lean_dec_ref(v_expectedType_3928_);
return v___x_3947_;
}
}
else
{
lean_object* v_options_3955_; lean_object* v___x_3956_; uint8_t v___x_3957_; 
v_options_3955_ = lean_ctor_get(v___y_3938_, 2);
v___x_3956_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3957_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3955_, v___x_3956_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3959_; 
lean_dec_ref(v_expectedType_3928_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v_inst_3929_);
v___x_3959_ = v___x_3944_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_inst_3929_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; 
lean_del_object(v___x_3944_);
v___x_3961_ = lean_box(0);
v___x_3962_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3928_, v_inst_3929_, v_hasTrace_3931_, v___x_3961_, v_hasTrace_3931_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
return v___x_3962_;
}
}
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_dec_ref(v_inst_3929_);
lean_dec_ref(v_expectedType_3928_);
v_a_3964_ = lean_ctor_get(v___x_3941_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3941_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3941_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3941_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_3973_; lean_object* v___x_3974_; 
v___x_3973_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_3974_ = l_Lean_stringToMessageData(v___x_3973_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(lean_object* v_upperBound_3975_, lean_object* v_fst_3976_, lean_object* v_args_3977_, uint8_t v___x_3978_, uint8_t v_compile_3979_, uint8_t v_logCompileErrors_3980_, uint8_t v_isMeta_3981_, lean_object* v_a_3982_, lean_object* v_b_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v_a_3990_; lean_object* v___y_3995_; uint8_t v___x_4014_; 
v___x_4014_ = lean_nat_dec_lt(v_a_3982_, v_upperBound_3975_);
if (v___x_4014_ == 0)
{
lean_object* v___x_4015_; 
lean_dec(v_a_3982_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v_b_3983_);
return v___x_4015_;
}
else
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = lean_array_fget_borrowed(v_fst_3976_, v_a_3982_);
v___x_4017_ = l_Lean_Expr_mvarId_x21(v___x_4016_);
lean_inc(v___x_4017_);
v___x_4018_ = l_Lean_MVarId_getDecl(v___x_4017_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v_type_4020_; lean_object* v___x_4021_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
lean_inc(v_a_4019_);
lean_dec_ref(v___x_4018_);
v_type_4020_ = lean_ctor_get(v_a_4019_, 2);
lean_inc_ref(v_type_4020_);
lean_dec(v_a_4019_);
v___x_4021_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4020_, v___y_3985_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc_n(v_a_4022_, 2);
lean_dec_ref(v___x_4021_);
v___x_4023_ = l_Lean_Meta_isProp(v_a_4022_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; lean_object* v_cls_4026_; lean_object* v___x_4027_; uint8_t v___x_4028_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref(v___x_4023_);
v___x_4025_ = lean_box(0);
v_cls_4026_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4027_ = lean_array_fget_borrowed(v_args_3977_, v_a_3982_);
v___x_4028_ = lean_unbox(v_a_4024_);
lean_dec(v_a_4024_);
if (v___x_4028_ == 0)
{
lean_object* v___x_4029_; 
lean_inc(v_a_4022_);
v___x_4029_ = l_Lean_Meta_isClass_x3f(v_a_4022_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4164_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4164_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4164_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
if (lean_obj_tag(v_a_4030_) == 0)
{
lean_del_object(v___x_4032_);
goto v___jp_4034_;
}
else
{
lean_dec_ref(v_a_4030_);
if (v___x_3978_ == 0)
{
lean_del_object(v___x_4032_);
goto v___jp_4034_;
}
else
{
lean_object* v_options_4124_; lean_object* v_inheritedTraceOptions_4125_; lean_object* v_a_4127_; lean_object* v___y_4130_; uint8_t v___y_4131_; lean_object* v_a_4136_; lean_object* v___y_4140_; lean_object* v___x_4144_; uint8_t v___x_4145_; 
v_options_4124_ = lean_ctor_get(v___y_3986_, 2);
v_inheritedTraceOptions_4125_ = lean_ctor_get(v___y_3986_, 13);
v___x_4144_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4145_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4124_, v___x_4144_);
if (v___x_4145_ == 0)
{
lean_object* v___x_4146_; 
lean_del_object(v___x_4032_);
lean_inc(v___x_4027_);
v___x_4146_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4027_, v_a_4022_, v_compile_3979_, v_logCompileErrors_3980_, v_isMeta_3981_, v___x_4017_, v___x_4025_, v___x_4025_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4146_;
goto v___jp_3994_;
}
else
{
lean_object* v___x_4147_; lean_object* v___x_4148_; 
v___x_4147_ = lean_box(0);
lean_inc(v_a_4022_);
v___x_4148_ = l_Lean_Meta_trySynthInstance(v_a_4022_, v___x_4147_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref(v___x_4148_);
if (lean_obj_tag(v_a_4149_) == 1)
{
lean_object* v_a_4150_; uint8_t v_hasTrace_4151_; 
v_a_4150_ = lean_ctor_get(v_a_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v_a_4149_);
v_hasTrace_4151_ = lean_ctor_get_uint8(v_options_4124_, sizeof(void*)*1);
if (v_hasTrace_4151_ == 0)
{
goto v___jp_4152_;
}
else
{
lean_object* v___x_4154_; uint8_t v___x_4155_; 
v___x_4154_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4155_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4125_, v_options_4124_, v___x_4154_);
if (v___x_4155_ == 0)
{
goto v___jp_4152_;
}
else
{
lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; 
v___x_4156_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_4150_);
v___x_4157_ = l_Lean_MessageData_ofExpr(v_a_4150_);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4026_, v___x_4158_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; lean_object* v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref(v___x_4159_);
lean_inc(v___x_4017_);
v___x_4161_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4017_, v_a_4150_, v_a_4160_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_4140_ = v___x_4161_;
goto v___jp_4139_;
}
else
{
lean_object* v_a_4162_; 
lean_dec(v_a_4150_);
v_a_4162_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4162_);
lean_dec_ref(v___x_4159_);
v_a_4136_ = v_a_4162_;
goto v___jp_4135_;
}
}
}
v___jp_4152_:
{
lean_object* v___x_4153_; 
lean_inc(v___x_4017_);
v___x_4153_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4017_, v_a_4150_, v___x_4025_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_4140_ = v___x_4153_;
goto v___jp_4139_;
}
}
else
{
lean_dec(v_a_4149_);
lean_del_object(v___x_4032_);
v_a_4127_ = v___x_4025_;
goto v___jp_4126_;
}
}
else
{
lean_object* v_a_4163_; 
v_a_4163_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4163_);
lean_dec_ref(v___x_4148_);
v_a_4136_ = v_a_4163_;
goto v___jp_4135_;
}
}
v___jp_4126_:
{
lean_object* v___x_4128_; 
lean_inc(v___x_4027_);
v___x_4128_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4027_, v_a_4022_, v_compile_3979_, v_logCompileErrors_3980_, v_isMeta_3981_, v___x_4017_, v___x_4025_, v_a_4127_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4128_;
goto v___jp_3994_;
}
v___jp_4129_:
{
if (v___y_4131_ == 0)
{
lean_dec_ref(v___y_4130_);
lean_del_object(v___x_4032_);
v_a_4127_ = v___x_4025_;
goto v___jp_4126_;
}
else
{
lean_object* v___x_4133_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
if (v_isShared_4033_ == 0)
{
lean_ctor_set_tag(v___x_4032_, 1);
lean_ctor_set(v___x_4032_, 0, v___y_4130_);
v___x_4133_ = v___x_4032_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___y_4130_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
}
v___jp_4135_:
{
uint8_t v___x_4137_; 
v___x_4137_ = l_Lean_Exception_isInterrupt(v_a_4136_);
if (v___x_4137_ == 0)
{
uint8_t v___x_4138_; 
lean_inc_ref(v_a_4136_);
v___x_4138_ = l_Lean_Exception_isRuntime(v_a_4136_);
v___y_4130_ = v_a_4136_;
v___y_4131_ = v___x_4138_;
goto v___jp_4129_;
}
else
{
v___y_4130_ = v_a_4136_;
v___y_4131_ = v___x_4137_;
goto v___jp_4129_;
}
}
v___jp_4139_:
{
if (lean_obj_tag(v___y_4140_) == 0)
{
lean_object* v_a_4141_; 
lean_del_object(v___x_4032_);
v_a_4141_ = lean_ctor_get(v___y_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref(v___y_4140_);
if (lean_obj_tag(v_a_4141_) == 0)
{
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
v_a_3990_ = v___x_4025_;
goto v___jp_3989_;
}
else
{
lean_object* v_a_4142_; 
v_a_4142_ = lean_ctor_get(v_a_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v_a_4141_);
v_a_4127_ = v_a_4142_;
goto v___jp_4126_;
}
}
else
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v___y_4140_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v___y_4140_);
v_a_4136_ = v_a_4143_;
goto v___jp_4135_;
}
}
}
}
v___jp_4034_:
{
lean_object* v_options_4035_; lean_object* v___x_4036_; uint8_t v___x_4037_; 
v_options_4035_ = lean_ctor_get(v___y_3986_, 2);
v___x_4036_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_4037_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4035_, v___x_4036_);
if (v___x_4037_ == 0)
{
lean_object* v___x_4038_; 
lean_dec(v_a_4022_);
lean_inc(v___x_4027_);
v___x_4038_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4017_, v___x_4027_, v___y_3985_);
if (lean_obj_tag(v___x_4038_) == 0)
{
lean_dec_ref(v___x_4038_);
v_a_3990_ = v___x_4025_;
goto v___jp_3989_;
}
else
{
lean_dec(v_a_3982_);
return v___x_4038_;
}
}
else
{
lean_object* v___x_4039_; 
lean_inc(v___y_3987_);
lean_inc_ref(v___y_3986_);
lean_inc(v___y_3985_);
lean_inc_ref(v___y_3984_);
lean_inc(v___x_4027_);
v___x_4039_ = lean_infer_type(v___x_4027_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4041_; 
v_a_4040_ = lean_ctor_get(v___x_4039_, 0);
lean_inc(v_a_4040_);
lean_dec_ref(v___x_4039_);
lean_inc(v_a_4022_);
v___x_4041_ = l_Lean_Meta_isExprDefEq(v_a_4022_, v_a_4040_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; uint8_t v___x_4043_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc(v_a_4042_);
lean_dec_ref(v___x_4041_);
v___x_4043_ = lean_unbox(v_a_4042_);
if (v___x_4043_ == 0)
{
lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4044_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4045_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4044_, v___y_3987_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; uint8_t v___x_4047_; uint8_t v___x_4048_; lean_object* v___x_4049_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc_n(v_a_4046_, 2);
lean_dec_ref(v___x_4045_);
v___x_4047_ = lean_unbox(v_a_4042_);
v___x_4048_ = lean_unbox(v_a_4042_);
lean_dec(v_a_4042_);
lean_inc(v___x_4027_);
v___x_4049_ = l_Lean_Meta_mkAuxDefinition(v_a_4046_, v_a_4022_, v___x_4027_, v___x_4047_, v___x_4048_, v___x_3978_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4051_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4050_);
lean_dec_ref(v___x_4049_);
v___x_4051_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4017_, v_a_4050_, v___y_3985_);
if (lean_obj_tag(v___x_4051_) == 0)
{
uint8_t v___x_4052_; lean_object* v___x_4053_; 
lean_dec_ref(v___x_4051_);
v___x_4052_ = 0;
lean_inc(v_a_4046_);
v___x_4053_ = l_Lean_Meta_setInlineAttribute(v_a_4046_, v___x_4052_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_dec_ref(v___x_4053_);
if (v_isMeta_3981_ == 0)
{
lean_object* v___x_4054_; 
v___x_4054_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4046_, v___x_4025_, v_compile_3979_, v_logCompileErrors_3980_, v___x_4025_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4054_;
goto v___jp_3994_;
}
else
{
lean_object* v___x_4055_; lean_object* v_env_4056_; lean_object* v_nextMacroScope_4057_; lean_object* v_ngen_4058_; lean_object* v_auxDeclNGen_4059_; lean_object* v_traceState_4060_; lean_object* v_messages_4061_; lean_object* v_infoState_4062_; lean_object* v_snapshotTasks_4063_; lean_object* v___x_4065_; uint8_t v_isShared_4066_; uint8_t v_isSharedCheck_4089_; 
v___x_4055_ = lean_st_ref_take(v___y_3987_);
v_env_4056_ = lean_ctor_get(v___x_4055_, 0);
v_nextMacroScope_4057_ = lean_ctor_get(v___x_4055_, 1);
v_ngen_4058_ = lean_ctor_get(v___x_4055_, 2);
v_auxDeclNGen_4059_ = lean_ctor_get(v___x_4055_, 3);
v_traceState_4060_ = lean_ctor_get(v___x_4055_, 4);
v_messages_4061_ = lean_ctor_get(v___x_4055_, 6);
v_infoState_4062_ = lean_ctor_get(v___x_4055_, 7);
v_snapshotTasks_4063_ = lean_ctor_get(v___x_4055_, 8);
v_isSharedCheck_4089_ = !lean_is_exclusive(v___x_4055_);
if (v_isSharedCheck_4089_ == 0)
{
lean_object* v_unused_4090_; 
v_unused_4090_ = lean_ctor_get(v___x_4055_, 5);
lean_dec(v_unused_4090_);
v___x_4065_ = v___x_4055_;
v_isShared_4066_ = v_isSharedCheck_4089_;
goto v_resetjp_4064_;
}
else
{
lean_inc(v_snapshotTasks_4063_);
lean_inc(v_infoState_4062_);
lean_inc(v_messages_4061_);
lean_inc(v_traceState_4060_);
lean_inc(v_auxDeclNGen_4059_);
lean_inc(v_ngen_4058_);
lean_inc(v_nextMacroScope_4057_);
lean_inc(v_env_4056_);
lean_dec(v___x_4055_);
v___x_4065_ = lean_box(0);
v_isShared_4066_ = v_isSharedCheck_4089_;
goto v_resetjp_4064_;
}
v_resetjp_4064_:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; lean_object* v___x_4070_; 
lean_inc(v_a_4046_);
v___x_4067_ = l_Lean_markMeta(v_env_4056_, v_a_4046_);
v___x_4068_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4066_ == 0)
{
lean_ctor_set(v___x_4065_, 5, v___x_4068_);
lean_ctor_set(v___x_4065_, 0, v___x_4067_);
v___x_4070_ = v___x_4065_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4088_; 
v_reuseFailAlloc_4088_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4067_);
lean_ctor_set(v_reuseFailAlloc_4088_, 1, v_nextMacroScope_4057_);
lean_ctor_set(v_reuseFailAlloc_4088_, 2, v_ngen_4058_);
lean_ctor_set(v_reuseFailAlloc_4088_, 3, v_auxDeclNGen_4059_);
lean_ctor_set(v_reuseFailAlloc_4088_, 4, v_traceState_4060_);
lean_ctor_set(v_reuseFailAlloc_4088_, 5, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4088_, 6, v_messages_4061_);
lean_ctor_set(v_reuseFailAlloc_4088_, 7, v_infoState_4062_);
lean_ctor_set(v_reuseFailAlloc_4088_, 8, v_snapshotTasks_4063_);
v___x_4070_ = v_reuseFailAlloc_4088_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v_mctx_4073_; lean_object* v_zetaDeltaFVarIds_4074_; lean_object* v_postponed_4075_; lean_object* v_diag_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4086_; 
v___x_4071_ = lean_st_ref_set(v___y_3987_, v___x_4070_);
v___x_4072_ = lean_st_ref_take(v___y_3985_);
v_mctx_4073_ = lean_ctor_get(v___x_4072_, 0);
v_zetaDeltaFVarIds_4074_ = lean_ctor_get(v___x_4072_, 2);
v_postponed_4075_ = lean_ctor_get(v___x_4072_, 3);
v_diag_4076_ = lean_ctor_get(v___x_4072_, 4);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4086_ == 0)
{
lean_object* v_unused_4087_; 
v_unused_4087_ = lean_ctor_get(v___x_4072_, 1);
lean_dec(v_unused_4087_);
v___x_4078_ = v___x_4072_;
v_isShared_4079_ = v_isSharedCheck_4086_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_diag_4076_);
lean_inc(v_postponed_4075_);
lean_inc(v_zetaDeltaFVarIds_4074_);
lean_inc(v_mctx_4073_);
lean_dec(v___x_4072_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4086_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4080_; lean_object* v___x_4082_; 
v___x_4080_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4079_ == 0)
{
lean_ctor_set(v___x_4078_, 1, v___x_4080_);
v___x_4082_ = v___x_4078_;
goto v_reusejp_4081_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_mctx_4073_);
lean_ctor_set(v_reuseFailAlloc_4085_, 1, v___x_4080_);
lean_ctor_set(v_reuseFailAlloc_4085_, 2, v_zetaDeltaFVarIds_4074_);
lean_ctor_set(v_reuseFailAlloc_4085_, 3, v_postponed_4075_);
lean_ctor_set(v_reuseFailAlloc_4085_, 4, v_diag_4076_);
v___x_4082_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4081_;
}
v_reusejp_4081_:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = lean_st_ref_set(v___y_3985_, v___x_4082_);
v___x_4084_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4046_, v___x_4025_, v_compile_3979_, v_logCompileErrors_3980_, v___x_4025_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4084_;
goto v___jp_3994_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4046_);
lean_dec(v_a_3982_);
return v___x_4053_;
}
}
else
{
lean_dec(v_a_4046_);
lean_dec(v_a_3982_);
return v___x_4051_;
}
}
else
{
lean_object* v_a_4091_; lean_object* v___x_4093_; uint8_t v_isShared_4094_; uint8_t v_isSharedCheck_4098_; 
lean_dec(v_a_4046_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4091_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4098_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4098_ == 0)
{
v___x_4093_ = v___x_4049_;
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
else
{
lean_inc(v_a_4091_);
lean_dec(v___x_4049_);
v___x_4093_ = lean_box(0);
v_isShared_4094_ = v_isSharedCheck_4098_;
goto v_resetjp_4092_;
}
v_resetjp_4092_:
{
lean_object* v___x_4096_; 
if (v_isShared_4094_ == 0)
{
v___x_4096_ = v___x_4093_;
goto v_reusejp_4095_;
}
else
{
lean_object* v_reuseFailAlloc_4097_; 
v_reuseFailAlloc_4097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4097_, 0, v_a_4091_);
v___x_4096_ = v_reuseFailAlloc_4097_;
goto v_reusejp_4095_;
}
v_reusejp_4095_:
{
return v___x_4096_;
}
}
}
}
else
{
lean_object* v_a_4099_; lean_object* v___x_4101_; uint8_t v_isShared_4102_; uint8_t v_isSharedCheck_4106_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4099_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4106_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4106_ == 0)
{
v___x_4101_ = v___x_4045_;
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
else
{
lean_inc(v_a_4099_);
lean_dec(v___x_4045_);
v___x_4101_ = lean_box(0);
v_isShared_4102_ = v_isSharedCheck_4106_;
goto v_resetjp_4100_;
}
v_resetjp_4100_:
{
lean_object* v___x_4104_; 
if (v_isShared_4102_ == 0)
{
v___x_4104_ = v___x_4101_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v_a_4099_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
}
}
else
{
lean_object* v___x_4107_; 
lean_dec(v_a_4042_);
lean_dec(v_a_4022_);
lean_inc(v___x_4027_);
v___x_4107_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4017_, v___x_4027_, v___y_3985_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_dec_ref(v___x_4107_);
v_a_3990_ = v___x_4025_;
goto v___jp_3989_;
}
else
{
lean_dec(v_a_3982_);
return v___x_4107_;
}
}
}
else
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4115_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4108_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4115_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4115_ == 0)
{
v___x_4110_ = v___x_4041_;
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4041_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4115_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v___x_4113_; 
if (v_isShared_4111_ == 0)
{
v___x_4113_ = v___x_4110_;
goto v_reusejp_4112_;
}
else
{
lean_object* v_reuseFailAlloc_4114_; 
v_reuseFailAlloc_4114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_a_4108_);
v___x_4113_ = v_reuseFailAlloc_4114_;
goto v_reusejp_4112_;
}
v_reusejp_4112_:
{
return v___x_4113_;
}
}
}
}
else
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4123_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4116_ = lean_ctor_get(v___x_4039_, 0);
v_isSharedCheck_4123_ = !lean_is_exclusive(v___x_4039_);
if (v_isSharedCheck_4123_ == 0)
{
v___x_4118_ = v___x_4039_;
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4039_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4123_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4121_; 
if (v_isShared_4119_ == 0)
{
v___x_4121_ = v___x_4118_;
goto v_reusejp_4120_;
}
else
{
lean_object* v_reuseFailAlloc_4122_; 
v_reuseFailAlloc_4122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
v___x_4121_ = v_reuseFailAlloc_4122_;
goto v_reusejp_4120_;
}
v_reusejp_4120_:
{
return v___x_4121_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4165_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4029_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4029_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
else
{
lean_object* v___x_4173_; 
lean_inc(v___y_3987_);
lean_inc_ref(v___y_3986_);
lean_inc(v___y_3985_);
lean_inc_ref(v___y_3984_);
lean_inc(v___x_4027_);
v___x_4173_ = lean_infer_type(v___x_4027_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4173_) == 0)
{
lean_object* v_a_4174_; lean_object* v___x_4175_; 
v_a_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc_n(v_a_4174_, 2);
lean_dec_ref(v___x_4173_);
lean_inc(v_a_4022_);
v___x_4175_ = l_Lean_Meta_isExprDefEq(v_a_4022_, v_a_4174_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4175_) == 0)
{
lean_object* v_a_4176_; uint8_t v___x_4177_; 
v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
lean_inc(v_a_4176_);
lean_dec_ref(v___x_4175_);
v___x_4177_ = lean_unbox(v_a_4176_);
lean_dec(v_a_4176_);
if (v___x_4177_ == 0)
{
lean_object* v_options_4178_; lean_object* v_inheritedTraceOptions_4179_; uint8_t v_hasTrace_4180_; 
v_options_4178_ = lean_ctor_get(v___y_3986_, 2);
v_inheritedTraceOptions_4179_ = lean_ctor_get(v___y_3986_, 13);
v_hasTrace_4180_ = lean_ctor_get_uint8(v_options_4178_, sizeof(void*)*1);
if (v_hasTrace_4180_ == 0)
{
lean_dec(v_a_4174_);
goto v___jp_4181_;
}
else
{
lean_object* v___x_4183_; uint8_t v___x_4184_; 
v___x_4183_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4184_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4179_, v_options_4178_, v___x_4183_);
if (v___x_4184_ == 0)
{
lean_dec(v_a_4174_);
goto v___jp_4181_;
}
else
{
lean_object* v___x_4185_; lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4185_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_3982_);
v___x_4186_ = l_Nat_reprFast(v_a_3982_);
v___x_4187_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4187_, 0, v___x_4186_);
v___x_4188_ = l_Lean_MessageData_ofFormat(v___x_4187_);
v___x_4189_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4189_, 0, v___x_4185_);
lean_ctor_set(v___x_4189_, 1, v___x_4188_);
v___x_4190_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_4191_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4191_, 0, v___x_4189_);
lean_ctor_set(v___x_4191_, 1, v___x_4190_);
lean_inc(v_a_4022_);
v___x_4192_ = l_Lean_MessageData_ofExpr(v_a_4022_);
v___x_4193_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4193_, 0, v___x_4191_);
lean_ctor_set(v___x_4193_, 1, v___x_4192_);
v___x_4194_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_4195_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4195_, 0, v___x_4193_);
lean_ctor_set(v___x_4195_, 1, v___x_4194_);
v___x_4196_ = l_Lean_MessageData_ofExpr(v_a_4174_);
v___x_4197_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4195_);
lean_ctor_set(v___x_4197_, 1, v___x_4196_);
v___x_4198_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_4199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4199_, 0, v___x_4197_);
lean_ctor_set(v___x_4199_, 1, v___x_4198_);
lean_inc(v___x_4027_);
v___x_4200_ = l_Lean_MessageData_ofExpr(v___x_4027_);
v___x_4201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4201_, 0, v___x_4199_);
lean_ctor_set(v___x_4201_, 1, v___x_4200_);
v___x_4202_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4026_, v___x_4201_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref(v___x_4202_);
lean_inc(v___x_4027_);
v___x_4204_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4022_, v___x_4027_, v___x_3978_, v___x_4017_, v___x_4025_, v_a_4203_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4204_;
goto v___jp_3994_;
}
else
{
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
return v___x_4202_;
}
}
}
v___jp_4181_:
{
lean_object* v___x_4182_; 
lean_inc(v___x_4027_);
v___x_4182_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4022_, v___x_4027_, v___x_3978_, v___x_4017_, v___x_4025_, v___x_4025_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
v___y_3995_ = v___x_4182_;
goto v___jp_3994_;
}
}
else
{
lean_object* v___x_4205_; 
lean_dec(v_a_4174_);
lean_dec(v_a_4022_);
lean_inc(v___x_4027_);
v___x_4205_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4017_, v___x_4027_, v___y_3985_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_dec_ref(v___x_4205_);
v_a_3990_ = v___x_4025_;
goto v___jp_3989_;
}
else
{
lean_dec(v_a_3982_);
return v___x_4205_;
}
}
}
else
{
lean_object* v_a_4206_; lean_object* v___x_4208_; uint8_t v_isShared_4209_; uint8_t v_isSharedCheck_4213_; 
lean_dec(v_a_4174_);
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4206_ = lean_ctor_get(v___x_4175_, 0);
v_isSharedCheck_4213_ = !lean_is_exclusive(v___x_4175_);
if (v_isSharedCheck_4213_ == 0)
{
v___x_4208_ = v___x_4175_;
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
else
{
lean_inc(v_a_4206_);
lean_dec(v___x_4175_);
v___x_4208_ = lean_box(0);
v_isShared_4209_ = v_isSharedCheck_4213_;
goto v_resetjp_4207_;
}
v_resetjp_4207_:
{
lean_object* v___x_4211_; 
if (v_isShared_4209_ == 0)
{
v___x_4211_ = v___x_4208_;
goto v_reusejp_4210_;
}
else
{
lean_object* v_reuseFailAlloc_4212_; 
v_reuseFailAlloc_4212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4212_, 0, v_a_4206_);
v___x_4211_ = v_reuseFailAlloc_4212_;
goto v_reusejp_4210_;
}
v_reusejp_4210_:
{
return v___x_4211_;
}
}
}
}
else
{
lean_object* v_a_4214_; lean_object* v___x_4216_; uint8_t v_isShared_4217_; uint8_t v_isSharedCheck_4221_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4214_ = lean_ctor_get(v___x_4173_, 0);
v_isSharedCheck_4221_ = !lean_is_exclusive(v___x_4173_);
if (v_isSharedCheck_4221_ == 0)
{
v___x_4216_ = v___x_4173_;
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
else
{
lean_inc(v_a_4214_);
lean_dec(v___x_4173_);
v___x_4216_ = lean_box(0);
v_isShared_4217_ = v_isSharedCheck_4221_;
goto v_resetjp_4215_;
}
v_resetjp_4215_:
{
lean_object* v___x_4219_; 
if (v_isShared_4217_ == 0)
{
v___x_4219_ = v___x_4216_;
goto v_reusejp_4218_;
}
else
{
lean_object* v_reuseFailAlloc_4220_; 
v_reuseFailAlloc_4220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4220_, 0, v_a_4214_);
v___x_4219_ = v_reuseFailAlloc_4220_;
goto v_reusejp_4218_;
}
v_reusejp_4218_:
{
return v___x_4219_;
}
}
}
}
}
else
{
lean_object* v_a_4222_; lean_object* v___x_4224_; uint8_t v_isShared_4225_; uint8_t v_isSharedCheck_4229_; 
lean_dec(v_a_4022_);
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4222_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4229_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4229_ == 0)
{
v___x_4224_ = v___x_4023_;
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
else
{
lean_inc(v_a_4222_);
lean_dec(v___x_4023_);
v___x_4224_ = lean_box(0);
v_isShared_4225_ = v_isSharedCheck_4229_;
goto v_resetjp_4223_;
}
v_resetjp_4223_:
{
lean_object* v___x_4227_; 
if (v_isShared_4225_ == 0)
{
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
return v___x_4227_;
}
}
}
}
else
{
lean_object* v_a_4230_; lean_object* v___x_4232_; uint8_t v_isShared_4233_; uint8_t v_isSharedCheck_4237_; 
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4230_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4237_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4237_ == 0)
{
v___x_4232_ = v___x_4021_;
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
else
{
lean_inc(v_a_4230_);
lean_dec(v___x_4021_);
v___x_4232_ = lean_box(0);
v_isShared_4233_ = v_isSharedCheck_4237_;
goto v_resetjp_4231_;
}
v_resetjp_4231_:
{
lean_object* v___x_4235_; 
if (v_isShared_4233_ == 0)
{
v___x_4235_ = v___x_4232_;
goto v_reusejp_4234_;
}
else
{
lean_object* v_reuseFailAlloc_4236_; 
v_reuseFailAlloc_4236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4236_, 0, v_a_4230_);
v___x_4235_ = v_reuseFailAlloc_4236_;
goto v_reusejp_4234_;
}
v_reusejp_4234_:
{
return v___x_4235_;
}
}
}
}
else
{
lean_object* v_a_4238_; lean_object* v___x_4240_; uint8_t v_isShared_4241_; uint8_t v_isSharedCheck_4245_; 
lean_dec(v___x_4017_);
lean_dec(v_a_3982_);
v_a_4238_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4245_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4245_ == 0)
{
v___x_4240_ = v___x_4018_;
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
else
{
lean_inc(v_a_4238_);
lean_dec(v___x_4018_);
v___x_4240_ = lean_box(0);
v_isShared_4241_ = v_isSharedCheck_4245_;
goto v_resetjp_4239_;
}
v_resetjp_4239_:
{
lean_object* v___x_4243_; 
if (v_isShared_4241_ == 0)
{
v___x_4243_ = v___x_4240_;
goto v_reusejp_4242_;
}
else
{
lean_object* v_reuseFailAlloc_4244_; 
v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
v___x_4243_ = v_reuseFailAlloc_4244_;
goto v_reusejp_4242_;
}
v_reusejp_4242_:
{
return v___x_4243_;
}
}
}
}
v___jp_3989_:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3991_ = lean_unsigned_to_nat(1u);
v___x_3992_ = lean_nat_add(v_a_3982_, v___x_3991_);
lean_dec(v_a_3982_);
v_a_3982_ = v___x_3992_;
v_b_3983_ = v_a_3990_;
goto _start;
}
v___jp_3994_:
{
if (lean_obj_tag(v___y_3995_) == 0)
{
lean_object* v_a_3996_; lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4005_; 
v_a_3996_ = lean_ctor_get(v___y_3995_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v___y_3995_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3998_ = v___y_3995_;
v_isShared_3999_ = v_isSharedCheck_4005_;
goto v_resetjp_3997_;
}
else
{
lean_inc(v_a_3996_);
lean_dec(v___y_3995_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4005_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
if (lean_obj_tag(v_a_3996_) == 0)
{
lean_object* v_a_4000_; lean_object* v___x_4002_; 
lean_dec(v_a_3982_);
v_a_4000_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_a_4000_);
lean_dec_ref(v_a_3996_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v_a_4000_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_4000_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
else
{
lean_object* v_a_4004_; 
lean_del_object(v___x_3998_);
v_a_4004_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_a_4004_);
lean_dec_ref(v_a_3996_);
v_a_3990_ = v_a_4004_;
goto v___jp_3989_;
}
}
}
else
{
lean_object* v_a_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4013_; 
lean_dec(v_a_3982_);
v_a_4006_ = lean_ctor_get(v___y_3995_, 0);
v_isSharedCheck_4013_ = !lean_is_exclusive(v___y_3995_);
if (v_isSharedCheck_4013_ == 0)
{
v___x_4008_ = v___y_3995_;
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_a_4006_);
lean_dec(v___y_3995_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4013_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4011_; 
if (v_isShared_4009_ == 0)
{
v___x_4011_ = v___x_4008_;
goto v_reusejp_4010_;
}
else
{
lean_object* v_reuseFailAlloc_4012_; 
v_reuseFailAlloc_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4012_, 0, v_a_4006_);
v___x_4011_ = v_reuseFailAlloc_4012_;
goto v_reusejp_4010_;
}
v_reusejp_4010_:
{
return v___x_4011_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object* v_upperBound_4246_, lean_object* v_fst_4247_, lean_object* v_args_4248_, uint8_t v___x_4249_, uint8_t v_compile_4250_, uint8_t v_logCompileErrors_4251_, uint8_t v_isMeta_4252_, lean_object* v_a_4253_, lean_object* v_b_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_){
_start:
{
lean_object* v_a_4261_; lean_object* v___y_4266_; uint8_t v___x_4285_; 
v___x_4285_ = lean_nat_dec_lt(v_a_4253_, v_upperBound_4246_);
if (v___x_4285_ == 0)
{
lean_object* v___x_4286_; 
lean_dec(v_a_4253_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v_b_4254_);
return v___x_4286_;
}
else
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4289_; 
v___x_4287_ = lean_array_fget_borrowed(v_fst_4247_, v_a_4253_);
v___x_4288_ = l_Lean_Expr_mvarId_x21(v___x_4287_);
lean_inc(v___x_4288_);
v___x_4289_ = l_Lean_MVarId_getDecl(v___x_4288_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4289_) == 0)
{
lean_object* v_a_4290_; lean_object* v_type_4291_; lean_object* v___x_4292_; 
v_a_4290_ = lean_ctor_get(v___x_4289_, 0);
lean_inc(v_a_4290_);
lean_dec_ref(v___x_4289_);
v_type_4291_ = lean_ctor_get(v_a_4290_, 2);
lean_inc_ref(v_type_4291_);
lean_dec(v_a_4290_);
v___x_4292_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4291_, v___y_4256_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; lean_object* v___x_4294_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc_n(v_a_4293_, 2);
lean_dec_ref(v___x_4292_);
v___x_4294_ = l_Lean_Meta_isProp(v_a_4293_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4294_) == 0)
{
lean_object* v_a_4295_; lean_object* v___x_4296_; lean_object* v_cls_4297_; lean_object* v___x_4298_; uint8_t v___x_4299_; 
v_a_4295_ = lean_ctor_get(v___x_4294_, 0);
lean_inc(v_a_4295_);
lean_dec_ref(v___x_4294_);
v___x_4296_ = lean_box(0);
v_cls_4297_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4298_ = lean_array_fget_borrowed(v_args_4248_, v_a_4253_);
v___x_4299_ = lean_unbox(v_a_4295_);
lean_dec(v_a_4295_);
if (v___x_4299_ == 0)
{
lean_object* v___x_4300_; 
lean_inc(v_a_4293_);
v___x_4300_ = l_Lean_Meta_isClass_x3f(v_a_4293_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4303_; uint8_t v_isShared_4304_; uint8_t v_isSharedCheck_4435_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4435_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4435_ == 0)
{
v___x_4303_ = v___x_4300_;
v_isShared_4304_ = v_isSharedCheck_4435_;
goto v_resetjp_4302_;
}
else
{
lean_inc(v_a_4301_);
lean_dec(v___x_4300_);
v___x_4303_ = lean_box(0);
v_isShared_4304_ = v_isSharedCheck_4435_;
goto v_resetjp_4302_;
}
v_resetjp_4302_:
{
if (lean_obj_tag(v_a_4301_) == 0)
{
lean_del_object(v___x_4303_);
goto v___jp_4305_;
}
else
{
lean_dec_ref(v_a_4301_);
if (v___x_4249_ == 0)
{
lean_del_object(v___x_4303_);
goto v___jp_4305_;
}
else
{
lean_object* v_options_4395_; lean_object* v_inheritedTraceOptions_4396_; lean_object* v_a_4398_; lean_object* v___y_4401_; uint8_t v___y_4402_; lean_object* v_a_4407_; lean_object* v___y_4411_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_options_4395_ = lean_ctor_get(v___y_4257_, 2);
v_inheritedTraceOptions_4396_ = lean_ctor_get(v___y_4257_, 13);
v___x_4415_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4416_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4395_, v___x_4415_);
if (v___x_4416_ == 0)
{
lean_object* v___x_4417_; 
lean_del_object(v___x_4303_);
lean_inc(v___x_4298_);
v___x_4417_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4298_, v_a_4293_, v_compile_4250_, v_logCompileErrors_4251_, v_isMeta_4252_, v___x_4288_, v___x_4296_, v___x_4296_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4417_;
goto v___jp_4265_;
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4418_ = lean_box(0);
lean_inc(v_a_4293_);
v___x_4419_ = l_Lean_Meta_trySynthInstance(v_a_4293_, v___x_4418_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4419_) == 0)
{
lean_object* v_a_4420_; 
v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4420_);
lean_dec_ref(v___x_4419_);
if (lean_obj_tag(v_a_4420_) == 1)
{
lean_object* v_a_4421_; uint8_t v_hasTrace_4422_; 
v_a_4421_ = lean_ctor_get(v_a_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref(v_a_4420_);
v_hasTrace_4422_ = lean_ctor_get_uint8(v_options_4395_, sizeof(void*)*1);
if (v_hasTrace_4422_ == 0)
{
goto v___jp_4423_;
}
else
{
lean_object* v___x_4425_; uint8_t v___x_4426_; 
v___x_4425_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4426_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4396_, v_options_4395_, v___x_4425_);
if (v___x_4426_ == 0)
{
goto v___jp_4423_;
}
else
{
lean_object* v___x_4427_; lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; 
v___x_4427_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_4421_);
v___x_4428_ = l_Lean_MessageData_ofExpr(v_a_4421_);
v___x_4429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4427_);
lean_ctor_set(v___x_4429_, 1, v___x_4428_);
v___x_4430_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4297_, v___x_4429_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; lean_object* v___x_4432_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref(v___x_4430_);
lean_inc(v___x_4288_);
v___x_4432_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4288_, v_a_4421_, v_a_4431_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4411_ = v___x_4432_;
goto v___jp_4410_;
}
else
{
lean_object* v_a_4433_; 
lean_dec(v_a_4421_);
v_a_4433_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4433_);
lean_dec_ref(v___x_4430_);
v_a_4407_ = v_a_4433_;
goto v___jp_4406_;
}
}
}
v___jp_4423_:
{
lean_object* v___x_4424_; 
lean_inc(v___x_4288_);
v___x_4424_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4288_, v_a_4421_, v___x_4296_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4411_ = v___x_4424_;
goto v___jp_4410_;
}
}
else
{
lean_dec(v_a_4420_);
lean_del_object(v___x_4303_);
v_a_4398_ = v___x_4296_;
goto v___jp_4397_;
}
}
else
{
lean_object* v_a_4434_; 
v_a_4434_ = lean_ctor_get(v___x_4419_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4419_);
v_a_4407_ = v_a_4434_;
goto v___jp_4406_;
}
}
v___jp_4397_:
{
lean_object* v___x_4399_; 
lean_inc(v___x_4298_);
v___x_4399_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4298_, v_a_4293_, v_compile_4250_, v_logCompileErrors_4251_, v_isMeta_4252_, v___x_4288_, v___x_4296_, v_a_4398_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4399_;
goto v___jp_4265_;
}
v___jp_4400_:
{
if (v___y_4402_ == 0)
{
lean_dec_ref(v___y_4401_);
lean_del_object(v___x_4303_);
v_a_4398_ = v___x_4296_;
goto v___jp_4397_;
}
else
{
lean_object* v___x_4404_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
if (v_isShared_4304_ == 0)
{
lean_ctor_set_tag(v___x_4303_, 1);
lean_ctor_set(v___x_4303_, 0, v___y_4401_);
v___x_4404_ = v___x_4303_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v___y_4401_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
v___jp_4406_:
{
uint8_t v___x_4408_; 
v___x_4408_ = l_Lean_Exception_isInterrupt(v_a_4407_);
if (v___x_4408_ == 0)
{
uint8_t v___x_4409_; 
lean_inc_ref(v_a_4407_);
v___x_4409_ = l_Lean_Exception_isRuntime(v_a_4407_);
v___y_4401_ = v_a_4407_;
v___y_4402_ = v___x_4409_;
goto v___jp_4400_;
}
else
{
v___y_4401_ = v_a_4407_;
v___y_4402_ = v___x_4408_;
goto v___jp_4400_;
}
}
v___jp_4410_:
{
if (lean_obj_tag(v___y_4411_) == 0)
{
lean_object* v_a_4412_; 
lean_del_object(v___x_4303_);
v_a_4412_ = lean_ctor_get(v___y_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref(v___y_4411_);
if (lean_obj_tag(v_a_4412_) == 0)
{
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
v_a_4261_ = v___x_4296_;
goto v___jp_4260_;
}
else
{
lean_object* v_a_4413_; 
v_a_4413_ = lean_ctor_get(v_a_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref(v_a_4412_);
v_a_4398_ = v_a_4413_;
goto v___jp_4397_;
}
}
else
{
lean_object* v_a_4414_; 
v_a_4414_ = lean_ctor_get(v___y_4411_, 0);
lean_inc(v_a_4414_);
lean_dec_ref(v___y_4411_);
v_a_4407_ = v_a_4414_;
goto v___jp_4406_;
}
}
}
}
v___jp_4305_:
{
lean_object* v_options_4306_; lean_object* v___x_4307_; uint8_t v___x_4308_; 
v_options_4306_ = lean_ctor_get(v___y_4257_, 2);
v___x_4307_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_4308_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4306_, v___x_4307_);
if (v___x_4308_ == 0)
{
lean_object* v___x_4309_; 
lean_dec(v_a_4293_);
lean_inc(v___x_4298_);
v___x_4309_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4288_, v___x_4298_, v___y_4256_);
if (lean_obj_tag(v___x_4309_) == 0)
{
lean_dec_ref(v___x_4309_);
v_a_4261_ = v___x_4296_;
goto v___jp_4260_;
}
else
{
lean_dec(v_a_4253_);
return v___x_4309_;
}
}
else
{
lean_object* v___x_4310_; 
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___x_4298_);
v___x_4310_ = lean_infer_type(v___x_4298_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_object* v_a_4311_; lean_object* v___x_4312_; 
v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
lean_inc(v_a_4311_);
lean_dec_ref(v___x_4310_);
lean_inc(v_a_4293_);
v___x_4312_ = l_Lean_Meta_isExprDefEq(v_a_4293_, v_a_4311_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; uint8_t v___x_4314_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref(v___x_4312_);
v___x_4314_ = lean_unbox(v_a_4313_);
if (v___x_4314_ == 0)
{
lean_object* v___x_4315_; lean_object* v___x_4316_; 
v___x_4315_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4316_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4315_, v___y_4258_);
if (lean_obj_tag(v___x_4316_) == 0)
{
lean_object* v_a_4317_; uint8_t v___x_4318_; uint8_t v___x_4319_; lean_object* v___x_4320_; 
v_a_4317_ = lean_ctor_get(v___x_4316_, 0);
lean_inc_n(v_a_4317_, 2);
lean_dec_ref(v___x_4316_);
v___x_4318_ = lean_unbox(v_a_4313_);
v___x_4319_ = lean_unbox(v_a_4313_);
lean_dec(v_a_4313_);
lean_inc(v___x_4298_);
v___x_4320_ = l_Lean_Meta_mkAuxDefinition(v_a_4317_, v_a_4293_, v___x_4298_, v___x_4318_, v___x_4319_, v___x_4249_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4320_) == 0)
{
lean_object* v_a_4321_; lean_object* v___x_4322_; 
v_a_4321_ = lean_ctor_get(v___x_4320_, 0);
lean_inc(v_a_4321_);
lean_dec_ref(v___x_4320_);
v___x_4322_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4288_, v_a_4321_, v___y_4256_);
if (lean_obj_tag(v___x_4322_) == 0)
{
uint8_t v___x_4323_; lean_object* v___x_4324_; 
lean_dec_ref(v___x_4322_);
v___x_4323_ = 0;
lean_inc(v_a_4317_);
v___x_4324_ = l_Lean_Meta_setInlineAttribute(v_a_4317_, v___x_4323_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4324_) == 0)
{
lean_dec_ref(v___x_4324_);
if (v_isMeta_4252_ == 0)
{
lean_object* v___x_4325_; 
v___x_4325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4317_, v___x_4296_, v_compile_4250_, v_logCompileErrors_4251_, v___x_4296_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4325_;
goto v___jp_4265_;
}
else
{
lean_object* v___x_4326_; lean_object* v_env_4327_; lean_object* v_nextMacroScope_4328_; lean_object* v_ngen_4329_; lean_object* v_auxDeclNGen_4330_; lean_object* v_traceState_4331_; lean_object* v_messages_4332_; lean_object* v_infoState_4333_; lean_object* v_snapshotTasks_4334_; lean_object* v___x_4336_; uint8_t v_isShared_4337_; uint8_t v_isSharedCheck_4360_; 
v___x_4326_ = lean_st_ref_take(v___y_4258_);
v_env_4327_ = lean_ctor_get(v___x_4326_, 0);
v_nextMacroScope_4328_ = lean_ctor_get(v___x_4326_, 1);
v_ngen_4329_ = lean_ctor_get(v___x_4326_, 2);
v_auxDeclNGen_4330_ = lean_ctor_get(v___x_4326_, 3);
v_traceState_4331_ = lean_ctor_get(v___x_4326_, 4);
v_messages_4332_ = lean_ctor_get(v___x_4326_, 6);
v_infoState_4333_ = lean_ctor_get(v___x_4326_, 7);
v_snapshotTasks_4334_ = lean_ctor_get(v___x_4326_, 8);
v_isSharedCheck_4360_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4360_ == 0)
{
lean_object* v_unused_4361_; 
v_unused_4361_ = lean_ctor_get(v___x_4326_, 5);
lean_dec(v_unused_4361_);
v___x_4336_ = v___x_4326_;
v_isShared_4337_ = v_isSharedCheck_4360_;
goto v_resetjp_4335_;
}
else
{
lean_inc(v_snapshotTasks_4334_);
lean_inc(v_infoState_4333_);
lean_inc(v_messages_4332_);
lean_inc(v_traceState_4331_);
lean_inc(v_auxDeclNGen_4330_);
lean_inc(v_ngen_4329_);
lean_inc(v_nextMacroScope_4328_);
lean_inc(v_env_4327_);
lean_dec(v___x_4326_);
v___x_4336_ = lean_box(0);
v_isShared_4337_ = v_isSharedCheck_4360_;
goto v_resetjp_4335_;
}
v_resetjp_4335_:
{
lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4341_; 
lean_inc(v_a_4317_);
v___x_4338_ = l_Lean_markMeta(v_env_4327_, v_a_4317_);
v___x_4339_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4337_ == 0)
{
lean_ctor_set(v___x_4336_, 5, v___x_4339_);
lean_ctor_set(v___x_4336_, 0, v___x_4338_);
v___x_4341_ = v___x_4336_;
goto v_reusejp_4340_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4338_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_nextMacroScope_4328_);
lean_ctor_set(v_reuseFailAlloc_4359_, 2, v_ngen_4329_);
lean_ctor_set(v_reuseFailAlloc_4359_, 3, v_auxDeclNGen_4330_);
lean_ctor_set(v_reuseFailAlloc_4359_, 4, v_traceState_4331_);
lean_ctor_set(v_reuseFailAlloc_4359_, 5, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4359_, 6, v_messages_4332_);
lean_ctor_set(v_reuseFailAlloc_4359_, 7, v_infoState_4333_);
lean_ctor_set(v_reuseFailAlloc_4359_, 8, v_snapshotTasks_4334_);
v___x_4341_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4340_;
}
v_reusejp_4340_:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; lean_object* v_mctx_4344_; lean_object* v_zetaDeltaFVarIds_4345_; lean_object* v_postponed_4346_; lean_object* v_diag_4347_; lean_object* v___x_4349_; uint8_t v_isShared_4350_; uint8_t v_isSharedCheck_4357_; 
v___x_4342_ = lean_st_ref_set(v___y_4258_, v___x_4341_);
v___x_4343_ = lean_st_ref_take(v___y_4256_);
v_mctx_4344_ = lean_ctor_get(v___x_4343_, 0);
v_zetaDeltaFVarIds_4345_ = lean_ctor_get(v___x_4343_, 2);
v_postponed_4346_ = lean_ctor_get(v___x_4343_, 3);
v_diag_4347_ = lean_ctor_get(v___x_4343_, 4);
v_isSharedCheck_4357_ = !lean_is_exclusive(v___x_4343_);
if (v_isSharedCheck_4357_ == 0)
{
lean_object* v_unused_4358_; 
v_unused_4358_ = lean_ctor_get(v___x_4343_, 1);
lean_dec(v_unused_4358_);
v___x_4349_ = v___x_4343_;
v_isShared_4350_ = v_isSharedCheck_4357_;
goto v_resetjp_4348_;
}
else
{
lean_inc(v_diag_4347_);
lean_inc(v_postponed_4346_);
lean_inc(v_zetaDeltaFVarIds_4345_);
lean_inc(v_mctx_4344_);
lean_dec(v___x_4343_);
v___x_4349_ = lean_box(0);
v_isShared_4350_ = v_isSharedCheck_4357_;
goto v_resetjp_4348_;
}
v_resetjp_4348_:
{
lean_object* v___x_4351_; lean_object* v___x_4353_; 
v___x_4351_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4350_ == 0)
{
lean_ctor_set(v___x_4349_, 1, v___x_4351_);
v___x_4353_ = v___x_4349_;
goto v_reusejp_4352_;
}
else
{
lean_object* v_reuseFailAlloc_4356_; 
v_reuseFailAlloc_4356_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4356_, 0, v_mctx_4344_);
lean_ctor_set(v_reuseFailAlloc_4356_, 1, v___x_4351_);
lean_ctor_set(v_reuseFailAlloc_4356_, 2, v_zetaDeltaFVarIds_4345_);
lean_ctor_set(v_reuseFailAlloc_4356_, 3, v_postponed_4346_);
lean_ctor_set(v_reuseFailAlloc_4356_, 4, v_diag_4347_);
v___x_4353_ = v_reuseFailAlloc_4356_;
goto v_reusejp_4352_;
}
v_reusejp_4352_:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; 
v___x_4354_ = lean_st_ref_set(v___y_4256_, v___x_4353_);
v___x_4355_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4317_, v___x_4296_, v_compile_4250_, v_logCompileErrors_4251_, v___x_4296_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4355_;
goto v___jp_4265_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4317_);
lean_dec(v_a_4253_);
return v___x_4324_;
}
}
else
{
lean_dec(v_a_4317_);
lean_dec(v_a_4253_);
return v___x_4322_;
}
}
else
{
lean_object* v_a_4362_; lean_object* v___x_4364_; uint8_t v_isShared_4365_; uint8_t v_isSharedCheck_4369_; 
lean_dec(v_a_4317_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4362_ = lean_ctor_get(v___x_4320_, 0);
v_isSharedCheck_4369_ = !lean_is_exclusive(v___x_4320_);
if (v_isSharedCheck_4369_ == 0)
{
v___x_4364_ = v___x_4320_;
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
else
{
lean_inc(v_a_4362_);
lean_dec(v___x_4320_);
v___x_4364_ = lean_box(0);
v_isShared_4365_ = v_isSharedCheck_4369_;
goto v_resetjp_4363_;
}
v_resetjp_4363_:
{
lean_object* v___x_4367_; 
if (v_isShared_4365_ == 0)
{
v___x_4367_ = v___x_4364_;
goto v_reusejp_4366_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
v___x_4367_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4366_;
}
v_reusejp_4366_:
{
return v___x_4367_;
}
}
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_dec(v_a_4313_);
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4370_ = lean_ctor_get(v___x_4316_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4316_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4316_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4316_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
lean_object* v___x_4378_; 
lean_dec(v_a_4313_);
lean_dec(v_a_4293_);
lean_inc(v___x_4298_);
v___x_4378_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4288_, v___x_4298_, v___y_4256_);
if (lean_obj_tag(v___x_4378_) == 0)
{
lean_dec_ref(v___x_4378_);
v_a_4261_ = v___x_4296_;
goto v___jp_4260_;
}
else
{
lean_dec(v_a_4253_);
return v___x_4378_;
}
}
}
else
{
lean_object* v_a_4379_; lean_object* v___x_4381_; uint8_t v_isShared_4382_; uint8_t v_isSharedCheck_4386_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4379_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4386_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4386_ == 0)
{
v___x_4381_ = v___x_4312_;
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
else
{
lean_inc(v_a_4379_);
lean_dec(v___x_4312_);
v___x_4381_ = lean_box(0);
v_isShared_4382_ = v_isSharedCheck_4386_;
goto v_resetjp_4380_;
}
v_resetjp_4380_:
{
lean_object* v___x_4384_; 
if (v_isShared_4382_ == 0)
{
v___x_4384_ = v___x_4381_;
goto v_reusejp_4383_;
}
else
{
lean_object* v_reuseFailAlloc_4385_; 
v_reuseFailAlloc_4385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4385_, 0, v_a_4379_);
v___x_4384_ = v_reuseFailAlloc_4385_;
goto v_reusejp_4383_;
}
v_reusejp_4383_:
{
return v___x_4384_;
}
}
}
}
else
{
lean_object* v_a_4387_; lean_object* v___x_4389_; uint8_t v_isShared_4390_; uint8_t v_isSharedCheck_4394_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4387_ = lean_ctor_get(v___x_4310_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v___x_4310_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4389_ = v___x_4310_;
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
else
{
lean_inc(v_a_4387_);
lean_dec(v___x_4310_);
v___x_4389_ = lean_box(0);
v_isShared_4390_ = v_isSharedCheck_4394_;
goto v_resetjp_4388_;
}
v_resetjp_4388_:
{
lean_object* v___x_4392_; 
if (v_isShared_4390_ == 0)
{
v___x_4392_ = v___x_4389_;
goto v_reusejp_4391_;
}
else
{
lean_object* v_reuseFailAlloc_4393_; 
v_reuseFailAlloc_4393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4393_, 0, v_a_4387_);
v___x_4392_ = v_reuseFailAlloc_4393_;
goto v_reusejp_4391_;
}
v_reusejp_4391_:
{
return v___x_4392_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4436_; lean_object* v___x_4438_; uint8_t v_isShared_4439_; uint8_t v_isSharedCheck_4443_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4436_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4443_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4443_ == 0)
{
v___x_4438_ = v___x_4300_;
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
else
{
lean_inc(v_a_4436_);
lean_dec(v___x_4300_);
v___x_4438_ = lean_box(0);
v_isShared_4439_ = v_isSharedCheck_4443_;
goto v_resetjp_4437_;
}
v_resetjp_4437_:
{
lean_object* v___x_4441_; 
if (v_isShared_4439_ == 0)
{
v___x_4441_ = v___x_4438_;
goto v_reusejp_4440_;
}
else
{
lean_object* v_reuseFailAlloc_4442_; 
v_reuseFailAlloc_4442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4442_, 0, v_a_4436_);
v___x_4441_ = v_reuseFailAlloc_4442_;
goto v_reusejp_4440_;
}
v_reusejp_4440_:
{
return v___x_4441_;
}
}
}
}
else
{
lean_object* v___x_4444_; 
lean_inc(v___y_4258_);
lean_inc_ref(v___y_4257_);
lean_inc(v___y_4256_);
lean_inc_ref(v___y_4255_);
lean_inc(v___x_4298_);
v___x_4444_ = lean_infer_type(v___x_4298_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v_a_4445_; lean_object* v___x_4446_; 
v_a_4445_ = lean_ctor_get(v___x_4444_, 0);
lean_inc_n(v_a_4445_, 2);
lean_dec_ref(v___x_4444_);
lean_inc(v_a_4293_);
v___x_4446_ = l_Lean_Meta_isExprDefEq(v_a_4293_, v_a_4445_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_object* v_a_4447_; uint8_t v___x_4448_; 
v_a_4447_ = lean_ctor_get(v___x_4446_, 0);
lean_inc(v_a_4447_);
lean_dec_ref(v___x_4446_);
v___x_4448_ = lean_unbox(v_a_4447_);
lean_dec(v_a_4447_);
if (v___x_4448_ == 0)
{
lean_object* v_options_4449_; lean_object* v_inheritedTraceOptions_4450_; uint8_t v_hasTrace_4451_; 
v_options_4449_ = lean_ctor_get(v___y_4257_, 2);
v_inheritedTraceOptions_4450_ = lean_ctor_get(v___y_4257_, 13);
v_hasTrace_4451_ = lean_ctor_get_uint8(v_options_4449_, sizeof(void*)*1);
if (v_hasTrace_4451_ == 0)
{
lean_dec(v_a_4445_);
goto v___jp_4452_;
}
else
{
lean_object* v___x_4454_; uint8_t v___x_4455_; 
v___x_4454_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4455_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4450_, v_options_4449_, v___x_4454_);
if (v___x_4455_ == 0)
{
lean_dec(v_a_4445_);
goto v___jp_4452_;
}
else
{
lean_object* v___x_4456_; lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; 
v___x_4456_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_4253_);
v___x_4457_ = l_Nat_reprFast(v_a_4253_);
v___x_4458_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4458_, 0, v___x_4457_);
v___x_4459_ = l_Lean_MessageData_ofFormat(v___x_4458_);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4456_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___x_4461_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4460_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
lean_inc(v_a_4293_);
v___x_4463_ = l_Lean_MessageData_ofExpr(v_a_4293_);
v___x_4464_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4464_, 0, v___x_4462_);
lean_ctor_set(v___x_4464_, 1, v___x_4463_);
v___x_4465_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_4466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4464_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = l_Lean_MessageData_ofExpr(v_a_4445_);
v___x_4468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4466_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_4470_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4470_, 0, v___x_4468_);
lean_ctor_set(v___x_4470_, 1, v___x_4469_);
lean_inc(v___x_4298_);
v___x_4471_ = l_Lean_MessageData_ofExpr(v___x_4298_);
v___x_4472_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4472_, 0, v___x_4470_);
lean_ctor_set(v___x_4472_, 1, v___x_4471_);
v___x_4473_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4297_, v___x_4472_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v_a_4474_; lean_object* v___x_4475_; 
v_a_4474_ = lean_ctor_get(v___x_4473_, 0);
lean_inc(v_a_4474_);
lean_dec_ref(v___x_4473_);
lean_inc(v___x_4298_);
v___x_4475_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4293_, v___x_4298_, v___x_4249_, v___x_4288_, v___x_4296_, v_a_4474_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4475_;
goto v___jp_4265_;
}
else
{
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
return v___x_4473_;
}
}
}
v___jp_4452_:
{
lean_object* v___x_4453_; 
lean_inc(v___x_4298_);
v___x_4453_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4293_, v___x_4298_, v___x_4249_, v___x_4288_, v___x_4296_, v___x_4296_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
v___y_4266_ = v___x_4453_;
goto v___jp_4265_;
}
}
else
{
lean_object* v___x_4476_; 
lean_dec(v_a_4445_);
lean_dec(v_a_4293_);
lean_inc(v___x_4298_);
v___x_4476_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4288_, v___x_4298_, v___y_4256_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_dec_ref(v___x_4476_);
v_a_4261_ = v___x_4296_;
goto v___jp_4260_;
}
else
{
lean_dec(v_a_4253_);
return v___x_4476_;
}
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_dec(v_a_4445_);
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4477_ = lean_ctor_get(v___x_4446_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4446_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4446_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4446_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4485_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4444_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4444_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
}
}
else
{
lean_object* v_a_4493_; lean_object* v___x_4495_; uint8_t v_isShared_4496_; uint8_t v_isSharedCheck_4500_; 
lean_dec(v_a_4293_);
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4493_ = lean_ctor_get(v___x_4294_, 0);
v_isSharedCheck_4500_ = !lean_is_exclusive(v___x_4294_);
if (v_isSharedCheck_4500_ == 0)
{
v___x_4495_ = v___x_4294_;
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
else
{
lean_inc(v_a_4493_);
lean_dec(v___x_4294_);
v___x_4495_ = lean_box(0);
v_isShared_4496_ = v_isSharedCheck_4500_;
goto v_resetjp_4494_;
}
v_resetjp_4494_:
{
lean_object* v___x_4498_; 
if (v_isShared_4496_ == 0)
{
v___x_4498_ = v___x_4495_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4499_; 
v_reuseFailAlloc_4499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4499_, 0, v_a_4493_);
v___x_4498_ = v_reuseFailAlloc_4499_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
return v___x_4498_;
}
}
}
}
else
{
lean_object* v_a_4501_; lean_object* v___x_4503_; uint8_t v_isShared_4504_; uint8_t v_isSharedCheck_4508_; 
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4501_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4508_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4508_ == 0)
{
v___x_4503_ = v___x_4292_;
v_isShared_4504_ = v_isSharedCheck_4508_;
goto v_resetjp_4502_;
}
else
{
lean_inc(v_a_4501_);
lean_dec(v___x_4292_);
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
else
{
lean_object* v_a_4509_; lean_object* v___x_4511_; uint8_t v_isShared_4512_; uint8_t v_isSharedCheck_4516_; 
lean_dec(v___x_4288_);
lean_dec(v_a_4253_);
v_a_4509_ = lean_ctor_get(v___x_4289_, 0);
v_isSharedCheck_4516_ = !lean_is_exclusive(v___x_4289_);
if (v_isSharedCheck_4516_ == 0)
{
v___x_4511_ = v___x_4289_;
v_isShared_4512_ = v_isSharedCheck_4516_;
goto v_resetjp_4510_;
}
else
{
lean_inc(v_a_4509_);
lean_dec(v___x_4289_);
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
v___jp_4260_:
{
lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; 
v___x_4262_ = lean_unsigned_to_nat(1u);
v___x_4263_ = lean_nat_add(v_a_4253_, v___x_4262_);
lean_dec(v_a_4253_);
v___x_4264_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_4246_, v_fst_4247_, v_args_4248_, v___x_4249_, v_compile_4250_, v_logCompileErrors_4251_, v_isMeta_4252_, v___x_4263_, v_a_4261_, v___y_4255_, v___y_4256_, v___y_4257_, v___y_4258_);
return v___x_4264_;
}
v___jp_4265_:
{
if (lean_obj_tag(v___y_4266_) == 0)
{
lean_object* v_a_4267_; lean_object* v___x_4269_; uint8_t v_isShared_4270_; uint8_t v_isSharedCheck_4276_; 
v_a_4267_ = lean_ctor_get(v___y_4266_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___y_4266_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4269_ = v___y_4266_;
v_isShared_4270_ = v_isSharedCheck_4276_;
goto v_resetjp_4268_;
}
else
{
lean_inc(v_a_4267_);
lean_dec(v___y_4266_);
v___x_4269_ = lean_box(0);
v_isShared_4270_ = v_isSharedCheck_4276_;
goto v_resetjp_4268_;
}
v_resetjp_4268_:
{
if (lean_obj_tag(v_a_4267_) == 0)
{
lean_object* v_a_4271_; lean_object* v___x_4273_; 
lean_dec(v_a_4253_);
v_a_4271_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_a_4271_);
lean_dec_ref(v_a_4267_);
if (v_isShared_4270_ == 0)
{
lean_ctor_set(v___x_4269_, 0, v_a_4271_);
v___x_4273_ = v___x_4269_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4271_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
else
{
lean_object* v_a_4275_; 
lean_del_object(v___x_4269_);
v_a_4275_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_a_4275_);
lean_dec_ref(v_a_4267_);
v_a_4261_ = v_a_4275_;
goto v___jp_4260_;
}
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_a_4253_);
v_a_4277_ = lean_ctor_get(v___y_4266_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___y_4266_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___y_4266_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___y_4266_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(lean_object* v_a_4517_, lean_object* v_expectedType_4518_, uint8_t v___x_4519_, uint8_t v_compile_4520_, uint8_t v_logCompileErrors_4521_, uint8_t v_isMeta_4522_, lean_object* v_x_4523_, lean_object* v_x_4524_, lean_object* v_x_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4554_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4571_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v_options_4574_; lean_object* v___y_4575_; 
if (lean_obj_tag(v_x_4523_) == 5)
{
lean_object* v_fn_4643_; lean_object* v_arg_4644_; lean_object* v___x_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; 
v_fn_4643_ = lean_ctor_get(v_x_4523_, 0);
lean_inc_ref(v_fn_4643_);
v_arg_4644_ = lean_ctor_get(v_x_4523_, 1);
lean_inc_ref(v_arg_4644_);
lean_dec_ref(v_x_4523_);
v___x_4645_ = lean_array_set(v_x_4524_, v_x_4525_, v_arg_4644_);
v___x_4646_ = lean_unsigned_to_nat(1u);
v___x_4647_ = lean_nat_sub(v_x_4525_, v___x_4646_);
lean_dec(v_x_4525_);
v_x_4523_ = v_fn_4643_;
v_x_4524_ = v___x_4645_;
v_x_4525_ = v___x_4647_;
goto _start;
}
else
{
lean_object* v_cls_4649_; lean_object* v___y_4651_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___x_4672_; 
lean_dec(v_x_4525_);
v_cls_4649_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4672_ = l_Lean_Expr_constName_x3f(v_x_4523_);
if (lean_obj_tag(v___x_4672_) == 0)
{
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
v___y_4651_ = v___y_4526_;
v___y_4652_ = v___y_4527_;
v___y_4653_ = v___y_4528_;
v___y_4654_ = v___y_4529_;
goto v___jp_4650_;
}
else
{
lean_object* v_val_4673_; lean_object* v___x_4674_; 
v_val_4673_ = lean_ctor_get(v___x_4672_, 0);
lean_inc(v_val_4673_);
lean_dec_ref(v___x_4672_);
v___x_4674_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4673_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4674_) == 0)
{
lean_object* v_a_4675_; 
v_a_4675_ = lean_ctor_get(v___x_4674_, 0);
lean_inc(v_a_4675_);
lean_dec_ref(v___x_4674_);
if (lean_obj_tag(v_a_4675_) == 6)
{
lean_object* v_val_4676_; lean_object* v___x_4677_; 
lean_dec_ref(v_a_4517_);
v_val_4676_ = lean_ctor_get(v_a_4675_, 0);
lean_inc_ref(v_val_4676_);
lean_dec_ref(v_a_4675_);
lean_inc(v___y_4529_);
lean_inc_ref(v___y_4528_);
lean_inc(v___y_4527_);
lean_inc_ref(v___y_4526_);
lean_inc_ref(v_x_4523_);
v___x_4677_ = lean_infer_type(v_x_4523_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4677_) == 0)
{
lean_object* v_a_4678_; uint8_t v___x_4679_; lean_object* v___x_4680_; 
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
lean_inc(v_a_4678_);
lean_dec_ref(v___x_4677_);
v___x_4679_ = 0;
v___x_4680_ = l_Lean_Meta_forallMetaTelescope(v_a_4678_, v___x_4679_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v_snd_4682_; lean_object* v_fst_4683_; lean_object* v___x_4685_; uint8_t v_isShared_4686_; uint8_t v_isSharedCheck_4783_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
lean_inc(v_a_4681_);
lean_dec_ref(v___x_4680_);
v_snd_4682_ = lean_ctor_get(v_a_4681_, 1);
v_fst_4683_ = lean_ctor_get(v_a_4681_, 0);
v_isSharedCheck_4783_ = !lean_is_exclusive(v_a_4681_);
if (v_isSharedCheck_4783_ == 0)
{
v___x_4685_ = v_a_4681_;
v_isShared_4686_ = v_isSharedCheck_4783_;
goto v_resetjp_4684_;
}
else
{
lean_inc(v_snd_4682_);
lean_inc(v_fst_4683_);
lean_dec(v_a_4681_);
v___x_4685_ = lean_box(0);
v_isShared_4686_ = v_isSharedCheck_4783_;
goto v_resetjp_4684_;
}
v_resetjp_4684_:
{
lean_object* v_snd_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4781_; 
v_snd_4687_ = lean_ctor_get(v_snd_4682_, 1);
v_isSharedCheck_4781_ = !lean_is_exclusive(v_snd_4682_);
if (v_isSharedCheck_4781_ == 0)
{
lean_object* v_unused_4782_; 
v_unused_4782_ = lean_ctor_get(v_snd_4682_, 0);
lean_dec(v_unused_4782_);
v___x_4689_ = v_snd_4682_;
v_isShared_4690_ = v_isSharedCheck_4781_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_snd_4687_);
lean_dec(v_snd_4682_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4781_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4691_; lean_object* v___y_4693_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___x_4728_; uint8_t v___x_4729_; 
v___x_4691_ = lean_array_get_size(v_x_4524_);
v___x_4728_ = lean_array_get_size(v_fst_4683_);
v___x_4729_ = lean_nat_dec_eq(v___x_4691_, v___x_4728_);
if (v___x_4729_ == 0)
{
lean_object* v___x_4730_; lean_object* v___x_4731_; lean_object* v___x_4733_; 
lean_dec(v_snd_4687_);
lean_dec(v_fst_4683_);
lean_dec_ref(v_val_4676_);
lean_dec_ref(v_expectedType_4518_);
v___x_4730_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_4731_ = l_Lean_MessageData_ofExpr(v_x_4523_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 7);
lean_ctor_set(v___x_4689_, 1, v___x_4731_);
lean_ctor_set(v___x_4689_, 0, v___x_4730_);
v___x_4733_ = v___x_4689_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4730_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4731_);
v___x_4733_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
lean_object* v___x_4734_; lean_object* v___x_4736_; 
v___x_4734_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 7);
lean_ctor_set(v___x_4685_, 1, v___x_4734_);
lean_ctor_set(v___x_4685_, 0, v___x_4733_);
v___x_4736_ = v___x_4685_;
goto v_reusejp_4735_;
}
else
{
lean_object* v_reuseFailAlloc_4743_; 
v_reuseFailAlloc_4743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4743_, 0, v___x_4733_);
lean_ctor_set(v_reuseFailAlloc_4743_, 1, v___x_4734_);
v___x_4736_ = v_reuseFailAlloc_4743_;
goto v_reusejp_4735_;
}
v_reusejp_4735_:
{
lean_object* v___x_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; 
v___x_4737_ = lean_array_to_list(v_x_4524_);
v___x_4738_ = lean_box(0);
v___x_4739_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_4737_, v___x_4738_);
v___x_4740_ = l_Lean_MessageData_ofList(v___x_4739_);
v___x_4741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4741_, 0, v___x_4736_);
lean_ctor_set(v___x_4741_, 1, v___x_4740_);
v___x_4742_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4741_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
return v___x_4742_;
}
}
}
else
{
lean_object* v___x_4745_; 
lean_inc_ref(v_expectedType_4518_);
v___x_4745_ = l_Lean_Meta_isExprDefEq(v_expectedType_4518_, v_snd_4687_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4745_) == 0)
{
lean_object* v_a_4746_; uint8_t v___x_4747_; 
v_a_4746_ = lean_ctor_get(v___x_4745_, 0);
lean_inc(v_a_4746_);
lean_dec_ref(v___x_4745_);
v___x_4747_ = lean_unbox(v_a_4746_);
if (v___x_4747_ == 0)
{
lean_object* v_toConstantVal_4748_; lean_object* v_name_4749_; lean_object* v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4753_; 
lean_dec(v_fst_4683_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
v_toConstantVal_4748_ = lean_ctor_get(v_val_4676_, 0);
lean_inc_ref(v_toConstantVal_4748_);
lean_dec_ref(v_val_4676_);
v_name_4749_ = lean_ctor_get(v_toConstantVal_4748_, 0);
lean_inc(v_name_4749_);
lean_dec_ref(v_toConstantVal_4748_);
v___x_4750_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_4751_ = l_Lean_MessageData_ofExpr(v_expectedType_4518_);
if (v_isShared_4690_ == 0)
{
lean_ctor_set_tag(v___x_4689_, 7);
lean_ctor_set(v___x_4689_, 1, v___x_4751_);
lean_ctor_set(v___x_4689_, 0, v___x_4750_);
v___x_4753_ = v___x_4689_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4750_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v___x_4751_);
v___x_4753_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
lean_object* v___x_4754_; lean_object* v___x_4756_; 
v___x_4754_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_4686_ == 0)
{
lean_ctor_set_tag(v___x_4685_, 7);
lean_ctor_set(v___x_4685_, 1, v___x_4754_);
lean_ctor_set(v___x_4685_, 0, v___x_4753_);
v___x_4756_ = v___x_4685_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v___x_4753_);
lean_ctor_set(v_reuseFailAlloc_4771_, 1, v___x_4754_);
v___x_4756_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
uint8_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
v___x_4757_ = lean_unbox(v_a_4746_);
lean_dec(v_a_4746_);
v___x_4758_ = l_Lean_MessageData_ofConstName(v_name_4749_, v___x_4757_);
v___x_4759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4756_);
lean_ctor_set(v___x_4759_, 1, v___x_4758_);
v___x_4760_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_4761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4761_, 0, v___x_4759_);
lean_ctor_set(v___x_4761_, 1, v___x_4760_);
v___x_4762_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4761_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
v_a_4763_ = lean_ctor_get(v___x_4762_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4762_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4762_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4762_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
else
{
lean_dec(v_a_4746_);
lean_del_object(v___x_4689_);
lean_del_object(v___x_4685_);
lean_dec_ref(v_expectedType_4518_);
v___y_4693_ = v___y_4526_;
v___y_4694_ = v___y_4527_;
v___y_4695_ = v___y_4528_;
v___y_4696_ = v___y_4529_;
goto v___jp_4692_;
}
}
else
{
lean_object* v_a_4773_; lean_object* v___x_4775_; uint8_t v_isShared_4776_; uint8_t v_isSharedCheck_4780_; 
lean_del_object(v___x_4689_);
lean_del_object(v___x_4685_);
lean_dec(v_fst_4683_);
lean_dec_ref(v_val_4676_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
lean_dec_ref(v_expectedType_4518_);
v_a_4773_ = lean_ctor_get(v___x_4745_, 0);
v_isSharedCheck_4780_ = !lean_is_exclusive(v___x_4745_);
if (v_isSharedCheck_4780_ == 0)
{
v___x_4775_ = v___x_4745_;
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
else
{
lean_inc(v_a_4773_);
lean_dec(v___x_4745_);
v___x_4775_ = lean_box(0);
v_isShared_4776_ = v_isSharedCheck_4780_;
goto v_resetjp_4774_;
}
v_resetjp_4774_:
{
lean_object* v___x_4778_; 
if (v_isShared_4776_ == 0)
{
v___x_4778_ = v___x_4775_;
goto v_reusejp_4777_;
}
else
{
lean_object* v_reuseFailAlloc_4779_; 
v_reuseFailAlloc_4779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4779_, 0, v_a_4773_);
v___x_4778_ = v_reuseFailAlloc_4779_;
goto v_reusejp_4777_;
}
v_reusejp_4777_:
{
return v___x_4778_;
}
}
}
}
v___jp_4692_:
{
lean_object* v_numParams_4697_; lean_object* v___x_4698_; lean_object* v___x_4699_; 
v_numParams_4697_ = lean_ctor_get(v_val_4676_, 3);
lean_inc(v_numParams_4697_);
lean_dec_ref(v_val_4676_);
v___x_4698_ = lean_box(0);
v___x_4699_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4691_, v_fst_4683_, v_x_4524_, v___x_4519_, v_compile_4520_, v_logCompileErrors_4521_, v_isMeta_4522_, v_numParams_4697_, v___x_4698_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec_ref(v_x_4524_);
if (lean_obj_tag(v___x_4699_) == 0)
{
size_t v_sz_4700_; size_t v___x_4701_; lean_object* v___x_4702_; 
lean_dec_ref(v___x_4699_);
v_sz_4700_ = lean_array_size(v_fst_4683_);
v___x_4701_ = ((size_t)0ULL);
v___x_4702_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4700_, v___x_4701_, v_fst_4683_, v___y_4694_);
if (lean_obj_tag(v___x_4702_) == 0)
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4711_; 
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4705_ = v___x_4702_;
v_isShared_4706_ = v_isSharedCheck_4711_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4702_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4711_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4707_; lean_object* v___x_4709_; 
v___x_4707_ = l_Lean_mkAppN(v_x_4523_, v_a_4703_);
lean_dec(v_a_4703_);
if (v_isShared_4706_ == 0)
{
lean_ctor_set(v___x_4705_, 0, v___x_4707_);
v___x_4709_ = v___x_4705_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v___x_4707_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
else
{
lean_object* v_a_4712_; lean_object* v___x_4714_; uint8_t v_isShared_4715_; uint8_t v_isSharedCheck_4719_; 
lean_dec_ref(v_x_4523_);
v_a_4712_ = lean_ctor_get(v___x_4702_, 0);
v_isSharedCheck_4719_ = !lean_is_exclusive(v___x_4702_);
if (v_isSharedCheck_4719_ == 0)
{
v___x_4714_ = v___x_4702_;
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
else
{
lean_inc(v_a_4712_);
lean_dec(v___x_4702_);
v___x_4714_ = lean_box(0);
v_isShared_4715_ = v_isSharedCheck_4719_;
goto v_resetjp_4713_;
}
v_resetjp_4713_:
{
lean_object* v___x_4717_; 
if (v_isShared_4715_ == 0)
{
v___x_4717_ = v___x_4714_;
goto v_reusejp_4716_;
}
else
{
lean_object* v_reuseFailAlloc_4718_; 
v_reuseFailAlloc_4718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4718_, 0, v_a_4712_);
v___x_4717_ = v_reuseFailAlloc_4718_;
goto v_reusejp_4716_;
}
v_reusejp_4716_:
{
return v___x_4717_;
}
}
}
}
else
{
lean_object* v_a_4720_; lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
lean_dec(v_fst_4683_);
lean_dec_ref(v_x_4523_);
v_a_4720_ = lean_ctor_get(v___x_4699_, 0);
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4699_);
if (v_isSharedCheck_4727_ == 0)
{
v___x_4722_ = v___x_4699_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_inc(v_a_4720_);
lean_dec(v___x_4699_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4720_);
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
}
}
}
else
{
lean_object* v_a_4784_; lean_object* v___x_4786_; uint8_t v_isShared_4787_; uint8_t v_isSharedCheck_4791_; 
lean_dec_ref(v_val_4676_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
lean_dec_ref(v_expectedType_4518_);
v_a_4784_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4791_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4791_ == 0)
{
v___x_4786_ = v___x_4680_;
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
else
{
lean_inc(v_a_4784_);
lean_dec(v___x_4680_);
v___x_4786_ = lean_box(0);
v_isShared_4787_ = v_isSharedCheck_4791_;
goto v_resetjp_4785_;
}
v_resetjp_4785_:
{
lean_object* v___x_4789_; 
if (v_isShared_4787_ == 0)
{
v___x_4789_ = v___x_4786_;
goto v_reusejp_4788_;
}
else
{
lean_object* v_reuseFailAlloc_4790_; 
v_reuseFailAlloc_4790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4790_, 0, v_a_4784_);
v___x_4789_ = v_reuseFailAlloc_4790_;
goto v_reusejp_4788_;
}
v_reusejp_4788_:
{
return v___x_4789_;
}
}
}
}
else
{
lean_dec_ref(v_val_4676_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
lean_dec_ref(v_expectedType_4518_);
return v___x_4677_;
}
}
else
{
lean_dec(v_a_4675_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
v___y_4651_ = v___y_4526_;
v___y_4652_ = v___y_4527_;
v___y_4653_ = v___y_4528_;
v___y_4654_ = v___y_4529_;
goto v___jp_4650_;
}
}
else
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4799_; 
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_x_4523_);
lean_dec_ref(v_expectedType_4518_);
lean_dec_ref(v_a_4517_);
v_a_4792_ = lean_ctor_get(v___x_4674_, 0);
v_isSharedCheck_4799_ = !lean_is_exclusive(v___x_4674_);
if (v_isSharedCheck_4799_ == 0)
{
v___x_4794_ = v___x_4674_;
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4674_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4799_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
lean_object* v___x_4797_; 
if (v_isShared_4795_ == 0)
{
v___x_4797_ = v___x_4794_;
goto v_reusejp_4796_;
}
else
{
lean_object* v_reuseFailAlloc_4798_; 
v_reuseFailAlloc_4798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4798_, 0, v_a_4792_);
v___x_4797_ = v_reuseFailAlloc_4798_;
goto v_reusejp_4796_;
}
v_reusejp_4796_:
{
return v___x_4797_;
}
}
}
}
v___jp_4650_:
{
lean_object* v_options_4655_; uint8_t v_hasTrace_4656_; 
v_options_4655_ = lean_ctor_get(v___y_4653_, 2);
v_hasTrace_4656_ = lean_ctor_get_uint8(v_options_4655_, sizeof(void*)*1);
if (v_hasTrace_4656_ == 0)
{
v___y_4571_ = v___y_4651_;
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v_options_4574_ = v_options_4655_;
v___y_4575_ = v___y_4654_;
goto v___jp_4570_;
}
else
{
lean_object* v_inheritedTraceOptions_4657_; lean_object* v___x_4658_; uint8_t v___x_4659_; 
v_inheritedTraceOptions_4657_ = lean_ctor_get(v___y_4653_, 13);
v___x_4658_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4659_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4657_, v_options_4655_, v___x_4658_);
if (v___x_4659_ == 0)
{
v___y_4571_ = v___y_4651_;
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v_options_4574_ = v_options_4655_;
v___y_4575_ = v___y_4654_;
goto v___jp_4570_;
}
else
{
lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; 
v___x_4660_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_4517_);
v___x_4661_ = l_Lean_MessageData_ofExpr(v_a_4517_);
v___x_4662_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4662_, 0, v___x_4660_);
lean_ctor_set(v___x_4662_, 1, v___x_4661_);
v___x_4663_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4649_, v___x_4662_, v___y_4651_, v___y_4652_, v___y_4653_, v___y_4654_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_dec_ref(v___x_4663_);
v___y_4571_ = v___y_4651_;
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v_options_4574_ = v_options_4655_;
v___y_4575_ = v___y_4654_;
goto v___jp_4570_;
}
else
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4671_; 
lean_dec_ref(v_expectedType_4518_);
lean_dec_ref(v_a_4517_);
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4671_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4669_; 
if (v_isShared_4667_ == 0)
{
v___x_4669_ = v___x_4666_;
goto v_reusejp_4668_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v_a_4664_);
v___x_4669_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4668_;
}
v_reusejp_4668_:
{
return v___x_4669_;
}
}
}
}
}
}
}
v___jp_4531_:
{
lean_object* v___x_4536_; 
v___x_4536_ = l_Lean_enableRealizationsForConst(v___y_4532_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4536_) == 0)
{
lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4543_ == 0)
{
lean_object* v_unused_4544_; 
v_unused_4544_ = lean_ctor_get(v___x_4536_, 0);
lean_dec(v_unused_4544_);
v___x_4538_ = v___x_4536_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_dec(v___x_4536_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
lean_ctor_set(v___x_4538_, 0, v___y_4533_);
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v___y_4533_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v___y_4533_);
v_a_4545_ = lean_ctor_get(v___x_4536_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4536_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4536_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4536_);
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
v___jp_4553_:
{
if (v_compile_4520_ == 0)
{
v___y_4532_ = v___y_4554_;
v___y_4533_ = v___y_4555_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
goto v___jp_4531_;
}
else
{
lean_object* v___x_4558_; lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; 
v___x_4558_ = lean_unsigned_to_nat(1u);
v___x_4559_ = lean_mk_empty_array_with_capacity(v___x_4558_);
lean_inc(v___y_4554_);
v___x_4560_ = lean_array_push(v___x_4559_, v___y_4554_);
v___x_4561_ = l_Lean_compileDecls(v___x_4560_, v_logCompileErrors_4521_, v___y_4556_, v___y_4557_);
if (lean_obj_tag(v___x_4561_) == 0)
{
lean_dec_ref(v___x_4561_);
v___y_4532_ = v___y_4554_;
v___y_4533_ = v___y_4555_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
goto v___jp_4531_;
}
else
{
lean_object* v_a_4562_; lean_object* v___x_4564_; uint8_t v_isShared_4565_; uint8_t v_isSharedCheck_4569_; 
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
v_a_4562_ = lean_ctor_get(v___x_4561_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4564_ = v___x_4561_;
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
else
{
lean_inc(v_a_4562_);
lean_dec(v___x_4561_);
v___x_4564_ = lean_box(0);
v_isShared_4565_ = v_isSharedCheck_4569_;
goto v_resetjp_4563_;
}
v_resetjp_4563_:
{
lean_object* v___x_4567_; 
if (v_isShared_4565_ == 0)
{
v___x_4567_ = v___x_4564_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_a_4562_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
}
v___jp_4570_:
{
lean_object* v___x_4576_; uint8_t v___x_4577_; 
v___x_4576_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4577_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4574_, v___x_4576_);
if (v___x_4577_ == 0)
{
lean_object* v___x_4578_; 
lean_dec_ref(v_expectedType_4518_);
v___x_4578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4578_, 0, v_a_4517_);
return v___x_4578_;
}
else
{
lean_object* v___x_4579_; 
lean_inc(v___y_4575_);
lean_inc_ref(v___y_4573_);
lean_inc(v___y_4572_);
lean_inc_ref(v___y_4571_);
lean_inc_ref(v_a_4517_);
v___x_4579_ = lean_infer_type(v_a_4517_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4575_);
if (lean_obj_tag(v___x_4579_) == 0)
{
lean_object* v_a_4580_; lean_object* v___x_4581_; 
v_a_4580_ = lean_ctor_get(v___x_4579_, 0);
lean_inc(v_a_4580_);
lean_dec_ref(v___x_4579_);
lean_inc_ref(v_expectedType_4518_);
v___x_4581_ = l_Lean_Meta_isExprDefEq(v_expectedType_4518_, v_a_4580_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4575_);
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4634_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4634_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4634_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
uint8_t v___x_4586_; 
v___x_4586_ = lean_unbox(v_a_4582_);
if (v___x_4586_ == 0)
{
lean_object* v___x_4587_; lean_object* v___x_4588_; lean_object* v_a_4589_; uint8_t v___x_4590_; uint8_t v___x_4591_; lean_object* v___x_4592_; 
lean_del_object(v___x_4584_);
v___x_4587_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4588_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4587_, v___y_4575_);
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc_n(v_a_4589_, 2);
lean_dec_ref(v___x_4588_);
v___x_4590_ = lean_unbox(v_a_4582_);
v___x_4591_ = lean_unbox(v_a_4582_);
lean_dec(v_a_4582_);
v___x_4592_ = l_Lean_Meta_mkAuxDefinition(v_a_4589_, v_expectedType_4518_, v_a_4517_, v___x_4590_, v___x_4591_, v___x_4519_, v___y_4571_, v___y_4572_, v___y_4573_, v___y_4575_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; uint8_t v___x_4594_; lean_object* v___x_4595_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref(v___x_4592_);
v___x_4594_ = 3;
lean_inc(v_a_4589_);
v___x_4595_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4589_, v___x_4594_, v___y_4572_, v___y_4575_);
lean_dec_ref(v___x_4595_);
if (v_isMeta_4522_ == 0)
{
v___y_4554_ = v_a_4589_;
v___y_4555_ = v_a_4593_;
v___y_4556_ = v___y_4573_;
v___y_4557_ = v___y_4575_;
goto v___jp_4553_;
}
else
{
lean_object* v___x_4596_; lean_object* v_env_4597_; lean_object* v_nextMacroScope_4598_; lean_object* v_ngen_4599_; lean_object* v_auxDeclNGen_4600_; lean_object* v_traceState_4601_; lean_object* v_messages_4602_; lean_object* v_infoState_4603_; lean_object* v_snapshotTasks_4604_; lean_object* v___x_4606_; uint8_t v_isShared_4607_; uint8_t v_isSharedCheck_4629_; 
v___x_4596_ = lean_st_ref_take(v___y_4575_);
v_env_4597_ = lean_ctor_get(v___x_4596_, 0);
v_nextMacroScope_4598_ = lean_ctor_get(v___x_4596_, 1);
v_ngen_4599_ = lean_ctor_get(v___x_4596_, 2);
v_auxDeclNGen_4600_ = lean_ctor_get(v___x_4596_, 3);
v_traceState_4601_ = lean_ctor_get(v___x_4596_, 4);
v_messages_4602_ = lean_ctor_get(v___x_4596_, 6);
v_infoState_4603_ = lean_ctor_get(v___x_4596_, 7);
v_snapshotTasks_4604_ = lean_ctor_get(v___x_4596_, 8);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4596_);
if (v_isSharedCheck_4629_ == 0)
{
lean_object* v_unused_4630_; 
v_unused_4630_ = lean_ctor_get(v___x_4596_, 5);
lean_dec(v_unused_4630_);
v___x_4606_ = v___x_4596_;
v_isShared_4607_ = v_isSharedCheck_4629_;
goto v_resetjp_4605_;
}
else
{
lean_inc(v_snapshotTasks_4604_);
lean_inc(v_infoState_4603_);
lean_inc(v_messages_4602_);
lean_inc(v_traceState_4601_);
lean_inc(v_auxDeclNGen_4600_);
lean_inc(v_ngen_4599_);
lean_inc(v_nextMacroScope_4598_);
lean_inc(v_env_4597_);
lean_dec(v___x_4596_);
v___x_4606_ = lean_box(0);
v_isShared_4607_ = v_isSharedCheck_4629_;
goto v_resetjp_4605_;
}
v_resetjp_4605_:
{
lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
lean_inc(v_a_4589_);
v___x_4608_ = l_Lean_markMeta(v_env_4597_, v_a_4589_);
v___x_4609_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4607_ == 0)
{
lean_ctor_set(v___x_4606_, 5, v___x_4609_);
lean_ctor_set(v___x_4606_, 0, v___x_4608_);
v___x_4611_ = v___x_4606_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4628_, 1, v_nextMacroScope_4598_);
lean_ctor_set(v_reuseFailAlloc_4628_, 2, v_ngen_4599_);
lean_ctor_set(v_reuseFailAlloc_4628_, 3, v_auxDeclNGen_4600_);
lean_ctor_set(v_reuseFailAlloc_4628_, 4, v_traceState_4601_);
lean_ctor_set(v_reuseFailAlloc_4628_, 5, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4628_, 6, v_messages_4602_);
lean_ctor_set(v_reuseFailAlloc_4628_, 7, v_infoState_4603_);
lean_ctor_set(v_reuseFailAlloc_4628_, 8, v_snapshotTasks_4604_);
v___x_4611_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v_mctx_4614_; lean_object* v_zetaDeltaFVarIds_4615_; lean_object* v_postponed_4616_; lean_object* v_diag_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4626_; 
v___x_4612_ = lean_st_ref_set(v___y_4575_, v___x_4611_);
v___x_4613_ = lean_st_ref_take(v___y_4572_);
v_mctx_4614_ = lean_ctor_get(v___x_4613_, 0);
v_zetaDeltaFVarIds_4615_ = lean_ctor_get(v___x_4613_, 2);
v_postponed_4616_ = lean_ctor_get(v___x_4613_, 3);
v_diag_4617_ = lean_ctor_get(v___x_4613_, 4);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v___x_4613_, 1);
lean_dec(v_unused_4627_);
v___x_4619_ = v___x_4613_;
v_isShared_4620_ = v_isSharedCheck_4626_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_diag_4617_);
lean_inc(v_postponed_4616_);
lean_inc(v_zetaDeltaFVarIds_4615_);
lean_inc(v_mctx_4614_);
lean_dec(v___x_4613_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4626_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4621_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v___x_4621_);
v___x_4623_ = v___x_4619_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_mctx_4614_);
lean_ctor_set(v_reuseFailAlloc_4625_, 1, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4625_, 2, v_zetaDeltaFVarIds_4615_);
lean_ctor_set(v_reuseFailAlloc_4625_, 3, v_postponed_4616_);
lean_ctor_set(v_reuseFailAlloc_4625_, 4, v_diag_4617_);
v___x_4623_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; 
v___x_4624_ = lean_st_ref_set(v___y_4572_, v___x_4623_);
v___y_4554_ = v_a_4589_;
v___y_4555_ = v_a_4593_;
v___y_4556_ = v___y_4573_;
v___y_4557_ = v___y_4575_;
goto v___jp_4553_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4589_);
return v___x_4592_;
}
}
else
{
lean_object* v___x_4632_; 
lean_dec(v_a_4582_);
lean_dec_ref(v_expectedType_4518_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_a_4517_);
v___x_4632_ = v___x_4584_;
goto v_reusejp_4631_;
}
else
{
lean_object* v_reuseFailAlloc_4633_; 
v_reuseFailAlloc_4633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4633_, 0, v_a_4517_);
v___x_4632_ = v_reuseFailAlloc_4633_;
goto v_reusejp_4631_;
}
v_reusejp_4631_:
{
return v___x_4632_;
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref(v_expectedType_4518_);
lean_dec_ref(v_a_4517_);
v_a_4635_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4581_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4581_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4518_);
lean_dec_ref(v_a_4517_);
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_a_4800_, lean_object* v_expectedType_4801_, uint8_t v___x_4802_, uint8_t v_compile_4803_, uint8_t v_logCompileErrors_4804_, uint8_t v_isMeta_4805_, lean_object* v_x_4806_, lean_object* v_x_4807_, lean_object* v_x_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_){
_start:
{
lean_object* v___y_4815_; lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4837_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4854_; lean_object* v___y_4855_; lean_object* v___y_4856_; lean_object* v_options_4857_; lean_object* v___y_4858_; 
if (lean_obj_tag(v_x_4806_) == 5)
{
lean_object* v_fn_4926_; lean_object* v_arg_4927_; lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; 
v_fn_4926_ = lean_ctor_get(v_x_4806_, 0);
lean_inc_ref(v_fn_4926_);
v_arg_4927_ = lean_ctor_get(v_x_4806_, 1);
lean_inc_ref(v_arg_4927_);
lean_dec_ref(v_x_4806_);
v___x_4928_ = lean_array_set(v_x_4807_, v_x_4808_, v_arg_4927_);
v___x_4929_ = lean_unsigned_to_nat(1u);
v___x_4930_ = lean_nat_sub(v_x_4808_, v___x_4929_);
v___x_4931_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(v_a_4800_, v_expectedType_4801_, v___x_4802_, v_compile_4803_, v_logCompileErrors_4804_, v_isMeta_4805_, v_fn_4926_, v___x_4928_, v___x_4930_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
return v___x_4931_;
}
else
{
lean_object* v_cls_4932_; lean_object* v___y_4934_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___x_4955_; 
v_cls_4932_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4955_ = l_Lean_Expr_constName_x3f(v_x_4806_);
if (lean_obj_tag(v___x_4955_) == 0)
{
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
v___y_4934_ = v___y_4809_;
v___y_4935_ = v___y_4810_;
v___y_4936_ = v___y_4811_;
v___y_4937_ = v___y_4812_;
goto v___jp_4933_;
}
else
{
lean_object* v_val_4956_; lean_object* v___x_4957_; 
v_val_4956_ = lean_ctor_get(v___x_4955_, 0);
lean_inc(v_val_4956_);
lean_dec_ref(v___x_4955_);
v___x_4957_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4956_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
if (lean_obj_tag(v___x_4957_) == 0)
{
lean_object* v_a_4958_; 
v_a_4958_ = lean_ctor_get(v___x_4957_, 0);
lean_inc(v_a_4958_);
lean_dec_ref(v___x_4957_);
if (lean_obj_tag(v_a_4958_) == 6)
{
lean_object* v_val_4959_; lean_object* v___x_4960_; 
lean_dec_ref(v_a_4800_);
v_val_4959_ = lean_ctor_get(v_a_4958_, 0);
lean_inc_ref(v_val_4959_);
lean_dec_ref(v_a_4958_);
lean_inc(v___y_4812_);
lean_inc_ref(v___y_4811_);
lean_inc(v___y_4810_);
lean_inc_ref(v___y_4809_);
lean_inc_ref(v_x_4806_);
v___x_4960_ = lean_infer_type(v_x_4806_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
if (lean_obj_tag(v___x_4960_) == 0)
{
lean_object* v_a_4961_; uint8_t v___x_4962_; lean_object* v___x_4963_; 
v_a_4961_ = lean_ctor_get(v___x_4960_, 0);
lean_inc(v_a_4961_);
lean_dec_ref(v___x_4960_);
v___x_4962_ = 0;
v___x_4963_ = l_Lean_Meta_forallMetaTelescope(v_a_4961_, v___x_4962_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
if (lean_obj_tag(v___x_4963_) == 0)
{
lean_object* v_a_4964_; lean_object* v_snd_4965_; lean_object* v_fst_4966_; lean_object* v___x_4968_; uint8_t v_isShared_4969_; uint8_t v_isSharedCheck_5066_; 
v_a_4964_ = lean_ctor_get(v___x_4963_, 0);
lean_inc(v_a_4964_);
lean_dec_ref(v___x_4963_);
v_snd_4965_ = lean_ctor_get(v_a_4964_, 1);
v_fst_4966_ = lean_ctor_get(v_a_4964_, 0);
v_isSharedCheck_5066_ = !lean_is_exclusive(v_a_4964_);
if (v_isSharedCheck_5066_ == 0)
{
v___x_4968_ = v_a_4964_;
v_isShared_4969_ = v_isSharedCheck_5066_;
goto v_resetjp_4967_;
}
else
{
lean_inc(v_snd_4965_);
lean_inc(v_fst_4966_);
lean_dec(v_a_4964_);
v___x_4968_ = lean_box(0);
v_isShared_4969_ = v_isSharedCheck_5066_;
goto v_resetjp_4967_;
}
v_resetjp_4967_:
{
lean_object* v_snd_4970_; lean_object* v___x_4972_; uint8_t v_isShared_4973_; uint8_t v_isSharedCheck_5064_; 
v_snd_4970_ = lean_ctor_get(v_snd_4965_, 1);
v_isSharedCheck_5064_ = !lean_is_exclusive(v_snd_4965_);
if (v_isSharedCheck_5064_ == 0)
{
lean_object* v_unused_5065_; 
v_unused_5065_ = lean_ctor_get(v_snd_4965_, 0);
lean_dec(v_unused_5065_);
v___x_4972_ = v_snd_4965_;
v_isShared_4973_ = v_isSharedCheck_5064_;
goto v_resetjp_4971_;
}
else
{
lean_inc(v_snd_4970_);
lean_dec(v_snd_4965_);
v___x_4972_ = lean_box(0);
v_isShared_4973_ = v_isSharedCheck_5064_;
goto v_resetjp_4971_;
}
v_resetjp_4971_:
{
lean_object* v___x_4974_; lean_object* v___y_4976_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___x_5011_; uint8_t v___x_5012_; 
v___x_4974_ = lean_array_get_size(v_x_4807_);
v___x_5011_ = lean_array_get_size(v_fst_4966_);
v___x_5012_ = lean_nat_dec_eq(v___x_4974_, v___x_5011_);
if (v___x_5012_ == 0)
{
lean_object* v___x_5013_; lean_object* v___x_5014_; lean_object* v___x_5016_; 
lean_dec(v_snd_4970_);
lean_dec(v_fst_4966_);
lean_dec_ref(v_val_4959_);
lean_dec_ref(v_expectedType_4801_);
v___x_5013_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_5014_ = l_Lean_MessageData_ofExpr(v_x_4806_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 7);
lean_ctor_set(v___x_4972_, 1, v___x_5014_);
lean_ctor_set(v___x_4972_, 0, v___x_5013_);
v___x_5016_ = v___x_4972_;
goto v_reusejp_5015_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5013_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5014_);
v___x_5016_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5015_;
}
v_reusejp_5015_:
{
lean_object* v___x_5017_; lean_object* v___x_5019_; 
v___x_5017_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_4969_ == 0)
{
lean_ctor_set_tag(v___x_4968_, 7);
lean_ctor_set(v___x_4968_, 1, v___x_5017_);
lean_ctor_set(v___x_4968_, 0, v___x_5016_);
v___x_5019_ = v___x_4968_;
goto v_reusejp_5018_;
}
else
{
lean_object* v_reuseFailAlloc_5026_; 
v_reuseFailAlloc_5026_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5026_, 0, v___x_5016_);
lean_ctor_set(v_reuseFailAlloc_5026_, 1, v___x_5017_);
v___x_5019_ = v_reuseFailAlloc_5026_;
goto v_reusejp_5018_;
}
v_reusejp_5018_:
{
lean_object* v___x_5020_; lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; 
v___x_5020_ = lean_array_to_list(v_x_4807_);
v___x_5021_ = lean_box(0);
v___x_5022_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_5020_, v___x_5021_);
v___x_5023_ = l_Lean_MessageData_ofList(v___x_5022_);
v___x_5024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5024_, 0, v___x_5019_);
lean_ctor_set(v___x_5024_, 1, v___x_5023_);
v___x_5025_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5024_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
return v___x_5025_;
}
}
}
else
{
lean_object* v___x_5028_; 
lean_inc_ref(v_expectedType_4801_);
v___x_5028_ = l_Lean_Meta_isExprDefEq(v_expectedType_4801_, v_snd_4970_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
if (lean_obj_tag(v___x_5028_) == 0)
{
lean_object* v_a_5029_; uint8_t v___x_5030_; 
v_a_5029_ = lean_ctor_get(v___x_5028_, 0);
lean_inc(v_a_5029_);
lean_dec_ref(v___x_5028_);
v___x_5030_ = lean_unbox(v_a_5029_);
if (v___x_5030_ == 0)
{
lean_object* v_toConstantVal_5031_; lean_object* v_name_5032_; lean_object* v___x_5033_; lean_object* v___x_5034_; lean_object* v___x_5036_; 
lean_dec(v_fst_4966_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
v_toConstantVal_5031_ = lean_ctor_get(v_val_4959_, 0);
lean_inc_ref(v_toConstantVal_5031_);
lean_dec_ref(v_val_4959_);
v_name_5032_ = lean_ctor_get(v_toConstantVal_5031_, 0);
lean_inc(v_name_5032_);
lean_dec_ref(v_toConstantVal_5031_);
v___x_5033_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_5034_ = l_Lean_MessageData_ofExpr(v_expectedType_4801_);
if (v_isShared_4973_ == 0)
{
lean_ctor_set_tag(v___x_4972_, 7);
lean_ctor_set(v___x_4972_, 1, v___x_5034_);
lean_ctor_set(v___x_4972_, 0, v___x_5033_);
v___x_5036_ = v___x_4972_;
goto v_reusejp_5035_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5033_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5034_);
v___x_5036_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5035_;
}
v_reusejp_5035_:
{
lean_object* v___x_5037_; lean_object* v___x_5039_; 
v___x_5037_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_4969_ == 0)
{
lean_ctor_set_tag(v___x_4968_, 7);
lean_ctor_set(v___x_4968_, 1, v___x_5037_);
lean_ctor_set(v___x_4968_, 0, v___x_5036_);
v___x_5039_ = v___x_4968_;
goto v_reusejp_5038_;
}
else
{
lean_object* v_reuseFailAlloc_5054_; 
v_reuseFailAlloc_5054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5054_, 0, v___x_5036_);
lean_ctor_set(v_reuseFailAlloc_5054_, 1, v___x_5037_);
v___x_5039_ = v_reuseFailAlloc_5054_;
goto v_reusejp_5038_;
}
v_reusejp_5038_:
{
uint8_t v___x_5040_; lean_object* v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v_a_5046_; lean_object* v___x_5048_; uint8_t v_isShared_5049_; uint8_t v_isSharedCheck_5053_; 
v___x_5040_ = lean_unbox(v_a_5029_);
lean_dec(v_a_5029_);
v___x_5041_ = l_Lean_MessageData_ofConstName(v_name_5032_, v___x_5040_);
v___x_5042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5042_, 0, v___x_5039_);
lean_ctor_set(v___x_5042_, 1, v___x_5041_);
v___x_5043_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_5044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5044_, 0, v___x_5042_);
lean_ctor_set(v___x_5044_, 1, v___x_5043_);
v___x_5045_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5044_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
v_a_5046_ = lean_ctor_get(v___x_5045_, 0);
v_isSharedCheck_5053_ = !lean_is_exclusive(v___x_5045_);
if (v_isSharedCheck_5053_ == 0)
{
v___x_5048_ = v___x_5045_;
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
else
{
lean_inc(v_a_5046_);
lean_dec(v___x_5045_);
v___x_5048_ = lean_box(0);
v_isShared_5049_ = v_isSharedCheck_5053_;
goto v_resetjp_5047_;
}
v_resetjp_5047_:
{
lean_object* v___x_5051_; 
if (v_isShared_5049_ == 0)
{
v___x_5051_ = v___x_5048_;
goto v_reusejp_5050_;
}
else
{
lean_object* v_reuseFailAlloc_5052_; 
v_reuseFailAlloc_5052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5052_, 0, v_a_5046_);
v___x_5051_ = v_reuseFailAlloc_5052_;
goto v_reusejp_5050_;
}
v_reusejp_5050_:
{
return v___x_5051_;
}
}
}
}
}
else
{
lean_dec(v_a_5029_);
lean_del_object(v___x_4972_);
lean_del_object(v___x_4968_);
lean_dec_ref(v_expectedType_4801_);
v___y_4976_ = v___y_4809_;
v___y_4977_ = v___y_4810_;
v___y_4978_ = v___y_4811_;
v___y_4979_ = v___y_4812_;
goto v___jp_4975_;
}
}
else
{
lean_object* v_a_5056_; lean_object* v___x_5058_; uint8_t v_isShared_5059_; uint8_t v_isSharedCheck_5063_; 
lean_del_object(v___x_4972_);
lean_del_object(v___x_4968_);
lean_dec(v_fst_4966_);
lean_dec_ref(v_val_4959_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
lean_dec_ref(v_expectedType_4801_);
v_a_5056_ = lean_ctor_get(v___x_5028_, 0);
v_isSharedCheck_5063_ = !lean_is_exclusive(v___x_5028_);
if (v_isSharedCheck_5063_ == 0)
{
v___x_5058_ = v___x_5028_;
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
else
{
lean_inc(v_a_5056_);
lean_dec(v___x_5028_);
v___x_5058_ = lean_box(0);
v_isShared_5059_ = v_isSharedCheck_5063_;
goto v_resetjp_5057_;
}
v_resetjp_5057_:
{
lean_object* v___x_5061_; 
if (v_isShared_5059_ == 0)
{
v___x_5061_ = v___x_5058_;
goto v_reusejp_5060_;
}
else
{
lean_object* v_reuseFailAlloc_5062_; 
v_reuseFailAlloc_5062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5062_, 0, v_a_5056_);
v___x_5061_ = v_reuseFailAlloc_5062_;
goto v_reusejp_5060_;
}
v_reusejp_5060_:
{
return v___x_5061_;
}
}
}
}
v___jp_4975_:
{
lean_object* v_numParams_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v_numParams_4980_ = lean_ctor_get(v_val_4959_, 3);
lean_inc(v_numParams_4980_);
lean_dec_ref(v_val_4959_);
v___x_4981_ = lean_box(0);
v___x_4982_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4974_, v_fst_4966_, v_x_4807_, v___x_4802_, v_compile_4803_, v_logCompileErrors_4804_, v_isMeta_4805_, v_numParams_4980_, v___x_4981_, v___y_4976_, v___y_4977_, v___y_4978_, v___y_4979_);
lean_dec_ref(v_x_4807_);
if (lean_obj_tag(v___x_4982_) == 0)
{
size_t v_sz_4983_; size_t v___x_4984_; lean_object* v___x_4985_; 
lean_dec_ref(v___x_4982_);
v_sz_4983_ = lean_array_size(v_fst_4966_);
v___x_4984_ = ((size_t)0ULL);
v___x_4985_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4983_, v___x_4984_, v_fst_4966_, v___y_4977_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; lean_object* v___x_4988_; uint8_t v_isShared_4989_; uint8_t v_isSharedCheck_4994_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_4994_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_4994_ == 0)
{
v___x_4988_ = v___x_4985_;
v_isShared_4989_ = v_isSharedCheck_4994_;
goto v_resetjp_4987_;
}
else
{
lean_inc(v_a_4986_);
lean_dec(v___x_4985_);
v___x_4988_ = lean_box(0);
v_isShared_4989_ = v_isSharedCheck_4994_;
goto v_resetjp_4987_;
}
v_resetjp_4987_:
{
lean_object* v___x_4990_; lean_object* v___x_4992_; 
v___x_4990_ = l_Lean_mkAppN(v_x_4806_, v_a_4986_);
lean_dec(v_a_4986_);
if (v_isShared_4989_ == 0)
{
lean_ctor_set(v___x_4988_, 0, v___x_4990_);
v___x_4992_ = v___x_4988_;
goto v_reusejp_4991_;
}
else
{
lean_object* v_reuseFailAlloc_4993_; 
v_reuseFailAlloc_4993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4993_, 0, v___x_4990_);
v___x_4992_ = v_reuseFailAlloc_4993_;
goto v_reusejp_4991_;
}
v_reusejp_4991_:
{
return v___x_4992_;
}
}
}
else
{
lean_object* v_a_4995_; lean_object* v___x_4997_; uint8_t v_isShared_4998_; uint8_t v_isSharedCheck_5002_; 
lean_dec_ref(v_x_4806_);
v_a_4995_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5002_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5002_ == 0)
{
v___x_4997_ = v___x_4985_;
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
else
{
lean_inc(v_a_4995_);
lean_dec(v___x_4985_);
v___x_4997_ = lean_box(0);
v_isShared_4998_ = v_isSharedCheck_5002_;
goto v_resetjp_4996_;
}
v_resetjp_4996_:
{
lean_object* v___x_5000_; 
if (v_isShared_4998_ == 0)
{
v___x_5000_ = v___x_4997_;
goto v_reusejp_4999_;
}
else
{
lean_object* v_reuseFailAlloc_5001_; 
v_reuseFailAlloc_5001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5001_, 0, v_a_4995_);
v___x_5000_ = v_reuseFailAlloc_5001_;
goto v_reusejp_4999_;
}
v_reusejp_4999_:
{
return v___x_5000_;
}
}
}
}
else
{
lean_object* v_a_5003_; lean_object* v___x_5005_; uint8_t v_isShared_5006_; uint8_t v_isSharedCheck_5010_; 
lean_dec(v_fst_4966_);
lean_dec_ref(v_x_4806_);
v_a_5003_ = lean_ctor_get(v___x_4982_, 0);
v_isSharedCheck_5010_ = !lean_is_exclusive(v___x_4982_);
if (v_isSharedCheck_5010_ == 0)
{
v___x_5005_ = v___x_4982_;
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
else
{
lean_inc(v_a_5003_);
lean_dec(v___x_4982_);
v___x_5005_ = lean_box(0);
v_isShared_5006_ = v_isSharedCheck_5010_;
goto v_resetjp_5004_;
}
v_resetjp_5004_:
{
lean_object* v___x_5008_; 
if (v_isShared_5006_ == 0)
{
v___x_5008_ = v___x_5005_;
goto v_reusejp_5007_;
}
else
{
lean_object* v_reuseFailAlloc_5009_; 
v_reuseFailAlloc_5009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5009_, 0, v_a_5003_);
v___x_5008_ = v_reuseFailAlloc_5009_;
goto v_reusejp_5007_;
}
v_reusejp_5007_:
{
return v___x_5008_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5067_; lean_object* v___x_5069_; uint8_t v_isShared_5070_; uint8_t v_isSharedCheck_5074_; 
lean_dec_ref(v_val_4959_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
lean_dec_ref(v_expectedType_4801_);
v_a_5067_ = lean_ctor_get(v___x_4963_, 0);
v_isSharedCheck_5074_ = !lean_is_exclusive(v___x_4963_);
if (v_isSharedCheck_5074_ == 0)
{
v___x_5069_ = v___x_4963_;
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
else
{
lean_inc(v_a_5067_);
lean_dec(v___x_4963_);
v___x_5069_ = lean_box(0);
v_isShared_5070_ = v_isSharedCheck_5074_;
goto v_resetjp_5068_;
}
v_resetjp_5068_:
{
lean_object* v___x_5072_; 
if (v_isShared_5070_ == 0)
{
v___x_5072_ = v___x_5069_;
goto v_reusejp_5071_;
}
else
{
lean_object* v_reuseFailAlloc_5073_; 
v_reuseFailAlloc_5073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5073_, 0, v_a_5067_);
v___x_5072_ = v_reuseFailAlloc_5073_;
goto v_reusejp_5071_;
}
v_reusejp_5071_:
{
return v___x_5072_;
}
}
}
}
else
{
lean_dec_ref(v_val_4959_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
lean_dec_ref(v_expectedType_4801_);
return v___x_4960_;
}
}
else
{
lean_dec(v_a_4958_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
v___y_4934_ = v___y_4809_;
v___y_4935_ = v___y_4810_;
v___y_4936_ = v___y_4811_;
v___y_4937_ = v___y_4812_;
goto v___jp_4933_;
}
}
else
{
lean_object* v_a_5075_; lean_object* v___x_5077_; uint8_t v_isShared_5078_; uint8_t v_isSharedCheck_5082_; 
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_x_4806_);
lean_dec_ref(v_expectedType_4801_);
lean_dec_ref(v_a_4800_);
v_a_5075_ = lean_ctor_get(v___x_4957_, 0);
v_isSharedCheck_5082_ = !lean_is_exclusive(v___x_4957_);
if (v_isSharedCheck_5082_ == 0)
{
v___x_5077_ = v___x_4957_;
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
else
{
lean_inc(v_a_5075_);
lean_dec(v___x_4957_);
v___x_5077_ = lean_box(0);
v_isShared_5078_ = v_isSharedCheck_5082_;
goto v_resetjp_5076_;
}
v_resetjp_5076_:
{
lean_object* v___x_5080_; 
if (v_isShared_5078_ == 0)
{
v___x_5080_ = v___x_5077_;
goto v_reusejp_5079_;
}
else
{
lean_object* v_reuseFailAlloc_5081_; 
v_reuseFailAlloc_5081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5081_, 0, v_a_5075_);
v___x_5080_ = v_reuseFailAlloc_5081_;
goto v_reusejp_5079_;
}
v_reusejp_5079_:
{
return v___x_5080_;
}
}
}
}
v___jp_4933_:
{
lean_object* v_options_4938_; uint8_t v_hasTrace_4939_; 
v_options_4938_ = lean_ctor_get(v___y_4936_, 2);
v_hasTrace_4939_ = lean_ctor_get_uint8(v_options_4938_, sizeof(void*)*1);
if (v_hasTrace_4939_ == 0)
{
v___y_4854_ = v___y_4934_;
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v_options_4857_ = v_options_4938_;
v___y_4858_ = v___y_4937_;
goto v___jp_4853_;
}
else
{
lean_object* v_inheritedTraceOptions_4940_; lean_object* v___x_4941_; uint8_t v___x_4942_; 
v_inheritedTraceOptions_4940_ = lean_ctor_get(v___y_4936_, 13);
v___x_4941_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4942_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4940_, v_options_4938_, v___x_4941_);
if (v___x_4942_ == 0)
{
v___y_4854_ = v___y_4934_;
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v_options_4857_ = v_options_4938_;
v___y_4858_ = v___y_4937_;
goto v___jp_4853_;
}
else
{
lean_object* v___x_4943_; lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; 
v___x_4943_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_4800_);
v___x_4944_ = l_Lean_MessageData_ofExpr(v_a_4800_);
v___x_4945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4945_, 0, v___x_4943_);
lean_ctor_set(v___x_4945_, 1, v___x_4944_);
v___x_4946_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4932_, v___x_4945_, v___y_4934_, v___y_4935_, v___y_4936_, v___y_4937_);
if (lean_obj_tag(v___x_4946_) == 0)
{
lean_dec_ref(v___x_4946_);
v___y_4854_ = v___y_4934_;
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v_options_4857_ = v_options_4938_;
v___y_4858_ = v___y_4937_;
goto v___jp_4853_;
}
else
{
lean_object* v_a_4947_; lean_object* v___x_4949_; uint8_t v_isShared_4950_; uint8_t v_isSharedCheck_4954_; 
lean_dec_ref(v_expectedType_4801_);
lean_dec_ref(v_a_4800_);
v_a_4947_ = lean_ctor_get(v___x_4946_, 0);
v_isSharedCheck_4954_ = !lean_is_exclusive(v___x_4946_);
if (v_isSharedCheck_4954_ == 0)
{
v___x_4949_ = v___x_4946_;
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
else
{
lean_inc(v_a_4947_);
lean_dec(v___x_4946_);
v___x_4949_ = lean_box(0);
v_isShared_4950_ = v_isSharedCheck_4954_;
goto v_resetjp_4948_;
}
v_resetjp_4948_:
{
lean_object* v___x_4952_; 
if (v_isShared_4950_ == 0)
{
v___x_4952_ = v___x_4949_;
goto v_reusejp_4951_;
}
else
{
lean_object* v_reuseFailAlloc_4953_; 
v_reuseFailAlloc_4953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4953_, 0, v_a_4947_);
v___x_4952_ = v_reuseFailAlloc_4953_;
goto v_reusejp_4951_;
}
v_reusejp_4951_:
{
return v___x_4952_;
}
}
}
}
}
}
}
v___jp_4814_:
{
lean_object* v___x_4819_; 
v___x_4819_ = l_Lean_enableRealizationsForConst(v___y_4815_, v___y_4817_, v___y_4818_);
if (lean_obj_tag(v___x_4819_) == 0)
{
lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4826_ == 0)
{
lean_object* v_unused_4827_; 
v_unused_4827_ = lean_ctor_get(v___x_4819_, 0);
lean_dec(v_unused_4827_);
v___x_4821_ = v___x_4819_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_dec(v___x_4819_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
lean_ctor_set(v___x_4821_, 0, v___y_4816_);
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___y_4816_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
else
{
lean_object* v_a_4828_; lean_object* v___x_4830_; uint8_t v_isShared_4831_; uint8_t v_isSharedCheck_4835_; 
lean_dec_ref(v___y_4816_);
v_a_4828_ = lean_ctor_get(v___x_4819_, 0);
v_isSharedCheck_4835_ = !lean_is_exclusive(v___x_4819_);
if (v_isSharedCheck_4835_ == 0)
{
v___x_4830_ = v___x_4819_;
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
else
{
lean_inc(v_a_4828_);
lean_dec(v___x_4819_);
v___x_4830_ = lean_box(0);
v_isShared_4831_ = v_isSharedCheck_4835_;
goto v_resetjp_4829_;
}
v_resetjp_4829_:
{
lean_object* v___x_4833_; 
if (v_isShared_4831_ == 0)
{
v___x_4833_ = v___x_4830_;
goto v_reusejp_4832_;
}
else
{
lean_object* v_reuseFailAlloc_4834_; 
v_reuseFailAlloc_4834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4834_, 0, v_a_4828_);
v___x_4833_ = v_reuseFailAlloc_4834_;
goto v_reusejp_4832_;
}
v_reusejp_4832_:
{
return v___x_4833_;
}
}
}
}
v___jp_4836_:
{
if (v_compile_4803_ == 0)
{
v___y_4815_ = v___y_4837_;
v___y_4816_ = v___y_4838_;
v___y_4817_ = v___y_4839_;
v___y_4818_ = v___y_4840_;
goto v___jp_4814_;
}
else
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4841_ = lean_unsigned_to_nat(1u);
v___x_4842_ = lean_mk_empty_array_with_capacity(v___x_4841_);
lean_inc(v___y_4837_);
v___x_4843_ = lean_array_push(v___x_4842_, v___y_4837_);
v___x_4844_ = l_Lean_compileDecls(v___x_4843_, v_logCompileErrors_4804_, v___y_4839_, v___y_4840_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_dec_ref(v___x_4844_);
v___y_4815_ = v___y_4837_;
v___y_4816_ = v___y_4838_;
v___y_4817_ = v___y_4839_;
v___y_4818_ = v___y_4840_;
goto v___jp_4814_;
}
else
{
lean_object* v_a_4845_; lean_object* v___x_4847_; uint8_t v_isShared_4848_; uint8_t v_isSharedCheck_4852_; 
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
v_isSharedCheck_4852_ = !lean_is_exclusive(v___x_4844_);
if (v_isSharedCheck_4852_ == 0)
{
v___x_4847_ = v___x_4844_;
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
else
{
lean_inc(v_a_4845_);
lean_dec(v___x_4844_);
v___x_4847_ = lean_box(0);
v_isShared_4848_ = v_isSharedCheck_4852_;
goto v_resetjp_4846_;
}
v_resetjp_4846_:
{
lean_object* v___x_4850_; 
if (v_isShared_4848_ == 0)
{
v___x_4850_ = v___x_4847_;
goto v_reusejp_4849_;
}
else
{
lean_object* v_reuseFailAlloc_4851_; 
v_reuseFailAlloc_4851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4851_, 0, v_a_4845_);
v___x_4850_ = v_reuseFailAlloc_4851_;
goto v_reusejp_4849_;
}
v_reusejp_4849_:
{
return v___x_4850_;
}
}
}
}
}
v___jp_4853_:
{
lean_object* v___x_4859_; uint8_t v___x_4860_; 
v___x_4859_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4860_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4857_, v___x_4859_);
if (v___x_4860_ == 0)
{
lean_object* v___x_4861_; 
lean_dec_ref(v_expectedType_4801_);
v___x_4861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4861_, 0, v_a_4800_);
return v___x_4861_;
}
else
{
lean_object* v___x_4862_; 
lean_inc(v___y_4858_);
lean_inc_ref(v___y_4856_);
lean_inc(v___y_4855_);
lean_inc_ref(v___y_4854_);
lean_inc_ref(v_a_4800_);
v___x_4862_ = lean_infer_type(v_a_4800_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4858_);
if (lean_obj_tag(v___x_4862_) == 0)
{
lean_object* v_a_4863_; lean_object* v___x_4864_; 
v_a_4863_ = lean_ctor_get(v___x_4862_, 0);
lean_inc(v_a_4863_);
lean_dec_ref(v___x_4862_);
lean_inc_ref(v_expectedType_4801_);
v___x_4864_ = l_Lean_Meta_isExprDefEq(v_expectedType_4801_, v_a_4863_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4858_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4867_; uint8_t v_isShared_4868_; uint8_t v_isSharedCheck_4917_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4917_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4917_ == 0)
{
v___x_4867_ = v___x_4864_;
v_isShared_4868_ = v_isSharedCheck_4917_;
goto v_resetjp_4866_;
}
else
{
lean_inc(v_a_4865_);
lean_dec(v___x_4864_);
v___x_4867_ = lean_box(0);
v_isShared_4868_ = v_isSharedCheck_4917_;
goto v_resetjp_4866_;
}
v_resetjp_4866_:
{
uint8_t v___x_4869_; 
v___x_4869_ = lean_unbox(v_a_4865_);
if (v___x_4869_ == 0)
{
lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v_a_4872_; uint8_t v___x_4873_; uint8_t v___x_4874_; lean_object* v___x_4875_; 
lean_del_object(v___x_4867_);
v___x_4870_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4871_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4870_, v___y_4858_);
v_a_4872_ = lean_ctor_get(v___x_4871_, 0);
lean_inc_n(v_a_4872_, 2);
lean_dec_ref(v___x_4871_);
v___x_4873_ = lean_unbox(v_a_4865_);
v___x_4874_ = lean_unbox(v_a_4865_);
lean_dec(v_a_4865_);
v___x_4875_ = l_Lean_Meta_mkAuxDefinition(v_a_4872_, v_expectedType_4801_, v_a_4800_, v___x_4873_, v___x_4874_, v___x_4802_, v___y_4854_, v___y_4855_, v___y_4856_, v___y_4858_);
if (lean_obj_tag(v___x_4875_) == 0)
{
lean_object* v_a_4876_; uint8_t v___x_4877_; lean_object* v___x_4878_; 
v_a_4876_ = lean_ctor_get(v___x_4875_, 0);
lean_inc(v_a_4876_);
lean_dec_ref(v___x_4875_);
v___x_4877_ = 3;
lean_inc(v_a_4872_);
v___x_4878_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4872_, v___x_4877_, v___y_4855_, v___y_4858_);
lean_dec_ref(v___x_4878_);
if (v_isMeta_4805_ == 0)
{
v___y_4837_ = v_a_4872_;
v___y_4838_ = v_a_4876_;
v___y_4839_ = v___y_4856_;
v___y_4840_ = v___y_4858_;
goto v___jp_4836_;
}
else
{
lean_object* v___x_4879_; lean_object* v_env_4880_; lean_object* v_nextMacroScope_4881_; lean_object* v_ngen_4882_; lean_object* v_auxDeclNGen_4883_; lean_object* v_traceState_4884_; lean_object* v_messages_4885_; lean_object* v_infoState_4886_; lean_object* v_snapshotTasks_4887_; lean_object* v___x_4889_; uint8_t v_isShared_4890_; uint8_t v_isSharedCheck_4912_; 
v___x_4879_ = lean_st_ref_take(v___y_4858_);
v_env_4880_ = lean_ctor_get(v___x_4879_, 0);
v_nextMacroScope_4881_ = lean_ctor_get(v___x_4879_, 1);
v_ngen_4882_ = lean_ctor_get(v___x_4879_, 2);
v_auxDeclNGen_4883_ = lean_ctor_get(v___x_4879_, 3);
v_traceState_4884_ = lean_ctor_get(v___x_4879_, 4);
v_messages_4885_ = lean_ctor_get(v___x_4879_, 6);
v_infoState_4886_ = lean_ctor_get(v___x_4879_, 7);
v_snapshotTasks_4887_ = lean_ctor_get(v___x_4879_, 8);
v_isSharedCheck_4912_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4912_ == 0)
{
lean_object* v_unused_4913_; 
v_unused_4913_ = lean_ctor_get(v___x_4879_, 5);
lean_dec(v_unused_4913_);
v___x_4889_ = v___x_4879_;
v_isShared_4890_ = v_isSharedCheck_4912_;
goto v_resetjp_4888_;
}
else
{
lean_inc(v_snapshotTasks_4887_);
lean_inc(v_infoState_4886_);
lean_inc(v_messages_4885_);
lean_inc(v_traceState_4884_);
lean_inc(v_auxDeclNGen_4883_);
lean_inc(v_ngen_4882_);
lean_inc(v_nextMacroScope_4881_);
lean_inc(v_env_4880_);
lean_dec(v___x_4879_);
v___x_4889_ = lean_box(0);
v_isShared_4890_ = v_isSharedCheck_4912_;
goto v_resetjp_4888_;
}
v_resetjp_4888_:
{
lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4894_; 
lean_inc(v_a_4872_);
v___x_4891_ = l_Lean_markMeta(v_env_4880_, v_a_4872_);
v___x_4892_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4890_ == 0)
{
lean_ctor_set(v___x_4889_, 5, v___x_4892_);
lean_ctor_set(v___x_4889_, 0, v___x_4891_);
v___x_4894_ = v___x_4889_;
goto v_reusejp_4893_;
}
else
{
lean_object* v_reuseFailAlloc_4911_; 
v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4891_);
lean_ctor_set(v_reuseFailAlloc_4911_, 1, v_nextMacroScope_4881_);
lean_ctor_set(v_reuseFailAlloc_4911_, 2, v_ngen_4882_);
lean_ctor_set(v_reuseFailAlloc_4911_, 3, v_auxDeclNGen_4883_);
lean_ctor_set(v_reuseFailAlloc_4911_, 4, v_traceState_4884_);
lean_ctor_set(v_reuseFailAlloc_4911_, 5, v___x_4892_);
lean_ctor_set(v_reuseFailAlloc_4911_, 6, v_messages_4885_);
lean_ctor_set(v_reuseFailAlloc_4911_, 7, v_infoState_4886_);
lean_ctor_set(v_reuseFailAlloc_4911_, 8, v_snapshotTasks_4887_);
v___x_4894_ = v_reuseFailAlloc_4911_;
goto v_reusejp_4893_;
}
v_reusejp_4893_:
{
lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v_mctx_4897_; lean_object* v_zetaDeltaFVarIds_4898_; lean_object* v_postponed_4899_; lean_object* v_diag_4900_; lean_object* v___x_4902_; uint8_t v_isShared_4903_; uint8_t v_isSharedCheck_4909_; 
v___x_4895_ = lean_st_ref_set(v___y_4858_, v___x_4894_);
v___x_4896_ = lean_st_ref_take(v___y_4855_);
v_mctx_4897_ = lean_ctor_get(v___x_4896_, 0);
v_zetaDeltaFVarIds_4898_ = lean_ctor_get(v___x_4896_, 2);
v_postponed_4899_ = lean_ctor_get(v___x_4896_, 3);
v_diag_4900_ = lean_ctor_get(v___x_4896_, 4);
v_isSharedCheck_4909_ = !lean_is_exclusive(v___x_4896_);
if (v_isSharedCheck_4909_ == 0)
{
lean_object* v_unused_4910_; 
v_unused_4910_ = lean_ctor_get(v___x_4896_, 1);
lean_dec(v_unused_4910_);
v___x_4902_ = v___x_4896_;
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
else
{
lean_inc(v_diag_4900_);
lean_inc(v_postponed_4899_);
lean_inc(v_zetaDeltaFVarIds_4898_);
lean_inc(v_mctx_4897_);
lean_dec(v___x_4896_);
v___x_4902_ = lean_box(0);
v_isShared_4903_ = v_isSharedCheck_4909_;
goto v_resetjp_4901_;
}
v_resetjp_4901_:
{
lean_object* v___x_4904_; lean_object* v___x_4906_; 
v___x_4904_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4903_ == 0)
{
lean_ctor_set(v___x_4902_, 1, v___x_4904_);
v___x_4906_ = v___x_4902_;
goto v_reusejp_4905_;
}
else
{
lean_object* v_reuseFailAlloc_4908_; 
v_reuseFailAlloc_4908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4908_, 0, v_mctx_4897_);
lean_ctor_set(v_reuseFailAlloc_4908_, 1, v___x_4904_);
lean_ctor_set(v_reuseFailAlloc_4908_, 2, v_zetaDeltaFVarIds_4898_);
lean_ctor_set(v_reuseFailAlloc_4908_, 3, v_postponed_4899_);
lean_ctor_set(v_reuseFailAlloc_4908_, 4, v_diag_4900_);
v___x_4906_ = v_reuseFailAlloc_4908_;
goto v_reusejp_4905_;
}
v_reusejp_4905_:
{
lean_object* v___x_4907_; 
v___x_4907_ = lean_st_ref_set(v___y_4855_, v___x_4906_);
v___y_4837_ = v_a_4872_;
v___y_4838_ = v_a_4876_;
v___y_4839_ = v___y_4856_;
v___y_4840_ = v___y_4858_;
goto v___jp_4836_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4872_);
return v___x_4875_;
}
}
else
{
lean_object* v___x_4915_; 
lean_dec(v_a_4865_);
lean_dec_ref(v_expectedType_4801_);
if (v_isShared_4868_ == 0)
{
lean_ctor_set(v___x_4867_, 0, v_a_4800_);
v___x_4915_ = v___x_4867_;
goto v_reusejp_4914_;
}
else
{
lean_object* v_reuseFailAlloc_4916_; 
v_reuseFailAlloc_4916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4916_, 0, v_a_4800_);
v___x_4915_ = v_reuseFailAlloc_4916_;
goto v_reusejp_4914_;
}
v_reusejp_4914_:
{
return v___x_4915_;
}
}
}
}
else
{
lean_object* v_a_4918_; lean_object* v___x_4920_; uint8_t v_isShared_4921_; uint8_t v_isSharedCheck_4925_; 
lean_dec_ref(v_expectedType_4801_);
lean_dec_ref(v_a_4800_);
v_a_4918_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4925_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4925_ == 0)
{
v___x_4920_ = v___x_4864_;
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
else
{
lean_inc(v_a_4918_);
lean_dec(v___x_4864_);
v___x_4920_ = lean_box(0);
v_isShared_4921_ = v_isSharedCheck_4925_;
goto v_resetjp_4919_;
}
v_resetjp_4919_:
{
lean_object* v___x_4923_; 
if (v_isShared_4921_ == 0)
{
v___x_4923_ = v___x_4920_;
goto v_reusejp_4922_;
}
else
{
lean_object* v_reuseFailAlloc_4924_; 
v_reuseFailAlloc_4924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4924_, 0, v_a_4918_);
v___x_4923_ = v_reuseFailAlloc_4924_;
goto v_reusejp_4922_;
}
v_reusejp_4922_:
{
return v___x_4923_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4801_);
lean_dec_ref(v_a_4800_);
return v___x_4862_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5083_, lean_object* v_inst_5084_, uint8_t v___x_5085_, uint8_t v_compile_5086_, uint8_t v_logCompileErrors_5087_, uint8_t v_isMeta_5088_, lean_object* v_____r_5089_, lean_object* v___y_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_){
_start:
{
lean_object* v___x_5095_; 
lean_inc_ref(v_expectedType_5083_);
v___x_5095_ = l_Lean_Meta_isProp(v_expectedType_5083_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
if (lean_obj_tag(v___x_5095_) == 0)
{
lean_object* v_a_5096_; lean_object* v___x_5098_; uint8_t v_isShared_5099_; uint8_t v_isSharedCheck_5117_; 
v_a_5096_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5117_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5117_ == 0)
{
v___x_5098_ = v___x_5095_;
v_isShared_5099_ = v_isSharedCheck_5117_;
goto v_resetjp_5097_;
}
else
{
lean_inc(v_a_5096_);
lean_dec(v___x_5095_);
v___x_5098_ = lean_box(0);
v_isShared_5099_ = v_isSharedCheck_5117_;
goto v_resetjp_5097_;
}
v_resetjp_5097_:
{
uint8_t v___x_5100_; 
v___x_5100_ = lean_unbox(v_a_5096_);
lean_dec(v_a_5096_);
if (v___x_5100_ == 0)
{
lean_object* v___x_5101_; 
lean_del_object(v___x_5098_);
lean_inc(v___y_5093_);
lean_inc_ref(v___y_5092_);
lean_inc(v___y_5091_);
lean_inc_ref(v___y_5090_);
v___x_5101_ = lean_whnf(v_inst_5084_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
if (lean_obj_tag(v___x_5101_) == 0)
{
lean_object* v_a_5102_; lean_object* v_dummy_5103_; lean_object* v_nargs_5104_; lean_object* v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v_a_5102_ = lean_ctor_get(v___x_5101_, 0);
lean_inc_n(v_a_5102_, 2);
lean_dec_ref(v___x_5101_);
v_dummy_5103_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5104_ = l_Lean_Expr_getAppNumArgs(v_a_5102_);
lean_inc(v_nargs_5104_);
v___x_5105_ = lean_mk_array(v_nargs_5104_, v_dummy_5103_);
v___x_5106_ = lean_unsigned_to_nat(1u);
v___x_5107_ = lean_nat_sub(v_nargs_5104_, v___x_5106_);
lean_dec(v_nargs_5104_);
v___x_5108_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_a_5102_, v_expectedType_5083_, v___x_5085_, v_compile_5086_, v_logCompileErrors_5087_, v_isMeta_5088_, v_a_5102_, v___x_5105_, v___x_5107_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
lean_dec(v___x_5107_);
return v___x_5108_;
}
else
{
lean_dec_ref(v_expectedType_5083_);
return v___x_5101_;
}
}
else
{
lean_object* v_options_5109_; lean_object* v___x_5110_; uint8_t v___x_5111_; 
v_options_5109_ = lean_ctor_get(v___y_5092_, 2);
v___x_5110_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5111_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5109_, v___x_5110_);
if (v___x_5111_ == 0)
{
lean_object* v___x_5113_; 
lean_dec_ref(v_expectedType_5083_);
if (v_isShared_5099_ == 0)
{
lean_ctor_set(v___x_5098_, 0, v_inst_5084_);
v___x_5113_ = v___x_5098_;
goto v_reusejp_5112_;
}
else
{
lean_object* v_reuseFailAlloc_5114_; 
v_reuseFailAlloc_5114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5114_, 0, v_inst_5084_);
v___x_5113_ = v_reuseFailAlloc_5114_;
goto v_reusejp_5112_;
}
v_reusejp_5112_:
{
return v___x_5113_;
}
}
else
{
lean_object* v___x_5115_; lean_object* v___x_5116_; 
lean_del_object(v___x_5098_);
v___x_5115_ = lean_box(0);
v___x_5116_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5083_, v_inst_5084_, v___x_5085_, v___x_5115_, v___x_5085_, v___y_5090_, v___y_5091_, v___y_5092_, v___y_5093_);
return v___x_5116_;
}
}
}
}
else
{
lean_object* v_a_5118_; lean_object* v___x_5120_; uint8_t v_isShared_5121_; uint8_t v_isSharedCheck_5125_; 
lean_dec_ref(v_inst_5084_);
lean_dec_ref(v_expectedType_5083_);
v_a_5118_ = lean_ctor_get(v___x_5095_, 0);
v_isSharedCheck_5125_ = !lean_is_exclusive(v___x_5095_);
if (v_isSharedCheck_5125_ == 0)
{
v___x_5120_ = v___x_5095_;
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
else
{
lean_inc(v_a_5118_);
lean_dec(v___x_5095_);
v___x_5120_ = lean_box(0);
v_isShared_5121_ = v_isSharedCheck_5125_;
goto v_resetjp_5119_;
}
v_resetjp_5119_:
{
lean_object* v___x_5123_; 
if (v_isShared_5121_ == 0)
{
v___x_5123_ = v___x_5120_;
goto v_reusejp_5122_;
}
else
{
lean_object* v_reuseFailAlloc_5124_; 
v_reuseFailAlloc_5124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5124_, 0, v_a_5118_);
v___x_5123_ = v_reuseFailAlloc_5124_;
goto v_reusejp_5122_;
}
v_reusejp_5122_:
{
return v___x_5123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5126_, lean_object* v_expectedType_5127_, uint8_t v_compile_5128_, uint8_t v_logCompileErrors_5129_, uint8_t v_isMeta_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_){
_start:
{
lean_object* v___x_5136_; lean_object* v_options_5137_; uint8_t v_foApprox_5138_; uint8_t v_ctxApprox_5139_; uint8_t v_quasiPatternApprox_5140_; uint8_t v_constApprox_5141_; uint8_t v_isDefEqStuckEx_5142_; uint8_t v_unificationHints_5143_; uint8_t v_proofIrrelevance_5144_; uint8_t v_assignSyntheticOpaque_5145_; uint8_t v_offsetCnstrs_5146_; uint8_t v_etaStruct_5147_; uint8_t v_univApprox_5148_; uint8_t v_iota_5149_; uint8_t v_beta_5150_; uint8_t v_proj_5151_; uint8_t v_zeta_5152_; uint8_t v_zetaDelta_5153_; uint8_t v_zetaUnused_5154_; uint8_t v_zetaHave_5155_; lean_object* v___x_5157_; uint8_t v_isShared_5158_; uint8_t v_isSharedCheck_5403_; 
v___x_5136_ = l_Lean_Meta_Context_config(v_a_5131_);
v_options_5137_ = lean_ctor_get(v_a_5133_, 2);
v_foApprox_5138_ = lean_ctor_get_uint8(v___x_5136_, 0);
v_ctxApprox_5139_ = lean_ctor_get_uint8(v___x_5136_, 1);
v_quasiPatternApprox_5140_ = lean_ctor_get_uint8(v___x_5136_, 2);
v_constApprox_5141_ = lean_ctor_get_uint8(v___x_5136_, 3);
v_isDefEqStuckEx_5142_ = lean_ctor_get_uint8(v___x_5136_, 4);
v_unificationHints_5143_ = lean_ctor_get_uint8(v___x_5136_, 5);
v_proofIrrelevance_5144_ = lean_ctor_get_uint8(v___x_5136_, 6);
v_assignSyntheticOpaque_5145_ = lean_ctor_get_uint8(v___x_5136_, 7);
v_offsetCnstrs_5146_ = lean_ctor_get_uint8(v___x_5136_, 8);
v_etaStruct_5147_ = lean_ctor_get_uint8(v___x_5136_, 10);
v_univApprox_5148_ = lean_ctor_get_uint8(v___x_5136_, 11);
v_iota_5149_ = lean_ctor_get_uint8(v___x_5136_, 12);
v_beta_5150_ = lean_ctor_get_uint8(v___x_5136_, 13);
v_proj_5151_ = lean_ctor_get_uint8(v___x_5136_, 14);
v_zeta_5152_ = lean_ctor_get_uint8(v___x_5136_, 15);
v_zetaDelta_5153_ = lean_ctor_get_uint8(v___x_5136_, 16);
v_zetaUnused_5154_ = lean_ctor_get_uint8(v___x_5136_, 17);
v_zetaHave_5155_ = lean_ctor_get_uint8(v___x_5136_, 18);
v_isSharedCheck_5403_ = !lean_is_exclusive(v___x_5136_);
if (v_isSharedCheck_5403_ == 0)
{
v___x_5157_ = v___x_5136_;
v_isShared_5158_ = v_isSharedCheck_5403_;
goto v_resetjp_5156_;
}
else
{
lean_dec(v___x_5136_);
v___x_5157_ = lean_box(0);
v_isShared_5158_ = v_isSharedCheck_5403_;
goto v_resetjp_5156_;
}
v_resetjp_5156_:
{
uint8_t v_trackZetaDelta_5159_; lean_object* v_zetaDeltaSet_5160_; lean_object* v_lctx_5161_; lean_object* v_localInstances_5162_; lean_object* v_defEqCtx_x3f_5163_; lean_object* v_synthPendingDepth_5164_; lean_object* v_canUnfold_x3f_5165_; uint8_t v_univApprox_5166_; uint8_t v_inTypeClassResolution_5167_; uint8_t v_cacheInferType_5168_; lean_object* v_inheritedTraceOptions_5169_; uint8_t v_hasTrace_5170_; uint8_t v___x_5171_; lean_object* v_config_5173_; 
v_trackZetaDelta_5159_ = lean_ctor_get_uint8(v_a_5131_, sizeof(void*)*7);
v_zetaDeltaSet_5160_ = lean_ctor_get(v_a_5131_, 1);
v_lctx_5161_ = lean_ctor_get(v_a_5131_, 2);
v_localInstances_5162_ = lean_ctor_get(v_a_5131_, 3);
v_defEqCtx_x3f_5163_ = lean_ctor_get(v_a_5131_, 4);
v_synthPendingDepth_5164_ = lean_ctor_get(v_a_5131_, 5);
v_canUnfold_x3f_5165_ = lean_ctor_get(v_a_5131_, 6);
v_univApprox_5166_ = lean_ctor_get_uint8(v_a_5131_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5167_ = lean_ctor_get_uint8(v_a_5131_, sizeof(void*)*7 + 2);
v_cacheInferType_5168_ = lean_ctor_get_uint8(v_a_5131_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5169_ = lean_ctor_get(v_a_5133_, 13);
v_hasTrace_5170_ = lean_ctor_get_uint8(v_options_5137_, sizeof(void*)*1);
v___x_5171_ = 3;
if (v_isShared_5158_ == 0)
{
v_config_5173_ = v___x_5157_;
goto v_reusejp_5172_;
}
else
{
lean_object* v_reuseFailAlloc_5402_; 
v_reuseFailAlloc_5402_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 0, v_foApprox_5138_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 1, v_ctxApprox_5139_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 2, v_quasiPatternApprox_5140_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 3, v_constApprox_5141_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 4, v_isDefEqStuckEx_5142_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 5, v_unificationHints_5143_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 6, v_proofIrrelevance_5144_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 7, v_assignSyntheticOpaque_5145_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 8, v_offsetCnstrs_5146_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 10, v_etaStruct_5147_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 11, v_univApprox_5148_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 12, v_iota_5149_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 13, v_beta_5150_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 14, v_proj_5151_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 15, v_zeta_5152_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 16, v_zetaDelta_5153_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 17, v_zetaUnused_5154_);
lean_ctor_set_uint8(v_reuseFailAlloc_5402_, 18, v_zetaHave_5155_);
v_config_5173_ = v_reuseFailAlloc_5402_;
goto v_reusejp_5172_;
}
v_reusejp_5172_:
{
uint64_t v___x_5174_; uint64_t v___x_5175_; uint64_t v___x_5176_; uint64_t v___x_5177_; uint64_t v___x_5178_; uint64_t v_key_5179_; lean_object* v___x_5180_; lean_object* v___x_5181_; 
lean_ctor_set_uint8(v_config_5173_, 9, v___x_5171_);
v___x_5174_ = l_Lean_Meta_Context_configKey(v_a_5131_);
v___x_5175_ = 2ULL;
v___x_5176_ = lean_uint64_shift_right(v___x_5174_, v___x_5175_);
v___x_5177_ = lean_uint64_shift_left(v___x_5176_, v___x_5175_);
v___x_5178_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5179_ = lean_uint64_lor(v___x_5177_, v___x_5178_);
v___x_5180_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5180_, 0, v_config_5173_);
lean_ctor_set_uint64(v___x_5180_, sizeof(void*)*1, v_key_5179_);
lean_inc(v_canUnfold_x3f_5165_);
lean_inc(v_synthPendingDepth_5164_);
lean_inc(v_defEqCtx_x3f_5163_);
lean_inc_ref(v_localInstances_5162_);
lean_inc_ref(v_lctx_5161_);
lean_inc(v_zetaDeltaSet_5160_);
v___x_5181_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5181_, 0, v___x_5180_);
lean_ctor_set(v___x_5181_, 1, v_zetaDeltaSet_5160_);
lean_ctor_set(v___x_5181_, 2, v_lctx_5161_);
lean_ctor_set(v___x_5181_, 3, v_localInstances_5162_);
lean_ctor_set(v___x_5181_, 4, v_defEqCtx_x3f_5163_);
lean_ctor_set(v___x_5181_, 5, v_synthPendingDepth_5164_);
lean_ctor_set(v___x_5181_, 6, v_canUnfold_x3f_5165_);
lean_ctor_set_uint8(v___x_5181_, sizeof(void*)*7, v_trackZetaDelta_5159_);
lean_ctor_set_uint8(v___x_5181_, sizeof(void*)*7 + 1, v_univApprox_5166_);
lean_ctor_set_uint8(v___x_5181_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5167_);
lean_ctor_set_uint8(v___x_5181_, sizeof(void*)*7 + 3, v_cacheInferType_5168_);
if (v_hasTrace_5170_ == 0)
{
lean_object* v___x_5182_; 
lean_inc_ref(v_expectedType_5127_);
v___x_5182_ = l_Lean_Meta_isClass_x3f(v_expectedType_5127_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5182_) == 0)
{
lean_object* v_a_5183_; lean_object* v___x_5185_; uint8_t v_isShared_5186_; uint8_t v_isSharedCheck_5220_; 
v_a_5183_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5220_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5220_ == 0)
{
v___x_5185_ = v___x_5182_;
v_isShared_5186_ = v_isSharedCheck_5220_;
goto v_resetjp_5184_;
}
else
{
lean_inc(v_a_5183_);
lean_dec(v___x_5182_);
v___x_5185_ = lean_box(0);
v_isShared_5186_ = v_isSharedCheck_5220_;
goto v_resetjp_5184_;
}
v_resetjp_5184_:
{
if (lean_obj_tag(v_a_5183_) == 1)
{
lean_object* v___x_5187_; 
lean_dec_ref(v_a_5183_);
lean_del_object(v___x_5185_);
lean_inc_ref(v_expectedType_5127_);
v___x_5187_ = l_Lean_Meta_isProp(v_expectedType_5127_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5187_) == 0)
{
lean_object* v_a_5188_; lean_object* v___x_5190_; uint8_t v_isShared_5191_; uint8_t v_isSharedCheck_5208_; 
v_a_5188_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5208_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5208_ == 0)
{
v___x_5190_ = v___x_5187_;
v_isShared_5191_ = v_isSharedCheck_5208_;
goto v_resetjp_5189_;
}
else
{
lean_inc(v_a_5188_);
lean_dec(v___x_5187_);
v___x_5190_ = lean_box(0);
v_isShared_5191_ = v_isSharedCheck_5208_;
goto v_resetjp_5189_;
}
v_resetjp_5189_:
{
uint8_t v___x_5192_; 
v___x_5192_ = lean_unbox(v_a_5188_);
lean_dec(v_a_5188_);
if (v___x_5192_ == 0)
{
lean_object* v___x_5193_; 
lean_del_object(v___x_5190_);
lean_inc(v_a_5134_);
lean_inc_ref(v_a_5133_);
lean_inc(v_a_5132_);
lean_inc_ref(v___x_5181_);
v___x_5193_ = lean_whnf(v_inst_5126_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5193_) == 0)
{
lean_object* v_a_5194_; lean_object* v_dummy_5195_; lean_object* v_nargs_5196_; lean_object* v___x_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v_a_5194_ = lean_ctor_get(v___x_5193_, 0);
lean_inc_n(v_a_5194_, 2);
lean_dec_ref(v___x_5193_);
v_dummy_5195_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5196_ = l_Lean_Expr_getAppNumArgs(v_a_5194_);
lean_inc(v_nargs_5196_);
v___x_5197_ = lean_mk_array(v_nargs_5196_, v_dummy_5195_);
v___x_5198_ = lean_unsigned_to_nat(1u);
v___x_5199_ = lean_nat_sub(v_nargs_5196_, v___x_5198_);
lean_dec(v_nargs_5196_);
v___x_5200_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_a_5194_, v_expectedType_5127_, v_hasTrace_5170_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v_a_5194_, v___x_5197_, v___x_5199_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
lean_dec_ref(v___x_5181_);
lean_dec(v___x_5199_);
return v___x_5200_;
}
else
{
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
return v___x_5193_;
}
}
else
{
lean_object* v___x_5201_; uint8_t v___x_5202_; 
v___x_5201_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5202_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5137_, v___x_5201_);
if (v___x_5202_ == 0)
{
lean_object* v___x_5204_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
if (v_isShared_5191_ == 0)
{
lean_ctor_set(v___x_5190_, 0, v_inst_5126_);
v___x_5204_ = v___x_5190_;
goto v_reusejp_5203_;
}
else
{
lean_object* v_reuseFailAlloc_5205_; 
v_reuseFailAlloc_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5205_, 0, v_inst_5126_);
v___x_5204_ = v_reuseFailAlloc_5205_;
goto v_reusejp_5203_;
}
v_reusejp_5203_:
{
return v___x_5204_;
}
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
lean_del_object(v___x_5190_);
v___x_5206_ = lean_box(0);
v___x_5207_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5127_, v_inst_5126_, v___x_5202_, v___x_5206_, v___x_5202_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
lean_dec_ref(v___x_5181_);
return v___x_5207_;
}
}
}
}
else
{
lean_object* v_a_5209_; lean_object* v___x_5211_; uint8_t v_isShared_5212_; uint8_t v_isSharedCheck_5216_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5209_ = lean_ctor_get(v___x_5187_, 0);
v_isSharedCheck_5216_ = !lean_is_exclusive(v___x_5187_);
if (v_isSharedCheck_5216_ == 0)
{
v___x_5211_ = v___x_5187_;
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
else
{
lean_inc(v_a_5209_);
lean_dec(v___x_5187_);
v___x_5211_ = lean_box(0);
v_isShared_5212_ = v_isSharedCheck_5216_;
goto v_resetjp_5210_;
}
v_resetjp_5210_:
{
lean_object* v___x_5214_; 
if (v_isShared_5212_ == 0)
{
v___x_5214_ = v___x_5211_;
goto v_reusejp_5213_;
}
else
{
lean_object* v_reuseFailAlloc_5215_; 
v_reuseFailAlloc_5215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5215_, 0, v_a_5209_);
v___x_5214_ = v_reuseFailAlloc_5215_;
goto v_reusejp_5213_;
}
v_reusejp_5213_:
{
return v___x_5214_;
}
}
}
}
else
{
lean_object* v___x_5218_; 
lean_dec(v_a_5183_);
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
if (v_isShared_5186_ == 0)
{
lean_ctor_set(v___x_5185_, 0, v_inst_5126_);
v___x_5218_ = v___x_5185_;
goto v_reusejp_5217_;
}
else
{
lean_object* v_reuseFailAlloc_5219_; 
v_reuseFailAlloc_5219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5219_, 0, v_inst_5126_);
v___x_5218_ = v_reuseFailAlloc_5219_;
goto v_reusejp_5217_;
}
v_reusejp_5217_:
{
return v___x_5218_;
}
}
}
}
else
{
lean_object* v_a_5221_; lean_object* v___x_5223_; uint8_t v_isShared_5224_; uint8_t v_isSharedCheck_5228_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5221_ = lean_ctor_get(v___x_5182_, 0);
v_isSharedCheck_5228_ = !lean_is_exclusive(v___x_5182_);
if (v_isSharedCheck_5228_ == 0)
{
v___x_5223_ = v___x_5182_;
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
else
{
lean_inc(v_a_5221_);
lean_dec(v___x_5182_);
v___x_5223_ = lean_box(0);
v_isShared_5224_ = v_isSharedCheck_5228_;
goto v_resetjp_5222_;
}
v_resetjp_5222_:
{
lean_object* v___x_5226_; 
if (v_isShared_5224_ == 0)
{
v___x_5226_ = v___x_5223_;
goto v_reusejp_5225_;
}
else
{
lean_object* v_reuseFailAlloc_5227_; 
v_reuseFailAlloc_5227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5227_, 0, v_a_5221_);
v___x_5226_ = v_reuseFailAlloc_5227_;
goto v_reusejp_5225_;
}
v_reusejp_5225_:
{
return v___x_5226_;
}
}
}
}
else
{
lean_object* v___f_5229_; lean_object* v_cls_5230_; lean_object* v___x_5231_; lean_object* v___x_5232_; uint8_t v___x_5233_; lean_object* v___y_5235_; lean_object* v___y_5236_; lean_object* v_a_5237_; lean_object* v___y_5247_; lean_object* v___y_5248_; lean_object* v_a_5249_; lean_object* v___y_5252_; lean_object* v___y_5253_; lean_object* v_a_5254_; lean_object* v___y_5257_; lean_object* v___y_5258_; lean_object* v___y_5259_; lean_object* v___y_5263_; lean_object* v___y_5264_; lean_object* v_a_5265_; lean_object* v___y_5278_; lean_object* v___y_5279_; lean_object* v_a_5280_; lean_object* v___y_5283_; lean_object* v___y_5284_; lean_object* v_a_5285_; lean_object* v___y_5288_; lean_object* v___y_5289_; lean_object* v___y_5290_; 
lean_inc_ref(v_expectedType_5127_);
v___f_5229_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5229_, 0, v_expectedType_5127_);
v_cls_5230_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5231_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1));
v___x_5232_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_5233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5169_, v_options_5137_, v___x_5232_);
if (v___x_5233_ == 0)
{
lean_object* v___x_5334_; uint8_t v___x_5335_; lean_object* v___y_5337_; lean_object* v___y_5338_; lean_object* v___y_5339_; lean_object* v___y_5340_; 
v___x_5334_ = l_Lean_trace_profiler;
v___x_5335_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5137_, v___x_5334_);
if (v___x_5335_ == 0)
{
lean_object* v___x_5372_; 
lean_dec_ref(v___f_5229_);
lean_inc_ref(v_expectedType_5127_);
v___x_5372_ = l_Lean_Meta_isClass_x3f(v_expectedType_5127_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5372_) == 0)
{
lean_object* v_a_5373_; lean_object* v___x_5375_; uint8_t v_isShared_5376_; uint8_t v_isSharedCheck_5393_; 
v_a_5373_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5393_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5393_ == 0)
{
v___x_5375_ = v___x_5372_;
v_isShared_5376_ = v_isSharedCheck_5393_;
goto v_resetjp_5374_;
}
else
{
lean_inc(v_a_5373_);
lean_dec(v___x_5372_);
v___x_5375_ = lean_box(0);
v_isShared_5376_ = v_isSharedCheck_5393_;
goto v_resetjp_5374_;
}
v_resetjp_5374_:
{
if (lean_obj_tag(v_a_5373_) == 1)
{
lean_del_object(v___x_5375_);
if (v___x_5233_ == 0)
{
lean_dec_ref(v_a_5373_);
v___y_5337_ = v___x_5181_;
v___y_5338_ = v_a_5132_;
v___y_5339_ = v_a_5133_;
v___y_5340_ = v_a_5134_;
goto v___jp_5336_;
}
else
{
lean_object* v_val_5377_; lean_object* v___x_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; 
v_val_5377_ = lean_ctor_get(v_a_5373_, 0);
lean_inc(v_val_5377_);
lean_dec_ref(v_a_5373_);
v___x_5378_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5379_ = l_Lean_MessageData_ofName(v_val_5377_);
v___x_5380_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5380_, 0, v___x_5378_);
lean_ctor_set(v___x_5380_, 1, v___x_5379_);
v___x_5381_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5230_, v___x_5380_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5381_) == 0)
{
lean_dec_ref(v___x_5381_);
v___y_5337_ = v___x_5181_;
v___y_5338_ = v_a_5132_;
v___y_5339_ = v_a_5133_;
v___y_5340_ = v_a_5134_;
goto v___jp_5336_;
}
else
{
lean_object* v_a_5382_; lean_object* v___x_5384_; uint8_t v_isShared_5385_; uint8_t v_isSharedCheck_5389_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5382_ = lean_ctor_get(v___x_5381_, 0);
v_isSharedCheck_5389_ = !lean_is_exclusive(v___x_5381_);
if (v_isSharedCheck_5389_ == 0)
{
v___x_5384_ = v___x_5381_;
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
else
{
lean_inc(v_a_5382_);
lean_dec(v___x_5381_);
v___x_5384_ = lean_box(0);
v_isShared_5385_ = v_isSharedCheck_5389_;
goto v_resetjp_5383_;
}
v_resetjp_5383_:
{
lean_object* v___x_5387_; 
if (v_isShared_5385_ == 0)
{
v___x_5387_ = v___x_5384_;
goto v_reusejp_5386_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v_a_5382_);
v___x_5387_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5386_;
}
v_reusejp_5386_:
{
return v___x_5387_;
}
}
}
}
}
else
{
lean_object* v___x_5391_; 
lean_dec(v_a_5373_);
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
if (v_isShared_5376_ == 0)
{
lean_ctor_set(v___x_5375_, 0, v_inst_5126_);
v___x_5391_ = v___x_5375_;
goto v_reusejp_5390_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v_inst_5126_);
v___x_5391_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5390_;
}
v_reusejp_5390_:
{
return v___x_5391_;
}
}
}
}
else
{
lean_object* v_a_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5401_; 
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5394_ = lean_ctor_get(v___x_5372_, 0);
v_isSharedCheck_5401_ = !lean_is_exclusive(v___x_5372_);
if (v_isSharedCheck_5401_ == 0)
{
v___x_5396_ = v___x_5372_;
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_a_5394_);
lean_dec(v___x_5372_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5401_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
lean_object* v___x_5399_; 
if (v_isShared_5397_ == 0)
{
v___x_5399_ = v___x_5396_;
goto v_reusejp_5398_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v_a_5394_);
v___x_5399_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5398_;
}
v_reusejp_5398_:
{
return v___x_5399_;
}
}
}
}
else
{
goto v___jp_5293_;
}
v___jp_5336_:
{
lean_object* v___x_5341_; 
lean_inc_ref(v_expectedType_5127_);
v___x_5341_ = l_Lean_Meta_isProp(v_expectedType_5127_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
if (lean_obj_tag(v___x_5341_) == 0)
{
lean_object* v_a_5342_; lean_object* v___x_5344_; uint8_t v_isShared_5345_; uint8_t v_isSharedCheck_5363_; 
v_a_5342_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5363_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5363_ == 0)
{
v___x_5344_ = v___x_5341_;
v_isShared_5345_ = v_isSharedCheck_5363_;
goto v_resetjp_5343_;
}
else
{
lean_inc(v_a_5342_);
lean_dec(v___x_5341_);
v___x_5344_ = lean_box(0);
v_isShared_5345_ = v_isSharedCheck_5363_;
goto v_resetjp_5343_;
}
v_resetjp_5343_:
{
uint8_t v___x_5346_; 
v___x_5346_ = lean_unbox(v_a_5342_);
lean_dec(v_a_5342_);
if (v___x_5346_ == 0)
{
lean_object* v___x_5347_; 
lean_del_object(v___x_5344_);
lean_inc(v___y_5340_);
lean_inc_ref(v___y_5339_);
lean_inc(v___y_5338_);
lean_inc_ref(v___y_5337_);
v___x_5347_ = lean_whnf(v_inst_5126_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
if (lean_obj_tag(v___x_5347_) == 0)
{
lean_object* v_a_5348_; lean_object* v_dummy_5349_; lean_object* v_nargs_5350_; lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; 
v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
lean_inc_n(v_a_5348_, 2);
lean_dec_ref(v___x_5347_);
v_dummy_5349_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5350_ = l_Lean_Expr_getAppNumArgs(v_a_5348_);
lean_inc(v_nargs_5350_);
v___x_5351_ = lean_mk_array(v_nargs_5350_, v_dummy_5349_);
v___x_5352_ = lean_unsigned_to_nat(1u);
v___x_5353_ = lean_nat_sub(v_nargs_5350_, v___x_5352_);
lean_dec(v_nargs_5350_);
v___x_5354_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_5348_, v_expectedType_5127_, v___x_5335_, v_hasTrace_5170_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v_a_5348_, v___x_5351_, v___x_5353_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec_ref(v___y_5337_);
lean_dec(v___x_5353_);
return v___x_5354_;
}
else
{
lean_dec_ref(v___y_5337_);
lean_dec_ref(v_expectedType_5127_);
return v___x_5347_;
}
}
else
{
lean_object* v_options_5355_; lean_object* v___x_5356_; uint8_t v___x_5357_; 
v_options_5355_ = lean_ctor_get(v___y_5339_, 2);
v___x_5356_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5357_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5355_, v___x_5356_);
if (v___x_5357_ == 0)
{
lean_object* v___x_5359_; 
lean_dec_ref(v___y_5337_);
lean_dec_ref(v_expectedType_5127_);
if (v_isShared_5345_ == 0)
{
lean_ctor_set(v___x_5344_, 0, v_inst_5126_);
v___x_5359_ = v___x_5344_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5360_; 
v_reuseFailAlloc_5360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5360_, 0, v_inst_5126_);
v___x_5359_ = v_reuseFailAlloc_5360_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
return v___x_5359_;
}
}
else
{
lean_object* v___x_5361_; lean_object* v___x_5362_; 
lean_del_object(v___x_5344_);
v___x_5361_ = lean_box(0);
v___x_5362_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5127_, v_inst_5126_, v_hasTrace_5170_, v___x_5361_, v_hasTrace_5170_, v___y_5337_, v___y_5338_, v___y_5339_, v___y_5340_);
lean_dec_ref(v___y_5337_);
return v___x_5362_;
}
}
}
}
else
{
lean_object* v_a_5364_; lean_object* v___x_5366_; uint8_t v_isShared_5367_; uint8_t v_isSharedCheck_5371_; 
lean_dec_ref(v___y_5337_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5364_ = lean_ctor_get(v___x_5341_, 0);
v_isSharedCheck_5371_ = !lean_is_exclusive(v___x_5341_);
if (v_isSharedCheck_5371_ == 0)
{
v___x_5366_ = v___x_5341_;
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
else
{
lean_inc(v_a_5364_);
lean_dec(v___x_5341_);
v___x_5366_ = lean_box(0);
v_isShared_5367_ = v_isSharedCheck_5371_;
goto v_resetjp_5365_;
}
v_resetjp_5365_:
{
lean_object* v___x_5369_; 
if (v_isShared_5367_ == 0)
{
v___x_5369_ = v___x_5366_;
goto v_reusejp_5368_;
}
else
{
lean_object* v_reuseFailAlloc_5370_; 
v_reuseFailAlloc_5370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5370_, 0, v_a_5364_);
v___x_5369_ = v_reuseFailAlloc_5370_;
goto v_reusejp_5368_;
}
v_reusejp_5368_:
{
return v___x_5369_;
}
}
}
}
}
else
{
goto v___jp_5293_;
}
v___jp_5234_:
{
lean_object* v___x_5238_; double v___x_5239_; double v___x_5240_; lean_object* v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; 
v___x_5238_ = lean_io_get_num_heartbeats();
v___x_5239_ = lean_float_of_nat(v___y_5236_);
v___x_5240_ = lean_float_of_nat(v___x_5238_);
v___x_5241_ = lean_box_float(v___x_5239_);
v___x_5242_ = lean_box_float(v___x_5240_);
v___x_5243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5243_, 0, v___x_5241_);
lean_ctor_set(v___x_5243_, 1, v___x_5242_);
v___x_5244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5244_, 0, v_a_5237_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_5230_, v_hasTrace_5170_, v___x_5231_, v_options_5137_, v___x_5233_, v___y_5235_, v___f_5229_, v___x_5244_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
lean_dec_ref(v___x_5181_);
return v___x_5245_;
}
v___jp_5246_:
{
lean_object* v___x_5250_; 
v___x_5250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5250_, 0, v_a_5249_);
v___y_5235_ = v___y_5247_;
v___y_5236_ = v___y_5248_;
v_a_5237_ = v___x_5250_;
goto v___jp_5234_;
}
v___jp_5251_:
{
lean_object* v___x_5255_; 
v___x_5255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5255_, 0, v_a_5254_);
v___y_5235_ = v___y_5252_;
v___y_5236_ = v___y_5253_;
v_a_5237_ = v___x_5255_;
goto v___jp_5234_;
}
v___jp_5256_:
{
if (lean_obj_tag(v___y_5259_) == 0)
{
lean_object* v_a_5260_; 
v_a_5260_ = lean_ctor_get(v___y_5259_, 0);
lean_inc(v_a_5260_);
lean_dec_ref(v___y_5259_);
v___y_5247_ = v___y_5257_;
v___y_5248_ = v___y_5258_;
v_a_5249_ = v_a_5260_;
goto v___jp_5246_;
}
else
{
lean_object* v_a_5261_; 
v_a_5261_ = lean_ctor_get(v___y_5259_, 0);
lean_inc(v_a_5261_);
lean_dec_ref(v___y_5259_);
v___y_5252_ = v___y_5257_;
v___y_5253_ = v___y_5258_;
v_a_5254_ = v_a_5261_;
goto v___jp_5251_;
}
}
v___jp_5262_:
{
lean_object* v___x_5266_; double v___x_5267_; double v___x_5268_; double v___x_5269_; double v___x_5270_; double v___x_5271_; lean_object* v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; 
v___x_5266_ = lean_io_mono_nanos_now();
v___x_5267_ = lean_float_of_nat(v___y_5264_);
v___x_5268_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5269_ = lean_float_div(v___x_5267_, v___x_5268_);
v___x_5270_ = lean_float_of_nat(v___x_5266_);
v___x_5271_ = lean_float_div(v___x_5270_, v___x_5268_);
v___x_5272_ = lean_box_float(v___x_5269_);
v___x_5273_ = lean_box_float(v___x_5271_);
v___x_5274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5272_);
lean_ctor_set(v___x_5274_, 1, v___x_5273_);
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v_a_5265_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_5230_, v_hasTrace_5170_, v___x_5231_, v_options_5137_, v___x_5233_, v___y_5263_, v___f_5229_, v___x_5275_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
lean_dec_ref(v___x_5181_);
return v___x_5276_;
}
v___jp_5277_:
{
lean_object* v___x_5281_; 
v___x_5281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5281_, 0, v_a_5280_);
v___y_5263_ = v___y_5278_;
v___y_5264_ = v___y_5279_;
v_a_5265_ = v___x_5281_;
goto v___jp_5262_;
}
v___jp_5282_:
{
lean_object* v___x_5286_; 
v___x_5286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5286_, 0, v_a_5285_);
v___y_5263_ = v___y_5283_;
v___y_5264_ = v___y_5284_;
v_a_5265_ = v___x_5286_;
goto v___jp_5262_;
}
v___jp_5287_:
{
if (lean_obj_tag(v___y_5290_) == 0)
{
lean_object* v_a_5291_; 
v_a_5291_ = lean_ctor_get(v___y_5290_, 0);
lean_inc(v_a_5291_);
lean_dec_ref(v___y_5290_);
v___y_5278_ = v___y_5288_;
v___y_5279_ = v___y_5289_;
v_a_5280_ = v_a_5291_;
goto v___jp_5277_;
}
else
{
lean_object* v_a_5292_; 
v_a_5292_ = lean_ctor_get(v___y_5290_, 0);
lean_inc(v_a_5292_);
lean_dec_ref(v___y_5290_);
v___y_5283_ = v___y_5288_;
v___y_5284_ = v___y_5289_;
v_a_5285_ = v_a_5292_;
goto v___jp_5282_;
}
}
v___jp_5293_:
{
lean_object* v___x_5294_; 
v___x_5294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v_a_5134_);
if (lean_obj_tag(v___x_5294_) == 0)
{
lean_object* v_a_5295_; lean_object* v___x_5296_; uint8_t v___x_5297_; 
v_a_5295_ = lean_ctor_get(v___x_5294_, 0);
lean_inc(v_a_5295_);
lean_dec_ref(v___x_5294_);
v___x_5296_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5297_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5137_, v___x_5296_);
if (v___x_5297_ == 0)
{
lean_object* v___x_5298_; lean_object* v___x_5299_; 
v___x_5298_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5127_);
v___x_5299_ = l_Lean_Meta_isClass_x3f(v_expectedType_5127_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5299_) == 0)
{
lean_object* v_a_5300_; 
v_a_5300_ = lean_ctor_get(v___x_5299_, 0);
lean_inc(v_a_5300_);
lean_dec_ref(v___x_5299_);
if (lean_obj_tag(v_a_5300_) == 1)
{
if (v___x_5233_ == 0)
{
lean_object* v___x_5301_; lean_object* v___x_5302_; 
lean_dec_ref(v_a_5300_);
v___x_5301_ = lean_box(0);
v___x_5302_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5127_, v_inst_5126_, v___x_5297_, v_hasTrace_5170_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v___x_5301_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
v___y_5288_ = v_a_5295_;
v___y_5289_ = v___x_5298_;
v___y_5290_ = v___x_5302_;
goto v___jp_5287_;
}
else
{
lean_object* v_val_5303_; lean_object* v___x_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; 
v_val_5303_ = lean_ctor_get(v_a_5300_, 0);
lean_inc(v_val_5303_);
lean_dec_ref(v_a_5300_);
v___x_5304_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5305_ = l_Lean_MessageData_ofName(v_val_5303_);
v___x_5306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5306_, 0, v___x_5304_);
lean_ctor_set(v___x_5306_, 1, v___x_5305_);
v___x_5307_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5230_, v___x_5306_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5307_) == 0)
{
lean_object* v_a_5308_; lean_object* v___x_5309_; 
v_a_5308_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5308_);
lean_dec_ref(v___x_5307_);
v___x_5309_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5127_, v_inst_5126_, v___x_5297_, v_hasTrace_5170_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v_a_5308_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
v___y_5288_ = v_a_5295_;
v___y_5289_ = v___x_5298_;
v___y_5290_ = v___x_5309_;
goto v___jp_5287_;
}
else
{
lean_object* v_a_5310_; 
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5310_ = lean_ctor_get(v___x_5307_, 0);
lean_inc(v_a_5310_);
lean_dec_ref(v___x_5307_);
v___y_5283_ = v_a_5295_;
v___y_5284_ = v___x_5298_;
v_a_5285_ = v_a_5310_;
goto v___jp_5282_;
}
}
}
else
{
lean_dec(v_a_5300_);
lean_dec_ref(v_expectedType_5127_);
v___y_5278_ = v_a_5295_;
v___y_5279_ = v___x_5298_;
v_a_5280_ = v_inst_5126_;
goto v___jp_5277_;
}
}
else
{
lean_object* v_a_5311_; 
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5311_ = lean_ctor_get(v___x_5299_, 0);
lean_inc(v_a_5311_);
lean_dec_ref(v___x_5299_);
v___y_5283_ = v_a_5295_;
v___y_5284_ = v___x_5298_;
v_a_5285_ = v_a_5311_;
goto v___jp_5282_;
}
}
else
{
lean_object* v___x_5312_; lean_object* v___x_5313_; 
v___x_5312_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5127_);
v___x_5313_ = l_Lean_Meta_isClass_x3f(v_expectedType_5127_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5313_) == 0)
{
lean_object* v_a_5314_; 
v_a_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5314_);
lean_dec_ref(v___x_5313_);
if (lean_obj_tag(v_a_5314_) == 1)
{
if (v___x_5233_ == 0)
{
lean_object* v___x_5315_; lean_object* v___x_5316_; 
lean_dec_ref(v_a_5314_);
v___x_5315_ = lean_box(0);
v___x_5316_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5127_, v_inst_5126_, v___x_5297_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v___x_5315_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
v___y_5257_ = v_a_5295_;
v___y_5258_ = v___x_5312_;
v___y_5259_ = v___x_5316_;
goto v___jp_5256_;
}
else
{
lean_object* v_val_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; 
v_val_5317_ = lean_ctor_get(v_a_5314_, 0);
lean_inc(v_val_5317_);
lean_dec_ref(v_a_5314_);
v___x_5318_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5319_ = l_Lean_MessageData_ofName(v_val_5317_);
v___x_5320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5320_, 0, v___x_5318_);
lean_ctor_set(v___x_5320_, 1, v___x_5319_);
v___x_5321_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5230_, v___x_5320_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
if (lean_obj_tag(v___x_5321_) == 0)
{
lean_object* v_a_5322_; lean_object* v___x_5323_; 
v_a_5322_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_a_5322_);
lean_dec_ref(v___x_5321_);
v___x_5323_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5127_, v_inst_5126_, v___x_5297_, v_compile_5128_, v_logCompileErrors_5129_, v_isMeta_5130_, v_a_5322_, v___x_5181_, v_a_5132_, v_a_5133_, v_a_5134_);
v___y_5257_ = v_a_5295_;
v___y_5258_ = v___x_5312_;
v___y_5259_ = v___x_5323_;
goto v___jp_5256_;
}
else
{
lean_object* v_a_5324_; 
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5324_ = lean_ctor_get(v___x_5321_, 0);
lean_inc(v_a_5324_);
lean_dec_ref(v___x_5321_);
v___y_5252_ = v_a_5295_;
v___y_5253_ = v___x_5312_;
v_a_5254_ = v_a_5324_;
goto v___jp_5251_;
}
}
}
else
{
lean_dec(v_a_5314_);
lean_dec_ref(v_expectedType_5127_);
v___y_5247_ = v_a_5295_;
v___y_5248_ = v___x_5312_;
v_a_5249_ = v_inst_5126_;
goto v___jp_5246_;
}
}
else
{
lean_object* v_a_5325_; 
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5325_ = lean_ctor_get(v___x_5313_, 0);
lean_inc(v_a_5325_);
lean_dec_ref(v___x_5313_);
v___y_5252_ = v_a_5295_;
v___y_5253_ = v___x_5312_;
v_a_5254_ = v_a_5325_;
goto v___jp_5251_;
}
}
}
else
{
lean_object* v_a_5326_; lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5333_; 
lean_dec_ref(v___f_5229_);
lean_dec_ref(v___x_5181_);
lean_dec_ref(v_expectedType_5127_);
lean_dec_ref(v_inst_5126_);
v_a_5326_ = lean_ctor_get(v___x_5294_, 0);
v_isSharedCheck_5333_ = !lean_is_exclusive(v___x_5294_);
if (v_isSharedCheck_5333_ == 0)
{
v___x_5328_ = v___x_5294_;
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
else
{
lean_inc(v_a_5326_);
lean_dec(v___x_5294_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5333_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v___x_5331_; 
if (v_isShared_5329_ == 0)
{
v___x_5331_ = v___x_5328_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5332_; 
v_reuseFailAlloc_5332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5332_, 0, v_a_5326_);
v___x_5331_ = v_reuseFailAlloc_5332_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
return v___x_5331_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(lean_object* v___x_5404_, lean_object* v_a_5405_, uint8_t v_compile_5406_, uint8_t v_logCompileErrors_5407_, uint8_t v_isMeta_5408_, lean_object* v___x_5409_, lean_object* v___x_5410_, lean_object* v_____r_5411_, lean_object* v___y_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_){
_start:
{
lean_object* v___x_5417_; 
v___x_5417_ = l_Lean_Meta_wrapInstance(v___x_5404_, v_a_5405_, v_compile_5406_, v_logCompileErrors_5407_, v_isMeta_5408_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_);
if (lean_obj_tag(v___x_5417_) == 0)
{
lean_object* v_a_5418_; lean_object* v___x_5419_; 
v_a_5418_ = lean_ctor_get(v___x_5417_, 0);
lean_inc(v_a_5418_);
lean_dec_ref(v___x_5417_);
v___x_5419_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_5409_, v_a_5418_, v___y_5413_);
if (lean_obj_tag(v___x_5419_) == 0)
{
lean_object* v___x_5421_; uint8_t v_isShared_5422_; uint8_t v_isSharedCheck_5427_; 
v_isSharedCheck_5427_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5427_ == 0)
{
lean_object* v_unused_5428_; 
v_unused_5428_ = lean_ctor_get(v___x_5419_, 0);
lean_dec(v_unused_5428_);
v___x_5421_ = v___x_5419_;
v_isShared_5422_ = v_isSharedCheck_5427_;
goto v_resetjp_5420_;
}
else
{
lean_dec(v___x_5419_);
v___x_5421_ = lean_box(0);
v_isShared_5422_ = v_isSharedCheck_5427_;
goto v_resetjp_5420_;
}
v_resetjp_5420_:
{
lean_object* v___x_5423_; lean_object* v___x_5425_; 
v___x_5423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5423_, 0, v___x_5410_);
if (v_isShared_5422_ == 0)
{
lean_ctor_set(v___x_5421_, 0, v___x_5423_);
v___x_5425_ = v___x_5421_;
goto v_reusejp_5424_;
}
else
{
lean_object* v_reuseFailAlloc_5426_; 
v_reuseFailAlloc_5426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5426_, 0, v___x_5423_);
v___x_5425_ = v_reuseFailAlloc_5426_;
goto v_reusejp_5424_;
}
v_reusejp_5424_:
{
return v___x_5425_;
}
}
}
else
{
lean_object* v_a_5429_; lean_object* v___x_5431_; uint8_t v_isShared_5432_; uint8_t v_isSharedCheck_5436_; 
v_a_5429_ = lean_ctor_get(v___x_5419_, 0);
v_isSharedCheck_5436_ = !lean_is_exclusive(v___x_5419_);
if (v_isSharedCheck_5436_ == 0)
{
v___x_5431_ = v___x_5419_;
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
else
{
lean_inc(v_a_5429_);
lean_dec(v___x_5419_);
v___x_5431_ = lean_box(0);
v_isShared_5432_ = v_isSharedCheck_5436_;
goto v_resetjp_5430_;
}
v_resetjp_5430_:
{
lean_object* v___x_5434_; 
if (v_isShared_5432_ == 0)
{
v___x_5434_ = v___x_5431_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_object* v_a_5437_; lean_object* v___x_5439_; uint8_t v_isShared_5440_; uint8_t v_isSharedCheck_5444_; 
lean_dec(v___x_5409_);
v_a_5437_ = lean_ctor_get(v___x_5417_, 0);
v_isSharedCheck_5444_ = !lean_is_exclusive(v___x_5417_);
if (v_isSharedCheck_5444_ == 0)
{
v___x_5439_ = v___x_5417_;
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
else
{
lean_inc(v_a_5437_);
lean_dec(v___x_5417_);
v___x_5439_ = lean_box(0);
v_isShared_5440_ = v_isSharedCheck_5444_;
goto v_resetjp_5438_;
}
v_resetjp_5438_:
{
lean_object* v___x_5442_; 
if (v_isShared_5440_ == 0)
{
v___x_5442_ = v___x_5439_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed(lean_object* v___x_5445_, lean_object* v_a_5446_, lean_object* v_compile_5447_, lean_object* v_logCompileErrors_5448_, lean_object* v_isMeta_5449_, lean_object* v___x_5450_, lean_object* v___x_5451_, lean_object* v_____r_5452_, lean_object* v___y_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_){
_start:
{
uint8_t v_compile_boxed_5458_; uint8_t v_logCompileErrors_boxed_5459_; uint8_t v_isMeta_boxed_5460_; lean_object* v_res_5461_; 
v_compile_boxed_5458_ = lean_unbox(v_compile_5447_);
v_logCompileErrors_boxed_5459_ = lean_unbox(v_logCompileErrors_5448_);
v_isMeta_boxed_5460_ = lean_unbox(v_isMeta_5449_);
v_res_5461_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_5445_, v_a_5446_, v_compile_boxed_5458_, v_logCompileErrors_boxed_5459_, v_isMeta_boxed_5460_, v___x_5450_, v___x_5451_, v_____r_5452_, v___y_5453_, v___y_5454_, v___y_5455_, v___y_5456_);
lean_dec(v___y_5456_);
lean_dec_ref(v___y_5455_);
lean_dec(v___y_5454_);
lean_dec_ref(v___y_5453_);
return v_res_5461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_5462_, lean_object* v_inst_5463_, lean_object* v___x_5464_, lean_object* v_hasTrace_5465_, lean_object* v_compile_5466_, lean_object* v_logCompileErrors_5467_, lean_object* v_isMeta_5468_, lean_object* v_____r_5469_, lean_object* v___y_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_){
_start:
{
uint8_t v___x_122036__boxed_5475_; uint8_t v_hasTrace_boxed_5476_; uint8_t v_compile_boxed_5477_; uint8_t v_logCompileErrors_boxed_5478_; uint8_t v_isMeta_boxed_5479_; lean_object* v_res_5480_; 
v___x_122036__boxed_5475_ = lean_unbox(v___x_5464_);
v_hasTrace_boxed_5476_ = lean_unbox(v_hasTrace_5465_);
v_compile_boxed_5477_ = lean_unbox(v_compile_5466_);
v_logCompileErrors_boxed_5478_ = lean_unbox(v_logCompileErrors_5467_);
v_isMeta_boxed_5479_ = lean_unbox(v_isMeta_5468_);
v_res_5480_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5462_, v_inst_5463_, v___x_122036__boxed_5475_, v_hasTrace_boxed_5476_, v_compile_boxed_5477_, v_logCompileErrors_boxed_5478_, v_isMeta_boxed_5479_, v_____r_5469_, v___y_5470_, v___y_5471_, v___y_5472_, v___y_5473_);
lean_dec(v___y_5473_);
lean_dec_ref(v___y_5472_);
lean_dec(v___y_5471_);
lean_dec_ref(v___y_5470_);
return v_res_5480_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_5481_, lean_object* v_inst_5482_, lean_object* v___x_5483_, lean_object* v_compile_5484_, lean_object* v_logCompileErrors_5485_, lean_object* v_isMeta_5486_, lean_object* v_____r_5487_, lean_object* v___y_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_){
_start:
{
uint8_t v___x_122060__boxed_5493_; uint8_t v_compile_boxed_5494_; uint8_t v_logCompileErrors_boxed_5495_; uint8_t v_isMeta_boxed_5496_; lean_object* v_res_5497_; 
v___x_122060__boxed_5493_ = lean_unbox(v___x_5483_);
v_compile_boxed_5494_ = lean_unbox(v_compile_5484_);
v_logCompileErrors_boxed_5495_ = lean_unbox(v_logCompileErrors_5485_);
v_isMeta_boxed_5496_ = lean_unbox(v_isMeta_5486_);
v_res_5497_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5481_, v_inst_5482_, v___x_122060__boxed_5493_, v_compile_boxed_5494_, v_logCompileErrors_boxed_5495_, v_isMeta_boxed_5496_, v_____r_5487_, v___y_5488_, v___y_5489_, v___y_5490_, v___y_5491_);
lean_dec(v___y_5491_);
lean_dec_ref(v___y_5490_);
lean_dec(v___y_5489_);
lean_dec_ref(v___y_5488_);
return v_res_5497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object* v_a_5498_, lean_object* v_expectedType_5499_, lean_object* v___x_5500_, lean_object* v___x_5501_, lean_object* v_compile_5502_, lean_object* v_logCompileErrors_5503_, lean_object* v_isMeta_5504_, lean_object* v_x_5505_, lean_object* v_x_5506_, lean_object* v_x_5507_, lean_object* v___y_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_){
_start:
{
uint8_t v___x_122109__boxed_5513_; uint8_t v___x_122110__boxed_5514_; uint8_t v_compile_boxed_5515_; uint8_t v_logCompileErrors_boxed_5516_; uint8_t v_isMeta_boxed_5517_; lean_object* v_res_5518_; 
v___x_122109__boxed_5513_ = lean_unbox(v___x_5500_);
v___x_122110__boxed_5514_ = lean_unbox(v___x_5501_);
v_compile_boxed_5515_ = lean_unbox(v_compile_5502_);
v_logCompileErrors_boxed_5516_ = lean_unbox(v_logCompileErrors_5503_);
v_isMeta_boxed_5517_ = lean_unbox(v_isMeta_5504_);
v_res_5518_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_a_5498_, v_expectedType_5499_, v___x_122109__boxed_5513_, v___x_122110__boxed_5514_, v_compile_boxed_5515_, v_logCompileErrors_boxed_5516_, v_isMeta_boxed_5517_, v_x_5505_, v_x_5506_, v_x_5507_, v___y_5508_, v___y_5509_, v___y_5510_, v___y_5511_);
lean_dec(v___y_5511_);
lean_dec_ref(v___y_5510_);
lean_dec(v___y_5509_);
lean_dec_ref(v___y_5508_);
return v_res_5518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21___boxed(lean_object* v_a_5519_, lean_object* v_expectedType_5520_, lean_object* v___x_5521_, lean_object* v_compile_5522_, lean_object* v_logCompileErrors_5523_, lean_object* v_isMeta_5524_, lean_object* v_x_5525_, lean_object* v_x_5526_, lean_object* v_x_5527_, lean_object* v___y_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_){
_start:
{
uint8_t v___x_122265__boxed_5533_; uint8_t v_compile_boxed_5534_; uint8_t v_logCompileErrors_boxed_5535_; uint8_t v_isMeta_boxed_5536_; lean_object* v_res_5537_; 
v___x_122265__boxed_5533_ = lean_unbox(v___x_5521_);
v_compile_boxed_5534_ = lean_unbox(v_compile_5522_);
v_logCompileErrors_boxed_5535_ = lean_unbox(v_logCompileErrors_5523_);
v_isMeta_boxed_5536_ = lean_unbox(v_isMeta_5524_);
v_res_5537_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(v_a_5519_, v_expectedType_5520_, v___x_122265__boxed_5533_, v_compile_boxed_5534_, v_logCompileErrors_boxed_5535_, v_isMeta_boxed_5536_, v_x_5525_, v_x_5526_, v_x_5527_, v___y_5528_, v___y_5529_, v___y_5530_, v___y_5531_);
lean_dec(v___y_5531_);
lean_dec_ref(v___y_5530_);
lean_dec(v___y_5529_);
lean_dec_ref(v___y_5528_);
return v_res_5537_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object* v_a_5538_, lean_object* v_expectedType_5539_, lean_object* v___x_5540_, lean_object* v___x_5541_, lean_object* v_compile_5542_, lean_object* v_logCompileErrors_5543_, lean_object* v_isMeta_5544_, lean_object* v_x_5545_, lean_object* v_x_5546_, lean_object* v_x_5547_, lean_object* v___y_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_){
_start:
{
uint8_t v___x_122433__boxed_5553_; uint8_t v___x_122434__boxed_5554_; uint8_t v_compile_boxed_5555_; uint8_t v_logCompileErrors_boxed_5556_; uint8_t v_isMeta_boxed_5557_; lean_object* v_res_5558_; 
v___x_122433__boxed_5553_ = lean_unbox(v___x_5540_);
v___x_122434__boxed_5554_ = lean_unbox(v___x_5541_);
v_compile_boxed_5555_ = lean_unbox(v_compile_5542_);
v_logCompileErrors_boxed_5556_ = lean_unbox(v_logCompileErrors_5543_);
v_isMeta_boxed_5557_ = lean_unbox(v_isMeta_5544_);
v_res_5558_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_5538_, v_expectedType_5539_, v___x_122433__boxed_5553_, v___x_122434__boxed_5554_, v_compile_boxed_5555_, v_logCompileErrors_boxed_5556_, v_isMeta_boxed_5557_, v_x_5545_, v_x_5546_, v_x_5547_, v___y_5548_, v___y_5549_, v___y_5550_, v___y_5551_);
lean_dec(v___y_5551_);
lean_dec_ref(v___y_5550_);
lean_dec(v___y_5549_);
lean_dec_ref(v___y_5548_);
lean_dec(v_x_5547_);
return v_res_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object* v_a_5559_, lean_object* v_expectedType_5560_, lean_object* v___x_5561_, lean_object* v_compile_5562_, lean_object* v_logCompileErrors_5563_, lean_object* v_isMeta_5564_, lean_object* v_x_5565_, lean_object* v_x_5566_, lean_object* v_x_5567_, lean_object* v___y_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_){
_start:
{
uint8_t v___x_122602__boxed_5573_; uint8_t v_compile_boxed_5574_; uint8_t v_logCompileErrors_boxed_5575_; uint8_t v_isMeta_boxed_5576_; lean_object* v_res_5577_; 
v___x_122602__boxed_5573_ = lean_unbox(v___x_5561_);
v_compile_boxed_5574_ = lean_unbox(v_compile_5562_);
v_logCompileErrors_boxed_5575_ = lean_unbox(v_logCompileErrors_5563_);
v_isMeta_boxed_5576_ = lean_unbox(v_isMeta_5564_);
v_res_5577_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_a_5559_, v_expectedType_5560_, v___x_122602__boxed_5573_, v_compile_boxed_5574_, v_logCompileErrors_boxed_5575_, v_isMeta_boxed_5576_, v_x_5565_, v_x_5566_, v_x_5567_, v___y_5568_, v___y_5569_, v___y_5570_, v___y_5571_);
lean_dec(v___y_5571_);
lean_dec_ref(v___y_5570_);
lean_dec(v___y_5569_);
lean_dec_ref(v___y_5568_);
lean_dec(v_x_5567_);
return v_res_5577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12___boxed(lean_object* v_a_5578_, lean_object* v_expectedType_5579_, lean_object* v___x_5580_, lean_object* v_compile_5581_, lean_object* v_logCompileErrors_5582_, lean_object* v_isMeta_5583_, lean_object* v_x_5584_, lean_object* v_x_5585_, lean_object* v_x_5586_, lean_object* v___y_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_){
_start:
{
uint8_t v___x_122770__boxed_5592_; uint8_t v_compile_boxed_5593_; uint8_t v_logCompileErrors_boxed_5594_; uint8_t v_isMeta_boxed_5595_; lean_object* v_res_5596_; 
v___x_122770__boxed_5592_ = lean_unbox(v___x_5580_);
v_compile_boxed_5593_ = lean_unbox(v_compile_5581_);
v_logCompileErrors_boxed_5594_ = lean_unbox(v_logCompileErrors_5582_);
v_isMeta_boxed_5595_ = lean_unbox(v_isMeta_5583_);
v_res_5596_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(v_a_5578_, v_expectedType_5579_, v___x_122770__boxed_5592_, v_compile_boxed_5593_, v_logCompileErrors_boxed_5594_, v_isMeta_boxed_5595_, v_x_5584_, v_x_5585_, v_x_5586_, v___y_5587_, v___y_5588_, v___y_5589_, v___y_5590_);
lean_dec(v___y_5590_);
lean_dec_ref(v___y_5589_);
lean_dec(v___y_5588_);
lean_dec_ref(v___y_5587_);
return v_res_5596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object* v_a_5597_, lean_object* v_expectedType_5598_, lean_object* v___x_5599_, lean_object* v_compile_5600_, lean_object* v_logCompileErrors_5601_, lean_object* v_isMeta_5602_, lean_object* v_x_5603_, lean_object* v_x_5604_, lean_object* v_x_5605_, lean_object* v___y_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_){
_start:
{
uint8_t v___x_122939__boxed_5611_; uint8_t v_compile_boxed_5612_; uint8_t v_logCompileErrors_boxed_5613_; uint8_t v_isMeta_boxed_5614_; lean_object* v_res_5615_; 
v___x_122939__boxed_5611_ = lean_unbox(v___x_5599_);
v_compile_boxed_5612_ = lean_unbox(v_compile_5600_);
v_logCompileErrors_boxed_5613_ = lean_unbox(v_logCompileErrors_5601_);
v_isMeta_boxed_5614_ = lean_unbox(v_isMeta_5602_);
v_res_5615_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_a_5597_, v_expectedType_5598_, v___x_122939__boxed_5611_, v_compile_boxed_5612_, v_logCompileErrors_boxed_5613_, v_isMeta_boxed_5614_, v_x_5603_, v_x_5604_, v_x_5605_, v___y_5606_, v___y_5607_, v___y_5608_, v___y_5609_);
lean_dec(v___y_5609_);
lean_dec_ref(v___y_5608_);
lean_dec(v___y_5607_);
lean_dec_ref(v___y_5606_);
lean_dec(v_x_5605_);
return v_res_5615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_5616_, lean_object* v_expectedType_5617_, lean_object* v_compile_5618_, lean_object* v_logCompileErrors_5619_, lean_object* v_isMeta_5620_, lean_object* v_a_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_){
_start:
{
uint8_t v_compile_boxed_5626_; uint8_t v_logCompileErrors_boxed_5627_; uint8_t v_isMeta_boxed_5628_; lean_object* v_res_5629_; 
v_compile_boxed_5626_ = lean_unbox(v_compile_5618_);
v_logCompileErrors_boxed_5627_ = lean_unbox(v_logCompileErrors_5619_);
v_isMeta_boxed_5628_ = lean_unbox(v_isMeta_5620_);
v_res_5629_ = l_Lean_Meta_wrapInstance(v_inst_5616_, v_expectedType_5617_, v_compile_boxed_5626_, v_logCompileErrors_boxed_5627_, v_isMeta_boxed_5628_, v_a_5621_, v_a_5622_, v_a_5623_, v_a_5624_);
lean_dec(v_a_5624_);
lean_dec_ref(v_a_5623_);
lean_dec(v_a_5622_);
lean_dec_ref(v_a_5621_);
return v_res_5629_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object* v_upperBound_5630_, lean_object* v_fst_5631_, lean_object* v_args_5632_, lean_object* v_compile_5633_, lean_object* v_logCompileErrors_5634_, lean_object* v_isMeta_5635_, lean_object* v___x_5636_, lean_object* v_a_5637_, lean_object* v_b_5638_, lean_object* v___y_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_){
_start:
{
uint8_t v_compile_boxed_5644_; uint8_t v_logCompileErrors_boxed_5645_; uint8_t v_isMeta_boxed_5646_; uint8_t v___x_123294__boxed_5647_; lean_object* v_res_5648_; 
v_compile_boxed_5644_ = lean_unbox(v_compile_5633_);
v_logCompileErrors_boxed_5645_ = lean_unbox(v_logCompileErrors_5634_);
v_isMeta_boxed_5646_ = lean_unbox(v_isMeta_5635_);
v___x_123294__boxed_5647_ = lean_unbox(v___x_5636_);
v_res_5648_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_5630_, v_fst_5631_, v_args_5632_, v_compile_boxed_5644_, v_logCompileErrors_boxed_5645_, v_isMeta_boxed_5646_, v___x_123294__boxed_5647_, v_a_5637_, v_b_5638_, v___y_5639_, v___y_5640_, v___y_5641_, v___y_5642_);
lean_dec(v___y_5642_);
lean_dec_ref(v___y_5641_);
lean_dec(v___y_5640_);
lean_dec_ref(v___y_5639_);
lean_dec_ref(v_args_5632_);
lean_dec_ref(v_fst_5631_);
lean_dec(v_upperBound_5630_);
return v_res_5648_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg___boxed(lean_object* v_upperBound_5649_, lean_object* v_fst_5650_, lean_object* v_args_5651_, lean_object* v_compile_5652_, lean_object* v_logCompileErrors_5653_, lean_object* v_isMeta_5654_, lean_object* v___x_5655_, lean_object* v_a_5656_, lean_object* v_b_5657_, lean_object* v___y_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_){
_start:
{
uint8_t v_compile_boxed_5663_; uint8_t v_logCompileErrors_boxed_5664_; uint8_t v_isMeta_boxed_5665_; uint8_t v___x_123449__boxed_5666_; lean_object* v_res_5667_; 
v_compile_boxed_5663_ = lean_unbox(v_compile_5652_);
v_logCompileErrors_boxed_5664_ = lean_unbox(v_logCompileErrors_5653_);
v_isMeta_boxed_5665_ = lean_unbox(v_isMeta_5654_);
v___x_123449__boxed_5666_ = lean_unbox(v___x_5655_);
v_res_5667_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_5649_, v_fst_5650_, v_args_5651_, v_compile_boxed_5663_, v_logCompileErrors_boxed_5664_, v_isMeta_boxed_5665_, v___x_123449__boxed_5666_, v_a_5656_, v_b_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
lean_dec(v___y_5661_);
lean_dec_ref(v___y_5660_);
lean_dec(v___y_5659_);
lean_dec_ref(v___y_5658_);
lean_dec_ref(v_args_5651_);
lean_dec_ref(v_fst_5650_);
lean_dec(v_upperBound_5649_);
return v_res_5667_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object* v_upperBound_5668_, lean_object* v_fst_5669_, lean_object* v_args_5670_, lean_object* v___x_5671_, lean_object* v_compile_5672_, lean_object* v_logCompileErrors_5673_, lean_object* v_isMeta_5674_, lean_object* v_a_5675_, lean_object* v_b_5676_, lean_object* v___y_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_){
_start:
{
uint8_t v___x_123618__boxed_5682_; uint8_t v_compile_boxed_5683_; uint8_t v_logCompileErrors_boxed_5684_; uint8_t v_isMeta_boxed_5685_; lean_object* v_res_5686_; 
v___x_123618__boxed_5682_ = lean_unbox(v___x_5671_);
v_compile_boxed_5683_ = lean_unbox(v_compile_5672_);
v_logCompileErrors_boxed_5684_ = lean_unbox(v_logCompileErrors_5673_);
v_isMeta_boxed_5685_ = lean_unbox(v_isMeta_5674_);
v_res_5686_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_5668_, v_fst_5669_, v_args_5670_, v___x_123618__boxed_5682_, v_compile_boxed_5683_, v_logCompileErrors_boxed_5684_, v_isMeta_boxed_5685_, v_a_5675_, v_b_5676_, v___y_5677_, v___y_5678_, v___y_5679_, v___y_5680_);
lean_dec(v___y_5680_);
lean_dec_ref(v___y_5679_);
lean_dec(v___y_5678_);
lean_dec_ref(v___y_5677_);
lean_dec_ref(v_args_5670_);
lean_dec_ref(v_fst_5669_);
lean_dec(v_upperBound_5668_);
return v_res_5686_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg___boxed(lean_object* v_upperBound_5687_, lean_object* v_fst_5688_, lean_object* v_args_5689_, lean_object* v___x_5690_, lean_object* v_compile_5691_, lean_object* v_logCompileErrors_5692_, lean_object* v_isMeta_5693_, lean_object* v_a_5694_, lean_object* v_b_5695_, lean_object* v___y_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_){
_start:
{
uint8_t v___x_123788__boxed_5701_; uint8_t v_compile_boxed_5702_; uint8_t v_logCompileErrors_boxed_5703_; uint8_t v_isMeta_boxed_5704_; lean_object* v_res_5705_; 
v___x_123788__boxed_5701_ = lean_unbox(v___x_5690_);
v_compile_boxed_5702_ = lean_unbox(v_compile_5691_);
v_logCompileErrors_boxed_5703_ = lean_unbox(v_logCompileErrors_5692_);
v_isMeta_boxed_5704_ = lean_unbox(v_isMeta_5693_);
v_res_5705_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_5687_, v_fst_5688_, v_args_5689_, v___x_123788__boxed_5701_, v_compile_boxed_5702_, v_logCompileErrors_boxed_5703_, v_isMeta_boxed_5704_, v_a_5694_, v_b_5695_, v___y_5696_, v___y_5697_, v___y_5698_, v___y_5699_);
lean_dec(v___y_5699_);
lean_dec_ref(v___y_5698_);
lean_dec(v___y_5697_);
lean_dec_ref(v___y_5696_);
lean_dec_ref(v_args_5689_);
lean_dec_ref(v_fst_5688_);
lean_dec(v_upperBound_5687_);
return v_res_5705_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object* v_upperBound_5706_, lean_object* v_fst_5707_, lean_object* v_args_5708_, lean_object* v___x_5709_, lean_object* v_compile_5710_, lean_object* v_logCompileErrors_5711_, lean_object* v_isMeta_5712_, lean_object* v___x_5713_, lean_object* v_a_5714_, lean_object* v_b_5715_, lean_object* v___y_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_){
_start:
{
uint8_t v___x_123958__boxed_5721_; uint8_t v_compile_boxed_5722_; uint8_t v_logCompileErrors_boxed_5723_; uint8_t v_isMeta_boxed_5724_; uint8_t v___x_123959__boxed_5725_; lean_object* v_res_5726_; 
v___x_123958__boxed_5721_ = lean_unbox(v___x_5709_);
v_compile_boxed_5722_ = lean_unbox(v_compile_5710_);
v_logCompileErrors_boxed_5723_ = lean_unbox(v_logCompileErrors_5711_);
v_isMeta_boxed_5724_ = lean_unbox(v_isMeta_5712_);
v___x_123959__boxed_5725_ = lean_unbox(v___x_5713_);
v_res_5726_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_5706_, v_fst_5707_, v_args_5708_, v___x_123958__boxed_5721_, v_compile_boxed_5722_, v_logCompileErrors_boxed_5723_, v_isMeta_boxed_5724_, v___x_123959__boxed_5725_, v_a_5714_, v_b_5715_, v___y_5716_, v___y_5717_, v___y_5718_, v___y_5719_);
lean_dec(v___y_5719_);
lean_dec_ref(v___y_5718_);
lean_dec(v___y_5717_);
lean_dec_ref(v___y_5716_);
lean_dec_ref(v_args_5708_);
lean_dec_ref(v_fst_5707_);
lean_dec(v_upperBound_5706_);
return v_res_5726_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg___boxed(lean_object* v_upperBound_5727_, lean_object* v_fst_5728_, lean_object* v_args_5729_, lean_object* v___x_5730_, lean_object* v_compile_5731_, lean_object* v_logCompileErrors_5732_, lean_object* v_isMeta_5733_, lean_object* v___x_5734_, lean_object* v_a_5735_, lean_object* v_b_5736_, lean_object* v___y_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_){
_start:
{
uint8_t v___x_124132__boxed_5742_; uint8_t v_compile_boxed_5743_; uint8_t v_logCompileErrors_boxed_5744_; uint8_t v_isMeta_boxed_5745_; uint8_t v___x_124133__boxed_5746_; lean_object* v_res_5747_; 
v___x_124132__boxed_5742_ = lean_unbox(v___x_5730_);
v_compile_boxed_5743_ = lean_unbox(v_compile_5731_);
v_logCompileErrors_boxed_5744_ = lean_unbox(v_logCompileErrors_5732_);
v_isMeta_boxed_5745_ = lean_unbox(v_isMeta_5733_);
v___x_124133__boxed_5746_ = lean_unbox(v___x_5734_);
v_res_5747_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_5727_, v_fst_5728_, v_args_5729_, v___x_124132__boxed_5742_, v_compile_boxed_5743_, v_logCompileErrors_boxed_5744_, v_isMeta_boxed_5745_, v___x_124133__boxed_5746_, v_a_5735_, v_b_5736_, v___y_5737_, v___y_5738_, v___y_5739_, v___y_5740_);
lean_dec(v___y_5740_);
lean_dec_ref(v___y_5739_);
lean_dec(v___y_5738_);
lean_dec_ref(v___y_5737_);
lean_dec_ref(v_args_5729_);
lean_dec_ref(v_fst_5728_);
lean_dec(v_upperBound_5727_);
return v_res_5747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t v_sz_5748_, size_t v_i_5749_, lean_object* v_bs_5750_, lean_object* v___y_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_){
_start:
{
lean_object* v___x_5756_; 
v___x_5756_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_5748_, v_i_5749_, v_bs_5750_, v___y_5752_);
return v___x_5756_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_sz_5757_, lean_object* v_i_5758_, lean_object* v_bs_5759_, lean_object* v___y_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_){
_start:
{
size_t v_sz_boxed_5765_; size_t v_i_boxed_5766_; lean_object* v_res_5767_; 
v_sz_boxed_5765_ = lean_unbox_usize(v_sz_5757_);
lean_dec(v_sz_5757_);
v_i_boxed_5766_ = lean_unbox_usize(v_i_5758_);
lean_dec(v_i_5758_);
v_res_5767_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_boxed_5765_, v_i_boxed_5766_, v_bs_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_);
lean_dec(v___y_5763_);
lean_dec_ref(v___y_5762_);
lean_dec(v___y_5761_);
lean_dec_ref(v___y_5760_);
return v_res_5767_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(lean_object* v_upperBound_5768_, lean_object* v_fst_5769_, lean_object* v_args_5770_, uint8_t v_compile_5771_, uint8_t v_logCompileErrors_5772_, uint8_t v_isMeta_5773_, uint8_t v___x_5774_, lean_object* v_inst_5775_, lean_object* v_R_5776_, lean_object* v_a_5777_, lean_object* v_b_5778_, lean_object* v_c_5779_, lean_object* v___y_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_){
_start:
{
lean_object* v___x_5785_; 
v___x_5785_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_5768_, v_fst_5769_, v_args_5770_, v_compile_5771_, v_logCompileErrors_5772_, v_isMeta_5773_, v___x_5774_, v_a_5777_, v_b_5778_, v___y_5780_, v___y_5781_, v___y_5782_, v___y_5783_);
return v___x_5785_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_5786_ = _args[0];
lean_object* v_fst_5787_ = _args[1];
lean_object* v_args_5788_ = _args[2];
lean_object* v_compile_5789_ = _args[3];
lean_object* v_logCompileErrors_5790_ = _args[4];
lean_object* v_isMeta_5791_ = _args[5];
lean_object* v___x_5792_ = _args[6];
lean_object* v_inst_5793_ = _args[7];
lean_object* v_R_5794_ = _args[8];
lean_object* v_a_5795_ = _args[9];
lean_object* v_b_5796_ = _args[10];
lean_object* v_c_5797_ = _args[11];
lean_object* v___y_5798_ = _args[12];
lean_object* v___y_5799_ = _args[13];
lean_object* v___y_5800_ = _args[14];
lean_object* v___y_5801_ = _args[15];
lean_object* v___y_5802_ = _args[16];
_start:
{
uint8_t v_compile_boxed_5803_; uint8_t v_logCompileErrors_boxed_5804_; uint8_t v_isMeta_boxed_5805_; uint8_t v___x_129214__boxed_5806_; lean_object* v_res_5807_; 
v_compile_boxed_5803_ = lean_unbox(v_compile_5789_);
v_logCompileErrors_boxed_5804_ = lean_unbox(v_logCompileErrors_5790_);
v_isMeta_boxed_5805_ = lean_unbox(v_isMeta_5791_);
v___x_129214__boxed_5806_ = lean_unbox(v___x_5792_);
v_res_5807_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(v_upperBound_5786_, v_fst_5787_, v_args_5788_, v_compile_boxed_5803_, v_logCompileErrors_boxed_5804_, v_isMeta_boxed_5805_, v___x_129214__boxed_5806_, v_inst_5793_, v_R_5794_, v_a_5795_, v_b_5796_, v_c_5797_, v___y_5798_, v___y_5799_, v___y_5800_, v___y_5801_);
lean_dec(v___y_5801_);
lean_dec_ref(v___y_5800_);
lean_dec(v___y_5799_);
lean_dec_ref(v___y_5798_);
lean_dec_ref(v_args_5788_);
lean_dec_ref(v_fst_5787_);
lean_dec(v_upperBound_5786_);
return v_res_5807_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_00_u03b1_5808_, lean_object* v_msg_5809_, lean_object* v___y_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v___x_5815_; 
v___x_5815_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_5809_, v___y_5810_, v___y_5811_, v___y_5812_, v___y_5813_);
return v___x_5815_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object* v_00_u03b1_5816_, lean_object* v_msg_5817_, lean_object* v___y_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_){
_start:
{
lean_object* v_res_5823_; 
v_res_5823_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7(v_00_u03b1_5816_, v_msg_5817_, v___y_5818_, v___y_5819_, v___y_5820_, v___y_5821_);
lean_dec(v___y_5821_);
lean_dec_ref(v___y_5820_);
lean_dec(v___y_5819_);
lean_dec_ref(v___y_5818_);
return v_res_5823_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v_upperBound_5824_, lean_object* v_fst_5825_, lean_object* v_args_5826_, uint8_t v___x_5827_, uint8_t v_compile_5828_, uint8_t v_logCompileErrors_5829_, uint8_t v_isMeta_5830_, uint8_t v___x_5831_, lean_object* v_inst_5832_, lean_object* v_R_5833_, lean_object* v_a_5834_, lean_object* v_b_5835_, lean_object* v_c_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_5824_, v_fst_5825_, v_args_5826_, v___x_5827_, v_compile_5828_, v_logCompileErrors_5829_, v_isMeta_5830_, v___x_5831_, v_a_5834_, v_b_5835_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_5843_ = _args[0];
lean_object* v_fst_5844_ = _args[1];
lean_object* v_args_5845_ = _args[2];
lean_object* v___x_5846_ = _args[3];
lean_object* v_compile_5847_ = _args[4];
lean_object* v_logCompileErrors_5848_ = _args[5];
lean_object* v_isMeta_5849_ = _args[6];
lean_object* v___x_5850_ = _args[7];
lean_object* v_inst_5851_ = _args[8];
lean_object* v_R_5852_ = _args[9];
lean_object* v_a_5853_ = _args[10];
lean_object* v_b_5854_ = _args[11];
lean_object* v_c_5855_ = _args[12];
lean_object* v___y_5856_ = _args[13];
lean_object* v___y_5857_ = _args[14];
lean_object* v___y_5858_ = _args[15];
lean_object* v___y_5859_ = _args[16];
lean_object* v___y_5860_ = _args[17];
_start:
{
uint8_t v___x_129260__boxed_5861_; uint8_t v_compile_boxed_5862_; uint8_t v_logCompileErrors_boxed_5863_; uint8_t v_isMeta_boxed_5864_; uint8_t v___x_129261__boxed_5865_; lean_object* v_res_5866_; 
v___x_129260__boxed_5861_ = lean_unbox(v___x_5846_);
v_compile_boxed_5862_ = lean_unbox(v_compile_5847_);
v_logCompileErrors_boxed_5863_ = lean_unbox(v_logCompileErrors_5848_);
v_isMeta_boxed_5864_ = lean_unbox(v_isMeta_5849_);
v___x_129261__boxed_5865_ = lean_unbox(v___x_5850_);
v_res_5866_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(v_upperBound_5843_, v_fst_5844_, v_args_5845_, v___x_129260__boxed_5861_, v_compile_boxed_5862_, v_logCompileErrors_boxed_5863_, v_isMeta_boxed_5864_, v___x_129261__boxed_5865_, v_inst_5851_, v_R_5852_, v_a_5853_, v_b_5854_, v_c_5855_, v___y_5856_, v___y_5857_, v___y_5858_, v___y_5859_);
lean_dec(v___y_5859_);
lean_dec_ref(v___y_5858_);
lean_dec(v___y_5857_);
lean_dec_ref(v___y_5856_);
lean_dec_ref(v_args_5845_);
lean_dec_ref(v_fst_5844_);
lean_dec(v_upperBound_5843_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_upperBound_5867_, lean_object* v_fst_5868_, lean_object* v_args_5869_, uint8_t v___x_5870_, uint8_t v_compile_5871_, uint8_t v_logCompileErrors_5872_, uint8_t v_isMeta_5873_, lean_object* v_inst_5874_, lean_object* v_R_5875_, lean_object* v_a_5876_, lean_object* v_b_5877_, lean_object* v_c_5878_, lean_object* v___y_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_){
_start:
{
lean_object* v___x_5884_; 
v___x_5884_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_5867_, v_fst_5868_, v_args_5869_, v___x_5870_, v_compile_5871_, v_logCompileErrors_5872_, v_isMeta_5873_, v_a_5876_, v_b_5877_, v___y_5879_, v___y_5880_, v___y_5881_, v___y_5882_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_5885_ = _args[0];
lean_object* v_fst_5886_ = _args[1];
lean_object* v_args_5887_ = _args[2];
lean_object* v___x_5888_ = _args[3];
lean_object* v_compile_5889_ = _args[4];
lean_object* v_logCompileErrors_5890_ = _args[5];
lean_object* v_isMeta_5891_ = _args[6];
lean_object* v_inst_5892_ = _args[7];
lean_object* v_R_5893_ = _args[8];
lean_object* v_a_5894_ = _args[9];
lean_object* v_b_5895_ = _args[10];
lean_object* v_c_5896_ = _args[11];
lean_object* v___y_5897_ = _args[12];
lean_object* v___y_5898_ = _args[13];
lean_object* v___y_5899_ = _args[14];
lean_object* v___y_5900_ = _args[15];
lean_object* v___y_5901_ = _args[16];
_start:
{
uint8_t v___x_129292__boxed_5902_; uint8_t v_compile_boxed_5903_; uint8_t v_logCompileErrors_boxed_5904_; uint8_t v_isMeta_boxed_5905_; lean_object* v_res_5906_; 
v___x_129292__boxed_5902_ = lean_unbox(v___x_5888_);
v_compile_boxed_5903_ = lean_unbox(v_compile_5889_);
v_logCompileErrors_boxed_5904_ = lean_unbox(v_logCompileErrors_5890_);
v_isMeta_boxed_5905_ = lean_unbox(v_isMeta_5891_);
v_res_5906_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(v_upperBound_5885_, v_fst_5886_, v_args_5887_, v___x_129292__boxed_5902_, v_compile_boxed_5903_, v_logCompileErrors_boxed_5904_, v_isMeta_boxed_5905_, v_inst_5892_, v_R_5893_, v_a_5894_, v_b_5895_, v_c_5896_, v___y_5897_, v___y_5898_, v___y_5899_, v___y_5900_);
lean_dec(v___y_5900_);
lean_dec_ref(v___y_5899_);
lean_dec(v___y_5898_);
lean_dec_ref(v___y_5897_);
lean_dec_ref(v_args_5887_);
lean_dec_ref(v_fst_5886_);
lean_dec(v_upperBound_5885_);
return v_res_5906_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25(lean_object* v_00_u03b1_5907_, lean_object* v_x_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_){
_start:
{
lean_object* v___x_5914_; 
v___x_5914_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_x_5908_);
return v___x_5914_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___boxed(lean_object* v_00_u03b1_5915_, lean_object* v_x_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
lean_object* v_res_5922_; 
v_res_5922_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25(v_00_u03b1_5915_, v_x_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
return v_res_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5(lean_object* v_00_u03b1_5923_, lean_object* v_constName_5924_, lean_object* v___y_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_){
_start:
{
lean_object* v___x_5930_; 
v___x_5930_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_5924_, v___y_5925_, v___y_5926_, v___y_5927_, v___y_5928_);
return v___x_5930_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5931_, lean_object* v_constName_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_){
_start:
{
lean_object* v_res_5938_; 
v_res_5938_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5(v_00_u03b1_5931_, v_constName_5932_, v___y_5933_, v___y_5934_, v___y_5935_, v___y_5936_);
lean_dec(v___y_5936_);
lean_dec_ref(v___y_5935_);
lean_dec(v___y_5934_);
lean_dec_ref(v___y_5933_);
return v_res_5938_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8(lean_object* v_upperBound_5939_, lean_object* v_fst_5940_, lean_object* v_args_5941_, uint8_t v_compile_5942_, uint8_t v_logCompileErrors_5943_, uint8_t v_isMeta_5944_, uint8_t v___x_5945_, lean_object* v_inst_5946_, lean_object* v_R_5947_, lean_object* v_a_5948_, lean_object* v_b_5949_, lean_object* v_c_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_){
_start:
{
lean_object* v___x_5956_; 
v___x_5956_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_5939_, v_fst_5940_, v_args_5941_, v_compile_5942_, v_logCompileErrors_5943_, v_isMeta_5944_, v___x_5945_, v_a_5948_, v_b_5949_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_5957_ = _args[0];
lean_object* v_fst_5958_ = _args[1];
lean_object* v_args_5959_ = _args[2];
lean_object* v_compile_5960_ = _args[3];
lean_object* v_logCompileErrors_5961_ = _args[4];
lean_object* v_isMeta_5962_ = _args[5];
lean_object* v___x_5963_ = _args[6];
lean_object* v_inst_5964_ = _args[7];
lean_object* v_R_5965_ = _args[8];
lean_object* v_a_5966_ = _args[9];
lean_object* v_b_5967_ = _args[10];
lean_object* v_c_5968_ = _args[11];
lean_object* v___y_5969_ = _args[12];
lean_object* v___y_5970_ = _args[13];
lean_object* v___y_5971_ = _args[14];
lean_object* v___y_5972_ = _args[15];
lean_object* v___y_5973_ = _args[16];
_start:
{
uint8_t v_compile_boxed_5974_; uint8_t v_logCompileErrors_boxed_5975_; uint8_t v_isMeta_boxed_5976_; uint8_t v___x_129358__boxed_5977_; lean_object* v_res_5978_; 
v_compile_boxed_5974_ = lean_unbox(v_compile_5960_);
v_logCompileErrors_boxed_5975_ = lean_unbox(v_logCompileErrors_5961_);
v_isMeta_boxed_5976_ = lean_unbox(v_isMeta_5962_);
v___x_129358__boxed_5977_ = lean_unbox(v___x_5963_);
v_res_5978_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8(v_upperBound_5957_, v_fst_5958_, v_args_5959_, v_compile_boxed_5974_, v_logCompileErrors_boxed_5975_, v_isMeta_boxed_5976_, v___x_129358__boxed_5977_, v_inst_5964_, v_R_5965_, v_a_5966_, v_b_5967_, v_c_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
lean_dec(v___y_5972_);
lean_dec_ref(v___y_5971_);
lean_dec(v___y_5970_);
lean_dec_ref(v___y_5969_);
lean_dec_ref(v_args_5959_);
lean_dec_ref(v_fst_5958_);
lean_dec(v_upperBound_5957_);
return v_res_5978_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15(lean_object* v_upperBound_5979_, lean_object* v_fst_5980_, lean_object* v_args_5981_, uint8_t v___x_5982_, uint8_t v_compile_5983_, uint8_t v_logCompileErrors_5984_, uint8_t v_isMeta_5985_, uint8_t v___x_5986_, lean_object* v_inst_5987_, lean_object* v_R_5988_, lean_object* v_a_5989_, lean_object* v_b_5990_, lean_object* v_c_5991_, lean_object* v___y_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
lean_object* v___x_5997_; 
v___x_5997_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_5979_, v_fst_5980_, v_args_5981_, v___x_5982_, v_compile_5983_, v_logCompileErrors_5984_, v_isMeta_5985_, v___x_5986_, v_a_5989_, v_b_5990_, v___y_5992_, v___y_5993_, v___y_5994_, v___y_5995_);
return v___x_5997_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___boxed(lean_object** _args){
lean_object* v_upperBound_5998_ = _args[0];
lean_object* v_fst_5999_ = _args[1];
lean_object* v_args_6000_ = _args[2];
lean_object* v___x_6001_ = _args[3];
lean_object* v_compile_6002_ = _args[4];
lean_object* v_logCompileErrors_6003_ = _args[5];
lean_object* v_isMeta_6004_ = _args[6];
lean_object* v___x_6005_ = _args[7];
lean_object* v_inst_6006_ = _args[8];
lean_object* v_R_6007_ = _args[9];
lean_object* v_a_6008_ = _args[10];
lean_object* v_b_6009_ = _args[11];
lean_object* v_c_6010_ = _args[12];
lean_object* v___y_6011_ = _args[13];
lean_object* v___y_6012_ = _args[14];
lean_object* v___y_6013_ = _args[15];
lean_object* v___y_6014_ = _args[16];
lean_object* v___y_6015_ = _args[17];
_start:
{
uint8_t v___x_129387__boxed_6016_; uint8_t v_compile_boxed_6017_; uint8_t v_logCompileErrors_boxed_6018_; uint8_t v_isMeta_boxed_6019_; uint8_t v___x_129388__boxed_6020_; lean_object* v_res_6021_; 
v___x_129387__boxed_6016_ = lean_unbox(v___x_6001_);
v_compile_boxed_6017_ = lean_unbox(v_compile_6002_);
v_logCompileErrors_boxed_6018_ = lean_unbox(v_logCompileErrors_6003_);
v_isMeta_boxed_6019_ = lean_unbox(v_isMeta_6004_);
v___x_129388__boxed_6020_ = lean_unbox(v___x_6005_);
v_res_6021_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15(v_upperBound_5998_, v_fst_5999_, v_args_6000_, v___x_129387__boxed_6016_, v_compile_boxed_6017_, v_logCompileErrors_boxed_6018_, v_isMeta_boxed_6019_, v___x_129388__boxed_6020_, v_inst_6006_, v_R_6007_, v_a_6008_, v_b_6009_, v_c_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_);
lean_dec(v___y_6014_);
lean_dec_ref(v___y_6013_);
lean_dec(v___y_6012_);
lean_dec_ref(v___y_6011_);
lean_dec_ref(v_args_6000_);
lean_dec_ref(v_fst_5999_);
lean_dec(v_upperBound_5998_);
return v_res_6021_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19(lean_object* v_upperBound_6022_, lean_object* v_fst_6023_, lean_object* v_args_6024_, uint8_t v___x_6025_, uint8_t v_compile_6026_, uint8_t v_logCompileErrors_6027_, uint8_t v_isMeta_6028_, lean_object* v_inst_6029_, lean_object* v_R_6030_, lean_object* v_a_6031_, lean_object* v_b_6032_, lean_object* v_c_6033_, lean_object* v___y_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_){
_start:
{
lean_object* v___x_6039_; 
v___x_6039_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_6022_, v_fst_6023_, v_args_6024_, v___x_6025_, v_compile_6026_, v_logCompileErrors_6027_, v_isMeta_6028_, v_a_6031_, v_b_6032_, v___y_6034_, v___y_6035_, v___y_6036_, v___y_6037_);
return v___x_6039_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___boxed(lean_object** _args){
lean_object* v_upperBound_6040_ = _args[0];
lean_object* v_fst_6041_ = _args[1];
lean_object* v_args_6042_ = _args[2];
lean_object* v___x_6043_ = _args[3];
lean_object* v_compile_6044_ = _args[4];
lean_object* v_logCompileErrors_6045_ = _args[5];
lean_object* v_isMeta_6046_ = _args[6];
lean_object* v_inst_6047_ = _args[7];
lean_object* v_R_6048_ = _args[8];
lean_object* v_a_6049_ = _args[9];
lean_object* v_b_6050_ = _args[10];
lean_object* v_c_6051_ = _args[11];
lean_object* v___y_6052_ = _args[12];
lean_object* v___y_6053_ = _args[13];
lean_object* v___y_6054_ = _args[14];
lean_object* v___y_6055_ = _args[15];
lean_object* v___y_6056_ = _args[16];
_start:
{
uint8_t v___x_129419__boxed_6057_; uint8_t v_compile_boxed_6058_; uint8_t v_logCompileErrors_boxed_6059_; uint8_t v_isMeta_boxed_6060_; lean_object* v_res_6061_; 
v___x_129419__boxed_6057_ = lean_unbox(v___x_6043_);
v_compile_boxed_6058_ = lean_unbox(v_compile_6044_);
v_logCompileErrors_boxed_6059_ = lean_unbox(v_logCompileErrors_6045_);
v_isMeta_boxed_6060_ = lean_unbox(v_isMeta_6046_);
v_res_6061_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19(v_upperBound_6040_, v_fst_6041_, v_args_6042_, v___x_129419__boxed_6057_, v_compile_boxed_6058_, v_logCompileErrors_boxed_6059_, v_isMeta_boxed_6060_, v_inst_6047_, v_R_6048_, v_a_6049_, v_b_6050_, v_c_6051_, v___y_6052_, v___y_6053_, v___y_6054_, v___y_6055_);
lean_dec(v___y_6055_);
lean_dec_ref(v___y_6054_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec_ref(v_args_6042_);
lean_dec_ref(v_fst_6041_);
lean_dec(v_upperBound_6040_);
return v_res_6061_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_6062_, lean_object* v_ref_6063_, lean_object* v_constName_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_){
_start:
{
lean_object* v___x_6070_; 
v___x_6070_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_6063_, v_constName_6064_, v___y_6065_, v___y_6066_, v___y_6067_, v___y_6068_);
return v___x_6070_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_6071_, lean_object* v_ref_6072_, lean_object* v_constName_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_){
_start:
{
lean_object* v_res_6079_; 
v_res_6079_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7(v_00_u03b1_6071_, v_ref_6072_, v_constName_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_);
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6076_);
lean_dec(v___y_6075_);
lean_dec_ref(v___y_6074_);
lean_dec(v_ref_6072_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21(lean_object* v_00_u03b1_6080_, lean_object* v_ref_6081_, lean_object* v_msg_6082_, lean_object* v_declHint_6083_, lean_object* v___y_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_){
_start:
{
lean_object* v___x_6089_; 
v___x_6089_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_6081_, v_msg_6082_, v_declHint_6083_, v___y_6084_, v___y_6085_, v___y_6086_, v___y_6087_);
return v___x_6089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___boxed(lean_object* v_00_u03b1_6090_, lean_object* v_ref_6091_, lean_object* v_msg_6092_, lean_object* v_declHint_6093_, lean_object* v___y_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_){
_start:
{
lean_object* v_res_6099_; 
v_res_6099_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21(v_00_u03b1_6090_, v_ref_6091_, v_msg_6092_, v_declHint_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
lean_dec(v___y_6095_);
lean_dec_ref(v___y_6094_);
lean_dec(v_ref_6091_);
return v_res_6099_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31(lean_object* v_msg_6100_, lean_object* v_declHint_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_){
_start:
{
lean_object* v___x_6107_; 
v___x_6107_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_6100_, v_declHint_6101_, v___y_6105_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___boxed(lean_object* v_msg_6108_, lean_object* v_declHint_6109_, lean_object* v___y_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v_res_6115_; 
v_res_6115_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31(v_msg_6108_, v_declHint_6109_, v___y_6110_, v___y_6111_, v___y_6112_, v___y_6113_);
lean_dec(v___y_6113_);
lean_dec_ref(v___y_6112_);
lean_dec(v___y_6111_);
lean_dec_ref(v___y_6110_);
return v_res_6115_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30(lean_object* v_00_u03b1_6116_, lean_object* v_ref_6117_, lean_object* v_msg_6118_, lean_object* v___y_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_6117_, v_msg_6118_, v___y_6119_, v___y_6120_, v___y_6121_, v___y_6122_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___boxed(lean_object* v_00_u03b1_6125_, lean_object* v_ref_6126_, lean_object* v_msg_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_){
_start:
{
lean_object* v_res_6133_; 
v_res_6133_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30(v_00_u03b1_6125_, v_ref_6126_, v_msg_6127_, v___y_6128_, v___y_6129_, v___y_6130_, v___y_6131_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
lean_dec(v_ref_6126_);
return v_res_6133_;
}
}
lean_object* runtime_initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_instances = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_instances);
lean_dec_ref(res);
res = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_backward_inferInstanceAs_wrap_data = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_backward_inferInstanceAs_wrap_data);
lean_dec_ref(res);
res = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Closure(uint8_t builtin);
lean_object* initialize_Lean_Meta_SynthInstance(uint8_t builtin);
lean_object* initialize_Lean_Meta_CtorRecognizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_WrapInstance(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Closure(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_SynthInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CtorRecognizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_WrapInstance(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_WrapInstance(builtin);
}
#ifdef __cplusplus
}
#endif
