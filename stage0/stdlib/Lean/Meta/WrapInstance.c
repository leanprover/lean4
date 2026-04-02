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
static const lean_ctor_object l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4__value)}};
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
static const lean_ctor_object l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4__value)}};
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
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l_Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_));
v___x_63_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4_();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_85_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_86_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_87_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_));
v___x_88_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_85_, v___x_86_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4____boxed(lean_object* v_a_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_74059213____hygCtx___hyg_4_();
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_110_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_111_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_112_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_));
v___x_113_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_110_, v___x_111_, v___x_112_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4____boxed(lean_object* v_a_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_504867867____hygCtx___hyg_4_();
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = ((lean_object*)(l_Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_136_ = ((lean_object*)(l_Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_137_ = ((lean_object*)(l_Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_));
v___x_138_ = l_Lean_Option_register___at___00Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_913563019____hygCtx___hyg_4__spec__0(v___x_135_, v___x_136_, v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_2755641687____hygCtx___hyg_4_();
return v_res_140_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_185_ = lean_unsigned_to_nat(3246864463u);
v___x_186_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_187_ = l_Lean_Name_num___override(v___x_186_, v___x_185_);
return v___x_187_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; 
v___x_189_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_190_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_191_ = l_Lean_Name_str___override(v___x_190_, v___x_189_);
return v___x_191_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_195_; 
v___x_193_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_194_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_195_ = l_Lean_Name_str___override(v___x_194_, v___x_193_);
return v___x_195_;
}
}
static lean_object* _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_196_ = lean_unsigned_to_nat(2u);
v___x_197_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_198_ = l_Lean_Name_num___override(v___x_197_, v___x_196_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_200_; uint8_t v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_200_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_201_ = 0;
v___x_202_ = lean_obj_once(&l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_, &l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_);
v___x_203_ = l_Lean_registerTraceClass(v___x_200_, v___x_201_, v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2____boxed(lean_object* v_a_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_();
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(lean_object* v_e_206_, lean_object* v___y_207_){
_start:
{
uint8_t v___x_209_; 
v___x_209_ = l_Lean_Expr_hasMVar(v_e_206_);
if (v___x_209_ == 0)
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v_e_206_);
return v___x_210_;
}
else
{
lean_object* v___x_211_; lean_object* v_mctx_212_; lean_object* v___x_213_; lean_object* v_fst_214_; lean_object* v_snd_215_; lean_object* v___x_216_; lean_object* v_cache_217_; lean_object* v_zetaDeltaFVarIds_218_; lean_object* v_postponed_219_; lean_object* v_diag_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_229_; 
v___x_211_ = lean_st_ref_get(v___y_207_);
v_mctx_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_mctx_212_);
lean_dec(v___x_211_);
v___x_213_ = l_Lean_instantiateMVarsCore(v_mctx_212_, v_e_206_);
v_fst_214_ = lean_ctor_get(v___x_213_, 0);
lean_inc(v_fst_214_);
v_snd_215_ = lean_ctor_get(v___x_213_, 1);
lean_inc(v_snd_215_);
lean_dec_ref(v___x_213_);
v___x_216_ = lean_st_ref_take(v___y_207_);
v_cache_217_ = lean_ctor_get(v___x_216_, 1);
v_zetaDeltaFVarIds_218_ = lean_ctor_get(v___x_216_, 2);
v_postponed_219_ = lean_ctor_get(v___x_216_, 3);
v_diag_220_ = lean_ctor_get(v___x_216_, 4);
v_isSharedCheck_229_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_229_ == 0)
{
lean_object* v_unused_230_; 
v_unused_230_ = lean_ctor_get(v___x_216_, 0);
lean_dec(v_unused_230_);
v___x_222_ = v___x_216_;
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_diag_220_);
lean_inc(v_postponed_219_);
lean_inc(v_zetaDeltaFVarIds_218_);
lean_inc(v_cache_217_);
lean_dec(v___x_216_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_229_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_225_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 0, v_snd_215_);
v___x_225_ = v___x_222_;
goto v_reusejp_224_;
}
else
{
lean_object* v_reuseFailAlloc_228_; 
v_reuseFailAlloc_228_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_228_, 0, v_snd_215_);
lean_ctor_set(v_reuseFailAlloc_228_, 1, v_cache_217_);
lean_ctor_set(v_reuseFailAlloc_228_, 2, v_zetaDeltaFVarIds_218_);
lean_ctor_set(v_reuseFailAlloc_228_, 3, v_postponed_219_);
lean_ctor_set(v_reuseFailAlloc_228_, 4, v_diag_220_);
v___x_225_ = v_reuseFailAlloc_228_;
goto v_reusejp_224_;
}
v_reusejp_224_:
{
lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_226_ = lean_st_ref_set(v___y_207_, v___x_225_);
v___x_227_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_227_, 0, v_fst_214_);
return v___x_227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg___boxed(lean_object* v_e_231_, lean_object* v___y_232_, lean_object* v___y_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_231_, v___y_232_);
lean_dec(v___y_232_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(lean_object* v_e_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_, lean_object* v___y_239_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_e_235_, v___y_237_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___boxed(lean_object* v_e_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2(v_e_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
return v_res_248_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(lean_object* v_x_249_, lean_object* v_x_250_, lean_object* v_x_251_, lean_object* v_x_252_){
_start:
{
lean_object* v_ks_253_; lean_object* v_vs_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_278_; 
v_ks_253_ = lean_ctor_get(v_x_249_, 0);
v_vs_254_ = lean_ctor_get(v_x_249_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_x_249_);
if (v_isSharedCheck_278_ == 0)
{
v___x_256_ = v_x_249_;
v_isShared_257_ = v_isSharedCheck_278_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_vs_254_);
lean_inc(v_ks_253_);
lean_dec(v_x_249_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_278_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; uint8_t v___x_259_; 
v___x_258_ = lean_array_get_size(v_ks_253_);
v___x_259_ = lean_nat_dec_lt(v_x_250_, v___x_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_263_; 
lean_dec(v_x_250_);
v___x_260_ = lean_array_push(v_ks_253_, v_x_251_);
v___x_261_ = lean_array_push(v_vs_254_, v_x_252_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_261_);
lean_ctor_set(v___x_256_, 0, v___x_260_);
v___x_263_ = v___x_256_;
goto v_reusejp_262_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v___x_261_);
v___x_263_ = v_reuseFailAlloc_264_;
goto v_reusejp_262_;
}
v_reusejp_262_:
{
return v___x_263_;
}
}
else
{
lean_object* v_k_x27_265_; uint8_t v___x_266_; 
v_k_x27_265_ = lean_array_fget_borrowed(v_ks_253_, v_x_250_);
v___x_266_ = l_Lean_instBEqMVarId_beq(v_x_251_, v_k_x27_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_268_; 
if (v_isShared_257_ == 0)
{
v___x_268_ = v___x_256_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_ks_253_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_vs_254_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_269_; lean_object* v___x_270_; 
v___x_269_ = lean_unsigned_to_nat(1u);
v___x_270_ = lean_nat_add(v_x_250_, v___x_269_);
lean_dec(v_x_250_);
v_x_249_ = v___x_268_;
v_x_250_ = v___x_270_;
goto _start;
}
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_276_; 
v___x_273_ = lean_array_fset(v_ks_253_, v_x_250_, v_x_251_);
v___x_274_ = lean_array_fset(v_vs_254_, v_x_250_, v_x_252_);
lean_dec(v_x_250_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_274_);
lean_ctor_set(v___x_256_, 0, v___x_273_);
v___x_276_ = v___x_256_;
goto v_reusejp_275_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_273_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_274_);
v___x_276_ = v_reuseFailAlloc_277_;
goto v_reusejp_275_;
}
v_reusejp_275_:
{
return v___x_276_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_n_279_, lean_object* v_k_280_, lean_object* v_v_281_){
_start:
{
lean_object* v___x_282_; lean_object* v___x_283_; 
v___x_282_ = lean_unsigned_to_nat(0u);
v___x_283_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_279_, v___x_282_, v_k_280_, v_v_281_);
return v___x_283_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0(void){
_start:
{
size_t v___x_284_; size_t v___x_285_; size_t v___x_286_; 
v___x_284_ = ((size_t)5ULL);
v___x_285_ = ((size_t)1ULL);
v___x_286_ = lean_usize_shift_left(v___x_285_, v___x_284_);
return v___x_286_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1(void){
_start:
{
size_t v___x_287_; size_t v___x_288_; size_t v___x_289_; 
v___x_287_ = ((size_t)1ULL);
v___x_288_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__0);
v___x_289_ = lean_usize_sub(v___x_288_, v___x_287_);
return v___x_289_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(lean_object* v_x_291_, size_t v_x_292_, size_t v_x_293_, lean_object* v_x_294_, lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_291_) == 0)
{
lean_object* v_es_296_; size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; size_t v___x_300_; lean_object* v_j_301_; lean_object* v___x_302_; uint8_t v___x_303_; 
v_es_296_ = lean_ctor_get(v_x_291_, 0);
v___x_297_ = ((size_t)5ULL);
v___x_298_ = ((size_t)1ULL);
v___x_299_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__1);
v___x_300_ = lean_usize_land(v_x_292_, v___x_299_);
v_j_301_ = lean_usize_to_nat(v___x_300_);
v___x_302_ = lean_array_get_size(v_es_296_);
v___x_303_ = lean_nat_dec_lt(v_j_301_, v___x_302_);
if (v___x_303_ == 0)
{
lean_dec(v_j_301_);
lean_dec(v_x_295_);
lean_dec(v_x_294_);
return v_x_291_;
}
else
{
lean_object* v___x_305_; uint8_t v_isShared_306_; uint8_t v_isSharedCheck_340_; 
lean_inc_ref(v_es_296_);
v_isSharedCheck_340_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_340_ == 0)
{
lean_object* v_unused_341_; 
v_unused_341_ = lean_ctor_get(v_x_291_, 0);
lean_dec(v_unused_341_);
v___x_305_ = v_x_291_;
v_isShared_306_ = v_isSharedCheck_340_;
goto v_resetjp_304_;
}
else
{
lean_dec(v_x_291_);
v___x_305_ = lean_box(0);
v_isShared_306_ = v_isSharedCheck_340_;
goto v_resetjp_304_;
}
v_resetjp_304_:
{
lean_object* v_v_307_; lean_object* v___x_308_; lean_object* v_xs_x27_309_; lean_object* v___y_311_; 
v_v_307_ = lean_array_fget(v_es_296_, v_j_301_);
v___x_308_ = lean_box(0);
v_xs_x27_309_ = lean_array_fset(v_es_296_, v_j_301_, v___x_308_);
switch(lean_obj_tag(v_v_307_))
{
case 0:
{
lean_object* v_key_316_; lean_object* v_val_317_; lean_object* v___x_319_; uint8_t v_isShared_320_; uint8_t v_isSharedCheck_327_; 
v_key_316_ = lean_ctor_get(v_v_307_, 0);
v_val_317_ = lean_ctor_get(v_v_307_, 1);
v_isSharedCheck_327_ = !lean_is_exclusive(v_v_307_);
if (v_isSharedCheck_327_ == 0)
{
v___x_319_ = v_v_307_;
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
else
{
lean_inc(v_val_317_);
lean_inc(v_key_316_);
lean_dec(v_v_307_);
v___x_319_ = lean_box(0);
v_isShared_320_ = v_isSharedCheck_327_;
goto v_resetjp_318_;
}
v_resetjp_318_:
{
uint8_t v___x_321_; 
v___x_321_ = l_Lean_instBEqMVarId_beq(v_x_294_, v_key_316_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_del_object(v___x_319_);
v___x_322_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_316_, v_val_317_, v_x_294_, v_x_295_);
v___x_323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___y_311_ = v___x_323_;
goto v___jp_310_;
}
else
{
lean_object* v___x_325_; 
lean_dec(v_val_317_);
lean_dec(v_key_316_);
if (v_isShared_320_ == 0)
{
lean_ctor_set(v___x_319_, 1, v_x_295_);
lean_ctor_set(v___x_319_, 0, v_x_294_);
v___x_325_ = v___x_319_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_326_; 
v_reuseFailAlloc_326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_326_, 0, v_x_294_);
lean_ctor_set(v_reuseFailAlloc_326_, 1, v_x_295_);
v___x_325_ = v_reuseFailAlloc_326_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
v___y_311_ = v___x_325_;
goto v___jp_310_;
}
}
}
}
case 1:
{
lean_object* v_node_328_; lean_object* v___x_330_; uint8_t v_isShared_331_; uint8_t v_isSharedCheck_338_; 
v_node_328_ = lean_ctor_get(v_v_307_, 0);
v_isSharedCheck_338_ = !lean_is_exclusive(v_v_307_);
if (v_isSharedCheck_338_ == 0)
{
v___x_330_ = v_v_307_;
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
else
{
lean_inc(v_node_328_);
lean_dec(v_v_307_);
v___x_330_ = lean_box(0);
v_isShared_331_ = v_isSharedCheck_338_;
goto v_resetjp_329_;
}
v_resetjp_329_:
{
size_t v___x_332_; size_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_336_; 
v___x_332_ = lean_usize_shift_right(v_x_292_, v___x_297_);
v___x_333_ = lean_usize_add(v_x_293_, v___x_298_);
v___x_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_node_328_, v___x_332_, v___x_333_, v_x_294_, v_x_295_);
if (v_isShared_331_ == 0)
{
lean_ctor_set(v___x_330_, 0, v___x_334_);
v___x_336_ = v___x_330_;
goto v_reusejp_335_;
}
else
{
lean_object* v_reuseFailAlloc_337_; 
v_reuseFailAlloc_337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_337_, 0, v___x_334_);
v___x_336_ = v_reuseFailAlloc_337_;
goto v_reusejp_335_;
}
v_reusejp_335_:
{
v___y_311_ = v___x_336_;
goto v___jp_310_;
}
}
}
default: 
{
lean_object* v___x_339_; 
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v_x_294_);
lean_ctor_set(v___x_339_, 1, v_x_295_);
v___y_311_ = v___x_339_;
goto v___jp_310_;
}
}
v___jp_310_:
{
lean_object* v___x_312_; lean_object* v___x_314_; 
v___x_312_ = lean_array_fset(v_xs_x27_309_, v_j_301_, v___y_311_);
lean_dec(v_j_301_);
if (v_isShared_306_ == 0)
{
lean_ctor_set(v___x_305_, 0, v___x_312_);
v___x_314_ = v___x_305_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v___x_312_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
else
{
lean_object* v_ks_342_; lean_object* v_vs_343_; lean_object* v___x_345_; uint8_t v_isShared_346_; uint8_t v_isSharedCheck_363_; 
v_ks_342_ = lean_ctor_get(v_x_291_, 0);
v_vs_343_ = lean_ctor_get(v_x_291_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_291_);
if (v_isSharedCheck_363_ == 0)
{
v___x_345_ = v_x_291_;
v_isShared_346_ = v_isSharedCheck_363_;
goto v_resetjp_344_;
}
else
{
lean_inc(v_vs_343_);
lean_inc(v_ks_342_);
lean_dec(v_x_291_);
v___x_345_ = lean_box(0);
v_isShared_346_ = v_isSharedCheck_363_;
goto v_resetjp_344_;
}
v_resetjp_344_:
{
lean_object* v___x_348_; 
if (v_isShared_346_ == 0)
{
v___x_348_ = v___x_345_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_ks_342_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v_vs_343_);
v___x_348_ = v_reuseFailAlloc_362_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
lean_object* v_newNode_349_; uint8_t v___y_351_; size_t v___x_357_; uint8_t v___x_358_; 
v_newNode_349_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v___x_348_, v_x_294_, v_x_295_);
v___x_357_ = ((size_t)7ULL);
v___x_358_ = lean_usize_dec_le(v___x_357_, v_x_293_);
if (v___x_358_ == 0)
{
lean_object* v___x_359_; lean_object* v___x_360_; uint8_t v___x_361_; 
v___x_359_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_349_);
v___x_360_ = lean_unsigned_to_nat(4u);
v___x_361_ = lean_nat_dec_lt(v___x_359_, v___x_360_);
lean_dec(v___x_359_);
v___y_351_ = v___x_361_;
goto v___jp_350_;
}
else
{
v___y_351_ = v___x_358_;
goto v___jp_350_;
}
v___jp_350_:
{
if (v___y_351_ == 0)
{
lean_object* v_ks_352_; lean_object* v_vs_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_ks_352_ = lean_ctor_get(v_newNode_349_, 0);
lean_inc_ref(v_ks_352_);
v_vs_353_ = lean_ctor_get(v_newNode_349_, 1);
lean_inc_ref(v_vs_353_);
lean_dec_ref(v_newNode_349_);
v___x_354_ = lean_unsigned_to_nat(0u);
v___x_355_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___closed__2);
v___x_356_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_x_293_, v_ks_352_, v_vs_353_, v___x_354_, v___x_355_);
lean_dec_ref(v_vs_353_);
lean_dec_ref(v_ks_352_);
return v___x_356_;
}
else
{
return v_newNode_349_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(size_t v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
v___x_369_ = lean_array_get_size(v_keys_365_);
v___x_370_ = lean_nat_dec_lt(v_i_367_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v_i_367_);
return v_entries_368_;
}
else
{
lean_object* v_k_371_; lean_object* v_v_372_; uint64_t v___x_373_; size_t v_h_374_; size_t v___x_375_; lean_object* v___x_376_; size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v_h_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
v_k_371_ = lean_array_fget_borrowed(v_keys_365_, v_i_367_);
v_v_372_ = lean_array_fget_borrowed(v_vals_366_, v_i_367_);
v___x_373_ = l_Lean_instHashableMVarId_hash(v_k_371_);
v_h_374_ = lean_uint64_to_usize(v___x_373_);
v___x_375_ = ((size_t)5ULL);
v___x_376_ = lean_unsigned_to_nat(1u);
v___x_377_ = ((size_t)1ULL);
v___x_378_ = lean_usize_sub(v_depth_364_, v___x_377_);
v___x_379_ = lean_usize_mul(v___x_375_, v___x_378_);
v_h_380_ = lean_usize_shift_right(v_h_374_, v___x_379_);
v___x_381_ = lean_nat_add(v_i_367_, v___x_376_);
lean_dec(v_i_367_);
lean_inc(v_v_372_);
lean_inc(v_k_371_);
v___x_382_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_entries_368_, v_h_380_, v_depth_364_, v_k_371_, v_v_372_);
v_i_367_ = v___x_381_;
v_entries_368_ = v___x_382_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg___boxed(lean_object* v_depth_384_, lean_object* v_keys_385_, lean_object* v_vals_386_, lean_object* v_i_387_, lean_object* v_entries_388_){
_start:
{
size_t v_depth_boxed_389_; lean_object* v_res_390_; 
v_depth_boxed_389_ = lean_unbox_usize(v_depth_384_);
lean_dec(v_depth_384_);
v_res_390_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_389_, v_keys_385_, v_vals_386_, v_i_387_, v_entries_388_);
lean_dec_ref(v_vals_386_);
lean_dec_ref(v_keys_385_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_x_391_, lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_, lean_object* v_x_395_){
_start:
{
size_t v_x_2193__boxed_396_; size_t v_x_2194__boxed_397_; lean_object* v_res_398_; 
v_x_2193__boxed_396_ = lean_unbox_usize(v_x_392_);
lean_dec(v_x_392_);
v_x_2194__boxed_397_ = lean_unbox_usize(v_x_393_);
lean_dec(v_x_393_);
v_res_398_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_391_, v_x_2193__boxed_396_, v_x_2194__boxed_397_, v_x_394_, v_x_395_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(lean_object* v_x_399_, lean_object* v_x_400_, lean_object* v_x_401_){
_start:
{
uint64_t v___x_402_; size_t v___x_403_; size_t v___x_404_; lean_object* v___x_405_; 
v___x_402_ = l_Lean_instHashableMVarId_hash(v_x_400_);
v___x_403_ = lean_uint64_to_usize(v___x_402_);
v___x_404_ = ((size_t)1ULL);
v___x_405_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_399_, v___x_403_, v___x_404_, v_x_400_, v_x_401_);
return v___x_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(lean_object* v_mvarId_406_, lean_object* v_val_407_, lean_object* v___y_408_){
_start:
{
lean_object* v___x_410_; lean_object* v_mctx_411_; lean_object* v_cache_412_; lean_object* v_zetaDeltaFVarIds_413_; lean_object* v_postponed_414_; lean_object* v_diag_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_443_; 
v___x_410_ = lean_st_ref_take(v___y_408_);
v_mctx_411_ = lean_ctor_get(v___x_410_, 0);
v_cache_412_ = lean_ctor_get(v___x_410_, 1);
v_zetaDeltaFVarIds_413_ = lean_ctor_get(v___x_410_, 2);
v_postponed_414_ = lean_ctor_get(v___x_410_, 3);
v_diag_415_ = lean_ctor_get(v___x_410_, 4);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_410_);
if (v_isSharedCheck_443_ == 0)
{
v___x_417_ = v___x_410_;
v_isShared_418_ = v_isSharedCheck_443_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_diag_415_);
lean_inc(v_postponed_414_);
lean_inc(v_zetaDeltaFVarIds_413_);
lean_inc(v_cache_412_);
lean_inc(v_mctx_411_);
lean_dec(v___x_410_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_443_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v_depth_419_; lean_object* v_levelAssignDepth_420_; lean_object* v_lmvarCounter_421_; lean_object* v_mvarCounter_422_; lean_object* v_lDecls_423_; lean_object* v_decls_424_; lean_object* v_userNames_425_; lean_object* v_lAssignment_426_; lean_object* v_eAssignment_427_; lean_object* v_dAssignment_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_442_; 
v_depth_419_ = lean_ctor_get(v_mctx_411_, 0);
v_levelAssignDepth_420_ = lean_ctor_get(v_mctx_411_, 1);
v_lmvarCounter_421_ = lean_ctor_get(v_mctx_411_, 2);
v_mvarCounter_422_ = lean_ctor_get(v_mctx_411_, 3);
v_lDecls_423_ = lean_ctor_get(v_mctx_411_, 4);
v_decls_424_ = lean_ctor_get(v_mctx_411_, 5);
v_userNames_425_ = lean_ctor_get(v_mctx_411_, 6);
v_lAssignment_426_ = lean_ctor_get(v_mctx_411_, 7);
v_eAssignment_427_ = lean_ctor_get(v_mctx_411_, 8);
v_dAssignment_428_ = lean_ctor_get(v_mctx_411_, 9);
v_isSharedCheck_442_ = !lean_is_exclusive(v_mctx_411_);
if (v_isSharedCheck_442_ == 0)
{
v___x_430_ = v_mctx_411_;
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_dAssignment_428_);
lean_inc(v_eAssignment_427_);
lean_inc(v_lAssignment_426_);
lean_inc(v_userNames_425_);
lean_inc(v_decls_424_);
lean_inc(v_lDecls_423_);
lean_inc(v_mvarCounter_422_);
lean_inc(v_lmvarCounter_421_);
lean_inc(v_levelAssignDepth_420_);
lean_inc(v_depth_419_);
lean_dec(v_mctx_411_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_442_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
lean_object* v___x_432_; lean_object* v___x_434_; 
v___x_432_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_eAssignment_427_, v_mvarId_406_, v_val_407_);
if (v_isShared_431_ == 0)
{
lean_ctor_set(v___x_430_, 8, v___x_432_);
v___x_434_ = v___x_430_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_depth_419_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v_levelAssignDepth_420_);
lean_ctor_set(v_reuseFailAlloc_441_, 2, v_lmvarCounter_421_);
lean_ctor_set(v_reuseFailAlloc_441_, 3, v_mvarCounter_422_);
lean_ctor_set(v_reuseFailAlloc_441_, 4, v_lDecls_423_);
lean_ctor_set(v_reuseFailAlloc_441_, 5, v_decls_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 6, v_userNames_425_);
lean_ctor_set(v_reuseFailAlloc_441_, 7, v_lAssignment_426_);
lean_ctor_set(v_reuseFailAlloc_441_, 8, v___x_432_);
lean_ctor_set(v_reuseFailAlloc_441_, 9, v_dAssignment_428_);
v___x_434_ = v_reuseFailAlloc_441_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
lean_object* v___x_436_; 
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 0, v___x_434_);
v___x_436_ = v___x_417_;
goto v_reusejp_435_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v___x_434_);
lean_ctor_set(v_reuseFailAlloc_440_, 1, v_cache_412_);
lean_ctor_set(v_reuseFailAlloc_440_, 2, v_zetaDeltaFVarIds_413_);
lean_ctor_set(v_reuseFailAlloc_440_, 3, v_postponed_414_);
lean_ctor_set(v_reuseFailAlloc_440_, 4, v_diag_415_);
v___x_436_ = v_reuseFailAlloc_440_;
goto v_reusejp_435_;
}
v_reusejp_435_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_437_ = lean_st_ref_set(v___y_408_, v___x_436_);
v___x_438_ = lean_box(0);
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v___x_438_);
return v___x_439_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg___boxed(lean_object* v_mvarId_444_, lean_object* v_val_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_444_, v_val_445_, v___y_446_);
lean_dec(v___y_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(lean_object* v_fst_449_, lean_object* v_fst_450_, lean_object* v_args_451_, lean_object* v_range_452_, lean_object* v_b_453_, lean_object* v_i_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_stop_460_; lean_object* v_step_461_; uint8_t v___x_462_; 
v_stop_460_ = lean_ctor_get(v_range_452_, 1);
v_step_461_ = lean_ctor_get(v_range_452_, 2);
v___x_462_ = lean_nat_dec_lt(v_i_454_, v_stop_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec(v_i_454_);
v___x_463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_463_, 0, v_b_453_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; lean_object* v___x_465_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; uint8_t v___x_472_; 
v___x_464_ = 0;
v___x_465_ = lean_box(0);
v___x_469_ = lean_box(v___x_464_);
v___x_470_ = lean_array_get(v___x_469_, v_fst_449_, v_i_454_);
lean_dec(v___x_469_);
v___x_471_ = lean_unbox(v___x_470_);
lean_dec(v___x_470_);
v___x_472_ = l_Lean_BinderInfo_isInstImplicit(v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; 
v___x_473_ = l_Lean_instInhabitedExpr;
v___x_474_ = lean_array_get_borrowed(v___x_473_, v_fst_450_, v_i_454_);
v___x_475_ = l_Lean_Expr_mvarId_x21(v___x_474_);
v___x_476_ = lean_array_get_borrowed(v___x_473_, v_args_451_, v_i_454_);
lean_inc(v___x_476_);
v___x_477_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_475_, v___x_476_, v___y_456_);
lean_dec_ref(v___x_477_);
goto v___jp_466_;
}
else
{
goto v___jp_466_;
}
v___jp_466_:
{
lean_object* v___x_467_; 
v___x_467_ = lean_nat_add(v_i_454_, v_step_461_);
lean_dec(v_i_454_);
v_b_453_ = v___x_465_;
v_i_454_ = v___x_467_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg___boxed(lean_object* v_fst_478_, lean_object* v_fst_479_, lean_object* v_args_480_, lean_object* v_range_481_, lean_object* v_b_482_, lean_object* v_i_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_){
_start:
{
lean_object* v_res_489_; 
v_res_489_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_478_, v_fst_479_, v_args_480_, v_range_481_, v_b_482_, v_i_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
lean_dec_ref(v___y_484_);
lean_dec_ref(v_range_481_);
lean_dec_ref(v_args_480_);
lean_dec_ref(v_fst_479_);
lean_dec_ref(v_fst_478_);
return v_res_489_;
}
}
static lean_object* _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0(void){
_start:
{
lean_object* v___x_490_; lean_object* v_dummy_491_; 
v___x_490_ = lean_box(0);
v_dummy_491_ = l_Lean_Expr_sort___override(v___x_490_);
return v_dummy_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs(lean_object* v_type_492_, lean_object* v_a_493_, lean_object* v_a_494_, lean_object* v_a_495_, lean_object* v_a_496_){
_start:
{
lean_object* v_fn_498_; lean_object* v___x_499_; 
v_fn_498_ = l_Lean_Expr_getAppFn(v_type_492_);
lean_inc(v_a_496_);
lean_inc_ref(v_a_495_);
lean_inc(v_a_494_);
lean_inc_ref(v_a_493_);
lean_inc_ref(v_fn_498_);
v___x_499_ = lean_infer_type(v_fn_498_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; uint8_t v___x_501_; lean_object* v___x_502_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref(v___x_499_);
v___x_501_ = 0;
v___x_502_ = l_Lean_Meta_forallMetaTelescope(v_a_500_, v___x_501_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
if (lean_obj_tag(v___x_502_) == 0)
{
lean_object* v_a_503_; lean_object* v_snd_504_; lean_object* v_fst_505_; lean_object* v_fst_506_; lean_object* v_nargs_507_; lean_object* v_dummy_508_; lean_object* v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v_args_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
v_a_503_ = lean_ctor_get(v___x_502_, 0);
lean_inc(v_a_503_);
lean_dec_ref(v___x_502_);
v_snd_504_ = lean_ctor_get(v_a_503_, 1);
lean_inc(v_snd_504_);
v_fst_505_ = lean_ctor_get(v_a_503_, 0);
lean_inc(v_fst_505_);
lean_dec(v_a_503_);
v_fst_506_ = lean_ctor_get(v_snd_504_, 0);
lean_inc(v_fst_506_);
lean_dec(v_snd_504_);
v_nargs_507_ = l_Lean_Expr_getAppNumArgs(v_type_492_);
v_dummy_508_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
lean_inc(v_nargs_507_);
v___x_509_ = lean_mk_array(v_nargs_507_, v_dummy_508_);
v___x_510_ = lean_unsigned_to_nat(1u);
v___x_511_ = lean_nat_sub(v_nargs_507_, v___x_510_);
lean_dec(v_nargs_507_);
v_args_512_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_type_492_, v___x_509_, v___x_511_);
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = lean_array_get_size(v_fst_505_);
v___x_515_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_515_, 0, v___x_513_);
lean_ctor_set(v___x_515_, 1, v___x_514_);
lean_ctor_set(v___x_515_, 2, v___x_510_);
v___x_516_ = lean_box(0);
v___x_517_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_506_, v_fst_505_, v_args_512_, v___x_515_, v___x_516_, v___x_513_, v_a_493_, v_a_494_, v_a_495_, v_a_496_);
lean_dec_ref(v___x_515_);
lean_dec(v_fst_506_);
lean_dec_ref(v___x_517_);
v___x_518_ = lean_array_get_size(v_args_512_);
v___x_519_ = l_Array_extract___redArg(v_args_512_, v___x_514_, v___x_518_);
lean_dec_ref(v_args_512_);
v___x_520_ = l_Array_append___redArg(v_fst_505_, v___x_519_);
lean_dec_ref(v___x_519_);
v___x_521_ = l_Lean_mkAppN(v_fn_498_, v___x_520_);
lean_dec_ref(v___x_520_);
v___x_522_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v___x_521_, v_a_494_);
return v___x_522_;
}
else
{
lean_object* v_a_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_530_; 
lean_dec_ref(v_fn_498_);
lean_dec_ref(v_type_492_);
v_a_523_ = lean_ctor_get(v___x_502_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v___x_502_);
if (v_isSharedCheck_530_ == 0)
{
v___x_525_ = v___x_502_;
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_a_523_);
lean_dec(v___x_502_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_530_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_528_; 
if (v_isShared_526_ == 0)
{
v___x_528_ = v___x_525_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v_a_523_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
return v___x_528_;
}
}
}
}
else
{
lean_dec_ref(v_fn_498_);
lean_dec_ref(v_type_492_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_abstractInstImplicitArgs___boxed(lean_object* v_type_531_, lean_object* v_a_532_, lean_object* v_a_533_, lean_object* v_a_534_, lean_object* v_a_535_, lean_object* v_a_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Lean_Meta_abstractInstImplicitArgs(v_type_531_, v_a_532_, v_a_533_, v_a_534_, v_a_535_);
lean_dec(v_a_535_);
lean_dec_ref(v_a_534_);
lean_dec(v_a_533_);
lean_dec_ref(v_a_532_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(lean_object* v_mvarId_538_, lean_object* v_val_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v_mvarId_538_, v_val_539_, v___y_541_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___boxed(lean_object* v_mvarId_546_, lean_object* v_val_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v_res_553_; 
v_res_553_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0(v_mvarId_546_, v_val_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec_ref(v___y_548_);
return v_res_553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(lean_object* v_fst_554_, lean_object* v_fst_555_, lean_object* v_args_556_, lean_object* v_range_557_, lean_object* v_b_558_, lean_object* v_i_559_, lean_object* v_hs_560_, lean_object* v_hl_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___redArg(v_fst_554_, v_fst_555_, v_args_556_, v_range_557_, v_b_558_, v_i_559_, v___y_562_, v___y_563_, v___y_564_, v___y_565_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1___boxed(lean_object* v_fst_568_, lean_object* v_fst_569_, lean_object* v_args_570_, lean_object* v_range_571_, lean_object* v_b_572_, lean_object* v_i_573_, lean_object* v_hs_574_, lean_object* v_hl_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Init_Data_Range_Basic_0__Std_Legacy_Range_forIn_x27_loop___at___00Lean_Meta_abstractInstImplicitArgs_spec__1(v_fst_568_, v_fst_569_, v_args_570_, v_range_571_, v_b_572_, v_i_573_, v_hs_574_, v_hl_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_);
lean_dec(v___y_579_);
lean_dec_ref(v___y_578_);
lean_dec(v___y_577_);
lean_dec_ref(v___y_576_);
lean_dec_ref(v_range_571_);
lean_dec_ref(v_args_570_);
lean_dec_ref(v_fst_569_);
lean_dec_ref(v_fst_568_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0(lean_object* v_00_u03b2_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
lean_object* v___x_586_; 
v___x_586_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0___redArg(v_x_583_, v_x_584_, v_x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_587_, lean_object* v_x_588_, size_t v_x_589_, size_t v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
lean_object* v___x_593_; 
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___redArg(v_x_588_, v_x_589_, v_x_590_, v_x_591_, v_x_592_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_594_, lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_, lean_object* v_x_599_){
_start:
{
size_t v_x_2584__boxed_600_; size_t v_x_2585__boxed_601_; lean_object* v_res_602_; 
v_x_2584__boxed_600_ = lean_unbox_usize(v_x_596_);
lean_dec(v_x_596_);
v_x_2585__boxed_601_ = lean_unbox_usize(v_x_597_);
lean_dec(v_x_597_);
v_res_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2(v_00_u03b2_594_, v_x_595_, v_x_2584__boxed_600_, v_x_2585__boxed_601_, v_x_598_, v_x_599_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4(lean_object* v_00_u03b2_603_, lean_object* v_n_604_, lean_object* v_k_605_, lean_object* v_v_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4___redArg(v_n_604_, v_k_605_, v_v_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_608_, size_t v_depth_609_, lean_object* v_keys_610_, lean_object* v_vals_611_, lean_object* v_heq_612_, lean_object* v_i_613_, lean_object* v_entries_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_609_, v_keys_610_, v_vals_611_, v_i_613_, v_entries_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5___boxed(lean_object* v_00_u03b2_616_, lean_object* v_depth_617_, lean_object* v_keys_618_, lean_object* v_vals_619_, lean_object* v_heq_620_, lean_object* v_i_621_, lean_object* v_entries_622_){
_start:
{
size_t v_depth_boxed_623_; lean_object* v_res_624_; 
v_depth_boxed_623_ = lean_unbox_usize(v_depth_617_);
lean_dec(v_depth_617_);
v_res_624_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_616_, v_depth_boxed_623_, v_keys_618_, v_vals_619_, v_heq_620_, v_i_621_, v_entries_622_);
lean_dec_ref(v_vals_619_);
lean_dec_ref(v_keys_618_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_625_, lean_object* v_x_626_, lean_object* v_x_627_, lean_object* v_x_628_, lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_626_, v_x_627_, v_x_628_, v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(lean_object* v_opts_631_, lean_object* v_opt_632_){
_start:
{
lean_object* v_name_633_; lean_object* v_defValue_634_; lean_object* v_map_635_; lean_object* v___x_636_; 
v_name_633_ = lean_ctor_get(v_opt_632_, 0);
v_defValue_634_ = lean_ctor_get(v_opt_632_, 1);
v_map_635_ = lean_ctor_get(v_opts_631_, 0);
v___x_636_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_635_, v_name_633_);
if (lean_obj_tag(v___x_636_) == 0)
{
uint8_t v___x_637_; 
v___x_637_ = lean_unbox(v_defValue_634_);
return v___x_637_;
}
else
{
lean_object* v_val_638_; 
v_val_638_ = lean_ctor_get(v___x_636_, 0);
lean_inc(v_val_638_);
lean_dec_ref(v___x_636_);
if (lean_obj_tag(v_val_638_) == 1)
{
uint8_t v_v_639_; 
v_v_639_ = lean_ctor_get_uint8(v_val_638_, 0);
lean_dec_ref(v_val_638_);
return v_v_639_;
}
else
{
uint8_t v___x_640_; 
lean_dec(v_val_638_);
v___x_640_ = lean_unbox(v_defValue_634_);
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0___boxed(lean_object* v_opts_641_, lean_object* v_opt_642_){
_start:
{
uint8_t v_res_643_; lean_object* v_r_644_; 
v_res_643_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_641_, v_opt_642_);
lean_dec_ref(v_opt_642_);
lean_dec_ref(v_opts_641_);
v_r_644_ = lean_box(v_res_643_);
return v_r_644_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(lean_object* v_kind_645_, lean_object* v___y_646_){
_start:
{
lean_object* v___x_648_; lean_object* v_auxDeclNGen_649_; lean_object* v___x_650_; lean_object* v_env_651_; lean_object* v___x_652_; lean_object* v_fst_653_; lean_object* v_snd_654_; lean_object* v___x_655_; lean_object* v_env_656_; lean_object* v_nextMacroScope_657_; lean_object* v_ngen_658_; lean_object* v_traceState_659_; lean_object* v_cache_660_; lean_object* v_messages_661_; lean_object* v_infoState_662_; lean_object* v_snapshotTasks_663_; lean_object* v___x_665_; uint8_t v_isShared_666_; uint8_t v_isSharedCheck_672_; 
v___x_648_ = lean_st_ref_get(v___y_646_);
v_auxDeclNGen_649_ = lean_ctor_get(v___x_648_, 3);
lean_inc_ref(v_auxDeclNGen_649_);
lean_dec(v___x_648_);
v___x_650_ = lean_st_ref_get(v___y_646_);
v_env_651_ = lean_ctor_get(v___x_650_, 0);
lean_inc_ref(v_env_651_);
lean_dec(v___x_650_);
v___x_652_ = l_Lean_DeclNameGenerator_mkUniqueName(v_env_651_, v_auxDeclNGen_649_, v_kind_645_);
v_fst_653_ = lean_ctor_get(v___x_652_, 0);
lean_inc(v_fst_653_);
v_snd_654_ = lean_ctor_get(v___x_652_, 1);
lean_inc(v_snd_654_);
lean_dec_ref(v___x_652_);
v___x_655_ = lean_st_ref_take(v___y_646_);
v_env_656_ = lean_ctor_get(v___x_655_, 0);
v_nextMacroScope_657_ = lean_ctor_get(v___x_655_, 1);
v_ngen_658_ = lean_ctor_get(v___x_655_, 2);
v_traceState_659_ = lean_ctor_get(v___x_655_, 4);
v_cache_660_ = lean_ctor_get(v___x_655_, 5);
v_messages_661_ = lean_ctor_get(v___x_655_, 6);
v_infoState_662_ = lean_ctor_get(v___x_655_, 7);
v_snapshotTasks_663_ = lean_ctor_get(v___x_655_, 8);
v_isSharedCheck_672_ = !lean_is_exclusive(v___x_655_);
if (v_isSharedCheck_672_ == 0)
{
lean_object* v_unused_673_; 
v_unused_673_ = lean_ctor_get(v___x_655_, 3);
lean_dec(v_unused_673_);
v___x_665_ = v___x_655_;
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
else
{
lean_inc(v_snapshotTasks_663_);
lean_inc(v_infoState_662_);
lean_inc(v_messages_661_);
lean_inc(v_cache_660_);
lean_inc(v_traceState_659_);
lean_inc(v_ngen_658_);
lean_inc(v_nextMacroScope_657_);
lean_inc(v_env_656_);
lean_dec(v___x_655_);
v___x_665_ = lean_box(0);
v_isShared_666_ = v_isSharedCheck_672_;
goto v_resetjp_664_;
}
v_resetjp_664_:
{
lean_object* v___x_668_; 
if (v_isShared_666_ == 0)
{
lean_ctor_set(v___x_665_, 3, v_snd_654_);
v___x_668_ = v___x_665_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_671_; 
v_reuseFailAlloc_671_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_671_, 0, v_env_656_);
lean_ctor_set(v_reuseFailAlloc_671_, 1, v_nextMacroScope_657_);
lean_ctor_set(v_reuseFailAlloc_671_, 2, v_ngen_658_);
lean_ctor_set(v_reuseFailAlloc_671_, 3, v_snd_654_);
lean_ctor_set(v_reuseFailAlloc_671_, 4, v_traceState_659_);
lean_ctor_set(v_reuseFailAlloc_671_, 5, v_cache_660_);
lean_ctor_set(v_reuseFailAlloc_671_, 6, v_messages_661_);
lean_ctor_set(v_reuseFailAlloc_671_, 7, v_infoState_662_);
lean_ctor_set(v_reuseFailAlloc_671_, 8, v_snapshotTasks_663_);
v___x_668_ = v_reuseFailAlloc_671_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
lean_object* v___x_669_; lean_object* v___x_670_; 
v___x_669_ = lean_st_ref_set(v___y_646_, v___x_668_);
v___x_670_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_670_, 0, v_fst_653_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg___boxed(lean_object* v_kind_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_674_, v___y_675_);
lean_dec(v___y_675_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(lean_object* v_kind_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v_kind_678_, v___y_682_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___boxed(lean_object* v_kind_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1(v_kind_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
return v_res_691_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_692_; 
v___x_692_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_692_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__0);
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
return v___x_694_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_695_; lean_object* v___x_696_; 
v___x_695_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_696_, 0, v___x_695_);
lean_ctor_set(v___x_696_, 1, v___x_695_);
return v___x_696_;
}
}
static lean_object* _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__1);
v___x_698_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_698_, 0, v___x_697_);
lean_ctor_set(v___x_698_, 1, v___x_697_);
lean_ctor_set(v___x_698_, 2, v___x_697_);
lean_ctor_set(v___x_698_, 3, v___x_697_);
lean_ctor_set(v___x_698_, 4, v___x_697_);
lean_ctor_set(v___x_698_, 5, v___x_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(lean_object* v_declName_699_, uint8_t v_s_700_, lean_object* v___y_701_, lean_object* v___y_702_){
_start:
{
lean_object* v___x_704_; lean_object* v_env_705_; lean_object* v_nextMacroScope_706_; lean_object* v_ngen_707_; lean_object* v_auxDeclNGen_708_; lean_object* v_traceState_709_; lean_object* v_messages_710_; lean_object* v_infoState_711_; lean_object* v_snapshotTasks_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_741_; 
v___x_704_ = lean_st_ref_take(v___y_702_);
v_env_705_ = lean_ctor_get(v___x_704_, 0);
v_nextMacroScope_706_ = lean_ctor_get(v___x_704_, 1);
v_ngen_707_ = lean_ctor_get(v___x_704_, 2);
v_auxDeclNGen_708_ = lean_ctor_get(v___x_704_, 3);
v_traceState_709_ = lean_ctor_get(v___x_704_, 4);
v_messages_710_ = lean_ctor_get(v___x_704_, 6);
v_infoState_711_ = lean_ctor_get(v___x_704_, 7);
v_snapshotTasks_712_ = lean_ctor_get(v___x_704_, 8);
v_isSharedCheck_741_ = !lean_is_exclusive(v___x_704_);
if (v_isSharedCheck_741_ == 0)
{
lean_object* v_unused_742_; 
v_unused_742_ = lean_ctor_get(v___x_704_, 5);
lean_dec(v_unused_742_);
v___x_714_ = v___x_704_;
v_isShared_715_ = v_isSharedCheck_741_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snapshotTasks_712_);
lean_inc(v_infoState_711_);
lean_inc(v_messages_710_);
lean_inc(v_traceState_709_);
lean_inc(v_auxDeclNGen_708_);
lean_inc(v_ngen_707_);
lean_inc(v_nextMacroScope_706_);
lean_inc(v_env_705_);
lean_dec(v___x_704_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_741_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_721_; 
v___x_716_ = 0;
v___x_717_ = lean_box(0);
v___x_718_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_705_, v_declName_699_, v_s_700_, v___x_716_, v___x_717_);
v___x_719_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 5, v___x_719_);
lean_ctor_set(v___x_714_, 0, v___x_718_);
v___x_721_ = v___x_714_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_740_; 
v_reuseFailAlloc_740_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_740_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_740_, 1, v_nextMacroScope_706_);
lean_ctor_set(v_reuseFailAlloc_740_, 2, v_ngen_707_);
lean_ctor_set(v_reuseFailAlloc_740_, 3, v_auxDeclNGen_708_);
lean_ctor_set(v_reuseFailAlloc_740_, 4, v_traceState_709_);
lean_ctor_set(v_reuseFailAlloc_740_, 5, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_740_, 6, v_messages_710_);
lean_ctor_set(v_reuseFailAlloc_740_, 7, v_infoState_711_);
lean_ctor_set(v_reuseFailAlloc_740_, 8, v_snapshotTasks_712_);
v___x_721_ = v_reuseFailAlloc_740_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_mctx_724_; lean_object* v_zetaDeltaFVarIds_725_; lean_object* v_postponed_726_; lean_object* v_diag_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_738_; 
v___x_722_ = lean_st_ref_set(v___y_702_, v___x_721_);
v___x_723_ = lean_st_ref_take(v___y_701_);
v_mctx_724_ = lean_ctor_get(v___x_723_, 0);
v_zetaDeltaFVarIds_725_ = lean_ctor_get(v___x_723_, 2);
v_postponed_726_ = lean_ctor_get(v___x_723_, 3);
v_diag_727_ = lean_ctor_get(v___x_723_, 4);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_723_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v___x_723_, 1);
lean_dec(v_unused_739_);
v___x_729_ = v___x_723_;
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_diag_727_);
lean_inc(v_postponed_726_);
lean_inc(v_zetaDeltaFVarIds_725_);
lean_inc(v_mctx_724_);
lean_dec(v___x_723_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_738_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_731_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_730_ == 0)
{
lean_ctor_set(v___x_729_, 1, v___x_731_);
v___x_733_ = v___x_729_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_mctx_724_);
lean_ctor_set(v_reuseFailAlloc_737_, 1, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_737_, 2, v_zetaDeltaFVarIds_725_);
lean_ctor_set(v_reuseFailAlloc_737_, 3, v_postponed_726_);
lean_ctor_set(v_reuseFailAlloc_737_, 4, v_diag_727_);
v___x_733_ = v_reuseFailAlloc_737_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_734_ = lean_st_ref_set(v___y_701_, v___x_733_);
v___x_735_ = lean_box(0);
v___x_736_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_736_, 0, v___x_735_);
return v___x_736_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___boxed(lean_object* v_declName_743_, lean_object* v_s_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
uint8_t v_s_boxed_748_; lean_object* v_res_749_; 
v_s_boxed_748_ = lean_unbox(v_s_744_);
v_res_749_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_743_, v_s_boxed_748_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec(v___y_745_);
return v_res_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(lean_object* v_declName_750_, uint8_t v_s_751_, lean_object* v___y_752_, lean_object* v___y_753_, lean_object* v___y_754_, lean_object* v___y_755_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_declName_750_, v_s_751_, v___y_753_, v___y_755_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___boxed(lean_object* v_declName_758_, lean_object* v_s_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_){
_start:
{
uint8_t v_s_boxed_765_; lean_object* v_res_766_; 
v_s_boxed_765_ = lean_unbox(v_s_759_);
v_res_766_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2(v_declName_758_, v_s_boxed_765_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
lean_dec(v___y_763_);
lean_dec_ref(v___y_762_);
lean_dec(v___y_761_);
lean_dec_ref(v___y_760_);
return v_res_766_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_unsigned_to_nat(32u);
v___x_768_ = lean_mk_empty_array_with_capacity(v___x_767_);
v___x_769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_769_, 0, v___x_768_);
return v___x_769_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1(void){
_start:
{
size_t v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_770_ = ((size_t)5ULL);
v___x_771_ = lean_unsigned_to_nat(0u);
v___x_772_ = lean_unsigned_to_nat(32u);
v___x_773_ = lean_mk_empty_array_with_capacity(v___x_772_);
v___x_774_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__0);
v___x_775_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_775_, 0, v___x_774_);
lean_ctor_set(v___x_775_, 1, v___x_773_);
lean_ctor_set(v___x_775_, 2, v___x_771_);
lean_ctor_set(v___x_775_, 3, v___x_771_);
lean_ctor_set_usize(v___x_775_, 4, v___x_770_);
return v___x_775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(lean_object* v___y_776_){
_start:
{
lean_object* v___x_778_; lean_object* v_traceState_779_; lean_object* v_traces_780_; lean_object* v___x_781_; lean_object* v_traceState_782_; lean_object* v_env_783_; lean_object* v_nextMacroScope_784_; lean_object* v_ngen_785_; lean_object* v_auxDeclNGen_786_; lean_object* v_cache_787_; lean_object* v_messages_788_; lean_object* v_infoState_789_; lean_object* v_snapshotTasks_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_809_; 
v___x_778_ = lean_st_ref_get(v___y_776_);
v_traceState_779_ = lean_ctor_get(v___x_778_, 4);
lean_inc_ref(v_traceState_779_);
lean_dec(v___x_778_);
v_traces_780_ = lean_ctor_get(v_traceState_779_, 0);
lean_inc_ref(v_traces_780_);
lean_dec_ref(v_traceState_779_);
v___x_781_ = lean_st_ref_take(v___y_776_);
v_traceState_782_ = lean_ctor_get(v___x_781_, 4);
v_env_783_ = lean_ctor_get(v___x_781_, 0);
v_nextMacroScope_784_ = lean_ctor_get(v___x_781_, 1);
v_ngen_785_ = lean_ctor_get(v___x_781_, 2);
v_auxDeclNGen_786_ = lean_ctor_get(v___x_781_, 3);
v_cache_787_ = lean_ctor_get(v___x_781_, 5);
v_messages_788_ = lean_ctor_get(v___x_781_, 6);
v_infoState_789_ = lean_ctor_get(v___x_781_, 7);
v_snapshotTasks_790_ = lean_ctor_get(v___x_781_, 8);
v_isSharedCheck_809_ = !lean_is_exclusive(v___x_781_);
if (v_isSharedCheck_809_ == 0)
{
v___x_792_ = v___x_781_;
v_isShared_793_ = v_isSharedCheck_809_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_snapshotTasks_790_);
lean_inc(v_infoState_789_);
lean_inc(v_messages_788_);
lean_inc(v_cache_787_);
lean_inc(v_traceState_782_);
lean_inc(v_auxDeclNGen_786_);
lean_inc(v_ngen_785_);
lean_inc(v_nextMacroScope_784_);
lean_inc(v_env_783_);
lean_dec(v___x_781_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_809_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
uint64_t v_tid_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_807_; 
v_tid_794_ = lean_ctor_get_uint64(v_traceState_782_, sizeof(void*)*1);
v_isSharedCheck_807_ = !lean_is_exclusive(v_traceState_782_);
if (v_isSharedCheck_807_ == 0)
{
lean_object* v_unused_808_; 
v_unused_808_ = lean_ctor_get(v_traceState_782_, 0);
lean_dec(v_unused_808_);
v___x_796_ = v_traceState_782_;
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
else
{
lean_dec(v_traceState_782_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1, &l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___closed__1);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_806_; 
v_reuseFailAlloc_806_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_798_);
lean_ctor_set_uint64(v_reuseFailAlloc_806_, sizeof(void*)*1, v_tid_794_);
v___x_800_ = v_reuseFailAlloc_806_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
lean_object* v___x_802_; 
if (v_isShared_793_ == 0)
{
lean_ctor_set(v___x_792_, 4, v___x_800_);
v___x_802_ = v___x_792_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_env_783_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v_nextMacroScope_784_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_ngen_785_);
lean_ctor_set(v_reuseFailAlloc_805_, 3, v_auxDeclNGen_786_);
lean_ctor_set(v_reuseFailAlloc_805_, 4, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 5, v_cache_787_);
lean_ctor_set(v_reuseFailAlloc_805_, 6, v_messages_788_);
lean_ctor_set(v_reuseFailAlloc_805_, 7, v_infoState_789_);
lean_ctor_set(v_reuseFailAlloc_805_, 8, v_snapshotTasks_790_);
v___x_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_st_ref_set(v___y_776_, v___x_802_);
v___x_804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_804_, 0, v_traces_780_);
return v___x_804_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg___boxed(lean_object* v___y_810_, lean_object* v___y_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_810_);
lean_dec(v___y_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___boxed(lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_){
_start:
{
lean_object* v_res_824_; 
v_res_824_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10(v___y_819_, v___y_820_, v___y_821_, v___y_822_);
lean_dec(v___y_822_);
lean_dec_ref(v___y_821_);
lean_dec(v___y_820_);
lean_dec_ref(v___y_819_);
return v_res_824_;
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; 
v___x_826_ = ((lean_object*)(l_Lean_Meta_wrapInstance___lam__0___closed__0));
v___x_827_ = l_Lean_stringToMessageData(v___x_826_);
return v___x_827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0(lean_object* v_expectedType_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_){
_start:
{
lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; 
v___x_835_ = lean_obj_once(&l_Lean_Meta_wrapInstance___lam__0___closed__1, &l_Lean_Meta_wrapInstance___lam__0___closed__1_once, _init_l_Lean_Meta_wrapInstance___lam__0___closed__1);
v___x_836_ = l_Lean_MessageData_ofExpr(v_expectedType_828_);
v___x_837_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_837_, 0, v___x_835_);
lean_ctor_set(v___x_837_, 1, v___x_836_);
v___x_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_838_, 0, v___x_837_);
return v___x_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__0___boxed(lean_object* v_expectedType_839_, lean_object* v_x_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l_Lean_Meta_wrapInstance___lam__0(v_expectedType_839_, v_x_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec_ref(v_x_840_);
return v_res_846_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0(void){
_start:
{
lean_object* v___x_847_; 
v___x_847_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_847_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_848_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__0);
v___x_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_849_, 0, v___x_848_);
return v___x_849_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2(void){
_start:
{
lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v___x_850_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1);
v___x_851_ = lean_unsigned_to_nat(0u);
v___x_852_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_852_, 0, v___x_851_);
lean_ctor_set(v___x_852_, 1, v___x_851_);
lean_ctor_set(v___x_852_, 2, v___x_851_);
lean_ctor_set(v___x_852_, 3, v___x_851_);
lean_ctor_set(v___x_852_, 4, v___x_850_);
lean_ctor_set(v___x_852_, 5, v___x_850_);
lean_ctor_set(v___x_852_, 6, v___x_850_);
lean_ctor_set(v___x_852_, 7, v___x_850_);
lean_ctor_set(v___x_852_, 8, v___x_850_);
lean_ctor_set(v___x_852_, 9, v___x_850_);
return v___x_852_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3(void){
_start:
{
lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_853_ = lean_unsigned_to_nat(32u);
v___x_854_ = lean_mk_empty_array_with_capacity(v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
return v___x_855_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4(void){
_start:
{
size_t v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_856_ = ((size_t)5ULL);
v___x_857_ = lean_unsigned_to_nat(0u);
v___x_858_ = lean_unsigned_to_nat(32u);
v___x_859_ = lean_mk_empty_array_with_capacity(v___x_858_);
v___x_860_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__3);
v___x_861_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v___x_859_);
lean_ctor_set(v___x_861_, 2, v___x_857_);
lean_ctor_set(v___x_861_, 3, v___x_857_);
lean_ctor_set_usize(v___x_861_, 4, v___x_856_);
return v___x_861_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5(void){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; 
v___x_862_ = lean_box(1);
v___x_863_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__4);
v___x_864_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__1);
v___x_865_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_865_, 0, v___x_864_);
lean_ctor_set(v___x_865_, 1, v___x_863_);
lean_ctor_set(v___x_865_, 2, v___x_862_);
return v___x_865_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7(void){
_start:
{
lean_object* v___x_867_; lean_object* v___x_868_; 
v___x_867_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__6));
v___x_868_ = l_Lean_stringToMessageData(v___x_867_);
return v___x_868_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9(void){
_start:
{
lean_object* v___x_870_; lean_object* v___x_871_; 
v___x_870_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__8));
v___x_871_ = l_Lean_stringToMessageData(v___x_870_);
return v___x_871_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11(void){
_start:
{
lean_object* v___x_873_; lean_object* v___x_874_; 
v___x_873_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__10));
v___x_874_ = l_Lean_stringToMessageData(v___x_873_);
return v___x_874_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13(void){
_start:
{
lean_object* v___x_876_; lean_object* v___x_877_; 
v___x_876_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__12));
v___x_877_ = l_Lean_stringToMessageData(v___x_876_);
return v___x_877_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__14));
v___x_880_ = l_Lean_stringToMessageData(v___x_879_);
return v___x_880_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__16));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19(void){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__18));
v___x_886_ = l_Lean_stringToMessageData(v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(lean_object* v_msg_887_, lean_object* v_declHint_888_, lean_object* v___y_889_){
_start:
{
lean_object* v___x_891_; lean_object* v_env_892_; uint8_t v___x_893_; 
v___x_891_ = lean_st_ref_get(v___y_889_);
v_env_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc_ref(v_env_892_);
lean_dec(v___x_891_);
v___x_893_ = l_Lean_Name_isAnonymous(v_declHint_888_);
if (v___x_893_ == 0)
{
uint8_t v_isExporting_894_; 
v_isExporting_894_ = lean_ctor_get_uint8(v_env_892_, sizeof(void*)*8);
if (v_isExporting_894_ == 0)
{
lean_object* v___x_895_; 
lean_dec_ref(v_env_892_);
lean_dec(v_declHint_888_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v_msg_887_);
return v___x_895_;
}
else
{
lean_object* v___x_896_; uint8_t v___x_897_; 
lean_inc_ref(v_env_892_);
v___x_896_ = l_Lean_Environment_setExporting(v_env_892_, v___x_893_);
lean_inc(v_declHint_888_);
lean_inc_ref(v___x_896_);
v___x_897_ = l_Lean_Environment_contains(v___x_896_, v_declHint_888_, v_isExporting_894_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; 
lean_dec_ref(v___x_896_);
lean_dec_ref(v_env_892_);
lean_dec(v_declHint_888_);
v___x_898_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_898_, 0, v_msg_887_);
return v___x_898_;
}
else
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v_c_904_; lean_object* v___x_905_; 
v___x_899_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__2);
v___x_900_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__5);
v___x_901_ = l_Lean_Options_empty;
v___x_902_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_902_, 0, v___x_896_);
lean_ctor_set(v___x_902_, 1, v___x_899_);
lean_ctor_set(v___x_902_, 2, v___x_900_);
lean_ctor_set(v___x_902_, 3, v___x_901_);
lean_inc(v_declHint_888_);
v___x_903_ = l_Lean_MessageData_ofConstName(v_declHint_888_, v___x_893_);
v_c_904_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_904_, 0, v___x_902_);
lean_ctor_set(v_c_904_, 1, v___x_903_);
v___x_905_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_892_, v_declHint_888_);
if (lean_obj_tag(v___x_905_) == 0)
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v_env_892_);
lean_dec(v_declHint_888_);
v___x_906_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7);
v___x_907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_906_);
lean_ctor_set(v___x_907_, 1, v_c_904_);
v___x_908_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__9);
v___x_909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_907_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
v___x_910_ = l_Lean_MessageData_note(v___x_909_);
v___x_911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_911_, 0, v_msg_887_);
lean_ctor_set(v___x_911_, 1, v___x_910_);
v___x_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_912_, 0, v___x_911_);
return v___x_912_;
}
else
{
lean_object* v_val_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_948_; 
v_val_913_ = lean_ctor_get(v___x_905_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_905_);
if (v_isSharedCheck_948_ == 0)
{
v___x_915_ = v___x_905_;
v_isShared_916_ = v_isSharedCheck_948_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_val_913_);
lean_dec(v___x_905_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_948_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v_mod_920_; uint8_t v___x_921_; 
v___x_917_ = lean_box(0);
v___x_918_ = l_Lean_Environment_header(v_env_892_);
lean_dec_ref(v_env_892_);
v___x_919_ = l_Lean_EnvironmentHeader_moduleNames(v___x_918_);
v_mod_920_ = lean_array_get(v___x_917_, v___x_919_, v_val_913_);
lean_dec(v_val_913_);
lean_dec_ref(v___x_919_);
v___x_921_ = l_Lean_isPrivateName(v_declHint_888_);
lean_dec(v_declHint_888_);
if (v___x_921_ == 0)
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_933_; 
v___x_922_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__11);
v___x_923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_922_);
lean_ctor_set(v___x_923_, 1, v_c_904_);
v___x_924_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__13);
v___x_925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_925_, 0, v___x_923_);
lean_ctor_set(v___x_925_, 1, v___x_924_);
v___x_926_ = l_Lean_MessageData_ofName(v_mod_920_);
v___x_927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_927_, 0, v___x_925_);
lean_ctor_set(v___x_927_, 1, v___x_926_);
v___x_928_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__15);
v___x_929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_929_, 0, v___x_927_);
lean_ctor_set(v___x_929_, 1, v___x_928_);
v___x_930_ = l_Lean_MessageData_note(v___x_929_);
v___x_931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_931_, 0, v_msg_887_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 0);
lean_ctor_set(v___x_915_, 0, v___x_931_);
v___x_933_ = v___x_915_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v___x_931_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_946_; 
v___x_935_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__7);
v___x_936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_936_, 0, v___x_935_);
lean_ctor_set(v___x_936_, 1, v_c_904_);
v___x_937_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__17);
v___x_938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_938_, 0, v___x_936_);
lean_ctor_set(v___x_938_, 1, v___x_937_);
v___x_939_ = l_Lean_MessageData_ofName(v_mod_920_);
v___x_940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_938_);
lean_ctor_set(v___x_940_, 1, v___x_939_);
v___x_941_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___closed__19);
v___x_942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_940_);
lean_ctor_set(v___x_942_, 1, v___x_941_);
v___x_943_ = l_Lean_MessageData_note(v___x_942_);
v___x_944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_944_, 0, v_msg_887_);
lean_ctor_set(v___x_944_, 1, v___x_943_);
if (v_isShared_916_ == 0)
{
lean_ctor_set_tag(v___x_915_, 0);
lean_ctor_set(v___x_915_, 0, v___x_944_);
v___x_946_ = v___x_915_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v___x_944_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_949_; 
lean_dec_ref(v_env_892_);
lean_dec(v_declHint_888_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_msg_887_);
return v___x_949_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg___boxed(lean_object* v_msg_950_, lean_object* v_declHint_951_, lean_object* v___y_952_, lean_object* v___y_953_){
_start:
{
lean_object* v_res_954_; 
v_res_954_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_950_, v_declHint_951_, v___y_952_);
lean_dec(v___y_952_);
return v_res_954_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(lean_object* v_msg_955_, lean_object* v_declHint_956_, lean_object* v___y_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_){
_start:
{
lean_object* v___x_962_; lean_object* v_a_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_972_; 
v___x_962_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_955_, v_declHint_956_, v___y_960_);
v_a_963_ = lean_ctor_get(v___x_962_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_962_);
if (v_isSharedCheck_972_ == 0)
{
v___x_965_ = v___x_962_;
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_a_963_);
lean_dec(v___x_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_972_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
v___x_967_ = l_Lean_unknownIdentifierMessageTag;
v___x_968_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v_a_963_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_968_);
v___x_970_ = v___x_965_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29___boxed(lean_object* v_msg_973_, lean_object* v_declHint_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(v_msg_973_, v_declHint_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(lean_object* v_msgData_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_, lean_object* v___y_985_){
_start:
{
lean_object* v___x_987_; lean_object* v_env_988_; lean_object* v___x_989_; lean_object* v_mctx_990_; lean_object* v_lctx_991_; lean_object* v_options_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_987_ = lean_st_ref_get(v___y_985_);
v_env_988_ = lean_ctor_get(v___x_987_, 0);
lean_inc_ref(v_env_988_);
lean_dec(v___x_987_);
v___x_989_ = lean_st_ref_get(v___y_983_);
v_mctx_990_ = lean_ctor_get(v___x_989_, 0);
lean_inc_ref(v_mctx_990_);
lean_dec(v___x_989_);
v_lctx_991_ = lean_ctor_get(v___y_982_, 2);
v_options_992_ = lean_ctor_get(v___y_984_, 2);
lean_inc_ref(v_options_992_);
lean_inc_ref(v_lctx_991_);
v___x_993_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_993_, 0, v_env_988_);
lean_ctor_set(v___x_993_, 1, v_mctx_990_);
lean_ctor_set(v___x_993_, 2, v_lctx_991_);
lean_ctor_set(v___x_993_, 3, v_options_992_);
v___x_994_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_994_, 0, v___x_993_);
lean_ctor_set(v___x_994_, 1, v_msgData_981_);
v___x_995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_995_, 0, v___x_994_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3___boxed(lean_object* v_msgData_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v_res_1002_; 
v_res_1002_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msgData_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
lean_dec(v___y_998_);
lean_dec_ref(v___y_997_);
return v_res_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(lean_object* v_msg_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_){
_start:
{
lean_object* v_ref_1009_; lean_object* v___x_1010_; lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1019_; 
v_ref_1009_ = lean_ctor_get(v___y_1006_, 5);
v___x_1010_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1003_, v___y_1004_, v___y_1005_, v___y_1006_, v___y_1007_);
v_a_1011_ = lean_ctor_get(v___x_1010_, 0);
v_isSharedCheck_1019_ = !lean_is_exclusive(v___x_1010_);
if (v_isSharedCheck_1019_ == 0)
{
v___x_1013_ = v___x_1010_;
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_1010_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1019_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1015_; lean_object* v___x_1017_; 
lean_inc(v_ref_1009_);
v___x_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1015_, 0, v_ref_1009_);
lean_ctor_set(v___x_1015_, 1, v_a_1011_);
if (v_isShared_1014_ == 0)
{
lean_ctor_set_tag(v___x_1013_, 1);
lean_ctor_set(v___x_1013_, 0, v___x_1015_);
v___x_1017_ = v___x_1013_;
goto v_reusejp_1016_;
}
else
{
lean_object* v_reuseFailAlloc_1018_; 
v_reuseFailAlloc_1018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
v___x_1017_ = v_reuseFailAlloc_1018_;
goto v_reusejp_1016_;
}
v_reusejp_1016_:
{
return v___x_1017_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg___boxed(lean_object* v_msg_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_1020_, v___y_1021_, v___y_1022_, v___y_1023_, v___y_1024_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(lean_object* v_ref_1027_, lean_object* v_msg_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v_fileName_1034_; lean_object* v_fileMap_1035_; lean_object* v_options_1036_; lean_object* v_currRecDepth_1037_; lean_object* v_maxRecDepth_1038_; lean_object* v_ref_1039_; lean_object* v_currNamespace_1040_; lean_object* v_openDecls_1041_; lean_object* v_initHeartbeats_1042_; lean_object* v_maxHeartbeats_1043_; lean_object* v_quotContext_1044_; lean_object* v_currMacroScope_1045_; uint8_t v_diag_1046_; lean_object* v_cancelTk_x3f_1047_; uint8_t v_suppressElabErrors_1048_; lean_object* v_inheritedTraceOptions_1049_; lean_object* v_ref_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_fileName_1034_ = lean_ctor_get(v___y_1031_, 0);
v_fileMap_1035_ = lean_ctor_get(v___y_1031_, 1);
v_options_1036_ = lean_ctor_get(v___y_1031_, 2);
v_currRecDepth_1037_ = lean_ctor_get(v___y_1031_, 3);
v_maxRecDepth_1038_ = lean_ctor_get(v___y_1031_, 4);
v_ref_1039_ = lean_ctor_get(v___y_1031_, 5);
v_currNamespace_1040_ = lean_ctor_get(v___y_1031_, 6);
v_openDecls_1041_ = lean_ctor_get(v___y_1031_, 7);
v_initHeartbeats_1042_ = lean_ctor_get(v___y_1031_, 8);
v_maxHeartbeats_1043_ = lean_ctor_get(v___y_1031_, 9);
v_quotContext_1044_ = lean_ctor_get(v___y_1031_, 10);
v_currMacroScope_1045_ = lean_ctor_get(v___y_1031_, 11);
v_diag_1046_ = lean_ctor_get_uint8(v___y_1031_, sizeof(void*)*14);
v_cancelTk_x3f_1047_ = lean_ctor_get(v___y_1031_, 12);
v_suppressElabErrors_1048_ = lean_ctor_get_uint8(v___y_1031_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1049_ = lean_ctor_get(v___y_1031_, 13);
v_ref_1050_ = l_Lean_replaceRef(v_ref_1027_, v_ref_1039_);
lean_inc_ref(v_inheritedTraceOptions_1049_);
lean_inc(v_cancelTk_x3f_1047_);
lean_inc(v_currMacroScope_1045_);
lean_inc(v_quotContext_1044_);
lean_inc(v_maxHeartbeats_1043_);
lean_inc(v_initHeartbeats_1042_);
lean_inc(v_openDecls_1041_);
lean_inc(v_currNamespace_1040_);
lean_inc(v_maxRecDepth_1038_);
lean_inc(v_currRecDepth_1037_);
lean_inc_ref(v_options_1036_);
lean_inc_ref(v_fileMap_1035_);
lean_inc_ref(v_fileName_1034_);
v___x_1051_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1051_, 0, v_fileName_1034_);
lean_ctor_set(v___x_1051_, 1, v_fileMap_1035_);
lean_ctor_set(v___x_1051_, 2, v_options_1036_);
lean_ctor_set(v___x_1051_, 3, v_currRecDepth_1037_);
lean_ctor_set(v___x_1051_, 4, v_maxRecDepth_1038_);
lean_ctor_set(v___x_1051_, 5, v_ref_1050_);
lean_ctor_set(v___x_1051_, 6, v_currNamespace_1040_);
lean_ctor_set(v___x_1051_, 7, v_openDecls_1041_);
lean_ctor_set(v___x_1051_, 8, v_initHeartbeats_1042_);
lean_ctor_set(v___x_1051_, 9, v_maxHeartbeats_1043_);
lean_ctor_set(v___x_1051_, 10, v_quotContext_1044_);
lean_ctor_set(v___x_1051_, 11, v_currMacroScope_1045_);
lean_ctor_set(v___x_1051_, 12, v_cancelTk_x3f_1047_);
lean_ctor_set(v___x_1051_, 13, v_inheritedTraceOptions_1049_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*14, v_diag_1046_);
lean_ctor_set_uint8(v___x_1051_, sizeof(void*)*14 + 1, v_suppressElabErrors_1048_);
v___x_1052_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_1028_, v___y_1029_, v___y_1030_, v___x_1051_, v___y_1032_);
lean_dec_ref(v___x_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg___boxed(lean_object* v_ref_1053_, lean_object* v_msg_1054_, lean_object* v___y_1055_, lean_object* v___y_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_1053_, v_msg_1054_, v___y_1055_, v___y_1056_, v___y_1057_, v___y_1058_);
lean_dec(v___y_1058_);
lean_dec_ref(v___y_1057_);
lean_dec(v___y_1056_);
lean_dec_ref(v___y_1055_);
lean_dec(v_ref_1053_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(lean_object* v_ref_1061_, lean_object* v_msg_1062_, lean_object* v_declHint_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; lean_object* v_a_1070_; lean_object* v___x_1071_; 
v___x_1069_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29(v_msg_1062_, v_declHint_1063_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
v_a_1070_ = lean_ctor_get(v___x_1069_, 0);
lean_inc(v_a_1070_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_1061_, v_a_1070_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg___boxed(lean_object* v_ref_1072_, lean_object* v_msg_1073_, lean_object* v_declHint_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_1072_, v_msg_1073_, v_declHint_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_ref_1072_);
return v_res_1080_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1082_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__0));
v___x_1083_ = l_Lean_stringToMessageData(v___x_1082_);
return v___x_1083_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1085_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__2));
v___x_1086_ = l_Lean_stringToMessageData(v___x_1085_);
return v___x_1086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(lean_object* v_ref_1087_, lean_object* v_constName_1088_, lean_object* v___y_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_, lean_object* v___y_1092_){
_start:
{
lean_object* v___x_1094_; uint8_t v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; 
v___x_1094_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__1);
v___x_1095_ = 0;
lean_inc(v_constName_1088_);
v___x_1096_ = l_Lean_MessageData_ofConstName(v_constName_1088_, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1094_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_1099_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1097_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_1087_, v___x_1099_, v_constName_1088_, v___y_1089_, v___y_1090_, v___y_1091_, v___y_1092_);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___boxed(lean_object* v_ref_1101_, lean_object* v_constName_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_, lean_object* v___y_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_1101_, v_constName_1102_, v___y_1103_, v___y_1104_, v___y_1105_, v___y_1106_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1104_);
lean_dec_ref(v___y_1103_);
lean_dec(v_ref_1101_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(lean_object* v_constName_1109_, lean_object* v___y_1110_, lean_object* v___y_1111_, lean_object* v___y_1112_, lean_object* v___y_1113_){
_start:
{
lean_object* v_ref_1115_; lean_object* v___x_1116_; 
v_ref_1115_ = lean_ctor_get(v___y_1112_, 5);
v___x_1116_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_1115_, v_constName_1109_, v___y_1110_, v___y_1111_, v___y_1112_, v___y_1113_);
return v___x_1116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg___boxed(lean_object* v_constName_1117_, lean_object* v___y_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_){
_start:
{
lean_object* v_res_1123_; 
v_res_1123_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_1117_, v___y_1118_, v___y_1119_, v___y_1120_, v___y_1121_);
lean_dec(v___y_1121_);
lean_dec_ref(v___y_1120_);
lean_dec(v___y_1119_);
lean_dec_ref(v___y_1118_);
return v_res_1123_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(lean_object* v_constName_1124_, lean_object* v___y_1125_, lean_object* v___y_1126_, lean_object* v___y_1127_, lean_object* v___y_1128_){
_start:
{
lean_object* v___x_1130_; lean_object* v_env_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v___x_1130_ = lean_st_ref_get(v___y_1128_);
v_env_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc_ref(v_env_1131_);
lean_dec(v___x_1130_);
v___x_1132_ = 0;
lean_inc(v_constName_1124_);
v___x_1133_ = l_Lean_Environment_find_x3f(v_env_1131_, v_constName_1124_, v___x_1132_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v___x_1134_; 
v___x_1134_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_1124_, v___y_1125_, v___y_1126_, v___y_1127_, v___y_1128_);
return v___x_1134_;
}
else
{
lean_object* v_val_1135_; lean_object* v___x_1137_; uint8_t v_isShared_1138_; uint8_t v_isSharedCheck_1142_; 
lean_dec(v_constName_1124_);
v_val_1135_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1142_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1142_ == 0)
{
v___x_1137_ = v___x_1133_;
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
else
{
lean_inc(v_val_1135_);
lean_dec(v___x_1133_);
v___x_1137_ = lean_box(0);
v_isShared_1138_ = v_isSharedCheck_1142_;
goto v_resetjp_1136_;
}
v_resetjp_1136_:
{
lean_object* v___x_1140_; 
if (v_isShared_1138_ == 0)
{
lean_ctor_set_tag(v___x_1137_, 0);
v___x_1140_ = v___x_1137_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1141_; 
v_reuseFailAlloc_1141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_val_1135_);
v___x_1140_ = v_reuseFailAlloc_1141_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
return v___x_1140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4___boxed(lean_object* v_constName_1143_, lean_object* v___y_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v_res_1149_; 
v_res_1149_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_constName_1143_, v___y_1144_, v___y_1145_, v___y_1146_, v___y_1147_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
lean_dec(v___y_1145_);
lean_dec_ref(v___y_1144_);
return v_res_1149_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0(void){
_start:
{
lean_object* v___x_1150_; double v___x_1151_; 
v___x_1150_ = lean_unsigned_to_nat(0u);
v___x_1151_ = lean_float_of_nat(v___x_1150_);
return v___x_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(lean_object* v_cls_1155_, lean_object* v_msg_1156_, lean_object* v___y_1157_, lean_object* v___y_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_ref_1162_; lean_object* v___x_1163_; lean_object* v_a_1164_; lean_object* v___x_1166_; uint8_t v_isShared_1167_; uint8_t v_isSharedCheck_1208_; 
v_ref_1162_ = lean_ctor_get(v___y_1159_, 5);
v___x_1163_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1156_, v___y_1157_, v___y_1158_, v___y_1159_, v___y_1160_);
v_a_1164_ = lean_ctor_get(v___x_1163_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1163_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1166_ = v___x_1163_;
v_isShared_1167_ = v_isSharedCheck_1208_;
goto v_resetjp_1165_;
}
else
{
lean_inc(v_a_1164_);
lean_dec(v___x_1163_);
v___x_1166_ = lean_box(0);
v_isShared_1167_ = v_isSharedCheck_1208_;
goto v_resetjp_1165_;
}
v_resetjp_1165_:
{
lean_object* v___x_1168_; lean_object* v_traceState_1169_; lean_object* v_env_1170_; lean_object* v_nextMacroScope_1171_; lean_object* v_ngen_1172_; lean_object* v_auxDeclNGen_1173_; lean_object* v_cache_1174_; lean_object* v_messages_1175_; lean_object* v_infoState_1176_; lean_object* v_snapshotTasks_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1207_; 
v___x_1168_ = lean_st_ref_take(v___y_1160_);
v_traceState_1169_ = lean_ctor_get(v___x_1168_, 4);
v_env_1170_ = lean_ctor_get(v___x_1168_, 0);
v_nextMacroScope_1171_ = lean_ctor_get(v___x_1168_, 1);
v_ngen_1172_ = lean_ctor_get(v___x_1168_, 2);
v_auxDeclNGen_1173_ = lean_ctor_get(v___x_1168_, 3);
v_cache_1174_ = lean_ctor_get(v___x_1168_, 5);
v_messages_1175_ = lean_ctor_get(v___x_1168_, 6);
v_infoState_1176_ = lean_ctor_get(v___x_1168_, 7);
v_snapshotTasks_1177_ = lean_ctor_get(v___x_1168_, 8);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1168_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1179_ = v___x_1168_;
v_isShared_1180_ = v_isSharedCheck_1207_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_snapshotTasks_1177_);
lean_inc(v_infoState_1176_);
lean_inc(v_messages_1175_);
lean_inc(v_cache_1174_);
lean_inc(v_traceState_1169_);
lean_inc(v_auxDeclNGen_1173_);
lean_inc(v_ngen_1172_);
lean_inc(v_nextMacroScope_1171_);
lean_inc(v_env_1170_);
lean_dec(v___x_1168_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1207_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
uint64_t v_tid_1181_; lean_object* v_traces_1182_; lean_object* v___x_1184_; uint8_t v_isShared_1185_; uint8_t v_isSharedCheck_1206_; 
v_tid_1181_ = lean_ctor_get_uint64(v_traceState_1169_, sizeof(void*)*1);
v_traces_1182_ = lean_ctor_get(v_traceState_1169_, 0);
v_isSharedCheck_1206_ = !lean_is_exclusive(v_traceState_1169_);
if (v_isSharedCheck_1206_ == 0)
{
v___x_1184_ = v_traceState_1169_;
v_isShared_1185_ = v_isSharedCheck_1206_;
goto v_resetjp_1183_;
}
else
{
lean_inc(v_traces_1182_);
lean_dec(v_traceState_1169_);
v___x_1184_ = lean_box(0);
v_isShared_1185_ = v_isSharedCheck_1206_;
goto v_resetjp_1183_;
}
v_resetjp_1183_:
{
lean_object* v___x_1186_; double v___x_1187_; uint8_t v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1196_; 
v___x_1186_ = lean_box(0);
v___x_1187_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0);
v___x_1188_ = 0;
v___x_1189_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1));
v___x_1190_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_1190_, 0, v_cls_1155_);
lean_ctor_set(v___x_1190_, 1, v___x_1186_);
lean_ctor_set(v___x_1190_, 2, v___x_1189_);
lean_ctor_set_float(v___x_1190_, sizeof(void*)*3, v___x_1187_);
lean_ctor_set_float(v___x_1190_, sizeof(void*)*3 + 8, v___x_1187_);
lean_ctor_set_uint8(v___x_1190_, sizeof(void*)*3 + 16, v___x_1188_);
v___x_1191_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__2));
v___x_1192_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1190_);
lean_ctor_set(v___x_1192_, 1, v_a_1164_);
lean_ctor_set(v___x_1192_, 2, v___x_1191_);
lean_inc(v_ref_1162_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v_ref_1162_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
v___x_1194_ = l_Lean_PersistentArray_push___redArg(v_traces_1182_, v___x_1193_);
if (v_isShared_1185_ == 0)
{
lean_ctor_set(v___x_1184_, 0, v___x_1194_);
v___x_1196_ = v___x_1184_;
goto v_reusejp_1195_;
}
else
{
lean_object* v_reuseFailAlloc_1205_; 
v_reuseFailAlloc_1205_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1205_, 0, v___x_1194_);
lean_ctor_set_uint64(v_reuseFailAlloc_1205_, sizeof(void*)*1, v_tid_1181_);
v___x_1196_ = v_reuseFailAlloc_1205_;
goto v_reusejp_1195_;
}
v_reusejp_1195_:
{
lean_object* v___x_1198_; 
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 4, v___x_1196_);
v___x_1198_ = v___x_1179_;
goto v_reusejp_1197_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_env_1170_);
lean_ctor_set(v_reuseFailAlloc_1204_, 1, v_nextMacroScope_1171_);
lean_ctor_set(v_reuseFailAlloc_1204_, 2, v_ngen_1172_);
lean_ctor_set(v_reuseFailAlloc_1204_, 3, v_auxDeclNGen_1173_);
lean_ctor_set(v_reuseFailAlloc_1204_, 4, v___x_1196_);
lean_ctor_set(v_reuseFailAlloc_1204_, 5, v_cache_1174_);
lean_ctor_set(v_reuseFailAlloc_1204_, 6, v_messages_1175_);
lean_ctor_set(v_reuseFailAlloc_1204_, 7, v_infoState_1176_);
lean_ctor_set(v_reuseFailAlloc_1204_, 8, v_snapshotTasks_1177_);
v___x_1198_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1197_;
}
v_reusejp_1197_:
{
lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1202_; 
v___x_1199_ = lean_st_ref_set(v___y_1160_, v___x_1198_);
v___x_1200_ = lean_box(0);
if (v_isShared_1167_ == 0)
{
lean_ctor_set(v___x_1166_, 0, v___x_1200_);
v___x_1202_ = v___x_1166_;
goto v_reusejp_1201_;
}
else
{
lean_object* v_reuseFailAlloc_1203_; 
v_reuseFailAlloc_1203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1203_, 0, v___x_1200_);
v___x_1202_ = v_reuseFailAlloc_1203_;
goto v_reusejp_1201_;
}
v_reusejp_1201_:
{
return v___x_1202_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___boxed(lean_object* v_cls_1209_, lean_object* v_msg_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1209_, v_msg_1210_, v___y_1211_, v___y_1212_, v___y_1213_, v___y_1214_);
lean_dec(v___y_1214_);
lean_dec_ref(v___y_1213_);
lean_dec(v___y_1212_);
lean_dec_ref(v___y_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(size_t v_sz_1217_, size_t v_i_1218_, lean_object* v_bs_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v___x_1222_; 
v___x_1222_ = lean_usize_dec_lt(v_i_1218_, v_sz_1217_);
if (v___x_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1223_, 0, v_bs_1219_);
return v___x_1223_;
}
else
{
lean_object* v_v_1224_; lean_object* v___x_1225_; 
v_v_1224_ = lean_array_uget_borrowed(v_bs_1219_, v_i_1218_);
lean_inc(v_v_1224_);
v___x_1225_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_v_1224_, v___y_1220_);
if (lean_obj_tag(v___x_1225_) == 0)
{
lean_object* v_a_1226_; lean_object* v___x_1227_; lean_object* v_bs_x27_1228_; size_t v___x_1229_; size_t v___x_1230_; lean_object* v___x_1231_; 
v_a_1226_ = lean_ctor_get(v___x_1225_, 0);
lean_inc(v_a_1226_);
lean_dec_ref(v___x_1225_);
v___x_1227_ = lean_unsigned_to_nat(0u);
v_bs_x27_1228_ = lean_array_uset(v_bs_1219_, v_i_1218_, v___x_1227_);
v___x_1229_ = ((size_t)1ULL);
v___x_1230_ = lean_usize_add(v_i_1218_, v___x_1229_);
v___x_1231_ = lean_array_uset(v_bs_x27_1228_, v_i_1218_, v_a_1226_);
v_i_1218_ = v___x_1230_;
v_bs_1219_ = v___x_1231_;
goto _start;
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec_ref(v_bs_1219_);
v_a_1233_ = lean_ctor_get(v___x_1225_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1225_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1225_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1225_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg___boxed(lean_object* v_sz_1241_, lean_object* v_i_1242_, lean_object* v_bs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
size_t v_sz_boxed_1246_; size_t v_i_boxed_1247_; lean_object* v_res_1248_; 
v_sz_boxed_1246_ = lean_unbox_usize(v_sz_1241_);
lean_dec(v_sz_1241_);
v_i_boxed_1247_ = lean_unbox_usize(v_i_1242_);
lean_dec(v_i_1242_);
v_res_1248_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_boxed_1246_, v_i_boxed_1247_, v_bs_1243_, v___y_1244_);
lean_dec(v___y_1244_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(lean_object* v_a_1249_, lean_object* v_a_1250_){
_start:
{
if (lean_obj_tag(v_a_1249_) == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = l_List_reverse___redArg(v_a_1250_);
return v___x_1251_;
}
else
{
lean_object* v_head_1252_; lean_object* v_tail_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1262_; 
v_head_1252_ = lean_ctor_get(v_a_1249_, 0);
v_tail_1253_ = lean_ctor_get(v_a_1249_, 1);
v_isSharedCheck_1262_ = !lean_is_exclusive(v_a_1249_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1255_ = v_a_1249_;
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_tail_1253_);
lean_inc(v_head_1252_);
lean_dec(v_a_1249_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1262_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1257_; lean_object* v___x_1259_; 
v___x_1257_ = l_Lean_MessageData_ofExpr(v_head_1252_);
if (v_isShared_1256_ == 0)
{
lean_ctor_set(v___x_1255_, 1, v_a_1250_);
lean_ctor_set(v___x_1255_, 0, v___x_1257_);
v___x_1259_ = v___x_1255_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v_a_1250_);
v___x_1259_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
v_a_1249_ = v_tail_1253_;
v_a_1250_ = v___x_1259_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(lean_object* v___x_1263_, lean_object* v_a_1264_, lean_object* v_____r_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
lean_object* v___x_1271_; 
v___x_1271_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1263_, v_a_1264_, v___y_1267_);
if (lean_obj_tag(v___x_1271_) == 0)
{
lean_object* v___x_1273_; uint8_t v_isShared_1274_; uint8_t v_isSharedCheck_1279_; 
v_isSharedCheck_1279_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1279_ == 0)
{
lean_object* v_unused_1280_; 
v_unused_1280_ = lean_ctor_get(v___x_1271_, 0);
lean_dec(v_unused_1280_);
v___x_1273_ = v___x_1271_;
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
else
{
lean_dec(v___x_1271_);
v___x_1273_ = lean_box(0);
v_isShared_1274_ = v_isSharedCheck_1279_;
goto v_resetjp_1272_;
}
v_resetjp_1272_:
{
lean_object* v___x_1275_; lean_object* v___x_1277_; 
v___x_1275_ = lean_box(0);
if (v_isShared_1274_ == 0)
{
lean_ctor_set(v___x_1273_, 0, v___x_1275_);
v___x_1277_ = v___x_1273_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
else
{
lean_object* v_a_1281_; lean_object* v___x_1283_; uint8_t v_isShared_1284_; uint8_t v_isSharedCheck_1288_; 
v_a_1281_ = lean_ctor_get(v___x_1271_, 0);
v_isSharedCheck_1288_ = !lean_is_exclusive(v___x_1271_);
if (v_isSharedCheck_1288_ == 0)
{
v___x_1283_ = v___x_1271_;
v_isShared_1284_ = v_isSharedCheck_1288_;
goto v_resetjp_1282_;
}
else
{
lean_inc(v_a_1281_);
lean_dec(v___x_1271_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed(lean_object* v___x_1289_, lean_object* v_a_1290_, lean_object* v_____r_1291_, lean_object* v___y_1292_, lean_object* v___y_1293_, lean_object* v___y_1294_, lean_object* v___y_1295_, lean_object* v___y_1296_){
_start:
{
lean_object* v_res_1297_; 
v_res_1297_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1289_, v_a_1290_, v_____r_1291_, v___y_1292_, v___y_1293_, v___y_1294_, v___y_1295_);
lean_dec(v___y_1295_);
lean_dec_ref(v___y_1294_);
lean_dec(v___y_1293_);
lean_dec_ref(v___y_1292_);
return v_res_1297_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(lean_object* v_a_1298_, lean_object* v___x_1299_, uint8_t v_compile_1300_, uint8_t v_logCompileErrors_1301_, lean_object* v_____r_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
if (v_compile_1300_ == 0)
{
goto v___jp_1308_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; 
v___x_1327_ = lean_unsigned_to_nat(1u);
v___x_1328_ = lean_mk_empty_array_with_capacity(v___x_1327_);
lean_inc(v_a_1298_);
v___x_1329_ = lean_array_push(v___x_1328_, v_a_1298_);
v___x_1330_ = l_Lean_compileDecls(v___x_1329_, v_logCompileErrors_1301_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1330_) == 0)
{
lean_dec_ref(v___x_1330_);
goto v___jp_1308_;
}
else
{
lean_object* v_a_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1338_; 
lean_dec(v_a_1298_);
v_a_1331_ = lean_ctor_get(v___x_1330_, 0);
v_isSharedCheck_1338_ = !lean_is_exclusive(v___x_1330_);
if (v_isSharedCheck_1338_ == 0)
{
v___x_1333_ = v___x_1330_;
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_a_1331_);
lean_dec(v___x_1330_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1338_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1337_; 
v_reuseFailAlloc_1337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1337_, 0, v_a_1331_);
v___x_1336_ = v_reuseFailAlloc_1337_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
return v___x_1336_;
}
}
}
}
v___jp_1308_:
{
lean_object* v___x_1309_; 
v___x_1309_ = l_Lean_enableRealizationsForConst(v_a_1298_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1309_) == 0)
{
lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1317_; 
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1317_ == 0)
{
lean_object* v_unused_1318_; 
v_unused_1318_ = lean_ctor_get(v___x_1309_, 0);
lean_dec(v_unused_1318_);
v___x_1311_ = v___x_1309_;
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
else
{
lean_dec(v___x_1309_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1317_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1313_; lean_object* v___x_1315_; 
v___x_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1313_, 0, v___x_1299_);
if (v_isShared_1312_ == 0)
{
lean_ctor_set(v___x_1311_, 0, v___x_1313_);
v___x_1315_ = v___x_1311_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1313_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
v_a_1319_ = lean_ctor_get(v___x_1309_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1309_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1309_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1309_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0___boxed(lean_object* v_a_1339_, lean_object* v___x_1340_, lean_object* v_compile_1341_, lean_object* v_logCompileErrors_1342_, lean_object* v_____r_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_compile_boxed_1349_; uint8_t v_logCompileErrors_boxed_1350_; lean_object* v_res_1351_; 
v_compile_boxed_1349_ = lean_unbox(v_compile_1341_);
v_logCompileErrors_boxed_1350_ = lean_unbox(v_logCompileErrors_1342_);
v_res_1351_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1339_, v___x_1340_, v_compile_boxed_1349_, v_logCompileErrors_boxed_1350_, v_____r_1343_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1351_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(lean_object* v_a_1352_, lean_object* v___x_1353_, uint8_t v___x_1354_, lean_object* v___x_1355_, lean_object* v___x_1356_, lean_object* v_____r_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = lean_box(0);
v___x_1364_ = l_Lean_Meta_mkAuxTheorem(v_a_1352_, v___x_1353_, v___x_1354_, v___x_1363_, v___x_1354_, v___y_1358_, v___y_1359_, v___y_1360_, v___y_1361_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref(v___x_1364_);
v___x_1366_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1355_, v_a_1365_, v___y_1359_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1374_; 
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1374_ == 0)
{
lean_object* v_unused_1375_; 
v_unused_1375_ = lean_ctor_get(v___x_1366_, 0);
lean_dec(v_unused_1375_);
v___x_1368_ = v___x_1366_;
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
else
{
lean_dec(v___x_1366_);
v___x_1368_ = lean_box(0);
v_isShared_1369_ = v_isSharedCheck_1374_;
goto v_resetjp_1367_;
}
v_resetjp_1367_:
{
lean_object* v___x_1370_; lean_object* v___x_1372_; 
v___x_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1370_, 0, v___x_1356_);
if (v_isShared_1369_ == 0)
{
lean_ctor_set(v___x_1368_, 0, v___x_1370_);
v___x_1372_ = v___x_1368_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v___x_1370_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1366_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1366_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
lean_dec(v___x_1355_);
v_a_1384_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1364_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1364_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3___boxed(lean_object* v_a_1392_, lean_object* v___x_1393_, lean_object* v___x_1394_, lean_object* v___x_1395_, lean_object* v___x_1396_, lean_object* v_____r_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_, lean_object* v___y_1401_, lean_object* v___y_1402_){
_start:
{
uint8_t v___x_120984__boxed_1403_; lean_object* v_res_1404_; 
v___x_120984__boxed_1403_ = lean_unbox(v___x_1394_);
v_res_1404_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1392_, v___x_1393_, v___x_120984__boxed_1403_, v___x_1395_, v___x_1396_, v_____r_1397_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
return v_res_1404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(size_t v_sz_1405_, size_t v_i_1406_, lean_object* v_bs_1407_){
_start:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_usize_dec_lt(v_i_1406_, v_sz_1405_);
if (v___x_1408_ == 0)
{
return v_bs_1407_;
}
else
{
lean_object* v_v_1409_; lean_object* v_msg_1410_; lean_object* v___x_1411_; lean_object* v_bs_x27_1412_; size_t v___x_1413_; size_t v___x_1414_; lean_object* v___x_1415_; 
v_v_1409_ = lean_array_uget_borrowed(v_bs_1407_, v_i_1406_);
v_msg_1410_ = lean_ctor_get(v_v_1409_, 1);
lean_inc_ref(v_msg_1410_);
v___x_1411_ = lean_unsigned_to_nat(0u);
v_bs_x27_1412_ = lean_array_uset(v_bs_1407_, v_i_1406_, v___x_1411_);
v___x_1413_ = ((size_t)1ULL);
v___x_1414_ = lean_usize_add(v_i_1406_, v___x_1413_);
v___x_1415_ = lean_array_uset(v_bs_x27_1412_, v_i_1406_, v_msg_1410_);
v_i_1406_ = v___x_1414_;
v_bs_1407_ = v___x_1415_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26___boxed(lean_object* v_sz_1417_, lean_object* v_i_1418_, lean_object* v_bs_1419_){
_start:
{
size_t v_sz_boxed_1420_; size_t v_i_boxed_1421_; lean_object* v_res_1422_; 
v_sz_boxed_1420_ = lean_unbox_usize(v_sz_1417_);
lean_dec(v_sz_1417_);
v_i_boxed_1421_ = lean_unbox_usize(v_i_1418_);
lean_dec(v_i_1418_);
v_res_1422_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(v_sz_boxed_1420_, v_i_boxed_1421_, v_bs_1419_);
return v_res_1422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(lean_object* v_oldTraces_1423_, lean_object* v_data_1424_, lean_object* v_ref_1425_, lean_object* v_msg_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_fileName_1432_; lean_object* v_fileMap_1433_; lean_object* v_options_1434_; lean_object* v_currRecDepth_1435_; lean_object* v_maxRecDepth_1436_; lean_object* v_ref_1437_; lean_object* v_currNamespace_1438_; lean_object* v_openDecls_1439_; lean_object* v_initHeartbeats_1440_; lean_object* v_maxHeartbeats_1441_; lean_object* v_quotContext_1442_; lean_object* v_currMacroScope_1443_; uint8_t v_diag_1444_; lean_object* v_cancelTk_x3f_1445_; uint8_t v_suppressElabErrors_1446_; lean_object* v_inheritedTraceOptions_1447_; lean_object* v___x_1448_; lean_object* v_traceState_1449_; lean_object* v_traces_1450_; lean_object* v_ref_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; size_t v_sz_1454_; size_t v___x_1455_; lean_object* v___x_1456_; lean_object* v_msg_1457_; lean_object* v___x_1458_; lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1496_; 
v_fileName_1432_ = lean_ctor_get(v___y_1429_, 0);
v_fileMap_1433_ = lean_ctor_get(v___y_1429_, 1);
v_options_1434_ = lean_ctor_get(v___y_1429_, 2);
v_currRecDepth_1435_ = lean_ctor_get(v___y_1429_, 3);
v_maxRecDepth_1436_ = lean_ctor_get(v___y_1429_, 4);
v_ref_1437_ = lean_ctor_get(v___y_1429_, 5);
v_currNamespace_1438_ = lean_ctor_get(v___y_1429_, 6);
v_openDecls_1439_ = lean_ctor_get(v___y_1429_, 7);
v_initHeartbeats_1440_ = lean_ctor_get(v___y_1429_, 8);
v_maxHeartbeats_1441_ = lean_ctor_get(v___y_1429_, 9);
v_quotContext_1442_ = lean_ctor_get(v___y_1429_, 10);
v_currMacroScope_1443_ = lean_ctor_get(v___y_1429_, 11);
v_diag_1444_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*14);
v_cancelTk_x3f_1445_ = lean_ctor_get(v___y_1429_, 12);
v_suppressElabErrors_1446_ = lean_ctor_get_uint8(v___y_1429_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_1447_ = lean_ctor_get(v___y_1429_, 13);
v___x_1448_ = lean_st_ref_get(v___y_1430_);
v_traceState_1449_ = lean_ctor_get(v___x_1448_, 4);
lean_inc_ref(v_traceState_1449_);
lean_dec(v___x_1448_);
v_traces_1450_ = lean_ctor_get(v_traceState_1449_, 0);
lean_inc_ref(v_traces_1450_);
lean_dec_ref(v_traceState_1449_);
v_ref_1451_ = l_Lean_replaceRef(v_ref_1425_, v_ref_1437_);
lean_inc_ref(v_inheritedTraceOptions_1447_);
lean_inc(v_cancelTk_x3f_1445_);
lean_inc(v_currMacroScope_1443_);
lean_inc(v_quotContext_1442_);
lean_inc(v_maxHeartbeats_1441_);
lean_inc(v_initHeartbeats_1440_);
lean_inc(v_openDecls_1439_);
lean_inc(v_currNamespace_1438_);
lean_inc(v_maxRecDepth_1436_);
lean_inc(v_currRecDepth_1435_);
lean_inc_ref(v_options_1434_);
lean_inc_ref(v_fileMap_1433_);
lean_inc_ref(v_fileName_1432_);
v___x_1452_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_1452_, 0, v_fileName_1432_);
lean_ctor_set(v___x_1452_, 1, v_fileMap_1433_);
lean_ctor_set(v___x_1452_, 2, v_options_1434_);
lean_ctor_set(v___x_1452_, 3, v_currRecDepth_1435_);
lean_ctor_set(v___x_1452_, 4, v_maxRecDepth_1436_);
lean_ctor_set(v___x_1452_, 5, v_ref_1451_);
lean_ctor_set(v___x_1452_, 6, v_currNamespace_1438_);
lean_ctor_set(v___x_1452_, 7, v_openDecls_1439_);
lean_ctor_set(v___x_1452_, 8, v_initHeartbeats_1440_);
lean_ctor_set(v___x_1452_, 9, v_maxHeartbeats_1441_);
lean_ctor_set(v___x_1452_, 10, v_quotContext_1442_);
lean_ctor_set(v___x_1452_, 11, v_currMacroScope_1443_);
lean_ctor_set(v___x_1452_, 12, v_cancelTk_x3f_1445_);
lean_ctor_set(v___x_1452_, 13, v_inheritedTraceOptions_1447_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*14, v_diag_1444_);
lean_ctor_set_uint8(v___x_1452_, sizeof(void*)*14 + 1, v_suppressElabErrors_1446_);
v___x_1453_ = l_Lean_PersistentArray_toArray___redArg(v_traces_1450_);
lean_dec_ref(v_traces_1450_);
v_sz_1454_ = lean_array_size(v___x_1453_);
v___x_1455_ = ((size_t)0ULL);
v___x_1456_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24_spec__26(v_sz_1454_, v___x_1455_, v___x_1453_);
v_msg_1457_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v_msg_1457_, 0, v_data_1424_);
lean_ctor_set(v_msg_1457_, 1, v_msg_1426_);
lean_ctor_set(v_msg_1457_, 2, v___x_1456_);
v___x_1458_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3_spec__3(v_msg_1457_, v___y_1427_, v___y_1428_, v___x_1452_, v___y_1430_);
lean_dec_ref(v___x_1452_);
v_a_1459_ = lean_ctor_get(v___x_1458_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1458_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1461_ = v___x_1458_;
v_isShared_1462_ = v_isSharedCheck_1496_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1458_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1496_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1463_; lean_object* v_traceState_1464_; lean_object* v_env_1465_; lean_object* v_nextMacroScope_1466_; lean_object* v_ngen_1467_; lean_object* v_auxDeclNGen_1468_; lean_object* v_cache_1469_; lean_object* v_messages_1470_; lean_object* v_infoState_1471_; lean_object* v_snapshotTasks_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1495_; 
v___x_1463_ = lean_st_ref_take(v___y_1430_);
v_traceState_1464_ = lean_ctor_get(v___x_1463_, 4);
v_env_1465_ = lean_ctor_get(v___x_1463_, 0);
v_nextMacroScope_1466_ = lean_ctor_get(v___x_1463_, 1);
v_ngen_1467_ = lean_ctor_get(v___x_1463_, 2);
v_auxDeclNGen_1468_ = lean_ctor_get(v___x_1463_, 3);
v_cache_1469_ = lean_ctor_get(v___x_1463_, 5);
v_messages_1470_ = lean_ctor_get(v___x_1463_, 6);
v_infoState_1471_ = lean_ctor_get(v___x_1463_, 7);
v_snapshotTasks_1472_ = lean_ctor_get(v___x_1463_, 8);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1474_ = v___x_1463_;
v_isShared_1475_ = v_isSharedCheck_1495_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_snapshotTasks_1472_);
lean_inc(v_infoState_1471_);
lean_inc(v_messages_1470_);
lean_inc(v_cache_1469_);
lean_inc(v_traceState_1464_);
lean_inc(v_auxDeclNGen_1468_);
lean_inc(v_ngen_1467_);
lean_inc(v_nextMacroScope_1466_);
lean_inc(v_env_1465_);
lean_dec(v___x_1463_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1495_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
uint64_t v_tid_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1493_; 
v_tid_1476_ = lean_ctor_get_uint64(v_traceState_1464_, sizeof(void*)*1);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_traceState_1464_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; 
v_unused_1494_ = lean_ctor_get(v_traceState_1464_, 0);
lean_dec(v_unused_1494_);
v___x_1478_ = v_traceState_1464_;
v_isShared_1479_ = v_isSharedCheck_1493_;
goto v_resetjp_1477_;
}
else
{
lean_dec(v_traceState_1464_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1493_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1483_; 
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v_ref_1425_);
lean_ctor_set(v___x_1480_, 1, v_a_1459_);
v___x_1481_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_1423_, v___x_1480_);
if (v_isShared_1479_ == 0)
{
lean_ctor_set(v___x_1478_, 0, v___x_1481_);
v___x_1483_ = v___x_1478_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1481_);
lean_ctor_set_uint64(v_reuseFailAlloc_1492_, sizeof(void*)*1, v_tid_1476_);
v___x_1483_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
lean_object* v___x_1485_; 
if (v_isShared_1475_ == 0)
{
lean_ctor_set(v___x_1474_, 4, v___x_1483_);
v___x_1485_ = v___x_1474_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_env_1465_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_nextMacroScope_1466_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v_ngen_1467_);
lean_ctor_set(v_reuseFailAlloc_1491_, 3, v_auxDeclNGen_1468_);
lean_ctor_set(v_reuseFailAlloc_1491_, 4, v___x_1483_);
lean_ctor_set(v_reuseFailAlloc_1491_, 5, v_cache_1469_);
lean_ctor_set(v_reuseFailAlloc_1491_, 6, v_messages_1470_);
lean_ctor_set(v_reuseFailAlloc_1491_, 7, v_infoState_1471_);
lean_ctor_set(v_reuseFailAlloc_1491_, 8, v_snapshotTasks_1472_);
v___x_1485_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1486_ = lean_st_ref_set(v___y_1430_, v___x_1485_);
v___x_1487_ = lean_box(0);
if (v_isShared_1462_ == 0)
{
lean_ctor_set(v___x_1461_, 0, v___x_1487_);
v___x_1489_ = v___x_1461_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v___x_1487_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24___boxed(lean_object* v_oldTraces_1497_, lean_object* v_data_1498_, lean_object* v_ref_1499_, lean_object* v_msg_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
lean_object* v_res_1506_; 
v_res_1506_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_oldTraces_1497_, v_data_1498_, v_ref_1499_, v_msg_1500_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___y_1504_);
lean_dec_ref(v___y_1503_);
lean_dec(v___y_1502_);
lean_dec_ref(v___y_1501_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(lean_object* v_opts_1507_, lean_object* v_opt_1508_){
_start:
{
lean_object* v_name_1509_; lean_object* v_defValue_1510_; lean_object* v_map_1511_; lean_object* v___x_1512_; 
v_name_1509_ = lean_ctor_get(v_opt_1508_, 0);
v_defValue_1510_ = lean_ctor_get(v_opt_1508_, 1);
v_map_1511_ = lean_ctor_get(v_opts_1507_, 0);
v___x_1512_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1511_, v_name_1509_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_inc(v_defValue_1510_);
return v_defValue_1510_;
}
else
{
lean_object* v_val_1513_; 
v_val_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_val_1513_);
lean_dec_ref(v___x_1512_);
if (lean_obj_tag(v_val_1513_) == 3)
{
lean_object* v_v_1514_; 
v_v_1514_ = lean_ctor_get(v_val_1513_, 0);
lean_inc(v_v_1514_);
lean_dec_ref(v_val_1513_);
return v_v_1514_;
}
else
{
lean_dec(v_val_1513_);
lean_inc(v_defValue_1510_);
return v_defValue_1510_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26___boxed(lean_object* v_opts_1515_, lean_object* v_opt_1516_){
_start:
{
lean_object* v_res_1517_; 
v_res_1517_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1515_, v_opt_1516_);
lean_dec_ref(v_opt_1516_);
lean_dec_ref(v_opts_1515_);
return v_res_1517_;
}
}
LEAN_EXPORT uint8_t l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(lean_object* v_e_1518_){
_start:
{
if (lean_obj_tag(v_e_1518_) == 0)
{
uint8_t v___x_1519_; 
v___x_1519_ = 2;
return v___x_1519_;
}
else
{
uint8_t v___x_1520_; 
v___x_1520_ = 0;
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23___boxed(lean_object* v_e_1521_){
_start:
{
uint8_t v_res_1522_; lean_object* v_r_1523_; 
v_res_1522_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(v_e_1521_);
lean_dec_ref(v_e_1521_);
v_r_1523_ = lean_box(v_res_1522_);
return v_r_1523_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(lean_object* v_x_1524_){
_start:
{
if (lean_obj_tag(v_x_1524_) == 0)
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
v_a_1526_ = lean_ctor_get(v_x_1524_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v_x_1524_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v_x_1524_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
lean_ctor_set_tag(v___x_1528_, 1);
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
}
}
}
else
{
lean_object* v_a_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1541_; 
v_a_1534_ = lean_ctor_get(v_x_1524_, 0);
v_isSharedCheck_1541_ = !lean_is_exclusive(v_x_1524_);
if (v_isSharedCheck_1541_ == 0)
{
v___x_1536_ = v_x_1524_;
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_a_1534_);
lean_dec(v_x_1524_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1541_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1539_; 
if (v_isShared_1537_ == 0)
{
lean_ctor_set_tag(v___x_1536_, 0);
v___x_1539_ = v___x_1536_;
goto v_reusejp_1538_;
}
else
{
lean_object* v_reuseFailAlloc_1540_; 
v_reuseFailAlloc_1540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1540_, 0, v_a_1534_);
v___x_1539_ = v_reuseFailAlloc_1540_;
goto v_reusejp_1538_;
}
v_reusejp_1538_:
{
return v___x_1539_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg___boxed(lean_object* v_x_1542_, lean_object* v___y_1543_){
_start:
{
lean_object* v_res_1544_; 
v_res_1544_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_x_1542_);
return v_res_1544_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1(void){
_start:
{
lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__0));
v___x_1547_ = l_Lean_stringToMessageData(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3(void){
_start:
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = ((lean_object*)(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__2));
v___x_1550_ = l_Lean_stringToMessageData(v___x_1549_);
return v___x_1550_;
}
}
static double _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4(void){
_start:
{
lean_object* v___x_1551_; double v___x_1552_; 
v___x_1551_ = lean_unsigned_to_nat(1000u);
v___x_1552_ = lean_float_of_nat(v___x_1551_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(lean_object* v_cls_1553_, uint8_t v_collapsed_1554_, lean_object* v_tag_1555_, lean_object* v_opts_1556_, uint8_t v_clsEnabled_1557_, lean_object* v_oldTraces_1558_, lean_object* v_msg_1559_, lean_object* v_resStartStop_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_fst_1566_; lean_object* v_snd_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1665_; 
v_fst_1566_ = lean_ctor_get(v_resStartStop_1560_, 0);
v_snd_1567_ = lean_ctor_get(v_resStartStop_1560_, 1);
v_isSharedCheck_1665_ = !lean_is_exclusive(v_resStartStop_1560_);
if (v_isSharedCheck_1665_ == 0)
{
v___x_1569_ = v_resStartStop_1560_;
v_isShared_1570_ = v_isSharedCheck_1665_;
goto v_resetjp_1568_;
}
else
{
lean_inc(v_snd_1567_);
lean_inc(v_fst_1566_);
lean_dec(v_resStartStop_1560_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1665_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___y_1572_; lean_object* v___y_1573_; lean_object* v_data_1574_; lean_object* v_fst_1585_; lean_object* v_snd_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1664_; 
v_fst_1585_ = lean_ctor_get(v_snd_1567_, 0);
v_snd_1586_ = lean_ctor_get(v_snd_1567_, 1);
v_isSharedCheck_1664_ = !lean_is_exclusive(v_snd_1567_);
if (v_isSharedCheck_1664_ == 0)
{
v___x_1588_ = v_snd_1567_;
v_isShared_1589_ = v_isSharedCheck_1664_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_snd_1586_);
lean_inc(v_fst_1585_);
lean_dec(v_snd_1567_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1664_;
goto v_resetjp_1587_;
}
v___jp_1571_:
{
lean_object* v___x_1575_; 
lean_inc(v___y_1572_);
v___x_1575_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__24(v_oldTraces_1558_, v_data_1574_, v___y_1572_, v___y_1573_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_);
if (lean_obj_tag(v___x_1575_) == 0)
{
lean_object* v___x_1576_; 
lean_dec_ref(v___x_1575_);
v___x_1576_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_fst_1566_);
return v___x_1576_;
}
else
{
lean_object* v_a_1577_; lean_object* v___x_1579_; uint8_t v_isShared_1580_; uint8_t v_isSharedCheck_1584_; 
lean_dec(v_fst_1566_);
v_a_1577_ = lean_ctor_get(v___x_1575_, 0);
v_isSharedCheck_1584_ = !lean_is_exclusive(v___x_1575_);
if (v_isSharedCheck_1584_ == 0)
{
v___x_1579_ = v___x_1575_;
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
else
{
lean_inc(v_a_1577_);
lean_dec(v___x_1575_);
v___x_1579_ = lean_box(0);
v_isShared_1580_ = v_isSharedCheck_1584_;
goto v_resetjp_1578_;
}
v_resetjp_1578_:
{
lean_object* v___x_1582_; 
if (v_isShared_1580_ == 0)
{
v___x_1582_ = v___x_1579_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1583_; 
v_reuseFailAlloc_1583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1583_, 0, v_a_1577_);
v___x_1582_ = v_reuseFailAlloc_1583_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
return v___x_1582_;
}
}
}
}
v_resetjp_1587_:
{
lean_object* v___x_1590_; uint8_t v___x_1591_; lean_object* v___y_1593_; lean_object* v_a_1594_; uint8_t v___y_1618_; double v___y_1649_; 
v___x_1590_ = l_Lean_trace_profiler;
v___x_1591_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_1556_, v___x_1590_);
if (v___x_1591_ == 0)
{
v___y_1618_ = v___x_1591_;
goto v___jp_1617_;
}
else
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = l_Lean_trace_profiler_useHeartbeats;
v___x_1655_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_opts_1556_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; lean_object* v___x_1657_; double v___x_1658_; double v___x_1659_; double v___x_1660_; 
v___x_1656_ = l_Lean_trace_profiler_threshold;
v___x_1657_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1556_, v___x_1656_);
v___x_1658_ = lean_float_of_nat(v___x_1657_);
v___x_1659_ = lean_float_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__4);
v___x_1660_ = lean_float_div(v___x_1658_, v___x_1659_);
v___y_1649_ = v___x_1660_;
goto v___jp_1648_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; double v___x_1663_; 
v___x_1661_ = l_Lean_trace_profiler_threshold;
v___x_1662_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__26(v_opts_1556_, v___x_1661_);
v___x_1663_ = lean_float_of_nat(v___x_1662_);
v___y_1649_ = v___x_1663_;
goto v___jp_1648_;
}
}
v___jp_1592_:
{
uint8_t v_result_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; 
v_result_1595_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__23(v_fst_1566_);
v___x_1596_ = l_Lean_TraceResult_toEmoji(v_result_1595_);
v___x_1597_ = l_Lean_stringToMessageData(v___x_1596_);
v___x_1598_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__1);
if (v_isShared_1589_ == 0)
{
lean_ctor_set_tag(v___x_1588_, 7);
lean_ctor_set(v___x_1588_, 1, v___x_1598_);
lean_ctor_set(v___x_1588_, 0, v___x_1597_);
v___x_1600_ = v___x_1588_;
goto v_reusejp_1599_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v___x_1597_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1598_);
v___x_1600_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1599_;
}
v_reusejp_1599_:
{
lean_object* v_m_1602_; 
if (v_isShared_1570_ == 0)
{
lean_ctor_set_tag(v___x_1569_, 7);
lean_ctor_set(v___x_1569_, 1, v_a_1594_);
lean_ctor_set(v___x_1569_, 0, v___x_1600_);
v_m_1602_ = v___x_1569_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v___x_1600_);
lean_ctor_set(v_reuseFailAlloc_1610_, 1, v_a_1594_);
v_m_1602_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
lean_object* v___x_1603_; lean_object* v___x_1604_; double v___x_1605_; lean_object* v_data_1606_; 
v___x_1603_ = lean_box(v_result_1595_);
v___x_1604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1604_, 0, v___x_1603_);
v___x_1605_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__0);
lean_inc_ref(v_tag_1555_);
lean_inc_ref(v___x_1604_);
lean_inc(v_cls_1553_);
v_data_1606_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1606_, 0, v_cls_1553_);
lean_ctor_set(v_data_1606_, 1, v___x_1604_);
lean_ctor_set(v_data_1606_, 2, v_tag_1555_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3, v___x_1605_);
lean_ctor_set_float(v_data_1606_, sizeof(void*)*3 + 8, v___x_1605_);
lean_ctor_set_uint8(v_data_1606_, sizeof(void*)*3 + 16, v_collapsed_1554_);
if (v___x_1591_ == 0)
{
lean_dec_ref(v___x_1604_);
lean_dec(v_snd_1586_);
lean_dec(v_fst_1585_);
lean_dec_ref(v_tag_1555_);
lean_dec(v_cls_1553_);
v___y_1572_ = v___y_1593_;
v___y_1573_ = v_m_1602_;
v_data_1574_ = v_data_1606_;
goto v___jp_1571_;
}
else
{
lean_object* v_data_1607_; double v___x_1608_; double v___x_1609_; 
lean_dec_ref(v_data_1606_);
v_data_1607_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v_data_1607_, 0, v_cls_1553_);
lean_ctor_set(v_data_1607_, 1, v___x_1604_);
lean_ctor_set(v_data_1607_, 2, v_tag_1555_);
v___x_1608_ = lean_unbox_float(v_fst_1585_);
lean_dec(v_fst_1585_);
lean_ctor_set_float(v_data_1607_, sizeof(void*)*3, v___x_1608_);
v___x_1609_ = lean_unbox_float(v_snd_1586_);
lean_dec(v_snd_1586_);
lean_ctor_set_float(v_data_1607_, sizeof(void*)*3 + 8, v___x_1609_);
lean_ctor_set_uint8(v_data_1607_, sizeof(void*)*3 + 16, v_collapsed_1554_);
v___y_1572_ = v___y_1593_;
v___y_1573_ = v_m_1602_;
v_data_1574_ = v_data_1607_;
goto v___jp_1571_;
}
}
}
}
v___jp_1612_:
{
lean_object* v_ref_1613_; lean_object* v___x_1614_; 
v_ref_1613_ = lean_ctor_get(v___y_1563_, 5);
lean_inc(v___y_1564_);
lean_inc_ref(v___y_1563_);
lean_inc(v___y_1562_);
lean_inc_ref(v___y_1561_);
lean_inc(v_fst_1566_);
v___x_1614_ = lean_apply_6(v_msg_1559_, v_fst_1566_, v___y_1561_, v___y_1562_, v___y_1563_, v___y_1564_, lean_box(0));
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref(v___x_1614_);
v___y_1593_ = v_ref_1613_;
v_a_1594_ = v_a_1615_;
goto v___jp_1592_;
}
else
{
lean_object* v___x_1616_; 
lean_dec_ref(v___x_1614_);
v___x_1616_ = lean_obj_once(&l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3, &l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3_once, _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___closed__3);
v___y_1593_ = v_ref_1613_;
v_a_1594_ = v___x_1616_;
goto v___jp_1592_;
}
}
v___jp_1617_:
{
if (v_clsEnabled_1557_ == 0)
{
if (v___y_1618_ == 0)
{
lean_object* v___x_1619_; lean_object* v_traceState_1620_; lean_object* v_env_1621_; lean_object* v_nextMacroScope_1622_; lean_object* v_ngen_1623_; lean_object* v_auxDeclNGen_1624_; lean_object* v_cache_1625_; lean_object* v_messages_1626_; lean_object* v_infoState_1627_; lean_object* v_snapshotTasks_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1647_; 
lean_del_object(v___x_1588_);
lean_dec(v_snd_1586_);
lean_dec(v_fst_1585_);
lean_del_object(v___x_1569_);
lean_dec_ref(v_msg_1559_);
lean_dec_ref(v_tag_1555_);
lean_dec(v_cls_1553_);
v___x_1619_ = lean_st_ref_take(v___y_1564_);
v_traceState_1620_ = lean_ctor_get(v___x_1619_, 4);
v_env_1621_ = lean_ctor_get(v___x_1619_, 0);
v_nextMacroScope_1622_ = lean_ctor_get(v___x_1619_, 1);
v_ngen_1623_ = lean_ctor_get(v___x_1619_, 2);
v_auxDeclNGen_1624_ = lean_ctor_get(v___x_1619_, 3);
v_cache_1625_ = lean_ctor_get(v___x_1619_, 5);
v_messages_1626_ = lean_ctor_get(v___x_1619_, 6);
v_infoState_1627_ = lean_ctor_get(v___x_1619_, 7);
v_snapshotTasks_1628_ = lean_ctor_get(v___x_1619_, 8);
v_isSharedCheck_1647_ = !lean_is_exclusive(v___x_1619_);
if (v_isSharedCheck_1647_ == 0)
{
v___x_1630_ = v___x_1619_;
v_isShared_1631_ = v_isSharedCheck_1647_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_snapshotTasks_1628_);
lean_inc(v_infoState_1627_);
lean_inc(v_messages_1626_);
lean_inc(v_cache_1625_);
lean_inc(v_traceState_1620_);
lean_inc(v_auxDeclNGen_1624_);
lean_inc(v_ngen_1623_);
lean_inc(v_nextMacroScope_1622_);
lean_inc(v_env_1621_);
lean_dec(v___x_1619_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1647_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
uint64_t v_tid_1632_; lean_object* v_traces_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1646_; 
v_tid_1632_ = lean_ctor_get_uint64(v_traceState_1620_, sizeof(void*)*1);
v_traces_1633_ = lean_ctor_get(v_traceState_1620_, 0);
v_isSharedCheck_1646_ = !lean_is_exclusive(v_traceState_1620_);
if (v_isSharedCheck_1646_ == 0)
{
v___x_1635_ = v_traceState_1620_;
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_traces_1633_);
lean_dec(v_traceState_1620_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1646_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
lean_object* v___x_1637_; lean_object* v___x_1639_; 
v___x_1637_ = l_Lean_PersistentArray_append___redArg(v_oldTraces_1558_, v_traces_1633_);
lean_dec_ref(v_traces_1633_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1637_);
v___x_1639_ = v___x_1635_;
goto v_reusejp_1638_;
}
else
{
lean_object* v_reuseFailAlloc_1645_; 
v_reuseFailAlloc_1645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_1645_, 0, v___x_1637_);
lean_ctor_set_uint64(v_reuseFailAlloc_1645_, sizeof(void*)*1, v_tid_1632_);
v___x_1639_ = v_reuseFailAlloc_1645_;
goto v_reusejp_1638_;
}
v_reusejp_1638_:
{
lean_object* v___x_1641_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 4, v___x_1639_);
v___x_1641_ = v___x_1630_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_env_1621_);
lean_ctor_set(v_reuseFailAlloc_1644_, 1, v_nextMacroScope_1622_);
lean_ctor_set(v_reuseFailAlloc_1644_, 2, v_ngen_1623_);
lean_ctor_set(v_reuseFailAlloc_1644_, 3, v_auxDeclNGen_1624_);
lean_ctor_set(v_reuseFailAlloc_1644_, 4, v___x_1639_);
lean_ctor_set(v_reuseFailAlloc_1644_, 5, v_cache_1625_);
lean_ctor_set(v_reuseFailAlloc_1644_, 6, v_messages_1626_);
lean_ctor_set(v_reuseFailAlloc_1644_, 7, v_infoState_1627_);
lean_ctor_set(v_reuseFailAlloc_1644_, 8, v_snapshotTasks_1628_);
v___x_1641_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1642_ = lean_st_ref_set(v___y_1564_, v___x_1641_);
v___x_1643_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_fst_1566_);
return v___x_1643_;
}
}
}
}
}
else
{
goto v___jp_1612_;
}
}
else
{
goto v___jp_1612_;
}
}
v___jp_1648_:
{
double v___x_1650_; double v___x_1651_; double v___x_1652_; uint8_t v___x_1653_; 
v___x_1650_ = lean_unbox_float(v_snd_1586_);
v___x_1651_ = lean_unbox_float(v_fst_1585_);
v___x_1652_ = lean_float_sub(v___x_1650_, v___x_1651_);
v___x_1653_ = lean_float_decLt(v___y_1649_, v___x_1652_);
v___y_1618_ = v___x_1653_;
goto v___jp_1617_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15___boxed(lean_object* v_cls_1666_, lean_object* v_collapsed_1667_, lean_object* v_tag_1668_, lean_object* v_opts_1669_, lean_object* v_clsEnabled_1670_, lean_object* v_oldTraces_1671_, lean_object* v_msg_1672_, lean_object* v_resStartStop_1673_, lean_object* v___y_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
uint8_t v_collapsed_boxed_1679_; uint8_t v_clsEnabled_boxed_1680_; lean_object* v_res_1681_; 
v_collapsed_boxed_1679_ = lean_unbox(v_collapsed_1667_);
v_clsEnabled_boxed_1680_ = lean_unbox(v_clsEnabled_1670_);
v_res_1681_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_1666_, v_collapsed_boxed_1679_, v_tag_1668_, v_opts_1669_, v_clsEnabled_boxed_1680_, v_oldTraces_1671_, v_msg_1672_, v_resStartStop_1673_, v___y_1674_, v___y_1675_, v___y_1676_, v___y_1677_);
lean_dec(v___y_1677_);
lean_dec_ref(v___y_1676_);
lean_dec(v___y_1675_);
lean_dec_ref(v___y_1674_);
lean_dec_ref(v_opts_1669_);
return v_res_1681_;
}
}
static uint64_t _init_l_Lean_Meta_wrapInstance___closed__0(void){
_start:
{
uint8_t v___x_1682_; uint64_t v___x_1683_; 
v___x_1682_ = 3;
v___x_1683_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1682_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4(void){
_start:
{
lean_object* v_cls_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_cls_1690_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_1691_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__3));
v___x_1692_ = l_Lean_Name_append(v___x_1691_, v_cls_1690_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6(void){
_start:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1694_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__5));
v___x_1695_ = l_Lean_stringToMessageData(v___x_1694_);
return v___x_1695_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_1697_; lean_object* v___x_1698_; 
v___x_1697_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__0));
v___x_1698_ = l_Lean_stringToMessageData(v___x_1697_);
return v___x_1698_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3(void){
_start:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1700_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__2));
v___x_1701_ = l_Lean_stringToMessageData(v___x_1700_);
return v___x_1701_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5(void){
_start:
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__4));
v___x_1704_ = l_Lean_stringToMessageData(v___x_1703_);
return v___x_1704_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1706_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__6));
v___x_1707_ = l_Lean_stringToMessageData(v___x_1706_);
return v___x_1707_;
}
}
static lean_object* _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1709_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__8));
v___x_1710_ = l_Lean_stringToMessageData(v___x_1709_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(lean_object* v_upperBound_1711_, lean_object* v_fst_1712_, lean_object* v_args_1713_, uint8_t v_compile_1714_, uint8_t v_logCompileErrors_1715_, uint8_t v_isMeta_1716_, uint8_t v___x_1717_, lean_object* v_a_1718_, lean_object* v_b_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
lean_object* v_a_1726_; lean_object* v___y_1731_; uint8_t v___x_1750_; 
v___x_1750_ = lean_nat_dec_lt(v_a_1718_, v_upperBound_1711_);
if (v___x_1750_ == 0)
{
lean_object* v___x_1751_; 
lean_dec(v_a_1718_);
v___x_1751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1751_, 0, v_b_1719_);
return v___x_1751_;
}
else
{
lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; 
v___x_1752_ = lean_array_fget_borrowed(v_fst_1712_, v_a_1718_);
v___x_1753_ = l_Lean_Expr_mvarId_x21(v___x_1752_);
lean_inc(v___x_1753_);
v___x_1754_ = l_Lean_MVarId_getDecl(v___x_1753_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1754_) == 0)
{
lean_object* v_a_1755_; lean_object* v_type_1756_; lean_object* v___x_1757_; 
v_a_1755_ = lean_ctor_get(v___x_1754_, 0);
lean_inc(v_a_1755_);
lean_dec_ref(v___x_1754_);
v_type_1756_ = lean_ctor_get(v_a_1755_, 2);
lean_inc_ref(v_type_1756_);
lean_dec(v_a_1755_);
v___x_1757_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_1756_, v___y_1721_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v___x_1759_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc_n(v_a_1758_, 2);
lean_dec_ref(v___x_1757_);
v___x_1759_ = l_Lean_Meta_isProp(v_a_1758_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1761_; lean_object* v_cls_1762_; lean_object* v___x_1763_; uint8_t v___x_1764_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
lean_inc(v_a_1760_);
lean_dec_ref(v___x_1759_);
v___x_1761_ = lean_box(0);
v_cls_1762_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_1763_ = lean_array_fget_borrowed(v_args_1713_, v_a_1718_);
v___x_1764_ = lean_unbox(v_a_1760_);
lean_dec(v_a_1760_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
lean_inc(v_a_1758_);
v___x_1765_ = l_Lean_Meta_isClass_x3f(v_a_1758_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1765_) == 0)
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1897_; 
v_a_1766_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1768_ = v___x_1765_;
v_isShared_1769_ = v_isSharedCheck_1897_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1765_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1897_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
if (lean_obj_tag(v_a_1766_) == 0)
{
lean_object* v_options_1770_; lean_object* v___x_1771_; uint8_t v___x_1772_; 
lean_del_object(v___x_1768_);
v_options_1770_ = lean_ctor_get(v___y_1722_, 2);
v___x_1771_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_1772_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1770_, v___x_1771_);
if (v___x_1772_ == 0)
{
lean_object* v___x_1773_; 
lean_dec(v_a_1758_);
lean_inc(v___x_1763_);
v___x_1773_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1753_, v___x_1763_, v___y_1721_);
if (lean_obj_tag(v___x_1773_) == 0)
{
lean_dec_ref(v___x_1773_);
v_a_1726_ = v___x_1761_;
goto v___jp_1725_;
}
else
{
lean_dec(v_a_1718_);
return v___x_1773_;
}
}
else
{
lean_object* v___x_1774_; 
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___x_1763_);
v___x_1774_ = lean_infer_type(v___x_1763_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1774_) == 0)
{
lean_object* v_a_1775_; lean_object* v___x_1776_; 
v_a_1775_ = lean_ctor_get(v___x_1774_, 0);
lean_inc(v_a_1775_);
lean_dec_ref(v___x_1774_);
lean_inc(v_a_1758_);
v___x_1776_ = l_Lean_Meta_isExprDefEq(v_a_1758_, v_a_1775_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; uint8_t v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref(v___x_1776_);
v___x_1778_ = lean_unbox(v_a_1777_);
lean_dec(v_a_1777_);
if (v___x_1778_ == 0)
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
v___x_1779_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_1780_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_1779_, v___y_1723_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc_n(v_a_1781_, 2);
lean_dec_ref(v___x_1780_);
lean_inc(v___x_1763_);
v___x_1782_ = l_Lean_Meta_mkAuxDefinition(v_a_1781_, v_a_1758_, v___x_1763_, v___x_1717_, v___x_1717_, v___x_1750_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1782_) == 0)
{
lean_object* v_a_1783_; lean_object* v___x_1784_; 
v_a_1783_ = lean_ctor_get(v___x_1782_, 0);
lean_inc(v_a_1783_);
lean_dec_ref(v___x_1782_);
v___x_1784_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1753_, v_a_1783_, v___y_1721_);
if (lean_obj_tag(v___x_1784_) == 0)
{
uint8_t v___x_1785_; lean_object* v___x_1786_; 
lean_dec_ref(v___x_1784_);
v___x_1785_ = 0;
lean_inc(v_a_1781_);
v___x_1786_ = l_Lean_Meta_setInlineAttribute(v_a_1781_, v___x_1785_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1786_) == 0)
{
lean_dec_ref(v___x_1786_);
if (v_isMeta_1716_ == 0)
{
lean_object* v___x_1787_; 
v___x_1787_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1781_, v___x_1761_, v_compile_1714_, v_logCompileErrors_1715_, v___x_1761_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1787_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1788_; lean_object* v_env_1789_; lean_object* v_nextMacroScope_1790_; lean_object* v_ngen_1791_; lean_object* v_auxDeclNGen_1792_; lean_object* v_traceState_1793_; lean_object* v_messages_1794_; lean_object* v_infoState_1795_; lean_object* v_snapshotTasks_1796_; lean_object* v___x_1798_; uint8_t v_isShared_1799_; uint8_t v_isSharedCheck_1822_; 
v___x_1788_ = lean_st_ref_take(v___y_1723_);
v_env_1789_ = lean_ctor_get(v___x_1788_, 0);
v_nextMacroScope_1790_ = lean_ctor_get(v___x_1788_, 1);
v_ngen_1791_ = lean_ctor_get(v___x_1788_, 2);
v_auxDeclNGen_1792_ = lean_ctor_get(v___x_1788_, 3);
v_traceState_1793_ = lean_ctor_get(v___x_1788_, 4);
v_messages_1794_ = lean_ctor_get(v___x_1788_, 6);
v_infoState_1795_ = lean_ctor_get(v___x_1788_, 7);
v_snapshotTasks_1796_ = lean_ctor_get(v___x_1788_, 8);
v_isSharedCheck_1822_ = !lean_is_exclusive(v___x_1788_);
if (v_isSharedCheck_1822_ == 0)
{
lean_object* v_unused_1823_; 
v_unused_1823_ = lean_ctor_get(v___x_1788_, 5);
lean_dec(v_unused_1823_);
v___x_1798_ = v___x_1788_;
v_isShared_1799_ = v_isSharedCheck_1822_;
goto v_resetjp_1797_;
}
else
{
lean_inc(v_snapshotTasks_1796_);
lean_inc(v_infoState_1795_);
lean_inc(v_messages_1794_);
lean_inc(v_traceState_1793_);
lean_inc(v_auxDeclNGen_1792_);
lean_inc(v_ngen_1791_);
lean_inc(v_nextMacroScope_1790_);
lean_inc(v_env_1789_);
lean_dec(v___x_1788_);
v___x_1798_ = lean_box(0);
v_isShared_1799_ = v_isSharedCheck_1822_;
goto v_resetjp_1797_;
}
v_resetjp_1797_:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1803_; 
lean_inc(v_a_1781_);
v___x_1800_ = l_Lean_markMeta(v_env_1789_, v_a_1781_);
v___x_1801_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_1799_ == 0)
{
lean_ctor_set(v___x_1798_, 5, v___x_1801_);
lean_ctor_set(v___x_1798_, 0, v___x_1800_);
v___x_1803_ = v___x_1798_;
goto v_reusejp_1802_;
}
else
{
lean_object* v_reuseFailAlloc_1821_; 
v_reuseFailAlloc_1821_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1800_);
lean_ctor_set(v_reuseFailAlloc_1821_, 1, v_nextMacroScope_1790_);
lean_ctor_set(v_reuseFailAlloc_1821_, 2, v_ngen_1791_);
lean_ctor_set(v_reuseFailAlloc_1821_, 3, v_auxDeclNGen_1792_);
lean_ctor_set(v_reuseFailAlloc_1821_, 4, v_traceState_1793_);
lean_ctor_set(v_reuseFailAlloc_1821_, 5, v___x_1801_);
lean_ctor_set(v_reuseFailAlloc_1821_, 6, v_messages_1794_);
lean_ctor_set(v_reuseFailAlloc_1821_, 7, v_infoState_1795_);
lean_ctor_set(v_reuseFailAlloc_1821_, 8, v_snapshotTasks_1796_);
v___x_1803_ = v_reuseFailAlloc_1821_;
goto v_reusejp_1802_;
}
v_reusejp_1802_:
{
lean_object* v___x_1804_; lean_object* v___x_1805_; lean_object* v_mctx_1806_; lean_object* v_zetaDeltaFVarIds_1807_; lean_object* v_postponed_1808_; lean_object* v_diag_1809_; lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1819_; 
v___x_1804_ = lean_st_ref_set(v___y_1723_, v___x_1803_);
v___x_1805_ = lean_st_ref_take(v___y_1721_);
v_mctx_1806_ = lean_ctor_get(v___x_1805_, 0);
v_zetaDeltaFVarIds_1807_ = lean_ctor_get(v___x_1805_, 2);
v_postponed_1808_ = lean_ctor_get(v___x_1805_, 3);
v_diag_1809_ = lean_ctor_get(v___x_1805_, 4);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1819_ == 0)
{
lean_object* v_unused_1820_; 
v_unused_1820_ = lean_ctor_get(v___x_1805_, 1);
lean_dec(v_unused_1820_);
v___x_1811_ = v___x_1805_;
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
else
{
lean_inc(v_diag_1809_);
lean_inc(v_postponed_1808_);
lean_inc(v_zetaDeltaFVarIds_1807_);
lean_inc(v_mctx_1806_);
lean_dec(v___x_1805_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1819_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1813_; lean_object* v___x_1815_; 
v___x_1813_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 1, v___x_1813_);
v___x_1815_ = v___x_1811_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_mctx_1806_);
lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1813_);
lean_ctor_set(v_reuseFailAlloc_1818_, 2, v_zetaDeltaFVarIds_1807_);
lean_ctor_set(v_reuseFailAlloc_1818_, 3, v_postponed_1808_);
lean_ctor_set(v_reuseFailAlloc_1818_, 4, v_diag_1809_);
v___x_1815_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
lean_object* v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = lean_st_ref_set(v___y_1721_, v___x_1815_);
v___x_1817_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_1781_, v___x_1761_, v_compile_1714_, v_logCompileErrors_1715_, v___x_1761_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1817_;
goto v___jp_1730_;
}
}
}
}
}
}
else
{
lean_dec(v_a_1781_);
lean_dec(v_a_1718_);
return v___x_1786_;
}
}
else
{
lean_dec(v_a_1781_);
lean_dec(v_a_1718_);
return v___x_1784_;
}
}
else
{
lean_object* v_a_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_1831_; 
lean_dec(v_a_1781_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1824_ = lean_ctor_get(v___x_1782_, 0);
v_isSharedCheck_1831_ = !lean_is_exclusive(v___x_1782_);
if (v_isSharedCheck_1831_ == 0)
{
v___x_1826_ = v___x_1782_;
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_a_1824_);
lean_dec(v___x_1782_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_1831_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v___x_1829_; 
if (v_isShared_1827_ == 0)
{
v___x_1829_ = v___x_1826_;
goto v_reusejp_1828_;
}
else
{
lean_object* v_reuseFailAlloc_1830_; 
v_reuseFailAlloc_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1830_, 0, v_a_1824_);
v___x_1829_ = v_reuseFailAlloc_1830_;
goto v_reusejp_1828_;
}
v_reusejp_1828_:
{
return v___x_1829_;
}
}
}
}
else
{
lean_object* v_a_1832_; lean_object* v___x_1834_; uint8_t v_isShared_1835_; uint8_t v_isSharedCheck_1839_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1832_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1839_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1839_ == 0)
{
v___x_1834_ = v___x_1780_;
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
else
{
lean_inc(v_a_1832_);
lean_dec(v___x_1780_);
v___x_1834_ = lean_box(0);
v_isShared_1835_ = v_isSharedCheck_1839_;
goto v_resetjp_1833_;
}
v_resetjp_1833_:
{
lean_object* v___x_1837_; 
if (v_isShared_1835_ == 0)
{
v___x_1837_ = v___x_1834_;
goto v_reusejp_1836_;
}
else
{
lean_object* v_reuseFailAlloc_1838_; 
v_reuseFailAlloc_1838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1838_, 0, v_a_1832_);
v___x_1837_ = v_reuseFailAlloc_1838_;
goto v_reusejp_1836_;
}
v_reusejp_1836_:
{
return v___x_1837_;
}
}
}
}
else
{
lean_object* v___x_1840_; 
lean_dec(v_a_1758_);
lean_inc(v___x_1763_);
v___x_1840_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1753_, v___x_1763_, v___y_1721_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_dec_ref(v___x_1840_);
v_a_1726_ = v___x_1761_;
goto v___jp_1725_;
}
else
{
lean_dec(v_a_1718_);
return v___x_1840_;
}
}
}
else
{
lean_object* v_a_1841_; lean_object* v___x_1843_; uint8_t v_isShared_1844_; uint8_t v_isSharedCheck_1848_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1841_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1848_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1848_ == 0)
{
v___x_1843_ = v___x_1776_;
v_isShared_1844_ = v_isSharedCheck_1848_;
goto v_resetjp_1842_;
}
else
{
lean_inc(v_a_1841_);
lean_dec(v___x_1776_);
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
}
else
{
lean_object* v_a_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1856_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1849_ = lean_ctor_get(v___x_1774_, 0);
v_isSharedCheck_1856_ = !lean_is_exclusive(v___x_1774_);
if (v_isSharedCheck_1856_ == 0)
{
v___x_1851_ = v___x_1774_;
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_a_1849_);
lean_dec(v___x_1774_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1856_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
lean_object* v___x_1854_; 
if (v_isShared_1852_ == 0)
{
v___x_1854_ = v___x_1851_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v_a_1849_);
v___x_1854_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
return v___x_1854_;
}
}
}
}
}
else
{
lean_object* v_options_1857_; lean_object* v_inheritedTraceOptions_1858_; lean_object* v_a_1860_; lean_object* v___y_1863_; uint8_t v___y_1864_; lean_object* v_a_1869_; lean_object* v___y_1873_; lean_object* v___x_1877_; uint8_t v___x_1878_; 
lean_dec_ref(v_a_1766_);
v_options_1857_ = lean_ctor_get(v___y_1722_, 2);
v_inheritedTraceOptions_1858_ = lean_ctor_get(v___y_1722_, 13);
v___x_1877_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_1878_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_1857_, v___x_1877_);
if (v___x_1878_ == 0)
{
lean_object* v___x_1879_; 
lean_del_object(v___x_1768_);
lean_inc(v___x_1763_);
v___x_1879_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_1763_, v_a_1758_, v_compile_1714_, v_logCompileErrors_1715_, v_isMeta_1716_, v___x_1753_, v___x_1761_, v___x_1761_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1879_;
goto v___jp_1730_;
}
else
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_box(0);
lean_inc(v_a_1758_);
v___x_1881_ = l_Lean_Meta_trySynthInstance(v_a_1758_, v___x_1880_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref(v___x_1881_);
if (lean_obj_tag(v_a_1882_) == 1)
{
lean_object* v_a_1883_; uint8_t v_hasTrace_1884_; 
v_a_1883_ = lean_ctor_get(v_a_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v_a_1882_);
v_hasTrace_1884_ = lean_ctor_get_uint8(v_options_1857_, sizeof(void*)*1);
if (v_hasTrace_1884_ == 0)
{
goto v___jp_1885_;
}
else
{
lean_object* v___x_1887_; uint8_t v___x_1888_; 
v___x_1887_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_1888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1858_, v_options_1857_, v___x_1887_);
if (v___x_1888_ == 0)
{
goto v___jp_1885_;
}
else
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_1883_);
v___x_1890_ = l_Lean_MessageData_ofExpr(v_a_1883_);
v___x_1891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1889_);
lean_ctor_set(v___x_1891_, 1, v___x_1890_);
v___x_1892_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1762_, v___x_1891_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v_a_1893_; lean_object* v___x_1894_; 
v_a_1893_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1893_);
lean_dec_ref(v___x_1892_);
lean_inc(v___x_1753_);
v___x_1894_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1753_, v_a_1883_, v_a_1893_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1873_ = v___x_1894_;
goto v___jp_1872_;
}
else
{
lean_object* v_a_1895_; 
lean_dec(v_a_1883_);
v_a_1895_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_a_1895_);
lean_dec_ref(v___x_1892_);
v_a_1869_ = v_a_1895_;
goto v___jp_1868_;
}
}
}
v___jp_1885_:
{
lean_object* v___x_1886_; 
lean_inc(v___x_1753_);
v___x_1886_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_1753_, v_a_1883_, v___x_1761_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1873_ = v___x_1886_;
goto v___jp_1872_;
}
}
else
{
lean_dec(v_a_1882_);
lean_del_object(v___x_1768_);
v_a_1860_ = v___x_1761_;
goto v___jp_1859_;
}
}
else
{
lean_object* v_a_1896_; 
v_a_1896_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1881_);
v_a_1869_ = v_a_1896_;
goto v___jp_1868_;
}
}
v___jp_1859_:
{
lean_object* v___x_1861_; 
lean_inc(v___x_1763_);
v___x_1861_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_1763_, v_a_1758_, v_compile_1714_, v_logCompileErrors_1715_, v_isMeta_1716_, v___x_1753_, v___x_1761_, v_a_1860_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1861_;
goto v___jp_1730_;
}
v___jp_1862_:
{
if (v___y_1864_ == 0)
{
lean_dec_ref(v___y_1863_);
lean_del_object(v___x_1768_);
v_a_1860_ = v___x_1761_;
goto v___jp_1859_;
}
else
{
lean_object* v___x_1866_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
if (v_isShared_1769_ == 0)
{
lean_ctor_set_tag(v___x_1768_, 1);
lean_ctor_set(v___x_1768_, 0, v___y_1863_);
v___x_1866_ = v___x_1768_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v___y_1863_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
v___jp_1868_:
{
uint8_t v___x_1870_; 
v___x_1870_ = l_Lean_Exception_isInterrupt(v_a_1869_);
if (v___x_1870_ == 0)
{
uint8_t v___x_1871_; 
lean_inc_ref(v_a_1869_);
v___x_1871_ = l_Lean_Exception_isRuntime(v_a_1869_);
v___y_1863_ = v_a_1869_;
v___y_1864_ = v___x_1871_;
goto v___jp_1862_;
}
else
{
v___y_1863_ = v_a_1869_;
v___y_1864_ = v___x_1870_;
goto v___jp_1862_;
}
}
v___jp_1872_:
{
if (lean_obj_tag(v___y_1873_) == 0)
{
lean_object* v_a_1874_; 
lean_del_object(v___x_1768_);
v_a_1874_ = lean_ctor_get(v___y_1873_, 0);
lean_inc(v_a_1874_);
lean_dec_ref(v___y_1873_);
if (lean_obj_tag(v_a_1874_) == 0)
{
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
v_a_1726_ = v___x_1761_;
goto v___jp_1725_;
}
else
{
lean_object* v_a_1875_; 
v_a_1875_ = lean_ctor_get(v_a_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v_a_1874_);
v_a_1860_ = v_a_1875_;
goto v___jp_1859_;
}
}
else
{
lean_object* v_a_1876_; 
v_a_1876_ = lean_ctor_get(v___y_1873_, 0);
lean_inc(v_a_1876_);
lean_dec_ref(v___y_1873_);
v_a_1869_ = v_a_1876_;
goto v___jp_1868_;
}
}
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1898_ = lean_ctor_get(v___x_1765_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1765_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1765_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
else
{
lean_object* v___x_1906_; 
lean_inc(v___y_1723_);
lean_inc_ref(v___y_1722_);
lean_inc(v___y_1721_);
lean_inc_ref(v___y_1720_);
lean_inc(v___x_1763_);
v___x_1906_ = lean_infer_type(v___x_1763_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_object* v_a_1907_; lean_object* v___x_1908_; 
v_a_1907_ = lean_ctor_get(v___x_1906_, 0);
lean_inc_n(v_a_1907_, 2);
lean_dec_ref(v___x_1906_);
lean_inc(v_a_1758_);
v___x_1908_ = l_Lean_Meta_isExprDefEq(v_a_1758_, v_a_1907_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1908_) == 0)
{
lean_object* v_a_1909_; uint8_t v___x_1910_; 
v_a_1909_ = lean_ctor_get(v___x_1908_, 0);
lean_inc(v_a_1909_);
lean_dec_ref(v___x_1908_);
v___x_1910_ = lean_unbox(v_a_1909_);
lean_dec(v_a_1909_);
if (v___x_1910_ == 0)
{
lean_object* v_options_1911_; lean_object* v_inheritedTraceOptions_1912_; uint8_t v_hasTrace_1913_; 
v_options_1911_ = lean_ctor_get(v___y_1722_, 2);
v_inheritedTraceOptions_1912_ = lean_ctor_get(v___y_1722_, 13);
v_hasTrace_1913_ = lean_ctor_get_uint8(v_options_1911_, sizeof(void*)*1);
if (v_hasTrace_1913_ == 0)
{
lean_dec(v_a_1907_);
goto v___jp_1914_;
}
else
{
lean_object* v___x_1916_; uint8_t v___x_1917_; 
v___x_1916_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_1917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_1912_, v_options_1911_, v___x_1916_);
if (v___x_1917_ == 0)
{
lean_dec(v_a_1907_);
goto v___jp_1914_;
}
else
{
lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1918_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_1718_);
v___x_1919_ = l_Nat_reprFast(v_a_1718_);
v___x_1920_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_1920_, 0, v___x_1919_);
v___x_1921_ = l_Lean_MessageData_ofFormat(v___x_1920_);
v___x_1922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1918_);
lean_ctor_set(v___x_1922_, 1, v___x_1921_);
v___x_1923_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_1924_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1924_, 0, v___x_1922_);
lean_ctor_set(v___x_1924_, 1, v___x_1923_);
lean_inc(v_a_1758_);
v___x_1925_ = l_Lean_MessageData_ofExpr(v_a_1758_);
v___x_1926_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1926_, 0, v___x_1924_);
lean_ctor_set(v___x_1926_, 1, v___x_1925_);
v___x_1927_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_1928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1926_);
lean_ctor_set(v___x_1928_, 1, v___x_1927_);
v___x_1929_ = l_Lean_MessageData_ofExpr(v_a_1907_);
v___x_1930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1930_, 0, v___x_1928_);
lean_ctor_set(v___x_1930_, 1, v___x_1929_);
v___x_1931_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_1932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1930_);
lean_ctor_set(v___x_1932_, 1, v___x_1931_);
lean_inc(v___x_1763_);
v___x_1933_ = l_Lean_MessageData_ofExpr(v___x_1763_);
v___x_1934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1934_, 0, v___x_1932_);
lean_ctor_set(v___x_1934_, 1, v___x_1933_);
v___x_1935_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_1762_, v___x_1934_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
if (lean_obj_tag(v___x_1935_) == 0)
{
lean_object* v_a_1936_; lean_object* v___x_1937_; 
v_a_1936_ = lean_ctor_get(v___x_1935_, 0);
lean_inc(v_a_1936_);
lean_dec_ref(v___x_1935_);
lean_inc(v___x_1763_);
v___x_1937_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1758_, v___x_1763_, v___x_1750_, v___x_1753_, v___x_1761_, v_a_1936_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1937_;
goto v___jp_1730_;
}
else
{
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
return v___x_1935_;
}
}
}
v___jp_1914_:
{
lean_object* v___x_1915_; 
lean_inc(v___x_1763_);
v___x_1915_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_1758_, v___x_1763_, v___x_1750_, v___x_1753_, v___x_1761_, v___x_1761_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
v___y_1731_ = v___x_1915_;
goto v___jp_1730_;
}
}
else
{
lean_object* v___x_1938_; 
lean_dec(v_a_1907_);
lean_dec(v_a_1758_);
lean_inc(v___x_1763_);
v___x_1938_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_1753_, v___x_1763_, v___y_1721_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_dec_ref(v___x_1938_);
v_a_1726_ = v___x_1761_;
goto v___jp_1725_;
}
else
{
lean_dec(v_a_1718_);
return v___x_1938_;
}
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_dec(v_a_1907_);
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1939_ = lean_ctor_get(v___x_1908_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1908_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1908_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1908_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_object* v_a_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1954_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1947_ = lean_ctor_get(v___x_1906_, 0);
v_isSharedCheck_1954_ = !lean_is_exclusive(v___x_1906_);
if (v_isSharedCheck_1954_ == 0)
{
v___x_1949_ = v___x_1906_;
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_a_1947_);
lean_dec(v___x_1906_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1954_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1950_ == 0)
{
v___x_1952_ = v___x_1949_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1953_; 
v_reuseFailAlloc_1953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1953_, 0, v_a_1947_);
v___x_1952_ = v_reuseFailAlloc_1953_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
return v___x_1952_;
}
}
}
}
}
else
{
lean_object* v_a_1955_; lean_object* v___x_1957_; uint8_t v_isShared_1958_; uint8_t v_isSharedCheck_1962_; 
lean_dec(v_a_1758_);
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1955_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1957_ = v___x_1759_;
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
else
{
lean_inc(v_a_1955_);
lean_dec(v___x_1759_);
v___x_1957_ = lean_box(0);
v_isShared_1958_ = v_isSharedCheck_1962_;
goto v_resetjp_1956_;
}
v_resetjp_1956_:
{
lean_object* v___x_1960_; 
if (v_isShared_1958_ == 0)
{
v___x_1960_ = v___x_1957_;
goto v_reusejp_1959_;
}
else
{
lean_object* v_reuseFailAlloc_1961_; 
v_reuseFailAlloc_1961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1961_, 0, v_a_1955_);
v___x_1960_ = v_reuseFailAlloc_1961_;
goto v_reusejp_1959_;
}
v_reusejp_1959_:
{
return v___x_1960_;
}
}
}
}
else
{
lean_object* v_a_1963_; lean_object* v___x_1965_; uint8_t v_isShared_1966_; uint8_t v_isSharedCheck_1970_; 
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1963_ = lean_ctor_get(v___x_1757_, 0);
v_isSharedCheck_1970_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1970_ == 0)
{
v___x_1965_ = v___x_1757_;
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
else
{
lean_inc(v_a_1963_);
lean_dec(v___x_1757_);
v___x_1965_ = lean_box(0);
v_isShared_1966_ = v_isSharedCheck_1970_;
goto v_resetjp_1964_;
}
v_resetjp_1964_:
{
lean_object* v___x_1968_; 
if (v_isShared_1966_ == 0)
{
v___x_1968_ = v___x_1965_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1969_; 
v_reuseFailAlloc_1969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1969_, 0, v_a_1963_);
v___x_1968_ = v_reuseFailAlloc_1969_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
return v___x_1968_;
}
}
}
}
else
{
lean_object* v_a_1971_; lean_object* v___x_1973_; uint8_t v_isShared_1974_; uint8_t v_isSharedCheck_1978_; 
lean_dec(v___x_1753_);
lean_dec(v_a_1718_);
v_a_1971_ = lean_ctor_get(v___x_1754_, 0);
v_isSharedCheck_1978_ = !lean_is_exclusive(v___x_1754_);
if (v_isSharedCheck_1978_ == 0)
{
v___x_1973_ = v___x_1754_;
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
else
{
lean_inc(v_a_1971_);
lean_dec(v___x_1754_);
v___x_1973_ = lean_box(0);
v_isShared_1974_ = v_isSharedCheck_1978_;
goto v_resetjp_1972_;
}
v_resetjp_1972_:
{
lean_object* v___x_1976_; 
if (v_isShared_1974_ == 0)
{
v___x_1976_ = v___x_1973_;
goto v_reusejp_1975_;
}
else
{
lean_object* v_reuseFailAlloc_1977_; 
v_reuseFailAlloc_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1977_, 0, v_a_1971_);
v___x_1976_ = v_reuseFailAlloc_1977_;
goto v_reusejp_1975_;
}
v_reusejp_1975_:
{
return v___x_1976_;
}
}
}
}
v___jp_1725_:
{
lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1727_ = lean_unsigned_to_nat(1u);
v___x_1728_ = lean_nat_add(v_a_1718_, v___x_1727_);
lean_dec(v_a_1718_);
v_a_1718_ = v___x_1728_;
v_b_1719_ = v_a_1726_;
goto _start;
}
v___jp_1730_:
{
if (lean_obj_tag(v___y_1731_) == 0)
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1741_; 
v_a_1732_ = lean_ctor_get(v___y_1731_, 0);
v_isSharedCheck_1741_ = !lean_is_exclusive(v___y_1731_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1734_ = v___y_1731_;
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___y_1731_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1741_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
if (lean_obj_tag(v_a_1732_) == 0)
{
lean_object* v_a_1736_; lean_object* v___x_1738_; 
lean_dec(v_a_1718_);
v_a_1736_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v_a_1732_);
if (v_isShared_1735_ == 0)
{
lean_ctor_set(v___x_1734_, 0, v_a_1736_);
v___x_1738_ = v___x_1734_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1736_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
else
{
lean_object* v_a_1740_; 
lean_del_object(v___x_1734_);
v_a_1740_ = lean_ctor_get(v_a_1732_, 0);
lean_inc(v_a_1740_);
lean_dec_ref(v_a_1732_);
v_a_1726_ = v_a_1740_;
goto v___jp_1725_;
}
}
}
else
{
lean_object* v_a_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1749_; 
lean_dec(v_a_1718_);
v_a_1742_ = lean_ctor_get(v___y_1731_, 0);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___y_1731_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1744_ = v___y_1731_;
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_a_1742_);
lean_dec(v___y_1731_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1749_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
lean_object* v___x_1747_; 
if (v_isShared_1745_ == 0)
{
v___x_1747_ = v___x_1744_;
goto v_reusejp_1746_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_a_1742_);
v___x_1747_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1746_;
}
v_reusejp_1746_:
{
return v___x_1747_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(lean_object* v_upperBound_1979_, lean_object* v_fst_1980_, lean_object* v_args_1981_, uint8_t v_compile_1982_, uint8_t v_logCompileErrors_1983_, uint8_t v_isMeta_1984_, uint8_t v___x_1985_, lean_object* v_a_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_a_1994_; lean_object* v___y_1999_; uint8_t v___x_2018_; 
v___x_2018_ = lean_nat_dec_lt(v_a_1986_, v_upperBound_1979_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
lean_dec(v_a_1986_);
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_b_1987_);
return v___x_2019_;
}
else
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2020_ = lean_array_fget_borrowed(v_fst_1980_, v_a_1986_);
v___x_2021_ = l_Lean_Expr_mvarId_x21(v___x_2020_);
lean_inc(v___x_2021_);
v___x_2022_ = l_Lean_MVarId_getDecl(v___x_2021_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v_type_2024_; lean_object* v___x_2025_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref(v___x_2022_);
v_type_2024_ = lean_ctor_get(v_a_2023_, 2);
lean_inc_ref(v_type_2024_);
lean_dec(v_a_2023_);
v___x_2025_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2024_, v___y_1989_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc_n(v_a_2026_, 2);
lean_dec_ref(v___x_2025_);
v___x_2027_ = l_Lean_Meta_isProp(v_a_2026_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v_cls_2030_; lean_object* v___x_2031_; uint8_t v___x_2032_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref(v___x_2027_);
v___x_2029_ = lean_box(0);
v_cls_2030_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2031_ = lean_array_fget_borrowed(v_args_1981_, v_a_1986_);
v___x_2032_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2032_ == 0)
{
lean_object* v___x_2033_; 
lean_inc(v_a_2026_);
v___x_2033_ = l_Lean_Meta_isClass_x3f(v_a_2026_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2165_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2036_ = v___x_2033_;
v_isShared_2037_ = v_isSharedCheck_2165_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2033_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2165_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
if (lean_obj_tag(v_a_2034_) == 0)
{
lean_object* v_options_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; 
lean_del_object(v___x_2036_);
v_options_2038_ = lean_ctor_get(v___y_1990_, 2);
v___x_2039_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2040_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2038_, v___x_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; 
lean_dec(v_a_2026_);
lean_inc(v___x_2031_);
v___x_2041_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2021_, v___x_2031_, v___y_1989_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref(v___x_2041_);
v_a_1994_ = v___x_2029_;
goto v___jp_1993_;
}
else
{
lean_dec(v_a_1986_);
return v___x_2041_;
}
}
else
{
lean_object* v___x_2042_; 
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___x_2031_);
v___x_2042_ = lean_infer_type(v___x_2031_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref(v___x_2042_);
lean_inc(v_a_2026_);
v___x_2044_ = l_Lean_Meta_isExprDefEq(v_a_2026_, v_a_2043_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2044_) == 0)
{
lean_object* v_a_2045_; uint8_t v___x_2046_; 
v_a_2045_ = lean_ctor_get(v___x_2044_, 0);
lean_inc(v_a_2045_);
lean_dec_ref(v___x_2044_);
v___x_2046_ = lean_unbox(v_a_2045_);
lean_dec(v_a_2045_);
if (v___x_2046_ == 0)
{
lean_object* v___x_2047_; lean_object* v___x_2048_; 
v___x_2047_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2048_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2047_, v___y_1991_);
if (lean_obj_tag(v___x_2048_) == 0)
{
lean_object* v_a_2049_; lean_object* v___x_2050_; 
v_a_2049_ = lean_ctor_get(v___x_2048_, 0);
lean_inc_n(v_a_2049_, 2);
lean_dec_ref(v___x_2048_);
lean_inc(v___x_2031_);
v___x_2050_ = l_Lean_Meta_mkAuxDefinition(v_a_2049_, v_a_2026_, v___x_2031_, v___x_1985_, v___x_1985_, v___x_2018_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2050_) == 0)
{
lean_object* v_a_2051_; lean_object* v___x_2052_; 
v_a_2051_ = lean_ctor_get(v___x_2050_, 0);
lean_inc(v_a_2051_);
lean_dec_ref(v___x_2050_);
v___x_2052_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2021_, v_a_2051_, v___y_1989_);
if (lean_obj_tag(v___x_2052_) == 0)
{
uint8_t v___x_2053_; lean_object* v___x_2054_; 
lean_dec_ref(v___x_2052_);
v___x_2053_ = 0;
lean_inc(v_a_2049_);
v___x_2054_ = l_Lean_Meta_setInlineAttribute(v_a_2049_, v___x_2053_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2054_) == 0)
{
lean_dec_ref(v___x_2054_);
if (v_isMeta_1984_ == 0)
{
lean_object* v___x_2055_; 
v___x_2055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2049_, v___x_2029_, v_compile_1982_, v_logCompileErrors_1983_, v___x_2029_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2055_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2056_; lean_object* v_env_2057_; lean_object* v_nextMacroScope_2058_; lean_object* v_ngen_2059_; lean_object* v_auxDeclNGen_2060_; lean_object* v_traceState_2061_; lean_object* v_messages_2062_; lean_object* v_infoState_2063_; lean_object* v_snapshotTasks_2064_; lean_object* v___x_2066_; uint8_t v_isShared_2067_; uint8_t v_isSharedCheck_2090_; 
v___x_2056_ = lean_st_ref_take(v___y_1991_);
v_env_2057_ = lean_ctor_get(v___x_2056_, 0);
v_nextMacroScope_2058_ = lean_ctor_get(v___x_2056_, 1);
v_ngen_2059_ = lean_ctor_get(v___x_2056_, 2);
v_auxDeclNGen_2060_ = lean_ctor_get(v___x_2056_, 3);
v_traceState_2061_ = lean_ctor_get(v___x_2056_, 4);
v_messages_2062_ = lean_ctor_get(v___x_2056_, 6);
v_infoState_2063_ = lean_ctor_get(v___x_2056_, 7);
v_snapshotTasks_2064_ = lean_ctor_get(v___x_2056_, 8);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2090_ == 0)
{
lean_object* v_unused_2091_; 
v_unused_2091_ = lean_ctor_get(v___x_2056_, 5);
lean_dec(v_unused_2091_);
v___x_2066_ = v___x_2056_;
v_isShared_2067_ = v_isSharedCheck_2090_;
goto v_resetjp_2065_;
}
else
{
lean_inc(v_snapshotTasks_2064_);
lean_inc(v_infoState_2063_);
lean_inc(v_messages_2062_);
lean_inc(v_traceState_2061_);
lean_inc(v_auxDeclNGen_2060_);
lean_inc(v_ngen_2059_);
lean_inc(v_nextMacroScope_2058_);
lean_inc(v_env_2057_);
lean_dec(v___x_2056_);
v___x_2066_ = lean_box(0);
v_isShared_2067_ = v_isSharedCheck_2090_;
goto v_resetjp_2065_;
}
v_resetjp_2065_:
{
lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2071_; 
lean_inc(v_a_2049_);
v___x_2068_ = l_Lean_markMeta(v_env_2057_, v_a_2049_);
v___x_2069_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2067_ == 0)
{
lean_ctor_set(v___x_2066_, 5, v___x_2069_);
lean_ctor_set(v___x_2066_, 0, v___x_2068_);
v___x_2071_ = v___x_2066_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v___x_2068_);
lean_ctor_set(v_reuseFailAlloc_2089_, 1, v_nextMacroScope_2058_);
lean_ctor_set(v_reuseFailAlloc_2089_, 2, v_ngen_2059_);
lean_ctor_set(v_reuseFailAlloc_2089_, 3, v_auxDeclNGen_2060_);
lean_ctor_set(v_reuseFailAlloc_2089_, 4, v_traceState_2061_);
lean_ctor_set(v_reuseFailAlloc_2089_, 5, v___x_2069_);
lean_ctor_set(v_reuseFailAlloc_2089_, 6, v_messages_2062_);
lean_ctor_set(v_reuseFailAlloc_2089_, 7, v_infoState_2063_);
lean_ctor_set(v_reuseFailAlloc_2089_, 8, v_snapshotTasks_2064_);
v___x_2071_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v_mctx_2074_; lean_object* v_zetaDeltaFVarIds_2075_; lean_object* v_postponed_2076_; lean_object* v_diag_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2087_; 
v___x_2072_ = lean_st_ref_set(v___y_1991_, v___x_2071_);
v___x_2073_ = lean_st_ref_take(v___y_1989_);
v_mctx_2074_ = lean_ctor_get(v___x_2073_, 0);
v_zetaDeltaFVarIds_2075_ = lean_ctor_get(v___x_2073_, 2);
v_postponed_2076_ = lean_ctor_get(v___x_2073_, 3);
v_diag_2077_ = lean_ctor_get(v___x_2073_, 4);
v_isSharedCheck_2087_ = !lean_is_exclusive(v___x_2073_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v___x_2073_, 1);
lean_dec(v_unused_2088_);
v___x_2079_ = v___x_2073_;
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_diag_2077_);
lean_inc(v_postponed_2076_);
lean_inc(v_zetaDeltaFVarIds_2075_);
lean_inc(v_mctx_2074_);
lean_dec(v___x_2073_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2087_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2081_; lean_object* v___x_2083_; 
v___x_2081_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2080_ == 0)
{
lean_ctor_set(v___x_2079_, 1, v___x_2081_);
v___x_2083_ = v___x_2079_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_mctx_2074_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v___x_2081_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v_zetaDeltaFVarIds_2075_);
lean_ctor_set(v_reuseFailAlloc_2086_, 3, v_postponed_2076_);
lean_ctor_set(v_reuseFailAlloc_2086_, 4, v_diag_2077_);
v___x_2083_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2084_ = lean_st_ref_set(v___y_1989_, v___x_2083_);
v___x_2085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2049_, v___x_2029_, v_compile_1982_, v_logCompileErrors_1983_, v___x_2029_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2085_;
goto v___jp_1998_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2049_);
lean_dec(v_a_1986_);
return v___x_2054_;
}
}
else
{
lean_dec(v_a_2049_);
lean_dec(v_a_1986_);
return v___x_2052_;
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec(v_a_2049_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2092_ = lean_ctor_get(v___x_2050_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2050_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2050_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2050_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2100_ = lean_ctor_get(v___x_2048_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_2048_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_2048_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_2048_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
else
{
lean_object* v___x_2108_; 
lean_dec(v_a_2026_);
lean_inc(v___x_2031_);
v___x_2108_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2021_, v___x_2031_, v___y_1989_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_dec_ref(v___x_2108_);
v_a_1994_ = v___x_2029_;
goto v___jp_1993_;
}
else
{
lean_dec(v_a_1986_);
return v___x_2108_;
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2109_ = lean_ctor_get(v___x_2044_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2044_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2044_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2044_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2124_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2117_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2119_ = v___x_2042_;
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2042_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2124_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2120_ == 0)
{
v___x_2122_ = v___x_2119_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_a_2117_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
}
else
{
lean_object* v_options_2125_; lean_object* v_inheritedTraceOptions_2126_; lean_object* v_a_2128_; lean_object* v___y_2131_; uint8_t v___y_2132_; lean_object* v_a_2137_; lean_object* v___y_2141_; lean_object* v___x_2145_; uint8_t v___x_2146_; 
lean_dec_ref(v_a_2034_);
v_options_2125_ = lean_ctor_get(v___y_1990_, 2);
v_inheritedTraceOptions_2126_ = lean_ctor_get(v___y_1990_, 13);
v___x_2145_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2146_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2125_, v___x_2145_);
if (v___x_2146_ == 0)
{
lean_object* v___x_2147_; 
lean_del_object(v___x_2036_);
lean_inc(v___x_2031_);
v___x_2147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2031_, v_a_2026_, v_compile_1982_, v_logCompileErrors_1983_, v_isMeta_1984_, v___x_2021_, v___x_2029_, v___x_2029_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2147_;
goto v___jp_1998_;
}
else
{
lean_object* v___x_2148_; lean_object* v___x_2149_; 
v___x_2148_ = lean_box(0);
lean_inc(v_a_2026_);
v___x_2149_ = l_Lean_Meta_trySynthInstance(v_a_2026_, v___x_2148_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2150_);
lean_dec_ref(v___x_2149_);
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v_a_2151_; uint8_t v_hasTrace_2152_; 
v_a_2151_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_a_2151_);
lean_dec_ref(v_a_2150_);
v_hasTrace_2152_ = lean_ctor_get_uint8(v_options_2125_, sizeof(void*)*1);
if (v_hasTrace_2152_ == 0)
{
goto v___jp_2153_;
}
else
{
lean_object* v___x_2155_; uint8_t v___x_2156_; 
v___x_2155_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2126_, v_options_2125_, v___x_2155_);
if (v___x_2156_ == 0)
{
goto v___jp_2153_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; 
v___x_2157_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_2151_);
v___x_2158_ = l_Lean_MessageData_ofExpr(v_a_2151_);
v___x_2159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2159_, 0, v___x_2157_);
lean_ctor_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2030_, v___x_2159_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2162_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2161_);
lean_dec_ref(v___x_2160_);
lean_inc(v___x_2021_);
v___x_2162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2021_, v_a_2151_, v_a_2161_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_2141_ = v___x_2162_;
goto v___jp_2140_;
}
else
{
lean_object* v_a_2163_; 
lean_dec(v_a_2151_);
v_a_2163_ = lean_ctor_get(v___x_2160_, 0);
lean_inc(v_a_2163_);
lean_dec_ref(v___x_2160_);
v_a_2137_ = v_a_2163_;
goto v___jp_2136_;
}
}
}
v___jp_2153_:
{
lean_object* v___x_2154_; 
lean_inc(v___x_2021_);
v___x_2154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2021_, v_a_2151_, v___x_2029_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_2141_ = v___x_2154_;
goto v___jp_2140_;
}
}
else
{
lean_dec(v_a_2150_);
lean_del_object(v___x_2036_);
v_a_2128_ = v___x_2029_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2164_; 
v_a_2164_ = lean_ctor_get(v___x_2149_, 0);
lean_inc(v_a_2164_);
lean_dec_ref(v___x_2149_);
v_a_2137_ = v_a_2164_;
goto v___jp_2136_;
}
}
v___jp_2127_:
{
lean_object* v___x_2129_; 
lean_inc(v___x_2031_);
v___x_2129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2031_, v_a_2026_, v_compile_1982_, v_logCompileErrors_1983_, v_isMeta_1984_, v___x_2021_, v___x_2029_, v_a_2128_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2129_;
goto v___jp_1998_;
}
v___jp_2130_:
{
if (v___y_2132_ == 0)
{
lean_dec_ref(v___y_2131_);
lean_del_object(v___x_2036_);
v_a_2128_ = v___x_2029_;
goto v___jp_2127_;
}
else
{
lean_object* v___x_2134_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
if (v_isShared_2037_ == 0)
{
lean_ctor_set_tag(v___x_2036_, 1);
lean_ctor_set(v___x_2036_, 0, v___y_2131_);
v___x_2134_ = v___x_2036_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v___y_2131_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
v___jp_2136_:
{
uint8_t v___x_2138_; 
v___x_2138_ = l_Lean_Exception_isInterrupt(v_a_2137_);
if (v___x_2138_ == 0)
{
uint8_t v___x_2139_; 
lean_inc_ref(v_a_2137_);
v___x_2139_ = l_Lean_Exception_isRuntime(v_a_2137_);
v___y_2131_ = v_a_2137_;
v___y_2132_ = v___x_2139_;
goto v___jp_2130_;
}
else
{
v___y_2131_ = v_a_2137_;
v___y_2132_ = v___x_2138_;
goto v___jp_2130_;
}
}
v___jp_2140_:
{
if (lean_obj_tag(v___y_2141_) == 0)
{
lean_object* v_a_2142_; 
lean_del_object(v___x_2036_);
v_a_2142_ = lean_ctor_get(v___y_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref(v___y_2141_);
if (lean_obj_tag(v_a_2142_) == 0)
{
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
v_a_1994_ = v___x_2029_;
goto v___jp_1993_;
}
else
{
lean_object* v_a_2143_; 
v_a_2143_ = lean_ctor_get(v_a_2142_, 0);
lean_inc(v_a_2143_);
lean_dec_ref(v_a_2142_);
v_a_2128_ = v_a_2143_;
goto v___jp_2127_;
}
}
else
{
lean_object* v_a_2144_; 
v_a_2144_ = lean_ctor_get(v___y_2141_, 0);
lean_inc(v_a_2144_);
lean_dec_ref(v___y_2141_);
v_a_2137_ = v_a_2144_;
goto v___jp_2136_;
}
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2166_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2033_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2033_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v___x_2174_; 
lean_inc(v___y_1991_);
lean_inc_ref(v___y_1990_);
lean_inc(v___y_1989_);
lean_inc_ref(v___y_1988_);
lean_inc(v___x_2031_);
v___x_2174_ = lean_infer_type(v___x_2031_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; lean_object* v___x_2176_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc_n(v_a_2175_, 2);
lean_dec_ref(v___x_2174_);
lean_inc(v_a_2026_);
v___x_2176_ = l_Lean_Meta_isExprDefEq(v_a_2026_, v_a_2175_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; uint8_t v___x_2178_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref(v___x_2176_);
v___x_2178_ = lean_unbox(v_a_2177_);
lean_dec(v_a_2177_);
if (v___x_2178_ == 0)
{
lean_object* v_options_2179_; lean_object* v_inheritedTraceOptions_2180_; uint8_t v_hasTrace_2181_; 
v_options_2179_ = lean_ctor_get(v___y_1990_, 2);
v_inheritedTraceOptions_2180_ = lean_ctor_get(v___y_1990_, 13);
v_hasTrace_2181_ = lean_ctor_get_uint8(v_options_2179_, sizeof(void*)*1);
if (v_hasTrace_2181_ == 0)
{
lean_dec(v_a_2175_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2184_; uint8_t v___x_2185_; 
v___x_2184_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2180_, v_options_2179_, v___x_2184_);
if (v___x_2185_ == 0)
{
lean_dec(v_a_2175_);
goto v___jp_2182_;
}
else
{
lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; 
v___x_2186_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_1986_);
v___x_2187_ = l_Nat_reprFast(v_a_1986_);
v___x_2188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
v___x_2189_ = l_Lean_MessageData_ofFormat(v___x_2188_);
v___x_2190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2190_, 0, v___x_2186_);
lean_ctor_set(v___x_2190_, 1, v___x_2189_);
v___x_2191_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_2192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2192_, 0, v___x_2190_);
lean_ctor_set(v___x_2192_, 1, v___x_2191_);
lean_inc(v_a_2026_);
v___x_2193_ = l_Lean_MessageData_ofExpr(v_a_2026_);
v___x_2194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2194_, 0, v___x_2192_);
lean_ctor_set(v___x_2194_, 1, v___x_2193_);
v___x_2195_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_2196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2196_, 0, v___x_2194_);
lean_ctor_set(v___x_2196_, 1, v___x_2195_);
v___x_2197_ = l_Lean_MessageData_ofExpr(v_a_2175_);
v___x_2198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2198_, 0, v___x_2196_);
lean_ctor_set(v___x_2198_, 1, v___x_2197_);
v___x_2199_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_2200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2198_);
lean_ctor_set(v___x_2200_, 1, v___x_2199_);
lean_inc(v___x_2031_);
v___x_2201_ = l_Lean_MessageData_ofExpr(v___x_2031_);
v___x_2202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2200_);
lean_ctor_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2030_, v___x_2202_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2203_) == 0)
{
lean_object* v_a_2204_; lean_object* v___x_2205_; 
v_a_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc(v_a_2204_);
lean_dec_ref(v___x_2203_);
lean_inc(v___x_2031_);
v___x_2205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2026_, v___x_2031_, v___x_2018_, v___x_2021_, v___x_2029_, v_a_2204_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2205_;
goto v___jp_1998_;
}
else
{
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
return v___x_2203_;
}
}
}
v___jp_2182_:
{
lean_object* v___x_2183_; 
lean_inc(v___x_2031_);
v___x_2183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2026_, v___x_2031_, v___x_2018_, v___x_2021_, v___x_2029_, v___x_2029_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
v___y_1999_ = v___x_2183_;
goto v___jp_1998_;
}
}
else
{
lean_object* v___x_2206_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2026_);
lean_inc(v___x_2031_);
v___x_2206_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2021_, v___x_2031_, v___y_1989_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_dec_ref(v___x_2206_);
v_a_1994_ = v___x_2029_;
goto v___jp_1993_;
}
else
{
lean_dec(v_a_1986_);
return v___x_2206_;
}
}
}
else
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2214_; 
lean_dec(v_a_2175_);
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2207_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2214_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2214_ == 0)
{
v___x_2209_ = v___x_2176_;
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2176_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2214_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2212_; 
if (v_isShared_2210_ == 0)
{
v___x_2212_ = v___x_2209_;
goto v_reusejp_2211_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_a_2207_);
v___x_2212_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2211_;
}
v_reusejp_2211_:
{
return v___x_2212_;
}
}
}
}
else
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2222_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2215_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2222_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2222_ == 0)
{
v___x_2217_ = v___x_2174_;
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2174_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2222_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v___x_2220_; 
if (v_isShared_2218_ == 0)
{
v___x_2220_ = v___x_2217_;
goto v_reusejp_2219_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v_a_2215_);
v___x_2220_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2219_;
}
v_reusejp_2219_:
{
return v___x_2220_;
}
}
}
}
}
else
{
lean_object* v_a_2223_; lean_object* v___x_2225_; uint8_t v_isShared_2226_; uint8_t v_isSharedCheck_2230_; 
lean_dec(v_a_2026_);
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2223_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2230_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2230_ == 0)
{
v___x_2225_ = v___x_2027_;
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
else
{
lean_inc(v_a_2223_);
lean_dec(v___x_2027_);
v___x_2225_ = lean_box(0);
v_isShared_2226_ = v_isSharedCheck_2230_;
goto v_resetjp_2224_;
}
v_resetjp_2224_:
{
lean_object* v___x_2228_; 
if (v_isShared_2226_ == 0)
{
v___x_2228_ = v___x_2225_;
goto v_reusejp_2227_;
}
else
{
lean_object* v_reuseFailAlloc_2229_; 
v_reuseFailAlloc_2229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2229_, 0, v_a_2223_);
v___x_2228_ = v_reuseFailAlloc_2229_;
goto v_reusejp_2227_;
}
v_reusejp_2227_:
{
return v___x_2228_;
}
}
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2231_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2025_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2025_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v___x_2021_);
lean_dec(v_a_1986_);
v_a_2239_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2022_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2022_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
v___jp_1993_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = lean_unsigned_to_nat(1u);
v___x_1996_ = lean_nat_add(v_a_1986_, v___x_1995_);
lean_dec(v_a_1986_);
v___x_1997_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_1979_, v_fst_1980_, v_args_1981_, v_compile_1982_, v_logCompileErrors_1983_, v_isMeta_1984_, v___x_1985_, v___x_1996_, v_a_1994_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_1997_;
}
v___jp_1998_:
{
if (lean_obj_tag(v___y_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2002_; uint8_t v_isShared_2003_; uint8_t v_isSharedCheck_2009_; 
v_a_2000_ = lean_ctor_get(v___y_1999_, 0);
v_isSharedCheck_2009_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2009_ == 0)
{
v___x_2002_ = v___y_1999_;
v_isShared_2003_ = v_isSharedCheck_2009_;
goto v_resetjp_2001_;
}
else
{
lean_inc(v_a_2000_);
lean_dec(v___y_1999_);
v___x_2002_ = lean_box(0);
v_isShared_2003_ = v_isSharedCheck_2009_;
goto v_resetjp_2001_;
}
v_resetjp_2001_:
{
if (lean_obj_tag(v_a_2000_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2006_; 
lean_dec(v_a_1986_);
v_a_2004_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v_a_2000_);
if (v_isShared_2003_ == 0)
{
lean_ctor_set(v___x_2002_, 0, v_a_2004_);
v___x_2006_ = v___x_2002_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2007_; 
v_reuseFailAlloc_2007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2007_, 0, v_a_2004_);
v___x_2006_ = v_reuseFailAlloc_2007_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
return v___x_2006_;
}
}
else
{
lean_object* v_a_2008_; 
lean_del_object(v___x_2002_);
v_a_2008_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_a_2008_);
lean_dec_ref(v_a_2000_);
v_a_1994_ = v_a_2008_;
goto v___jp_1993_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_a_1986_);
v_a_2010_ = lean_ctor_get(v___y_1999_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___y_1999_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___y_1999_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___y_1999_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8(void){
_start:
{
lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2248_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__7));
v___x_2249_ = l_Lean_stringToMessageData(v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10(void){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2251_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__9));
v___x_2252_ = l_Lean_stringToMessageData(v___x_2251_);
return v___x_2252_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__11));
v___x_2255_ = l_Lean_stringToMessageData(v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__13));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(lean_object* v_a_2259_, lean_object* v_expectedType_2260_, uint8_t v___x_2261_, uint8_t v_compile_2262_, uint8_t v_logCompileErrors_2263_, uint8_t v_isMeta_2264_, lean_object* v_x_2265_, lean_object* v_x_2266_, lean_object* v_x_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2296_; lean_object* v___y_2297_; lean_object* v___y_2298_; lean_object* v___y_2299_; 
if (lean_obj_tag(v_x_2265_) == 5)
{
lean_object* v_fn_2312_; lean_object* v_arg_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; 
v_fn_2312_ = lean_ctor_get(v_x_2265_, 0);
lean_inc_ref(v_fn_2312_);
v_arg_2313_ = lean_ctor_get(v_x_2265_, 1);
lean_inc_ref(v_arg_2313_);
lean_dec_ref(v_x_2265_);
v___x_2314_ = lean_array_set(v_x_2266_, v_x_2267_, v_arg_2313_);
v___x_2315_ = lean_unsigned_to_nat(1u);
v___x_2316_ = lean_nat_sub(v_x_2267_, v___x_2315_);
lean_dec(v_x_2267_);
v_x_2265_ = v_fn_2312_;
v_x_2266_ = v___x_2314_;
v_x_2267_ = v___x_2316_;
goto _start;
}
else
{
uint8_t v___x_2318_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___y_2322_; lean_object* v_options_2323_; lean_object* v___y_2324_; lean_object* v_cls_2390_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___x_2413_; 
lean_dec(v_x_2267_);
v___x_2318_ = 1;
v_cls_2390_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2413_ = l_Lean_Expr_constName_x3f(v_x_2265_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
v___y_2392_ = v___y_2268_;
v___y_2393_ = v___y_2269_;
v___y_2394_ = v___y_2270_;
v___y_2395_ = v___y_2271_;
goto v___jp_2391_;
}
else
{
lean_object* v_val_2414_; lean_object* v___x_2415_; 
v_val_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_val_2414_);
lean_dec_ref(v___x_2413_);
v___x_2415_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_2414_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref(v___x_2415_);
if (lean_obj_tag(v_a_2416_) == 6)
{
lean_object* v_val_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v_a_2259_);
v_val_2417_ = lean_ctor_get(v_a_2416_, 0);
lean_inc_ref(v_val_2417_);
lean_dec_ref(v_a_2416_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v___y_2269_);
lean_inc_ref(v___y_2268_);
lean_inc_ref(v_x_2265_);
v___x_2418_ = lean_infer_type(v_x_2265_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref(v___x_2418_);
v___x_2420_ = 0;
v___x_2421_ = l_Lean_Meta_forallMetaTelescope(v_a_2419_, v___x_2420_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_snd_2423_; lean_object* v_fst_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2523_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
v_snd_2423_ = lean_ctor_get(v_a_2422_, 1);
v_fst_2424_ = lean_ctor_get(v_a_2422_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_a_2422_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2426_ = v_a_2422_;
v_isShared_2427_ = v_isSharedCheck_2523_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_snd_2423_);
lean_inc(v_fst_2424_);
lean_dec(v_a_2422_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2523_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v_snd_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2521_; 
v_snd_2428_ = lean_ctor_get(v_snd_2423_, 1);
v_isSharedCheck_2521_ = !lean_is_exclusive(v_snd_2423_);
if (v_isSharedCheck_2521_ == 0)
{
lean_object* v_unused_2522_; 
v_unused_2522_ = lean_ctor_get(v_snd_2423_, 0);
lean_dec(v_unused_2522_);
v___x_2430_ = v_snd_2423_;
v_isShared_2431_ = v_isSharedCheck_2521_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_snd_2428_);
lean_dec(v_snd_2423_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2521_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2432_; lean_object* v___y_2434_; lean_object* v___y_2435_; lean_object* v___y_2436_; lean_object* v___y_2437_; lean_object* v___x_2469_; uint8_t v___x_2470_; 
v___x_2432_ = lean_array_get_size(v_x_2266_);
v___x_2469_ = lean_array_get_size(v_fst_2424_);
v___x_2470_ = lean_nat_dec_eq(v___x_2432_, v___x_2469_);
if (v___x_2470_ == 0)
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2474_; 
lean_dec(v_snd_2428_);
lean_dec(v_fst_2424_);
lean_dec_ref(v_val_2417_);
lean_dec_ref(v_expectedType_2260_);
v___x_2471_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_2472_ = l_Lean_MessageData_ofExpr(v_x_2265_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 7);
lean_ctor_set(v___x_2430_, 1, v___x_2472_);
lean_ctor_set(v___x_2430_, 0, v___x_2471_);
v___x_2474_ = v___x_2430_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2471_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v___x_2472_);
v___x_2474_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
lean_object* v___x_2475_; lean_object* v___x_2477_; 
v___x_2475_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 7);
lean_ctor_set(v___x_2426_, 1, v___x_2475_);
lean_ctor_set(v___x_2426_, 0, v___x_2474_);
v___x_2477_ = v___x_2426_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v___x_2474_);
lean_ctor_set(v_reuseFailAlloc_2484_, 1, v___x_2475_);
v___x_2477_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; 
v___x_2478_ = lean_array_to_list(v_x_2266_);
v___x_2479_ = lean_box(0);
v___x_2480_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_2478_, v___x_2479_);
v___x_2481_ = l_Lean_MessageData_ofList(v___x_2480_);
v___x_2482_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2482_, 0, v___x_2477_);
lean_ctor_set(v___x_2482_, 1, v___x_2481_);
v___x_2483_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2482_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
return v___x_2483_;
}
}
}
else
{
lean_object* v___x_2486_; 
lean_inc_ref(v_expectedType_2260_);
v___x_2486_ = l_Lean_Meta_isExprDefEq(v_expectedType_2260_, v_snd_2428_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; uint8_t v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref(v___x_2486_);
v___x_2488_ = lean_unbox(v_a_2487_);
lean_dec(v_a_2487_);
if (v___x_2488_ == 0)
{
lean_object* v_toConstantVal_2489_; lean_object* v_name_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2494_; 
lean_dec(v_fst_2424_);
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
v_toConstantVal_2489_ = lean_ctor_get(v_val_2417_, 0);
lean_inc_ref(v_toConstantVal_2489_);
lean_dec_ref(v_val_2417_);
v_name_2490_ = lean_ctor_get(v_toConstantVal_2489_, 0);
lean_inc(v_name_2490_);
lean_dec_ref(v_toConstantVal_2489_);
v___x_2491_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_2492_ = l_Lean_MessageData_ofExpr(v_expectedType_2260_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set_tag(v___x_2430_, 7);
lean_ctor_set(v___x_2430_, 1, v___x_2492_);
lean_ctor_set(v___x_2430_, 0, v___x_2491_);
v___x_2494_ = v___x_2430_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v___x_2491_);
lean_ctor_set(v_reuseFailAlloc_2512_, 1, v___x_2492_);
v___x_2494_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
lean_object* v___x_2495_; lean_object* v___x_2497_; 
v___x_2495_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_2427_ == 0)
{
lean_ctor_set_tag(v___x_2426_, 7);
lean_ctor_set(v___x_2426_, 1, v___x_2495_);
lean_ctor_set(v___x_2426_, 0, v___x_2494_);
v___x_2497_ = v___x_2426_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2511_; 
v_reuseFailAlloc_2511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2494_);
lean_ctor_set(v_reuseFailAlloc_2511_, 1, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2511_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v_a_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_2510_; 
v___x_2498_ = l_Lean_MessageData_ofConstName(v_name_2490_, v___x_2261_);
v___x_2499_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2499_, 0, v___x_2497_);
lean_ctor_set(v___x_2499_, 1, v___x_2498_);
v___x_2500_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_2501_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2499_);
lean_ctor_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2501_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
v_a_2503_ = lean_ctor_get(v___x_2502_, 0);
v_isSharedCheck_2510_ = !lean_is_exclusive(v___x_2502_);
if (v_isSharedCheck_2510_ == 0)
{
v___x_2505_ = v___x_2502_;
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_a_2503_);
lean_dec(v___x_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_2510_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2508_; 
if (v_isShared_2506_ == 0)
{
v___x_2508_ = v___x_2505_;
goto v_reusejp_2507_;
}
else
{
lean_object* v_reuseFailAlloc_2509_; 
v_reuseFailAlloc_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2509_, 0, v_a_2503_);
v___x_2508_ = v_reuseFailAlloc_2509_;
goto v_reusejp_2507_;
}
v_reusejp_2507_:
{
return v___x_2508_;
}
}
}
}
}
else
{
lean_del_object(v___x_2430_);
lean_del_object(v___x_2426_);
lean_dec_ref(v_expectedType_2260_);
v___y_2434_ = v___y_2268_;
v___y_2435_ = v___y_2269_;
v___y_2436_ = v___y_2270_;
v___y_2437_ = v___y_2271_;
goto v___jp_2433_;
}
}
else
{
lean_object* v_a_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2520_; 
lean_del_object(v___x_2430_);
lean_del_object(v___x_2426_);
lean_dec(v_fst_2424_);
lean_dec_ref(v_val_2417_);
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_expectedType_2260_);
v_a_2513_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2515_ = v___x_2486_;
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_a_2513_);
lean_dec(v___x_2486_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2520_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2518_; 
if (v_isShared_2516_ == 0)
{
v___x_2518_ = v___x_2515_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_a_2513_);
v___x_2518_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
return v___x_2518_;
}
}
}
}
v___jp_2433_:
{
lean_object* v_numParams_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_numParams_2438_ = lean_ctor_get(v_val_2417_, 3);
lean_inc(v_numParams_2438_);
lean_dec_ref(v_val_2417_);
v___x_2439_ = lean_box(0);
v___x_2440_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2432_, v_fst_2424_, v_x_2266_, v_compile_2262_, v_logCompileErrors_2263_, v_isMeta_2264_, v___x_2261_, v_numParams_2438_, v___x_2439_, v___y_2434_, v___y_2435_, v___y_2436_, v___y_2437_);
lean_dec_ref(v_x_2266_);
if (lean_obj_tag(v___x_2440_) == 0)
{
size_t v_sz_2441_; size_t v___x_2442_; lean_object* v___x_2443_; 
lean_dec_ref(v___x_2440_);
v_sz_2441_ = lean_array_size(v_fst_2424_);
v___x_2442_ = ((size_t)0ULL);
v___x_2443_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_2441_, v___x_2442_, v_fst_2424_, v___y_2435_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2452_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2446_ = v___x_2443_;
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2443_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2452_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = l_Lean_mkAppN(v_x_2265_, v_a_2444_);
lean_dec(v_a_2444_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 0, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec_ref(v_x_2265_);
v_a_2453_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2443_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2443_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_fst_2424_);
lean_dec_ref(v_x_2265_);
v_a_2461_ = lean_ctor_get(v___x_2440_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2440_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2440_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2440_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec_ref(v_val_2417_);
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_expectedType_2260_);
v_a_2524_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2421_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2421_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_dec_ref(v_val_2417_);
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_expectedType_2260_);
return v___x_2418_;
}
}
else
{
lean_dec(v_a_2416_);
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
v___y_2392_ = v___y_2268_;
v___y_2393_ = v___y_2269_;
v___y_2394_ = v___y_2270_;
v___y_2395_ = v___y_2271_;
goto v___jp_2391_;
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_dec_ref(v_x_2266_);
lean_dec_ref(v_x_2265_);
lean_dec_ref(v_expectedType_2260_);
lean_dec_ref(v_a_2259_);
v_a_2532_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2415_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2415_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
v___jp_2319_:
{
lean_object* v___x_2325_; uint8_t v___x_2326_; 
v___x_2325_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2326_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2323_, v___x_2325_);
if (v___x_2326_ == 0)
{
lean_object* v___x_2327_; 
lean_dec_ref(v_expectedType_2260_);
v___x_2327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2259_);
return v___x_2327_;
}
else
{
lean_object* v___x_2328_; 
lean_inc(v___y_2324_);
lean_inc_ref(v___y_2322_);
lean_inc(v___y_2321_);
lean_inc_ref(v___y_2320_);
lean_inc_ref(v_a_2259_);
v___x_2328_ = lean_infer_type(v_a_2259_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2324_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
lean_inc_ref(v_expectedType_2260_);
v___x_2330_ = l_Lean_Meta_isExprDefEq(v_expectedType_2260_, v_a_2329_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2324_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2381_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2381_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2381_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_unbox(v_a_2331_);
lean_dec(v_a_2331_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v_a_2338_; lean_object* v___x_2339_; 
lean_del_object(v___x_2333_);
v___x_2336_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2337_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2336_, v___y_2324_);
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc_n(v_a_2338_, 2);
lean_dec_ref(v___x_2337_);
v___x_2339_ = l_Lean_Meta_mkAuxDefinition(v_a_2338_, v_expectedType_2260_, v_a_2259_, v___x_2261_, v___x_2261_, v___x_2318_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2324_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; uint8_t v___x_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref(v___x_2339_);
v___x_2341_ = 3;
lean_inc(v_a_2338_);
v___x_2342_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_2338_, v___x_2341_, v___y_2321_, v___y_2324_);
lean_dec_ref(v___x_2342_);
if (v_isMeta_2264_ == 0)
{
v___y_2296_ = v_a_2338_;
v___y_2297_ = v_a_2340_;
v___y_2298_ = v___y_2322_;
v___y_2299_ = v___y_2324_;
goto v___jp_2295_;
}
else
{
lean_object* v___x_2343_; lean_object* v_env_2344_; lean_object* v_nextMacroScope_2345_; lean_object* v_ngen_2346_; lean_object* v_auxDeclNGen_2347_; lean_object* v_traceState_2348_; lean_object* v_messages_2349_; lean_object* v_infoState_2350_; lean_object* v_snapshotTasks_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2376_; 
v___x_2343_ = lean_st_ref_take(v___y_2324_);
v_env_2344_ = lean_ctor_get(v___x_2343_, 0);
v_nextMacroScope_2345_ = lean_ctor_get(v___x_2343_, 1);
v_ngen_2346_ = lean_ctor_get(v___x_2343_, 2);
v_auxDeclNGen_2347_ = lean_ctor_get(v___x_2343_, 3);
v_traceState_2348_ = lean_ctor_get(v___x_2343_, 4);
v_messages_2349_ = lean_ctor_get(v___x_2343_, 6);
v_infoState_2350_ = lean_ctor_get(v___x_2343_, 7);
v_snapshotTasks_2351_ = lean_ctor_get(v___x_2343_, 8);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2376_ == 0)
{
lean_object* v_unused_2377_; 
v_unused_2377_ = lean_ctor_get(v___x_2343_, 5);
lean_dec(v_unused_2377_);
v___x_2353_ = v___x_2343_;
v_isShared_2354_ = v_isSharedCheck_2376_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_snapshotTasks_2351_);
lean_inc(v_infoState_2350_);
lean_inc(v_messages_2349_);
lean_inc(v_traceState_2348_);
lean_inc(v_auxDeclNGen_2347_);
lean_inc(v_ngen_2346_);
lean_inc(v_nextMacroScope_2345_);
lean_inc(v_env_2344_);
lean_dec(v___x_2343_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2376_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
lean_inc(v_a_2338_);
v___x_2355_ = l_Lean_markMeta(v_env_2344_, v_a_2338_);
v___x_2356_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 5, v___x_2356_);
lean_ctor_set(v___x_2353_, 0, v___x_2355_);
v___x_2358_ = v___x_2353_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2355_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_nextMacroScope_2345_);
lean_ctor_set(v_reuseFailAlloc_2375_, 2, v_ngen_2346_);
lean_ctor_set(v_reuseFailAlloc_2375_, 3, v_auxDeclNGen_2347_);
lean_ctor_set(v_reuseFailAlloc_2375_, 4, v_traceState_2348_);
lean_ctor_set(v_reuseFailAlloc_2375_, 5, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2375_, 6, v_messages_2349_);
lean_ctor_set(v_reuseFailAlloc_2375_, 7, v_infoState_2350_);
lean_ctor_set(v_reuseFailAlloc_2375_, 8, v_snapshotTasks_2351_);
v___x_2358_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v_mctx_2361_; lean_object* v_zetaDeltaFVarIds_2362_; lean_object* v_postponed_2363_; lean_object* v_diag_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2373_; 
v___x_2359_ = lean_st_ref_set(v___y_2324_, v___x_2358_);
v___x_2360_ = lean_st_ref_take(v___y_2321_);
v_mctx_2361_ = lean_ctor_get(v___x_2360_, 0);
v_zetaDeltaFVarIds_2362_ = lean_ctor_get(v___x_2360_, 2);
v_postponed_2363_ = lean_ctor_get(v___x_2360_, 3);
v_diag_2364_ = lean_ctor_get(v___x_2360_, 4);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2373_ == 0)
{
lean_object* v_unused_2374_; 
v_unused_2374_ = lean_ctor_get(v___x_2360_, 1);
lean_dec(v_unused_2374_);
v___x_2366_ = v___x_2360_;
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_diag_2364_);
lean_inc(v_postponed_2363_);
lean_inc(v_zetaDeltaFVarIds_2362_);
lean_inc(v_mctx_2361_);
lean_dec(v___x_2360_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2373_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2368_; lean_object* v___x_2370_; 
v___x_2368_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2367_ == 0)
{
lean_ctor_set(v___x_2366_, 1, v___x_2368_);
v___x_2370_ = v___x_2366_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2372_; 
v_reuseFailAlloc_2372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_mctx_2361_);
lean_ctor_set(v_reuseFailAlloc_2372_, 1, v___x_2368_);
lean_ctor_set(v_reuseFailAlloc_2372_, 2, v_zetaDeltaFVarIds_2362_);
lean_ctor_set(v_reuseFailAlloc_2372_, 3, v_postponed_2363_);
lean_ctor_set(v_reuseFailAlloc_2372_, 4, v_diag_2364_);
v___x_2370_ = v_reuseFailAlloc_2372_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; 
v___x_2371_ = lean_st_ref_set(v___y_2321_, v___x_2370_);
v___y_2296_ = v_a_2338_;
v___y_2297_ = v_a_2340_;
v___y_2298_ = v___y_2322_;
v___y_2299_ = v___y_2324_;
goto v___jp_2295_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2338_);
return v___x_2339_;
}
}
else
{
lean_object* v___x_2379_; 
lean_dec_ref(v_expectedType_2260_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 0, v_a_2259_);
v___x_2379_ = v___x_2333_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2259_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v_expectedType_2260_);
lean_dec_ref(v_a_2259_);
v_a_2382_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2330_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2330_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2260_);
lean_dec_ref(v_a_2259_);
return v___x_2328_;
}
}
}
v___jp_2391_:
{
lean_object* v_options_2396_; uint8_t v_hasTrace_2397_; 
v_options_2396_ = lean_ctor_get(v___y_2394_, 2);
v_hasTrace_2397_ = lean_ctor_get_uint8(v_options_2396_, sizeof(void*)*1);
if (v_hasTrace_2397_ == 0)
{
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v___y_2322_ = v___y_2394_;
v_options_2323_ = v_options_2396_;
v___y_2324_ = v___y_2395_;
goto v___jp_2319_;
}
else
{
lean_object* v_inheritedTraceOptions_2398_; lean_object* v___x_2399_; uint8_t v___x_2400_; 
v_inheritedTraceOptions_2398_ = lean_ctor_get(v___y_2394_, 13);
v___x_2399_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2400_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2398_, v_options_2396_, v___x_2399_);
if (v___x_2400_ == 0)
{
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v___y_2322_ = v___y_2394_;
v_options_2323_ = v_options_2396_;
v___y_2324_ = v___y_2395_;
goto v___jp_2319_;
}
else
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v___x_2401_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_2259_);
v___x_2402_ = l_Lean_MessageData_ofExpr(v_a_2259_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2401_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2390_, v___x_2403_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_dec_ref(v___x_2404_);
v___y_2320_ = v___y_2392_;
v___y_2321_ = v___y_2393_;
v___y_2322_ = v___y_2394_;
v_options_2323_ = v_options_2396_;
v___y_2324_ = v___y_2395_;
goto v___jp_2319_;
}
else
{
lean_object* v_a_2405_; lean_object* v___x_2407_; uint8_t v_isShared_2408_; uint8_t v_isSharedCheck_2412_; 
lean_dec_ref(v_expectedType_2260_);
lean_dec_ref(v_a_2259_);
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2412_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2412_ == 0)
{
v___x_2407_ = v___x_2404_;
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
else
{
lean_inc(v_a_2405_);
lean_dec(v___x_2404_);
v___x_2407_ = lean_box(0);
v_isShared_2408_ = v_isSharedCheck_2412_;
goto v_resetjp_2406_;
}
v_resetjp_2406_:
{
lean_object* v___x_2410_; 
if (v_isShared_2408_ == 0)
{
v___x_2410_ = v___x_2407_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_a_2405_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
}
}
}
v___jp_2273_:
{
lean_object* v___x_2278_; 
v___x_2278_ = l_Lean_enableRealizationsForConst(v___y_2274_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2278_) == 0)
{
lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2285_ == 0)
{
lean_object* v_unused_2286_; 
v_unused_2286_ = lean_ctor_get(v___x_2278_, 0);
lean_dec(v_unused_2286_);
v___x_2280_ = v___x_2278_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_dec(v___x_2278_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___y_2275_);
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v___y_2275_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
else
{
lean_object* v_a_2287_; lean_object* v___x_2289_; uint8_t v_isShared_2290_; uint8_t v_isSharedCheck_2294_; 
lean_dec_ref(v___y_2275_);
v_a_2287_ = lean_ctor_get(v___x_2278_, 0);
v_isSharedCheck_2294_ = !lean_is_exclusive(v___x_2278_);
if (v_isSharedCheck_2294_ == 0)
{
v___x_2289_ = v___x_2278_;
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
else
{
lean_inc(v_a_2287_);
lean_dec(v___x_2278_);
v___x_2289_ = lean_box(0);
v_isShared_2290_ = v_isSharedCheck_2294_;
goto v_resetjp_2288_;
}
v_resetjp_2288_:
{
lean_object* v___x_2292_; 
if (v_isShared_2290_ == 0)
{
v___x_2292_ = v___x_2289_;
goto v_reusejp_2291_;
}
else
{
lean_object* v_reuseFailAlloc_2293_; 
v_reuseFailAlloc_2293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2293_, 0, v_a_2287_);
v___x_2292_ = v_reuseFailAlloc_2293_;
goto v_reusejp_2291_;
}
v_reusejp_2291_:
{
return v___x_2292_;
}
}
}
}
v___jp_2295_:
{
if (v_compile_2262_ == 0)
{
v___y_2274_ = v___y_2296_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2298_;
v___y_2277_ = v___y_2299_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2300_ = lean_unsigned_to_nat(1u);
v___x_2301_ = lean_mk_empty_array_with_capacity(v___x_2300_);
lean_inc(v___y_2296_);
v___x_2302_ = lean_array_push(v___x_2301_, v___y_2296_);
v___x_2303_ = l_Lean_compileDecls(v___x_2302_, v_logCompileErrors_2263_, v___y_2298_, v___y_2299_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_dec_ref(v___x_2303_);
v___y_2274_ = v___y_2296_;
v___y_2275_ = v___y_2297_;
v___y_2276_ = v___y_2298_;
v___y_2277_ = v___y_2299_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2311_; 
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2311_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2306_ = v___x_2303_;
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_a_2304_);
lean_dec(v___x_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2311_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2309_; 
if (v_isShared_2307_ == 0)
{
v___x_2309_ = v___x_2306_;
goto v_reusejp_2308_;
}
else
{
lean_object* v_reuseFailAlloc_2310_; 
v_reuseFailAlloc_2310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
v___x_2309_ = v_reuseFailAlloc_2310_;
goto v_reusejp_2308_;
}
v_reusejp_2308_:
{
return v___x_2309_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(lean_object* v_a_2540_, lean_object* v_expectedType_2541_, uint8_t v___x_2542_, uint8_t v_compile_2543_, uint8_t v_logCompileErrors_2544_, uint8_t v_isMeta_2545_, lean_object* v_x_2546_, lean_object* v_x_2547_, lean_object* v_x_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_){
_start:
{
lean_object* v___y_2555_; lean_object* v___y_2556_; lean_object* v___y_2557_; lean_object* v___y_2558_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; 
if (lean_obj_tag(v_x_2546_) == 5)
{
lean_object* v_fn_2593_; lean_object* v_arg_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v_fn_2593_ = lean_ctor_get(v_x_2546_, 0);
lean_inc_ref(v_fn_2593_);
v_arg_2594_ = lean_ctor_get(v_x_2546_, 1);
lean_inc_ref(v_arg_2594_);
lean_dec_ref(v_x_2546_);
v___x_2595_ = lean_array_set(v_x_2547_, v_x_2548_, v_arg_2594_);
v___x_2596_ = lean_unsigned_to_nat(1u);
v___x_2597_ = lean_nat_sub(v_x_2548_, v___x_2596_);
v___x_2598_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(v_a_2540_, v_expectedType_2541_, v___x_2542_, v_compile_2543_, v_logCompileErrors_2544_, v_isMeta_2545_, v_fn_2593_, v___x_2595_, v___x_2597_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2598_;
}
else
{
uint8_t v___x_2599_; lean_object* v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2603_; lean_object* v_options_2604_; lean_object* v___y_2605_; lean_object* v_cls_2671_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___x_2694_; 
v___x_2599_ = 1;
v_cls_2671_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2694_ = l_Lean_Expr_constName_x3f(v_x_2546_);
if (lean_obj_tag(v___x_2694_) == 0)
{
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
v___y_2673_ = v___y_2549_;
v___y_2674_ = v___y_2550_;
v___y_2675_ = v___y_2551_;
v___y_2676_ = v___y_2552_;
goto v___jp_2672_;
}
else
{
lean_object* v_val_2695_; lean_object* v___x_2696_; 
v_val_2695_ = lean_ctor_get(v___x_2694_, 0);
lean_inc(v_val_2695_);
lean_dec_ref(v___x_2694_);
v___x_2696_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_2695_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref(v___x_2696_);
if (lean_obj_tag(v_a_2697_) == 6)
{
lean_object* v_val_2698_; lean_object* v___x_2699_; 
lean_dec_ref(v_a_2540_);
v_val_2698_ = lean_ctor_get(v_a_2697_, 0);
lean_inc_ref(v_val_2698_);
lean_dec_ref(v_a_2697_);
lean_inc(v___y_2552_);
lean_inc_ref(v___y_2551_);
lean_inc(v___y_2550_);
lean_inc_ref(v___y_2549_);
lean_inc_ref(v_x_2546_);
v___x_2699_ = lean_infer_type(v_x_2546_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2699_) == 0)
{
lean_object* v_a_2700_; uint8_t v___x_2701_; lean_object* v___x_2702_; 
v_a_2700_ = lean_ctor_get(v___x_2699_, 0);
lean_inc(v_a_2700_);
lean_dec_ref(v___x_2699_);
v___x_2701_ = 0;
v___x_2702_ = l_Lean_Meta_forallMetaTelescope(v_a_2700_, v___x_2701_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v_snd_2704_; lean_object* v_fst_2705_; lean_object* v___x_2707_; uint8_t v_isShared_2708_; uint8_t v_isSharedCheck_2804_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref(v___x_2702_);
v_snd_2704_ = lean_ctor_get(v_a_2703_, 1);
v_fst_2705_ = lean_ctor_get(v_a_2703_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v_a_2703_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2707_ = v_a_2703_;
v_isShared_2708_ = v_isSharedCheck_2804_;
goto v_resetjp_2706_;
}
else
{
lean_inc(v_snd_2704_);
lean_inc(v_fst_2705_);
lean_dec(v_a_2703_);
v___x_2707_ = lean_box(0);
v_isShared_2708_ = v_isSharedCheck_2804_;
goto v_resetjp_2706_;
}
v_resetjp_2706_:
{
lean_object* v_snd_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2802_; 
v_snd_2709_ = lean_ctor_get(v_snd_2704_, 1);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_snd_2704_);
if (v_isSharedCheck_2802_ == 0)
{
lean_object* v_unused_2803_; 
v_unused_2803_ = lean_ctor_get(v_snd_2704_, 0);
lean_dec(v_unused_2803_);
v___x_2711_ = v_snd_2704_;
v_isShared_2712_ = v_isSharedCheck_2802_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_snd_2709_);
lean_dec(v_snd_2704_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2802_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2713_; lean_object* v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; lean_object* v___x_2750_; uint8_t v___x_2751_; 
v___x_2713_ = lean_array_get_size(v_x_2547_);
v___x_2750_ = lean_array_get_size(v_fst_2705_);
v___x_2751_ = lean_nat_dec_eq(v___x_2713_, v___x_2750_);
if (v___x_2751_ == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec(v_snd_2709_);
lean_dec(v_fst_2705_);
lean_dec_ref(v_val_2698_);
lean_dec_ref(v_expectedType_2541_);
v___x_2752_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_2753_ = l_Lean_MessageData_ofExpr(v_x_2546_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 7);
lean_ctor_set(v___x_2711_, 1, v___x_2753_);
lean_ctor_set(v___x_2711_, 0, v___x_2752_);
v___x_2755_ = v___x_2711_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v___x_2752_);
lean_ctor_set(v_reuseFailAlloc_2766_, 1, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 7);
lean_ctor_set(v___x_2707_, 1, v___x_2756_);
lean_ctor_set(v___x_2707_, 0, v___x_2755_);
v___x_2758_ = v___x_2707_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2765_, 1, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2759_ = lean_array_to_list(v_x_2547_);
v___x_2760_ = lean_box(0);
v___x_2761_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_2759_, v___x_2760_);
v___x_2762_ = l_Lean_MessageData_ofList(v___x_2761_);
v___x_2763_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2763_, 0, v___x_2758_);
lean_ctor_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2763_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
return v___x_2764_;
}
}
}
else
{
lean_object* v___x_2767_; 
lean_inc_ref(v_expectedType_2541_);
v___x_2767_ = l_Lean_Meta_isExprDefEq(v_expectedType_2541_, v_snd_2709_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
if (lean_obj_tag(v___x_2767_) == 0)
{
lean_object* v_a_2768_; uint8_t v___x_2769_; 
v_a_2768_ = lean_ctor_get(v___x_2767_, 0);
lean_inc(v_a_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = lean_unbox(v_a_2768_);
lean_dec(v_a_2768_);
if (v___x_2769_ == 0)
{
lean_object* v_toConstantVal_2770_; lean_object* v_name_2771_; lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_dec(v_fst_2705_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
v_toConstantVal_2770_ = lean_ctor_get(v_val_2698_, 0);
lean_inc_ref(v_toConstantVal_2770_);
lean_dec_ref(v_val_2698_);
v_name_2771_ = lean_ctor_get(v_toConstantVal_2770_, 0);
lean_inc(v_name_2771_);
lean_dec_ref(v_toConstantVal_2770_);
v___x_2772_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_2773_ = l_Lean_MessageData_ofExpr(v_expectedType_2541_);
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 7);
lean_ctor_set(v___x_2711_, 1, v___x_2773_);
lean_ctor_set(v___x_2711_, 0, v___x_2772_);
v___x_2775_ = v___x_2711_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2793_; 
v_reuseFailAlloc_2793_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2793_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2793_, 1, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2793_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_2708_ == 0)
{
lean_ctor_set_tag(v___x_2707_, 7);
lean_ctor_set(v___x_2707_, 1, v___x_2776_);
lean_ctor_set(v___x_2707_, 0, v___x_2775_);
v___x_2778_ = v___x_2707_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v___x_2775_);
lean_ctor_set(v_reuseFailAlloc_2792_, 1, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
v___x_2779_ = l_Lean_MessageData_ofConstName(v_name_2771_, v___x_2542_);
v___x_2780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2780_, 0, v___x_2778_);
lean_ctor_set(v___x_2780_, 1, v___x_2779_);
v___x_2781_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_2782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2780_);
lean_ctor_set(v___x_2782_, 1, v___x_2781_);
v___x_2783_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_2782_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
v_a_2784_ = lean_ctor_get(v___x_2783_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2783_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2783_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2783_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
}
else
{
lean_del_object(v___x_2711_);
lean_del_object(v___x_2707_);
lean_dec_ref(v_expectedType_2541_);
v___y_2715_ = v___y_2549_;
v___y_2716_ = v___y_2550_;
v___y_2717_ = v___y_2551_;
v___y_2718_ = v___y_2552_;
goto v___jp_2714_;
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_del_object(v___x_2711_);
lean_del_object(v___x_2707_);
lean_dec(v_fst_2705_);
lean_dec_ref(v_val_2698_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_expectedType_2541_);
v_a_2794_ = lean_ctor_get(v___x_2767_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2767_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2767_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2767_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
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
v___jp_2714_:
{
lean_object* v_numParams_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v_numParams_2719_ = lean_ctor_get(v_val_2698_, 3);
lean_inc(v_numParams_2719_);
lean_dec_ref(v_val_2698_);
v___x_2720_ = lean_box(0);
v___x_2721_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v___x_2713_, v_fst_2705_, v_x_2547_, v_compile_2543_, v_logCompileErrors_2544_, v_isMeta_2545_, v___x_2542_, v_numParams_2719_, v___x_2720_, v___y_2715_, v___y_2716_, v___y_2717_, v___y_2718_);
lean_dec_ref(v_x_2547_);
if (lean_obj_tag(v___x_2721_) == 0)
{
size_t v_sz_2722_; size_t v___x_2723_; lean_object* v___x_2724_; 
lean_dec_ref(v___x_2721_);
v_sz_2722_ = lean_array_size(v_fst_2705_);
v___x_2723_ = ((size_t)0ULL);
v___x_2724_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_2722_, v___x_2723_, v_fst_2705_, v___y_2716_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2733_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2733_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2733_ == 0)
{
v___x_2727_ = v___x_2724_;
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_dec(v___x_2724_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2733_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v___x_2731_; 
v___x_2729_ = l_Lean_mkAppN(v_x_2546_, v_a_2725_);
lean_dec(v_a_2725_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2729_);
v___x_2731_ = v___x_2727_;
goto v_reusejp_2730_;
}
else
{
lean_object* v_reuseFailAlloc_2732_; 
v_reuseFailAlloc_2732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2732_, 0, v___x_2729_);
v___x_2731_ = v_reuseFailAlloc_2732_;
goto v_reusejp_2730_;
}
v_reusejp_2730_:
{
return v___x_2731_;
}
}
}
else
{
lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2741_; 
lean_dec_ref(v_x_2546_);
v_a_2734_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2741_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2741_ == 0)
{
v___x_2736_ = v___x_2724_;
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2724_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2741_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2739_; 
if (v_isShared_2737_ == 0)
{
v___x_2739_ = v___x_2736_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v_a_2734_);
v___x_2739_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
return v___x_2739_;
}
}
}
}
else
{
lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2749_; 
lean_dec(v_fst_2705_);
lean_dec_ref(v_x_2546_);
v_a_2742_ = lean_ctor_get(v___x_2721_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2721_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2744_ = v___x_2721_;
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2721_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2749_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2747_; 
if (v_isShared_2745_ == 0)
{
v___x_2747_ = v___x_2744_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2805_; lean_object* v___x_2807_; uint8_t v_isShared_2808_; uint8_t v_isSharedCheck_2812_; 
lean_dec_ref(v_val_2698_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_expectedType_2541_);
v_a_2805_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2812_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2812_ == 0)
{
v___x_2807_ = v___x_2702_;
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
else
{
lean_inc(v_a_2805_);
lean_dec(v___x_2702_);
v___x_2807_ = lean_box(0);
v_isShared_2808_ = v_isSharedCheck_2812_;
goto v_resetjp_2806_;
}
v_resetjp_2806_:
{
lean_object* v___x_2810_; 
if (v_isShared_2808_ == 0)
{
v___x_2810_ = v___x_2807_;
goto v_reusejp_2809_;
}
else
{
lean_object* v_reuseFailAlloc_2811_; 
v_reuseFailAlloc_2811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2811_, 0, v_a_2805_);
v___x_2810_ = v_reuseFailAlloc_2811_;
goto v_reusejp_2809_;
}
v_reusejp_2809_:
{
return v___x_2810_;
}
}
}
}
else
{
lean_dec_ref(v_val_2698_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_expectedType_2541_);
return v___x_2699_;
}
}
else
{
lean_dec(v_a_2697_);
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
v___y_2673_ = v___y_2549_;
v___y_2674_ = v___y_2550_;
v___y_2675_ = v___y_2551_;
v___y_2676_ = v___y_2552_;
goto v___jp_2672_;
}
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_x_2547_);
lean_dec_ref(v_x_2546_);
lean_dec_ref(v_expectedType_2541_);
lean_dec_ref(v_a_2540_);
v_a_2813_ = lean_ctor_get(v___x_2696_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2696_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2696_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2696_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
v___jp_2600_:
{
lean_object* v___x_2606_; uint8_t v___x_2607_; 
v___x_2606_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_2607_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2604_, v___x_2606_);
if (v___x_2607_ == 0)
{
lean_object* v___x_2608_; 
lean_dec_ref(v_expectedType_2541_);
v___x_2608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2608_, 0, v_a_2540_);
return v___x_2608_;
}
else
{
lean_object* v___x_2609_; 
lean_inc(v___y_2605_);
lean_inc_ref(v___y_2603_);
lean_inc(v___y_2602_);
lean_inc_ref(v___y_2601_);
lean_inc_ref(v_a_2540_);
v___x_2609_ = lean_infer_type(v_a_2540_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2605_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref(v___x_2609_);
lean_inc_ref(v_expectedType_2541_);
v___x_2611_ = l_Lean_Meta_isExprDefEq(v_expectedType_2541_, v_a_2610_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2605_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2662_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2662_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2662_ == 0)
{
v___x_2614_ = v___x_2611_;
v_isShared_2615_ = v_isSharedCheck_2662_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2611_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2662_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
uint8_t v___x_2616_; 
v___x_2616_ = lean_unbox(v_a_2612_);
lean_dec(v_a_2612_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v_a_2619_; lean_object* v___x_2620_; 
lean_del_object(v___x_2614_);
v___x_2617_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2618_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2617_, v___y_2605_);
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc_n(v_a_2619_, 2);
lean_dec_ref(v___x_2618_);
v___x_2620_ = l_Lean_Meta_mkAuxDefinition(v_a_2619_, v_expectedType_2541_, v_a_2540_, v___x_2542_, v___x_2542_, v___x_2599_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2605_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; uint8_t v___x_2622_; lean_object* v___x_2623_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref(v___x_2620_);
v___x_2622_ = 3;
lean_inc(v_a_2619_);
v___x_2623_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_2619_, v___x_2622_, v___y_2602_, v___y_2605_);
lean_dec_ref(v___x_2623_);
if (v_isMeta_2545_ == 0)
{
v___y_2577_ = v_a_2621_;
v___y_2578_ = v_a_2619_;
v___y_2579_ = v___y_2603_;
v___y_2580_ = v___y_2605_;
goto v___jp_2576_;
}
else
{
lean_object* v___x_2624_; lean_object* v_env_2625_; lean_object* v_nextMacroScope_2626_; lean_object* v_ngen_2627_; lean_object* v_auxDeclNGen_2628_; lean_object* v_traceState_2629_; lean_object* v_messages_2630_; lean_object* v_infoState_2631_; lean_object* v_snapshotTasks_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2657_; 
v___x_2624_ = lean_st_ref_take(v___y_2605_);
v_env_2625_ = lean_ctor_get(v___x_2624_, 0);
v_nextMacroScope_2626_ = lean_ctor_get(v___x_2624_, 1);
v_ngen_2627_ = lean_ctor_get(v___x_2624_, 2);
v_auxDeclNGen_2628_ = lean_ctor_get(v___x_2624_, 3);
v_traceState_2629_ = lean_ctor_get(v___x_2624_, 4);
v_messages_2630_ = lean_ctor_get(v___x_2624_, 6);
v_infoState_2631_ = lean_ctor_get(v___x_2624_, 7);
v_snapshotTasks_2632_ = lean_ctor_get(v___x_2624_, 8);
v_isSharedCheck_2657_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2657_ == 0)
{
lean_object* v_unused_2658_; 
v_unused_2658_ = lean_ctor_get(v___x_2624_, 5);
lean_dec(v_unused_2658_);
v___x_2634_ = v___x_2624_;
v_isShared_2635_ = v_isSharedCheck_2657_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_snapshotTasks_2632_);
lean_inc(v_infoState_2631_);
lean_inc(v_messages_2630_);
lean_inc(v_traceState_2629_);
lean_inc(v_auxDeclNGen_2628_);
lean_inc(v_ngen_2627_);
lean_inc(v_nextMacroScope_2626_);
lean_inc(v_env_2625_);
lean_dec(v___x_2624_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2657_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2639_; 
lean_inc(v_a_2619_);
v___x_2636_ = l_Lean_markMeta(v_env_2625_, v_a_2619_);
v___x_2637_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2635_ == 0)
{
lean_ctor_set(v___x_2634_, 5, v___x_2637_);
lean_ctor_set(v___x_2634_, 0, v___x_2636_);
v___x_2639_ = v___x_2634_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2656_; 
v_reuseFailAlloc_2656_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2636_);
lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_nextMacroScope_2626_);
lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_ngen_2627_);
lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_auxDeclNGen_2628_);
lean_ctor_set(v_reuseFailAlloc_2656_, 4, v_traceState_2629_);
lean_ctor_set(v_reuseFailAlloc_2656_, 5, v___x_2637_);
lean_ctor_set(v_reuseFailAlloc_2656_, 6, v_messages_2630_);
lean_ctor_set(v_reuseFailAlloc_2656_, 7, v_infoState_2631_);
lean_ctor_set(v_reuseFailAlloc_2656_, 8, v_snapshotTasks_2632_);
v___x_2639_ = v_reuseFailAlloc_2656_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v_mctx_2642_; lean_object* v_zetaDeltaFVarIds_2643_; lean_object* v_postponed_2644_; lean_object* v_diag_2645_; lean_object* v___x_2647_; uint8_t v_isShared_2648_; uint8_t v_isSharedCheck_2654_; 
v___x_2640_ = lean_st_ref_set(v___y_2605_, v___x_2639_);
v___x_2641_ = lean_st_ref_take(v___y_2602_);
v_mctx_2642_ = lean_ctor_get(v___x_2641_, 0);
v_zetaDeltaFVarIds_2643_ = lean_ctor_get(v___x_2641_, 2);
v_postponed_2644_ = lean_ctor_get(v___x_2641_, 3);
v_diag_2645_ = lean_ctor_get(v___x_2641_, 4);
v_isSharedCheck_2654_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2654_ == 0)
{
lean_object* v_unused_2655_; 
v_unused_2655_ = lean_ctor_get(v___x_2641_, 1);
lean_dec(v_unused_2655_);
v___x_2647_ = v___x_2641_;
v_isShared_2648_ = v_isSharedCheck_2654_;
goto v_resetjp_2646_;
}
else
{
lean_inc(v_diag_2645_);
lean_inc(v_postponed_2644_);
lean_inc(v_zetaDeltaFVarIds_2643_);
lean_inc(v_mctx_2642_);
lean_dec(v___x_2641_);
v___x_2647_ = lean_box(0);
v_isShared_2648_ = v_isSharedCheck_2654_;
goto v_resetjp_2646_;
}
v_resetjp_2646_:
{
lean_object* v___x_2649_; lean_object* v___x_2651_; 
v___x_2649_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2648_ == 0)
{
lean_ctor_set(v___x_2647_, 1, v___x_2649_);
v___x_2651_ = v___x_2647_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2653_; 
v_reuseFailAlloc_2653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_mctx_2642_);
lean_ctor_set(v_reuseFailAlloc_2653_, 1, v___x_2649_);
lean_ctor_set(v_reuseFailAlloc_2653_, 2, v_zetaDeltaFVarIds_2643_);
lean_ctor_set(v_reuseFailAlloc_2653_, 3, v_postponed_2644_);
lean_ctor_set(v_reuseFailAlloc_2653_, 4, v_diag_2645_);
v___x_2651_ = v_reuseFailAlloc_2653_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
lean_object* v___x_2652_; 
v___x_2652_ = lean_st_ref_set(v___y_2602_, v___x_2651_);
v___y_2577_ = v_a_2621_;
v___y_2578_ = v_a_2619_;
v___y_2579_ = v___y_2603_;
v___y_2580_ = v___y_2605_;
goto v___jp_2576_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2619_);
return v___x_2620_;
}
}
else
{
lean_object* v___x_2660_; 
lean_dec_ref(v_expectedType_2541_);
if (v_isShared_2615_ == 0)
{
lean_ctor_set(v___x_2614_, 0, v_a_2540_);
v___x_2660_ = v___x_2614_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_a_2540_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
else
{
lean_object* v_a_2663_; lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2670_; 
lean_dec_ref(v_expectedType_2541_);
lean_dec_ref(v_a_2540_);
v_a_2663_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2665_ = v___x_2611_;
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
else
{
lean_inc(v_a_2663_);
lean_dec(v___x_2611_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2670_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
if (v_isShared_2666_ == 0)
{
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2669_; 
v_reuseFailAlloc_2669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2669_, 0, v_a_2663_);
v___x_2668_ = v_reuseFailAlloc_2669_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
return v___x_2668_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_2541_);
lean_dec_ref(v_a_2540_);
return v___x_2609_;
}
}
}
v___jp_2672_:
{
lean_object* v_options_2677_; uint8_t v_hasTrace_2678_; 
v_options_2677_ = lean_ctor_get(v___y_2675_, 2);
v_hasTrace_2678_ = lean_ctor_get_uint8(v_options_2677_, sizeof(void*)*1);
if (v_hasTrace_2678_ == 0)
{
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v___y_2603_ = v___y_2675_;
v_options_2604_ = v_options_2677_;
v___y_2605_ = v___y_2676_;
goto v___jp_2600_;
}
else
{
lean_object* v_inheritedTraceOptions_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_inheritedTraceOptions_2679_ = lean_ctor_get(v___y_2675_, 13);
v___x_2680_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2681_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2679_, v_options_2677_, v___x_2680_);
if (v___x_2681_ == 0)
{
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v___y_2603_ = v___y_2675_;
v_options_2604_ = v_options_2677_;
v___y_2605_ = v___y_2676_;
goto v___jp_2600_;
}
else
{
lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; 
v___x_2682_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_2540_);
v___x_2683_ = l_Lean_MessageData_ofExpr(v_a_2540_);
v___x_2684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2684_, 0, v___x_2682_);
lean_ctor_set(v___x_2684_, 1, v___x_2683_);
v___x_2685_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2671_, v___x_2684_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_dec_ref(v___x_2685_);
v___y_2601_ = v___y_2673_;
v___y_2602_ = v___y_2674_;
v___y_2603_ = v___y_2675_;
v_options_2604_ = v_options_2677_;
v___y_2605_ = v___y_2676_;
goto v___jp_2600_;
}
else
{
lean_object* v_a_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
lean_dec_ref(v_expectedType_2541_);
lean_dec_ref(v_a_2540_);
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2688_ = v___x_2685_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2686_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
}
}
}
}
v___jp_2554_:
{
lean_object* v___x_2559_; 
v___x_2559_ = l_Lean_enableRealizationsForConst(v___y_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2566_ == 0)
{
lean_object* v_unused_2567_; 
v_unused_2567_ = lean_ctor_get(v___x_2559_, 0);
lean_dec(v_unused_2567_);
v___x_2561_ = v___x_2559_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_dec(v___x_2559_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___y_2555_);
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___y_2555_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
else
{
lean_object* v_a_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2575_; 
lean_dec_ref(v___y_2555_);
v_a_2568_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2575_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2575_ == 0)
{
v___x_2570_ = v___x_2559_;
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_a_2568_);
lean_dec(v___x_2559_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2575_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v___x_2573_; 
if (v_isShared_2571_ == 0)
{
v___x_2573_ = v___x_2570_;
goto v_reusejp_2572_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_a_2568_);
v___x_2573_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2572_;
}
v_reusejp_2572_:
{
return v___x_2573_;
}
}
}
}
v___jp_2576_:
{
if (v_compile_2543_ == 0)
{
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___y_2580_;
goto v___jp_2554_;
}
else
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; 
v___x_2581_ = lean_unsigned_to_nat(1u);
v___x_2582_ = lean_mk_empty_array_with_capacity(v___x_2581_);
lean_inc(v___y_2578_);
v___x_2583_ = lean_array_push(v___x_2582_, v___y_2578_);
v___x_2584_ = l_Lean_compileDecls(v___x_2583_, v_logCompileErrors_2544_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_dec_ref(v___x_2584_);
v___y_2555_ = v___y_2577_;
v___y_2556_ = v___y_2578_;
v___y_2557_ = v___y_2579_;
v___y_2558_ = v___y_2580_;
goto v___jp_2554_;
}
else
{
lean_object* v_a_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2592_; 
lean_dec(v___y_2578_);
lean_dec_ref(v___y_2577_);
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2587_ = v___x_2584_;
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_a_2585_);
lean_dec(v___x_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2592_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2590_; 
if (v_isShared_2588_ == 0)
{
v___x_2590_ = v___x_2587_;
goto v_reusejp_2589_;
}
else
{
lean_object* v_reuseFailAlloc_2591_; 
v_reuseFailAlloc_2591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2591_, 0, v_a_2585_);
v___x_2590_ = v_reuseFailAlloc_2591_;
goto v_reusejp_2589_;
}
v_reusejp_2589_:
{
return v___x_2590_;
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
lean_object* v___x_2821_; double v___x_2822_; 
v___x_2821_ = lean_unsigned_to_nat(1000000000u);
v___x_2822_ = lean_float_of_nat(v___x_2821_);
return v___x_2822_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(lean_object* v_upperBound_2823_, lean_object* v_fst_2824_, lean_object* v_args_2825_, uint8_t v___x_2826_, uint8_t v_compile_2827_, uint8_t v_logCompileErrors_2828_, uint8_t v_isMeta_2829_, uint8_t v___x_2830_, lean_object* v_a_2831_, lean_object* v_b_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_){
_start:
{
lean_object* v_a_2839_; lean_object* v___y_2844_; uint8_t v___x_2863_; 
v___x_2863_ = lean_nat_dec_lt(v_a_2831_, v_upperBound_2823_);
if (v___x_2863_ == 0)
{
lean_object* v___x_2864_; 
lean_dec(v_a_2831_);
v___x_2864_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2864_, 0, v_b_2832_);
return v___x_2864_;
}
else
{
lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2865_ = lean_array_fget_borrowed(v_fst_2824_, v_a_2831_);
v___x_2866_ = l_Lean_Expr_mvarId_x21(v___x_2865_);
lean_inc(v___x_2866_);
v___x_2867_ = l_Lean_MVarId_getDecl(v___x_2866_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v_type_2869_; lean_object* v___x_2870_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
lean_inc(v_a_2868_);
lean_dec_ref(v___x_2867_);
v_type_2869_ = lean_ctor_get(v_a_2868_, 2);
lean_inc_ref(v_type_2869_);
lean_dec(v_a_2868_);
v___x_2870_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_2869_, v___y_2834_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc_n(v_a_2871_, 2);
lean_dec_ref(v___x_2870_);
v___x_2872_ = l_Lean_Meta_isProp(v_a_2871_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; lean_object* v_cls_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref(v___x_2872_);
v___x_2874_ = lean_box(0);
v_cls_2875_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_2876_ = lean_array_fget_borrowed(v_args_2825_, v_a_2831_);
v___x_2877_ = lean_unbox(v_a_2873_);
lean_dec(v_a_2873_);
if (v___x_2877_ == 0)
{
lean_object* v___x_2878_; 
lean_inc(v_a_2871_);
v___x_2878_ = l_Lean_Meta_isClass_x3f(v_a_2871_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_3013_; 
v_a_2879_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_2881_ = v___x_2878_;
v_isShared_2882_ = v_isSharedCheck_3013_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2878_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_3013_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v_a_2884_; lean_object* v___y_2887_; uint8_t v___y_2888_; lean_object* v_a_2893_; lean_object* v___y_2897_; lean_object* v___y_2902_; 
if (lean_obj_tag(v_a_2879_) == 0)
{
if (v___x_2830_ == 0)
{
lean_object* v_options_2926_; lean_object* v___x_2927_; uint8_t v___x_2928_; 
lean_del_object(v___x_2881_);
v_options_2926_ = lean_ctor_get(v___y_2835_, 2);
v___x_2927_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_2928_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2926_, v___x_2927_);
if (v___x_2928_ == 0)
{
lean_object* v___x_2929_; 
lean_dec(v_a_2871_);
lean_inc(v___x_2876_);
v___x_2929_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2866_, v___x_2876_, v___y_2834_);
if (lean_obj_tag(v___x_2929_) == 0)
{
lean_dec_ref(v___x_2929_);
v_a_2839_ = v___x_2874_;
goto v___jp_2838_;
}
else
{
lean_dec(v_a_2831_);
return v___x_2929_;
}
}
else
{
lean_object* v___x_2930_; 
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2833_);
lean_inc(v___x_2876_);
v___x_2930_ = lean_infer_type(v___x_2876_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v___x_2932_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
lean_dec_ref(v___x_2930_);
lean_inc(v_a_2871_);
v___x_2932_ = l_Lean_Meta_isExprDefEq(v_a_2871_, v_a_2931_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; uint8_t v___x_2934_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref(v___x_2932_);
v___x_2934_ = lean_unbox(v_a_2933_);
lean_dec(v_a_2933_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2935_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_2936_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_2935_, v___y_2836_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc_n(v_a_2937_, 2);
lean_dec_ref(v___x_2936_);
lean_inc(v___x_2876_);
v___x_2938_ = l_Lean_Meta_mkAuxDefinition(v_a_2937_, v_a_2871_, v___x_2876_, v___x_2830_, v___x_2830_, v___x_2826_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v___x_2940_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref(v___x_2938_);
v___x_2940_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2866_, v_a_2939_, v___y_2834_);
if (lean_obj_tag(v___x_2940_) == 0)
{
uint8_t v___x_2941_; lean_object* v___x_2942_; 
lean_dec_ref(v___x_2940_);
v___x_2941_ = 0;
lean_inc(v_a_2937_);
v___x_2942_ = l_Lean_Meta_setInlineAttribute(v_a_2937_, v___x_2941_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2942_) == 0)
{
lean_dec_ref(v___x_2942_);
if (v_isMeta_2829_ == 0)
{
lean_object* v___x_2943_; 
v___x_2943_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2937_, v___x_2874_, v_compile_2827_, v_logCompileErrors_2828_, v___x_2874_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_2943_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2944_; lean_object* v_env_2945_; lean_object* v_nextMacroScope_2946_; lean_object* v_ngen_2947_; lean_object* v_auxDeclNGen_2948_; lean_object* v_traceState_2949_; lean_object* v_messages_2950_; lean_object* v_infoState_2951_; lean_object* v_snapshotTasks_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2978_; 
v___x_2944_ = lean_st_ref_take(v___y_2836_);
v_env_2945_ = lean_ctor_get(v___x_2944_, 0);
v_nextMacroScope_2946_ = lean_ctor_get(v___x_2944_, 1);
v_ngen_2947_ = lean_ctor_get(v___x_2944_, 2);
v_auxDeclNGen_2948_ = lean_ctor_get(v___x_2944_, 3);
v_traceState_2949_ = lean_ctor_get(v___x_2944_, 4);
v_messages_2950_ = lean_ctor_get(v___x_2944_, 6);
v_infoState_2951_ = lean_ctor_get(v___x_2944_, 7);
v_snapshotTasks_2952_ = lean_ctor_get(v___x_2944_, 8);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2978_ == 0)
{
lean_object* v_unused_2979_; 
v_unused_2979_ = lean_ctor_get(v___x_2944_, 5);
lean_dec(v_unused_2979_);
v___x_2954_ = v___x_2944_;
v_isShared_2955_ = v_isSharedCheck_2978_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_snapshotTasks_2952_);
lean_inc(v_infoState_2951_);
lean_inc(v_messages_2950_);
lean_inc(v_traceState_2949_);
lean_inc(v_auxDeclNGen_2948_);
lean_inc(v_ngen_2947_);
lean_inc(v_nextMacroScope_2946_);
lean_inc(v_env_2945_);
lean_dec(v___x_2944_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2978_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; 
lean_inc(v_a_2937_);
v___x_2956_ = l_Lean_markMeta(v_env_2945_, v_a_2937_);
v___x_2957_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_2955_ == 0)
{
lean_ctor_set(v___x_2954_, 5, v___x_2957_);
lean_ctor_set(v___x_2954_, 0, v___x_2956_);
v___x_2959_ = v___x_2954_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2956_);
lean_ctor_set(v_reuseFailAlloc_2977_, 1, v_nextMacroScope_2946_);
lean_ctor_set(v_reuseFailAlloc_2977_, 2, v_ngen_2947_);
lean_ctor_set(v_reuseFailAlloc_2977_, 3, v_auxDeclNGen_2948_);
lean_ctor_set(v_reuseFailAlloc_2977_, 4, v_traceState_2949_);
lean_ctor_set(v_reuseFailAlloc_2977_, 5, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2977_, 6, v_messages_2950_);
lean_ctor_set(v_reuseFailAlloc_2977_, 7, v_infoState_2951_);
lean_ctor_set(v_reuseFailAlloc_2977_, 8, v_snapshotTasks_2952_);
v___x_2959_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_mctx_2962_; lean_object* v_zetaDeltaFVarIds_2963_; lean_object* v_postponed_2964_; lean_object* v_diag_2965_; lean_object* v___x_2967_; uint8_t v_isShared_2968_; uint8_t v_isSharedCheck_2975_; 
v___x_2960_ = lean_st_ref_set(v___y_2836_, v___x_2959_);
v___x_2961_ = lean_st_ref_take(v___y_2834_);
v_mctx_2962_ = lean_ctor_get(v___x_2961_, 0);
v_zetaDeltaFVarIds_2963_ = lean_ctor_get(v___x_2961_, 2);
v_postponed_2964_ = lean_ctor_get(v___x_2961_, 3);
v_diag_2965_ = lean_ctor_get(v___x_2961_, 4);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2975_ == 0)
{
lean_object* v_unused_2976_; 
v_unused_2976_ = lean_ctor_get(v___x_2961_, 1);
lean_dec(v_unused_2976_);
v___x_2967_ = v___x_2961_;
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
else
{
lean_inc(v_diag_2965_);
lean_inc(v_postponed_2964_);
lean_inc(v_zetaDeltaFVarIds_2963_);
lean_inc(v_mctx_2962_);
lean_dec(v___x_2961_);
v___x_2967_ = lean_box(0);
v_isShared_2968_ = v_isSharedCheck_2975_;
goto v_resetjp_2966_;
}
v_resetjp_2966_:
{
lean_object* v___x_2969_; lean_object* v___x_2971_; 
v___x_2969_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_2968_ == 0)
{
lean_ctor_set(v___x_2967_, 1, v___x_2969_);
v___x_2971_ = v___x_2967_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_mctx_2962_);
lean_ctor_set(v_reuseFailAlloc_2974_, 1, v___x_2969_);
lean_ctor_set(v_reuseFailAlloc_2974_, 2, v_zetaDeltaFVarIds_2963_);
lean_ctor_set(v_reuseFailAlloc_2974_, 3, v_postponed_2964_);
lean_ctor_set(v_reuseFailAlloc_2974_, 4, v_diag_2965_);
v___x_2971_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
v___x_2972_ = lean_st_ref_set(v___y_2834_, v___x_2971_);
v___x_2973_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_2937_, v___x_2874_, v_compile_2827_, v_logCompileErrors_2828_, v___x_2874_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_2973_;
goto v___jp_2843_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2937_);
lean_dec(v_a_2831_);
return v___x_2942_;
}
}
else
{
lean_dec(v_a_2937_);
lean_dec(v_a_2831_);
return v___x_2940_;
}
}
else
{
lean_object* v_a_2980_; lean_object* v___x_2982_; uint8_t v_isShared_2983_; uint8_t v_isSharedCheck_2987_; 
lean_dec(v_a_2937_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_2980_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2987_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2987_ == 0)
{
v___x_2982_ = v___x_2938_;
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
else
{
lean_inc(v_a_2980_);
lean_dec(v___x_2938_);
v___x_2982_ = lean_box(0);
v_isShared_2983_ = v_isSharedCheck_2987_;
goto v_resetjp_2981_;
}
v_resetjp_2981_:
{
lean_object* v___x_2985_; 
if (v_isShared_2983_ == 0)
{
v___x_2985_ = v___x_2982_;
goto v_reusejp_2984_;
}
else
{
lean_object* v_reuseFailAlloc_2986_; 
v_reuseFailAlloc_2986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2986_, 0, v_a_2980_);
v___x_2985_ = v_reuseFailAlloc_2986_;
goto v_reusejp_2984_;
}
v_reusejp_2984_:
{
return v___x_2985_;
}
}
}
}
else
{
lean_object* v_a_2988_; lean_object* v___x_2990_; uint8_t v_isShared_2991_; uint8_t v_isSharedCheck_2995_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_2988_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2995_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2995_ == 0)
{
v___x_2990_ = v___x_2936_;
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
else
{
lean_inc(v_a_2988_);
lean_dec(v___x_2936_);
v___x_2990_ = lean_box(0);
v_isShared_2991_ = v_isSharedCheck_2995_;
goto v_resetjp_2989_;
}
v_resetjp_2989_:
{
lean_object* v___x_2993_; 
if (v_isShared_2991_ == 0)
{
v___x_2993_ = v___x_2990_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2994_; 
v_reuseFailAlloc_2994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2994_, 0, v_a_2988_);
v___x_2993_ = v_reuseFailAlloc_2994_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
return v___x_2993_;
}
}
}
}
else
{
lean_object* v___x_2996_; 
lean_dec(v_a_2871_);
lean_inc(v___x_2876_);
v___x_2996_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2866_, v___x_2876_, v___y_2834_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_dec_ref(v___x_2996_);
v_a_2839_ = v___x_2874_;
goto v___jp_2838_;
}
else
{
lean_dec(v_a_2831_);
return v___x_2996_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_2997_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2932_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2932_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3005_ = lean_ctor_get(v___x_2930_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2930_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2930_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
}
else
{
goto v___jp_2904_;
}
}
else
{
lean_dec_ref(v_a_2879_);
goto v___jp_2904_;
}
v___jp_2883_:
{
lean_object* v___x_2885_; 
lean_inc(v___x_2876_);
v___x_2885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2876_, v_a_2871_, v_compile_2827_, v_logCompileErrors_2828_, v_isMeta_2829_, v___x_2866_, v___x_2874_, v_a_2884_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_2885_;
goto v___jp_2843_;
}
v___jp_2886_:
{
if (v___y_2888_ == 0)
{
lean_dec_ref(v___y_2887_);
lean_del_object(v___x_2881_);
v_a_2884_ = v___x_2874_;
goto v___jp_2883_;
}
else
{
lean_object* v___x_2890_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
if (v_isShared_2882_ == 0)
{
lean_ctor_set_tag(v___x_2881_, 1);
lean_ctor_set(v___x_2881_, 0, v___y_2887_);
v___x_2890_ = v___x_2881_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v___y_2887_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
v___jp_2892_:
{
uint8_t v___x_2894_; 
v___x_2894_ = l_Lean_Exception_isInterrupt(v_a_2893_);
if (v___x_2894_ == 0)
{
uint8_t v___x_2895_; 
lean_inc_ref(v_a_2893_);
v___x_2895_ = l_Lean_Exception_isRuntime(v_a_2893_);
v___y_2887_ = v_a_2893_;
v___y_2888_ = v___x_2895_;
goto v___jp_2886_;
}
else
{
v___y_2887_ = v_a_2893_;
v___y_2888_ = v___x_2894_;
goto v___jp_2886_;
}
}
v___jp_2896_:
{
if (lean_obj_tag(v___y_2897_) == 0)
{
lean_object* v_a_2898_; 
lean_del_object(v___x_2881_);
v_a_2898_ = lean_ctor_get(v___y_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref(v___y_2897_);
if (lean_obj_tag(v_a_2898_) == 0)
{
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
v_a_2839_ = v___x_2874_;
goto v___jp_2838_;
}
else
{
lean_object* v_a_2899_; 
v_a_2899_ = lean_ctor_get(v_a_2898_, 0);
lean_inc(v_a_2899_);
lean_dec_ref(v_a_2898_);
v_a_2884_ = v_a_2899_;
goto v___jp_2883_;
}
}
else
{
lean_object* v_a_2900_; 
v_a_2900_ = lean_ctor_get(v___y_2897_, 0);
lean_inc(v_a_2900_);
lean_dec_ref(v___y_2897_);
v_a_2893_ = v_a_2900_;
goto v___jp_2892_;
}
}
v___jp_2901_:
{
lean_object* v___x_2903_; 
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2833_);
v___x_2903_ = lean_apply_6(v___y_2902_, v___x_2874_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_, lean_box(0));
v___y_2897_ = v___x_2903_;
goto v___jp_2896_;
}
v___jp_2904_:
{
lean_object* v_options_2905_; lean_object* v_inheritedTraceOptions_2906_; lean_object* v___x_2907_; uint8_t v___x_2908_; 
v_options_2905_ = lean_ctor_get(v___y_2835_, 2);
v_inheritedTraceOptions_2906_ = lean_ctor_get(v___y_2835_, 13);
v___x_2907_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_2908_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_2905_, v___x_2907_);
if (v___x_2908_ == 0)
{
lean_object* v___x_2909_; 
lean_del_object(v___x_2881_);
lean_inc(v___x_2876_);
v___x_2909_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_2876_, v_a_2871_, v_compile_2827_, v_logCompileErrors_2828_, v_isMeta_2829_, v___x_2866_, v___x_2874_, v___x_2874_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_2909_;
goto v___jp_2843_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2910_ = lean_box(0);
lean_inc(v_a_2871_);
v___x_2911_ = l_Lean_Meta_trySynthInstance(v_a_2871_, v___x_2910_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v_a_2912_; 
v_a_2912_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2912_);
lean_dec_ref(v___x_2911_);
if (lean_obj_tag(v_a_2912_) == 1)
{
lean_object* v_a_2913_; uint8_t v_hasTrace_2914_; lean_object* v___f_2915_; 
v_a_2913_ = lean_ctor_get(v_a_2912_, 0);
lean_inc_n(v_a_2913_, 2);
lean_dec_ref(v_a_2912_);
v_hasTrace_2914_ = lean_ctor_get_uint8(v_options_2905_, sizeof(void*)*1);
lean_inc(v___x_2866_);
v___f_2915_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed), 8, 2);
lean_closure_set(v___f_2915_, 0, v___x_2866_);
lean_closure_set(v___f_2915_, 1, v_a_2913_);
if (v_hasTrace_2914_ == 0)
{
lean_dec(v_a_2913_);
v___y_2902_ = v___f_2915_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_2917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2906_, v_options_2905_, v___x_2916_);
if (v___x_2917_ == 0)
{
lean_dec(v_a_2913_);
v___y_2902_ = v___f_2915_;
goto v___jp_2901_;
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec_ref(v___f_2915_);
v___x_2918_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_2913_);
v___x_2919_ = l_Lean_MessageData_ofExpr(v_a_2913_);
v___x_2920_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2920_, 0, v___x_2918_);
lean_ctor_set(v___x_2920_, 1, v___x_2919_);
v___x_2921_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2875_, v___x_2920_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_2921_) == 0)
{
lean_object* v_a_2922_; lean_object* v___x_2923_; 
v_a_2922_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2922_);
lean_dec_ref(v___x_2921_);
lean_inc(v___x_2866_);
v___x_2923_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_2866_, v_a_2913_, v_a_2922_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2897_ = v___x_2923_;
goto v___jp_2896_;
}
else
{
lean_object* v_a_2924_; 
lean_dec(v_a_2913_);
v_a_2924_ = lean_ctor_get(v___x_2921_, 0);
lean_inc(v_a_2924_);
lean_dec_ref(v___x_2921_);
v_a_2893_ = v_a_2924_;
goto v___jp_2892_;
}
}
}
}
else
{
lean_dec(v_a_2912_);
lean_del_object(v___x_2881_);
v_a_2884_ = v___x_2874_;
goto v___jp_2883_;
}
}
else
{
lean_object* v_a_2925_; 
v_a_2925_ = lean_ctor_get(v___x_2911_, 0);
lean_inc(v_a_2925_);
lean_dec_ref(v___x_2911_);
v_a_2893_ = v_a_2925_;
goto v___jp_2892_;
}
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3014_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2878_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2878_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v___x_3022_; 
lean_inc(v___y_2836_);
lean_inc_ref(v___y_2835_);
lean_inc(v___y_2834_);
lean_inc_ref(v___y_2833_);
lean_inc(v___x_2876_);
v___x_3022_ = lean_infer_type(v___x_2876_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc_n(v_a_3023_, 2);
lean_dec_ref(v___x_3022_);
lean_inc(v_a_2871_);
v___x_3024_ = l_Lean_Meta_isExprDefEq(v_a_2871_, v_a_3023_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; uint8_t v___x_3026_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref(v___x_3024_);
v___x_3026_ = lean_unbox(v_a_3025_);
lean_dec(v_a_3025_);
if (v___x_3026_ == 0)
{
lean_object* v_options_3027_; lean_object* v_inheritedTraceOptions_3028_; uint8_t v_hasTrace_3029_; 
v_options_3027_ = lean_ctor_get(v___y_2835_, 2);
v_inheritedTraceOptions_3028_ = lean_ctor_get(v___y_2835_, 13);
v_hasTrace_3029_ = lean_ctor_get_uint8(v_options_3027_, sizeof(void*)*1);
if (v_hasTrace_3029_ == 0)
{
lean_dec(v_a_3023_);
goto v___jp_3030_;
}
else
{
lean_object* v___x_3032_; uint8_t v___x_3033_; 
v___x_3032_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3033_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3028_, v_options_3027_, v___x_3032_);
if (v___x_3033_ == 0)
{
lean_dec(v_a_3023_);
goto v___jp_3030_;
}
else
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3049_; lean_object* v___x_3050_; lean_object* v___x_3051_; 
v___x_3034_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_2831_);
v___x_3035_ = l_Nat_reprFast(v_a_2831_);
v___x_3036_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3036_, 0, v___x_3035_);
v___x_3037_ = l_Lean_MessageData_ofFormat(v___x_3036_);
v___x_3038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3038_, 0, v___x_3034_);
lean_ctor_set(v___x_3038_, 1, v___x_3037_);
v___x_3039_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_3040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3038_);
lean_ctor_set(v___x_3040_, 1, v___x_3039_);
lean_inc(v_a_2871_);
v___x_3041_ = l_Lean_MessageData_ofExpr(v_a_2871_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
v___x_3045_ = l_Lean_MessageData_ofExpr(v_a_3023_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_3048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3046_);
lean_ctor_set(v___x_3048_, 1, v___x_3047_);
lean_inc(v___x_2876_);
v___x_3049_ = l_Lean_MessageData_ofExpr(v___x_2876_);
v___x_3050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3048_);
lean_ctor_set(v___x_3050_, 1, v___x_3049_);
v___x_3051_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_2875_, v___x_3050_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
if (lean_obj_tag(v___x_3051_) == 0)
{
lean_object* v_a_3052_; lean_object* v___x_3053_; 
v_a_3052_ = lean_ctor_get(v___x_3051_, 0);
lean_inc(v_a_3052_);
lean_dec_ref(v___x_3051_);
lean_inc(v___x_2876_);
v___x_3053_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2871_, v___x_2876_, v___x_2826_, v___x_2866_, v___x_2874_, v_a_3052_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_3053_;
goto v___jp_2843_;
}
else
{
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
return v___x_3051_;
}
}
}
v___jp_3030_:
{
lean_object* v___x_3031_; 
lean_inc(v___x_2876_);
v___x_3031_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_2871_, v___x_2876_, v___x_2826_, v___x_2866_, v___x_2874_, v___x_2874_, v___y_2833_, v___y_2834_, v___y_2835_, v___y_2836_);
v___y_2844_ = v___x_3031_;
goto v___jp_2843_;
}
}
else
{
lean_object* v___x_3054_; 
lean_dec(v_a_3023_);
lean_dec(v_a_2871_);
lean_inc(v___x_2876_);
v___x_3054_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_2866_, v___x_2876_, v___y_2834_);
if (lean_obj_tag(v___x_3054_) == 0)
{
lean_dec_ref(v___x_3054_);
v_a_2839_ = v___x_2874_;
goto v___jp_2838_;
}
else
{
lean_dec(v_a_2831_);
return v___x_3054_;
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec(v_a_3023_);
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3055_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3024_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3024_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3063_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3022_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3022_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
else
{
lean_object* v_a_3071_; lean_object* v___x_3073_; uint8_t v_isShared_3074_; uint8_t v_isSharedCheck_3078_; 
lean_dec(v_a_2871_);
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3071_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3073_ = v___x_2872_;
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
else
{
lean_inc(v_a_3071_);
lean_dec(v___x_2872_);
v___x_3073_ = lean_box(0);
v_isShared_3074_ = v_isSharedCheck_3078_;
goto v_resetjp_3072_;
}
v_resetjp_3072_:
{
lean_object* v___x_3076_; 
if (v_isShared_3074_ == 0)
{
v___x_3076_ = v___x_3073_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v_a_3071_);
v___x_3076_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
return v___x_3076_;
}
}
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3079_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_2870_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_2870_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_dec(v___x_2866_);
lean_dec(v_a_2831_);
v_a_3087_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_2867_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_2867_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
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
v___jp_2838_:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; 
v___x_2840_ = lean_unsigned_to_nat(1u);
v___x_2841_ = lean_nat_add(v_a_2831_, v___x_2840_);
lean_dec(v_a_2831_);
v_a_2831_ = v___x_2841_;
v_b_2832_ = v_a_2839_;
goto _start;
}
v___jp_2843_:
{
if (lean_obj_tag(v___y_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2854_; 
v_a_2845_ = lean_ctor_get(v___y_2844_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___y_2844_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2847_ = v___y_2844_;
v_isShared_2848_ = v_isSharedCheck_2854_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_dec(v___y_2844_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2854_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
if (lean_obj_tag(v_a_2845_) == 0)
{
lean_object* v_a_2849_; lean_object* v___x_2851_; 
lean_dec(v_a_2831_);
v_a_2849_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_a_2849_);
lean_dec_ref(v_a_2845_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v_a_2849_);
v___x_2851_ = v___x_2847_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
else
{
lean_object* v_a_2853_; 
lean_del_object(v___x_2847_);
v_a_2853_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_a_2853_);
lean_dec_ref(v_a_2845_);
v_a_2839_ = v_a_2853_;
goto v___jp_2838_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2831_);
v_a_2855_ = lean_ctor_get(v___y_2844_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___y_2844_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___y_2844_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___y_2844_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(lean_object* v_upperBound_3095_, lean_object* v_fst_3096_, lean_object* v_args_3097_, uint8_t v___x_3098_, uint8_t v_compile_3099_, uint8_t v_logCompileErrors_3100_, uint8_t v_isMeta_3101_, uint8_t v___x_3102_, lean_object* v_a_3103_, lean_object* v_b_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_){
_start:
{
lean_object* v_a_3111_; lean_object* v___y_3116_; uint8_t v___x_3135_; 
v___x_3135_ = lean_nat_dec_lt(v_a_3103_, v_upperBound_3095_);
if (v___x_3135_ == 0)
{
lean_object* v___x_3136_; 
lean_dec(v_a_3103_);
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_b_3104_);
return v___x_3136_;
}
else
{
lean_object* v___x_3137_; lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_array_fget_borrowed(v_fst_3096_, v_a_3103_);
v___x_3138_ = l_Lean_Expr_mvarId_x21(v___x_3137_);
lean_inc(v___x_3138_);
v___x_3139_ = l_Lean_MVarId_getDecl(v___x_3138_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v_type_3141_; lean_object* v___x_3142_; 
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref(v___x_3139_);
v_type_3141_ = lean_ctor_get(v_a_3140_, 2);
lean_inc_ref(v_type_3141_);
lean_dec(v_a_3140_);
v___x_3142_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_3141_, v___y_3106_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc_n(v_a_3143_, 2);
lean_dec_ref(v___x_3142_);
v___x_3144_ = l_Lean_Meta_isProp(v_a_3143_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3144_) == 0)
{
lean_object* v_a_3145_; lean_object* v___x_3146_; lean_object* v_cls_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
lean_inc(v_a_3145_);
lean_dec_ref(v___x_3144_);
v___x_3146_ = lean_box(0);
v_cls_3147_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3148_ = lean_array_fget_borrowed(v_args_3097_, v_a_3103_);
v___x_3149_ = lean_unbox(v_a_3145_);
lean_dec(v_a_3145_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
lean_inc(v_a_3143_);
v___x_3150_ = l_Lean_Meta_isClass_x3f(v_a_3143_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3150_) == 0)
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3285_; 
v_a_3151_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3153_ = v___x_3150_;
v_isShared_3154_ = v_isSharedCheck_3285_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3150_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3285_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_a_3156_; lean_object* v___y_3159_; uint8_t v___y_3160_; lean_object* v_a_3165_; lean_object* v___y_3169_; lean_object* v___y_3174_; 
if (lean_obj_tag(v_a_3151_) == 0)
{
if (v___x_3102_ == 0)
{
lean_object* v_options_3198_; lean_object* v___x_3199_; uint8_t v___x_3200_; 
lean_del_object(v___x_3153_);
v_options_3198_ = lean_ctor_get(v___y_3107_, 2);
v___x_3199_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_3200_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3198_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v___x_3201_; 
lean_dec(v_a_3143_);
lean_inc(v___x_3148_);
v___x_3201_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3138_, v___x_3148_, v___y_3106_);
if (lean_obj_tag(v___x_3201_) == 0)
{
lean_dec_ref(v___x_3201_);
v_a_3111_ = v___x_3146_;
goto v___jp_3110_;
}
else
{
lean_dec(v_a_3103_);
return v___x_3201_;
}
}
else
{
lean_object* v___x_3202_; 
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___x_3148_);
v___x_3202_ = lean_infer_type(v___x_3148_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3204_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
lean_inc(v_a_3203_);
lean_dec_ref(v___x_3202_);
lean_inc(v_a_3143_);
v___x_3204_ = l_Lean_Meta_isExprDefEq(v_a_3143_, v_a_3203_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3204_) == 0)
{
lean_object* v_a_3205_; uint8_t v___x_3206_; 
v_a_3205_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_a_3205_);
lean_dec_ref(v___x_3204_);
v___x_3206_ = lean_unbox(v_a_3205_);
lean_dec(v_a_3205_);
if (v___x_3206_ == 0)
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
v___x_3207_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3208_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3207_, v___y_3108_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc_n(v_a_3209_, 2);
lean_dec_ref(v___x_3208_);
lean_inc(v___x_3148_);
v___x_3210_ = l_Lean_Meta_mkAuxDefinition(v_a_3209_, v_a_3143_, v___x_3148_, v___x_3102_, v___x_3102_, v___x_3098_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3210_) == 0)
{
lean_object* v_a_3211_; lean_object* v___x_3212_; 
v_a_3211_ = lean_ctor_get(v___x_3210_, 0);
lean_inc(v_a_3211_);
lean_dec_ref(v___x_3210_);
v___x_3212_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3138_, v_a_3211_, v___y_3106_);
if (lean_obj_tag(v___x_3212_) == 0)
{
uint8_t v___x_3213_; lean_object* v___x_3214_; 
lean_dec_ref(v___x_3212_);
v___x_3213_ = 0;
lean_inc(v_a_3209_);
v___x_3214_ = l_Lean_Meta_setInlineAttribute(v_a_3209_, v___x_3213_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_dec_ref(v___x_3214_);
if (v_isMeta_3101_ == 0)
{
lean_object* v___x_3215_; 
v___x_3215_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_3209_, v___x_3146_, v_compile_3099_, v_logCompileErrors_3100_, v___x_3146_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3215_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3216_; lean_object* v_env_3217_; lean_object* v_nextMacroScope_3218_; lean_object* v_ngen_3219_; lean_object* v_auxDeclNGen_3220_; lean_object* v_traceState_3221_; lean_object* v_messages_3222_; lean_object* v_infoState_3223_; lean_object* v_snapshotTasks_3224_; lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3250_; 
v___x_3216_ = lean_st_ref_take(v___y_3108_);
v_env_3217_ = lean_ctor_get(v___x_3216_, 0);
v_nextMacroScope_3218_ = lean_ctor_get(v___x_3216_, 1);
v_ngen_3219_ = lean_ctor_get(v___x_3216_, 2);
v_auxDeclNGen_3220_ = lean_ctor_get(v___x_3216_, 3);
v_traceState_3221_ = lean_ctor_get(v___x_3216_, 4);
v_messages_3222_ = lean_ctor_get(v___x_3216_, 6);
v_infoState_3223_ = lean_ctor_get(v___x_3216_, 7);
v_snapshotTasks_3224_ = lean_ctor_get(v___x_3216_, 8);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3216_);
if (v_isSharedCheck_3250_ == 0)
{
lean_object* v_unused_3251_; 
v_unused_3251_ = lean_ctor_get(v___x_3216_, 5);
lean_dec(v_unused_3251_);
v___x_3226_ = v___x_3216_;
v_isShared_3227_ = v_isSharedCheck_3250_;
goto v_resetjp_3225_;
}
else
{
lean_inc(v_snapshotTasks_3224_);
lean_inc(v_infoState_3223_);
lean_inc(v_messages_3222_);
lean_inc(v_traceState_3221_);
lean_inc(v_auxDeclNGen_3220_);
lean_inc(v_ngen_3219_);
lean_inc(v_nextMacroScope_3218_);
lean_inc(v_env_3217_);
lean_dec(v___x_3216_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3250_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3231_; 
lean_inc(v_a_3209_);
v___x_3228_ = l_Lean_markMeta(v_env_3217_, v_a_3209_);
v___x_3229_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 5, v___x_3229_);
lean_ctor_set(v___x_3226_, 0, v___x_3228_);
v___x_3231_ = v___x_3226_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3228_);
lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_nextMacroScope_3218_);
lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_ngen_3219_);
lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_auxDeclNGen_3220_);
lean_ctor_set(v_reuseFailAlloc_3249_, 4, v_traceState_3221_);
lean_ctor_set(v_reuseFailAlloc_3249_, 5, v___x_3229_);
lean_ctor_set(v_reuseFailAlloc_3249_, 6, v_messages_3222_);
lean_ctor_set(v_reuseFailAlloc_3249_, 7, v_infoState_3223_);
lean_ctor_set(v_reuseFailAlloc_3249_, 8, v_snapshotTasks_3224_);
v___x_3231_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v_mctx_3234_; lean_object* v_zetaDeltaFVarIds_3235_; lean_object* v_postponed_3236_; lean_object* v_diag_3237_; lean_object* v___x_3239_; uint8_t v_isShared_3240_; uint8_t v_isSharedCheck_3247_; 
v___x_3232_ = lean_st_ref_set(v___y_3108_, v___x_3231_);
v___x_3233_ = lean_st_ref_take(v___y_3106_);
v_mctx_3234_ = lean_ctor_get(v___x_3233_, 0);
v_zetaDeltaFVarIds_3235_ = lean_ctor_get(v___x_3233_, 2);
v_postponed_3236_ = lean_ctor_get(v___x_3233_, 3);
v_diag_3237_ = lean_ctor_get(v___x_3233_, 4);
v_isSharedCheck_3247_ = !lean_is_exclusive(v___x_3233_);
if (v_isSharedCheck_3247_ == 0)
{
lean_object* v_unused_3248_; 
v_unused_3248_ = lean_ctor_get(v___x_3233_, 1);
lean_dec(v_unused_3248_);
v___x_3239_ = v___x_3233_;
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
else
{
lean_inc(v_diag_3237_);
lean_inc(v_postponed_3236_);
lean_inc(v_zetaDeltaFVarIds_3235_);
lean_inc(v_mctx_3234_);
lean_dec(v___x_3233_);
v___x_3239_ = lean_box(0);
v_isShared_3240_ = v_isSharedCheck_3247_;
goto v_resetjp_3238_;
}
v_resetjp_3238_:
{
lean_object* v___x_3241_; lean_object* v___x_3243_; 
v___x_3241_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3240_ == 0)
{
lean_ctor_set(v___x_3239_, 1, v___x_3241_);
v___x_3243_ = v___x_3239_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3246_; 
v_reuseFailAlloc_3246_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3246_, 0, v_mctx_3234_);
lean_ctor_set(v_reuseFailAlloc_3246_, 1, v___x_3241_);
lean_ctor_set(v_reuseFailAlloc_3246_, 2, v_zetaDeltaFVarIds_3235_);
lean_ctor_set(v_reuseFailAlloc_3246_, 3, v_postponed_3236_);
lean_ctor_set(v_reuseFailAlloc_3246_, 4, v_diag_3237_);
v___x_3243_ = v_reuseFailAlloc_3246_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
lean_object* v___x_3244_; lean_object* v___x_3245_; 
v___x_3244_ = lean_st_ref_set(v___y_3106_, v___x_3243_);
v___x_3245_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_3209_, v___x_3146_, v_compile_3099_, v_logCompileErrors_3100_, v___x_3146_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3245_;
goto v___jp_3115_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3209_);
lean_dec(v_a_3103_);
return v___x_3214_;
}
}
else
{
lean_dec(v_a_3209_);
lean_dec(v_a_3103_);
return v___x_3212_;
}
}
else
{
lean_object* v_a_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3259_; 
lean_dec(v_a_3209_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3252_ = lean_ctor_get(v___x_3210_, 0);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3210_);
if (v_isSharedCheck_3259_ == 0)
{
v___x_3254_ = v___x_3210_;
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_a_3252_);
lean_dec(v___x_3210_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3259_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3257_; 
if (v_isShared_3255_ == 0)
{
v___x_3257_ = v___x_3254_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3252_);
v___x_3257_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
return v___x_3257_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3260_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3208_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3208_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
}
else
{
lean_object* v___x_3268_; 
lean_dec(v_a_3143_);
lean_inc(v___x_3148_);
v___x_3268_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3138_, v___x_3148_, v___y_3106_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_dec_ref(v___x_3268_);
v_a_3111_ = v___x_3146_;
goto v___jp_3110_;
}
else
{
lean_dec(v_a_3103_);
return v___x_3268_;
}
}
}
else
{
lean_object* v_a_3269_; lean_object* v___x_3271_; uint8_t v_isShared_3272_; uint8_t v_isSharedCheck_3276_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3269_ = lean_ctor_get(v___x_3204_, 0);
v_isSharedCheck_3276_ = !lean_is_exclusive(v___x_3204_);
if (v_isSharedCheck_3276_ == 0)
{
v___x_3271_ = v___x_3204_;
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
else
{
lean_inc(v_a_3269_);
lean_dec(v___x_3204_);
v___x_3271_ = lean_box(0);
v_isShared_3272_ = v_isSharedCheck_3276_;
goto v_resetjp_3270_;
}
v_resetjp_3270_:
{
lean_object* v___x_3274_; 
if (v_isShared_3272_ == 0)
{
v___x_3274_ = v___x_3271_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3275_; 
v_reuseFailAlloc_3275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3275_, 0, v_a_3269_);
v___x_3274_ = v_reuseFailAlloc_3275_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
return v___x_3274_;
}
}
}
}
else
{
lean_object* v_a_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3284_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3277_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3284_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3284_ == 0)
{
v___x_3279_ = v___x_3202_;
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_a_3277_);
lean_dec(v___x_3202_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3284_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3282_; 
if (v_isShared_3280_ == 0)
{
v___x_3282_ = v___x_3279_;
goto v_reusejp_3281_;
}
else
{
lean_object* v_reuseFailAlloc_3283_; 
v_reuseFailAlloc_3283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3283_, 0, v_a_3277_);
v___x_3282_ = v_reuseFailAlloc_3283_;
goto v_reusejp_3281_;
}
v_reusejp_3281_:
{
return v___x_3282_;
}
}
}
}
}
else
{
goto v___jp_3176_;
}
}
else
{
lean_dec_ref(v_a_3151_);
goto v___jp_3176_;
}
v___jp_3155_:
{
lean_object* v___x_3157_; 
lean_inc(v___x_3148_);
v___x_3157_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3148_, v_a_3143_, v_compile_3099_, v_logCompileErrors_3100_, v_isMeta_3101_, v___x_3138_, v___x_3146_, v_a_3156_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3157_;
goto v___jp_3115_;
}
v___jp_3158_:
{
if (v___y_3160_ == 0)
{
lean_dec_ref(v___y_3159_);
lean_del_object(v___x_3153_);
v_a_3156_ = v___x_3146_;
goto v___jp_3155_;
}
else
{
lean_object* v___x_3162_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set_tag(v___x_3153_, 1);
lean_ctor_set(v___x_3153_, 0, v___y_3159_);
v___x_3162_ = v___x_3153_;
goto v_reusejp_3161_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___y_3159_);
v___x_3162_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3161_;
}
v_reusejp_3161_:
{
return v___x_3162_;
}
}
}
v___jp_3164_:
{
uint8_t v___x_3166_; 
v___x_3166_ = l_Lean_Exception_isInterrupt(v_a_3165_);
if (v___x_3166_ == 0)
{
uint8_t v___x_3167_; 
lean_inc_ref(v_a_3165_);
v___x_3167_ = l_Lean_Exception_isRuntime(v_a_3165_);
v___y_3159_ = v_a_3165_;
v___y_3160_ = v___x_3167_;
goto v___jp_3158_;
}
else
{
v___y_3159_ = v_a_3165_;
v___y_3160_ = v___x_3166_;
goto v___jp_3158_;
}
}
v___jp_3168_:
{
if (lean_obj_tag(v___y_3169_) == 0)
{
lean_object* v_a_3170_; 
lean_del_object(v___x_3153_);
v_a_3170_ = lean_ctor_get(v___y_3169_, 0);
lean_inc(v_a_3170_);
lean_dec_ref(v___y_3169_);
if (lean_obj_tag(v_a_3170_) == 0)
{
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
v_a_3111_ = v___x_3146_;
goto v___jp_3110_;
}
else
{
lean_object* v_a_3171_; 
v_a_3171_ = lean_ctor_get(v_a_3170_, 0);
lean_inc(v_a_3171_);
lean_dec_ref(v_a_3170_);
v_a_3156_ = v_a_3171_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3172_; 
v_a_3172_ = lean_ctor_get(v___y_3169_, 0);
lean_inc(v_a_3172_);
lean_dec_ref(v___y_3169_);
v_a_3165_ = v_a_3172_;
goto v___jp_3164_;
}
}
v___jp_3173_:
{
lean_object* v___x_3175_; 
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
v___x_3175_ = lean_apply_6(v___y_3174_, v___x_3146_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_, lean_box(0));
v___y_3169_ = v___x_3175_;
goto v___jp_3168_;
}
v___jp_3176_:
{
lean_object* v_options_3177_; lean_object* v_inheritedTraceOptions_3178_; lean_object* v___x_3179_; uint8_t v___x_3180_; 
v_options_3177_ = lean_ctor_get(v___y_3107_, 2);
v_inheritedTraceOptions_3178_ = lean_ctor_get(v___y_3107_, 13);
v___x_3179_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_3180_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3177_, v___x_3179_);
if (v___x_3180_ == 0)
{
lean_object* v___x_3181_; 
lean_del_object(v___x_3153_);
lean_inc(v___x_3148_);
v___x_3181_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_3148_, v_a_3143_, v_compile_3099_, v_logCompileErrors_3100_, v_isMeta_3101_, v___x_3138_, v___x_3146_, v___x_3146_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3181_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_box(0);
lean_inc(v_a_3143_);
v___x_3183_ = l_Lean_Meta_trySynthInstance(v_a_3143_, v___x_3182_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref(v___x_3183_);
if (lean_obj_tag(v_a_3184_) == 1)
{
lean_object* v_a_3185_; uint8_t v_hasTrace_3186_; lean_object* v___f_3187_; 
v_a_3185_ = lean_ctor_get(v_a_3184_, 0);
lean_inc_n(v_a_3185_, 2);
lean_dec_ref(v_a_3184_);
v_hasTrace_3186_ = lean_ctor_get_uint8(v_options_3177_, sizeof(void*)*1);
lean_inc(v___x_3138_);
v___f_3187_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2___boxed), 8, 2);
lean_closure_set(v___f_3187_, 0, v___x_3138_);
lean_closure_set(v___f_3187_, 1, v_a_3185_);
if (v_hasTrace_3186_ == 0)
{
lean_dec(v_a_3185_);
v___y_3174_ = v___f_3187_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3188_; uint8_t v___x_3189_; 
v___x_3188_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3189_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3178_, v_options_3177_, v___x_3188_);
if (v___x_3189_ == 0)
{
lean_dec(v_a_3185_);
v___y_3174_ = v___f_3187_;
goto v___jp_3173_;
}
else
{
lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
lean_dec_ref(v___f_3187_);
v___x_3190_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_3185_);
v___x_3191_ = l_Lean_MessageData_ofExpr(v_a_3185_);
v___x_3192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3190_);
lean_ctor_set(v___x_3192_, 1, v___x_3191_);
v___x_3193_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3147_, v___x_3192_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3193_) == 0)
{
lean_object* v_a_3194_; lean_object* v___x_3195_; 
v_a_3194_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3194_);
lean_dec_ref(v___x_3193_);
lean_inc(v___x_3138_);
v___x_3195_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_3138_, v_a_3185_, v_a_3194_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3169_ = v___x_3195_;
goto v___jp_3168_;
}
else
{
lean_object* v_a_3196_; 
lean_dec(v_a_3185_);
v_a_3196_ = lean_ctor_get(v___x_3193_, 0);
lean_inc(v_a_3196_);
lean_dec_ref(v___x_3193_);
v_a_3165_ = v_a_3196_;
goto v___jp_3164_;
}
}
}
}
else
{
lean_dec(v_a_3184_);
lean_del_object(v___x_3153_);
v_a_3156_ = v___x_3146_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3197_; 
v_a_3197_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3197_);
lean_dec_ref(v___x_3183_);
v_a_3165_ = v_a_3197_;
goto v___jp_3164_;
}
}
}
}
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3286_ = lean_ctor_get(v___x_3150_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3150_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3150_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3150_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
}
}
}
}
else
{
lean_object* v___x_3294_; 
lean_inc(v___y_3108_);
lean_inc_ref(v___y_3107_);
lean_inc(v___y_3106_);
lean_inc_ref(v___y_3105_);
lean_inc(v___x_3148_);
v___x_3294_ = lean_infer_type(v___x_3148_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3294_) == 0)
{
lean_object* v_a_3295_; lean_object* v___x_3296_; 
v_a_3295_ = lean_ctor_get(v___x_3294_, 0);
lean_inc_n(v_a_3295_, 2);
lean_dec_ref(v___x_3294_);
lean_inc(v_a_3143_);
v___x_3296_ = l_Lean_Meta_isExprDefEq(v_a_3143_, v_a_3295_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3296_) == 0)
{
lean_object* v_a_3297_; uint8_t v___x_3298_; 
v_a_3297_ = lean_ctor_get(v___x_3296_, 0);
lean_inc(v_a_3297_);
lean_dec_ref(v___x_3296_);
v___x_3298_ = lean_unbox(v_a_3297_);
lean_dec(v_a_3297_);
if (v___x_3298_ == 0)
{
lean_object* v_options_3299_; lean_object* v_inheritedTraceOptions_3300_; uint8_t v_hasTrace_3301_; 
v_options_3299_ = lean_ctor_get(v___y_3107_, 2);
v_inheritedTraceOptions_3300_ = lean_ctor_get(v___y_3107_, 13);
v_hasTrace_3301_ = lean_ctor_get_uint8(v_options_3299_, sizeof(void*)*1);
if (v_hasTrace_3301_ == 0)
{
lean_dec(v_a_3295_);
goto v___jp_3302_;
}
else
{
lean_object* v___x_3304_; uint8_t v___x_3305_; 
v___x_3304_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3305_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3300_, v_options_3299_, v___x_3304_);
if (v___x_3305_ == 0)
{
lean_dec(v_a_3295_);
goto v___jp_3302_;
}
else
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; 
v___x_3306_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_3103_);
v___x_3307_ = l_Nat_reprFast(v_a_3103_);
v___x_3308_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3308_, 0, v___x_3307_);
v___x_3309_ = l_Lean_MessageData_ofFormat(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3306_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
lean_inc(v_a_3143_);
v___x_3313_ = l_Lean_MessageData_ofExpr(v_a_3143_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_MessageData_ofExpr(v_a_3295_);
v___x_3318_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3318_, 0, v___x_3316_);
lean_ctor_set(v___x_3318_, 1, v___x_3317_);
v___x_3319_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_3320_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
lean_inc(v___x_3148_);
v___x_3321_ = l_Lean_MessageData_ofExpr(v___x_3148_);
v___x_3322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3322_, 0, v___x_3320_);
lean_ctor_set(v___x_3322_, 1, v___x_3321_);
v___x_3323_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3147_, v___x_3322_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
if (lean_obj_tag(v___x_3323_) == 0)
{
lean_object* v_a_3324_; lean_object* v___x_3325_; 
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
lean_inc(v_a_3324_);
lean_dec_ref(v___x_3323_);
lean_inc(v___x_3148_);
v___x_3325_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_3143_, v___x_3148_, v___x_3098_, v___x_3138_, v___x_3146_, v_a_3324_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3325_;
goto v___jp_3115_;
}
else
{
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
return v___x_3323_;
}
}
}
v___jp_3302_:
{
lean_object* v___x_3303_; 
lean_inc(v___x_3148_);
v___x_3303_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_3143_, v___x_3148_, v___x_3098_, v___x_3138_, v___x_3146_, v___x_3146_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
v___y_3116_ = v___x_3303_;
goto v___jp_3115_;
}
}
else
{
lean_object* v___x_3326_; 
lean_dec(v_a_3295_);
lean_dec(v_a_3143_);
lean_inc(v___x_3148_);
v___x_3326_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_3138_, v___x_3148_, v___y_3106_);
if (lean_obj_tag(v___x_3326_) == 0)
{
lean_dec_ref(v___x_3326_);
v_a_3111_ = v___x_3146_;
goto v___jp_3110_;
}
else
{
lean_dec(v_a_3103_);
return v___x_3326_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec(v_a_3295_);
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3327_ = lean_ctor_get(v___x_3296_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3296_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3296_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v_a_3335_; lean_object* v___x_3337_; uint8_t v_isShared_3338_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3335_ = lean_ctor_get(v___x_3294_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3294_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3337_ = v___x_3294_;
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
else
{
lean_inc(v_a_3335_);
lean_dec(v___x_3294_);
v___x_3337_ = lean_box(0);
v_isShared_3338_ = v_isSharedCheck_3342_;
goto v_resetjp_3336_;
}
v_resetjp_3336_:
{
lean_object* v___x_3340_; 
if (v_isShared_3338_ == 0)
{
v___x_3340_ = v___x_3337_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_a_3335_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3350_; 
lean_dec(v_a_3143_);
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3343_ = lean_ctor_get(v___x_3144_, 0);
v_isSharedCheck_3350_ = !lean_is_exclusive(v___x_3144_);
if (v_isSharedCheck_3350_ == 0)
{
v___x_3345_ = v___x_3144_;
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3144_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3350_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v___x_3348_; 
if (v_isShared_3346_ == 0)
{
v___x_3348_ = v___x_3345_;
goto v_reusejp_3347_;
}
else
{
lean_object* v_reuseFailAlloc_3349_; 
v_reuseFailAlloc_3349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3349_, 0, v_a_3343_);
v___x_3348_ = v_reuseFailAlloc_3349_;
goto v_reusejp_3347_;
}
v_reusejp_3347_:
{
return v___x_3348_;
}
}
}
}
else
{
lean_object* v_a_3351_; lean_object* v___x_3353_; uint8_t v_isShared_3354_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3351_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3353_ = v___x_3142_;
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
else
{
lean_inc(v_a_3351_);
lean_dec(v___x_3142_);
v___x_3353_ = lean_box(0);
v_isShared_3354_ = v_isSharedCheck_3358_;
goto v_resetjp_3352_;
}
v_resetjp_3352_:
{
lean_object* v___x_3356_; 
if (v_isShared_3354_ == 0)
{
v___x_3356_ = v___x_3353_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v_a_3351_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
lean_dec(v___x_3138_);
lean_dec(v_a_3103_);
v_a_3359_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3139_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3139_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
v___jp_3110_:
{
lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; 
v___x_3112_ = lean_unsigned_to_nat(1u);
v___x_3113_ = lean_nat_add(v_a_3103_, v___x_3112_);
lean_dec(v_a_3103_);
v___x_3114_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_3095_, v_fst_3096_, v_args_3097_, v___x_3098_, v_compile_3099_, v_logCompileErrors_3100_, v_isMeta_3101_, v___x_3102_, v___x_3113_, v_a_3111_, v___y_3105_, v___y_3106_, v___y_3107_, v___y_3108_);
return v___x_3114_;
}
v___jp_3115_:
{
if (lean_obj_tag(v___y_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v___x_3119_; uint8_t v_isShared_3120_; uint8_t v_isSharedCheck_3126_; 
v_a_3117_ = lean_ctor_get(v___y_3116_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___y_3116_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3119_ = v___y_3116_;
v_isShared_3120_ = v_isSharedCheck_3126_;
goto v_resetjp_3118_;
}
else
{
lean_inc(v_a_3117_);
lean_dec(v___y_3116_);
v___x_3119_ = lean_box(0);
v_isShared_3120_ = v_isSharedCheck_3126_;
goto v_resetjp_3118_;
}
v_resetjp_3118_:
{
if (lean_obj_tag(v_a_3117_) == 0)
{
lean_object* v_a_3121_; lean_object* v___x_3123_; 
lean_dec(v_a_3103_);
v_a_3121_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_a_3121_);
lean_dec_ref(v_a_3117_);
if (v_isShared_3120_ == 0)
{
lean_ctor_set(v___x_3119_, 0, v_a_3121_);
v___x_3123_ = v___x_3119_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3121_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
else
{
lean_object* v_a_3125_; 
lean_del_object(v___x_3119_);
v_a_3125_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v_a_3117_);
v_a_3111_ = v_a_3125_;
goto v___jp_3110_;
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_a_3103_);
v_a_3127_ = lean_ctor_get(v___y_3116_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___y_3116_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___y_3116_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___y_3116_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(lean_object* v_a_3367_, lean_object* v_expectedType_3368_, uint8_t v___x_3369_, uint8_t v___x_3370_, uint8_t v_compile_3371_, uint8_t v_logCompileErrors_3372_, uint8_t v_isMeta_3373_, lean_object* v_x_3374_, lean_object* v_x_3375_, lean_object* v_x_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
lean_object* v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; lean_object* v___y_3386_; lean_object* v___y_3405_; lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3422_; lean_object* v___y_3423_; lean_object* v___y_3424_; lean_object* v_options_3425_; lean_object* v___y_3426_; 
if (lean_obj_tag(v_x_3374_) == 5)
{
lean_object* v_fn_3492_; lean_object* v_arg_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; 
v_fn_3492_ = lean_ctor_get(v_x_3374_, 0);
lean_inc_ref(v_fn_3492_);
v_arg_3493_ = lean_ctor_get(v_x_3374_, 1);
lean_inc_ref(v_arg_3493_);
lean_dec_ref(v_x_3374_);
v___x_3494_ = lean_array_set(v_x_3375_, v_x_3376_, v_arg_3493_);
v___x_3495_ = lean_unsigned_to_nat(1u);
v___x_3496_ = lean_nat_sub(v_x_3376_, v___x_3495_);
lean_dec(v_x_3376_);
v_x_3374_ = v_fn_3492_;
v_x_3375_ = v___x_3494_;
v_x_3376_ = v___x_3496_;
goto _start;
}
else
{
lean_object* v_cls_3498_; lean_object* v___y_3500_; lean_object* v___y_3501_; lean_object* v___y_3502_; lean_object* v___y_3503_; lean_object* v___x_3521_; 
lean_dec(v_x_3376_);
v_cls_3498_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3521_ = l_Lean_Expr_constName_x3f(v_x_3374_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
v___y_3500_ = v___y_3377_;
v___y_3501_ = v___y_3378_;
v___y_3502_ = v___y_3379_;
v___y_3503_ = v___y_3380_;
goto v___jp_3499_;
}
else
{
lean_object* v_val_3522_; lean_object* v___x_3523_; 
v_val_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_val_3522_);
lean_dec_ref(v___x_3521_);
v___x_3523_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3522_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref(v___x_3523_);
if (lean_obj_tag(v_a_3524_) == 6)
{
lean_object* v_val_3525_; lean_object* v___x_3526_; 
lean_dec_ref(v_a_3367_);
v_val_3525_ = lean_ctor_get(v_a_3524_, 0);
lean_inc_ref(v_val_3525_);
lean_dec_ref(v_a_3524_);
lean_inc(v___y_3380_);
lean_inc_ref(v___y_3379_);
lean_inc(v___y_3378_);
lean_inc_ref(v___y_3377_);
lean_inc_ref(v_x_3374_);
v___x_3526_ = lean_infer_type(v_x_3374_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; uint8_t v___x_3528_; lean_object* v___x_3529_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
lean_inc(v_a_3527_);
lean_dec_ref(v___x_3526_);
v___x_3528_ = 0;
v___x_3529_ = l_Lean_Meta_forallMetaTelescope(v_a_3527_, v___x_3528_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3529_) == 0)
{
lean_object* v_a_3530_; lean_object* v_snd_3531_; lean_object* v_fst_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3631_; 
v_a_3530_ = lean_ctor_get(v___x_3529_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v___x_3529_);
v_snd_3531_ = lean_ctor_get(v_a_3530_, 1);
v_fst_3532_ = lean_ctor_get(v_a_3530_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_a_3530_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3534_ = v_a_3530_;
v_isShared_3535_ = v_isSharedCheck_3631_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_snd_3531_);
lean_inc(v_fst_3532_);
lean_dec(v_a_3530_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3631_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v_snd_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3629_; 
v_snd_3536_ = lean_ctor_get(v_snd_3531_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_snd_3531_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_snd_3531_, 0);
lean_dec(v_unused_3630_);
v___x_3538_ = v_snd_3531_;
v_isShared_3539_ = v_isSharedCheck_3629_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_snd_3536_);
lean_dec(v_snd_3531_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3629_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3540_; lean_object* v___y_3542_; lean_object* v___y_3543_; lean_object* v___y_3544_; lean_object* v___y_3545_; lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3540_ = lean_array_get_size(v_x_3375_);
v___x_3577_ = lean_array_get_size(v_fst_3532_);
v___x_3578_ = lean_nat_dec_eq(v___x_3540_, v___x_3577_);
if (v___x_3578_ == 0)
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3582_; 
lean_dec(v_snd_3536_);
lean_dec(v_fst_3532_);
lean_dec_ref(v_val_3525_);
lean_dec_ref(v_expectedType_3368_);
v___x_3579_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_3580_ = l_Lean_MessageData_ofExpr(v_x_3374_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 7);
lean_ctor_set(v___x_3538_, 1, v___x_3580_);
lean_ctor_set(v___x_3538_, 0, v___x_3579_);
v___x_3582_ = v___x_3538_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3579_);
lean_ctor_set(v_reuseFailAlloc_3593_, 1, v___x_3580_);
v___x_3582_ = v_reuseFailAlloc_3593_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3583_; lean_object* v___x_3585_; 
v___x_3583_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 7);
lean_ctor_set(v___x_3534_, 1, v___x_3583_);
lean_ctor_set(v___x_3534_, 0, v___x_3582_);
v___x_3585_ = v___x_3534_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3592_, 1, v___x_3583_);
v___x_3585_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
lean_object* v___x_3586_; lean_object* v___x_3587_; lean_object* v___x_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3586_ = lean_array_to_list(v_x_3375_);
v___x_3587_ = lean_box(0);
v___x_3588_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3586_, v___x_3587_);
v___x_3589_ = l_Lean_MessageData_ofList(v___x_3588_);
v___x_3590_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3585_);
lean_ctor_set(v___x_3590_, 1, v___x_3589_);
v___x_3591_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3590_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
return v___x_3591_;
}
}
}
else
{
lean_object* v___x_3594_; 
lean_inc_ref(v_expectedType_3368_);
v___x_3594_ = l_Lean_Meta_isExprDefEq(v_expectedType_3368_, v_snd_3536_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; uint8_t v___x_3596_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref(v___x_3594_);
v___x_3596_ = lean_unbox(v_a_3595_);
lean_dec(v_a_3595_);
if (v___x_3596_ == 0)
{
lean_object* v_toConstantVal_3597_; lean_object* v_name_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3602_; 
lean_dec(v_fst_3532_);
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
v_toConstantVal_3597_ = lean_ctor_get(v_val_3525_, 0);
lean_inc_ref(v_toConstantVal_3597_);
lean_dec_ref(v_val_3525_);
v_name_3598_ = lean_ctor_get(v_toConstantVal_3597_, 0);
lean_inc(v_name_3598_);
lean_dec_ref(v_toConstantVal_3597_);
v___x_3599_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_3600_ = l_Lean_MessageData_ofExpr(v_expectedType_3368_);
if (v_isShared_3539_ == 0)
{
lean_ctor_set_tag(v___x_3538_, 7);
lean_ctor_set(v___x_3538_, 1, v___x_3600_);
lean_ctor_set(v___x_3538_, 0, v___x_3599_);
v___x_3602_ = v___x_3538_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v___x_3599_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
v___x_3603_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_3535_ == 0)
{
lean_ctor_set_tag(v___x_3534_, 7);
lean_ctor_set(v___x_3534_, 1, v___x_3603_);
lean_ctor_set(v___x_3534_, 0, v___x_3602_);
v___x_3605_ = v___x_3534_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3602_);
lean_ctor_set(v_reuseFailAlloc_3619_, 1, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
v___x_3606_ = l_Lean_MessageData_ofConstName(v_name_3598_, v___x_3369_);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3605_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3609_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
v_a_3611_ = lean_ctor_get(v___x_3610_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3610_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3610_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3610_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
}
else
{
lean_del_object(v___x_3538_);
lean_del_object(v___x_3534_);
lean_dec_ref(v_expectedType_3368_);
v___y_3542_ = v___y_3377_;
v___y_3543_ = v___y_3378_;
v___y_3544_ = v___y_3379_;
v___y_3545_ = v___y_3380_;
goto v___jp_3541_;
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_del_object(v___x_3538_);
lean_del_object(v___x_3534_);
lean_dec(v_fst_3532_);
lean_dec_ref(v_val_3525_);
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_expectedType_3368_);
v_a_3621_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3594_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3594_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
v___jp_3541_:
{
lean_object* v_numParams_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; 
v_numParams_3546_ = lean_ctor_get(v_val_3525_, 3);
lean_inc(v_numParams_3546_);
lean_dec_ref(v_val_3525_);
v___x_3547_ = lean_box(0);
v___x_3548_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_3540_, v_fst_3532_, v_x_3375_, v___x_3370_, v_compile_3371_, v_logCompileErrors_3372_, v_isMeta_3373_, v___x_3369_, v_numParams_3546_, v___x_3547_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec_ref(v_x_3375_);
if (lean_obj_tag(v___x_3548_) == 0)
{
size_t v_sz_3549_; size_t v___x_3550_; lean_object* v___x_3551_; 
lean_dec_ref(v___x_3548_);
v_sz_3549_ = lean_array_size(v_fst_3532_);
v___x_3550_ = ((size_t)0ULL);
v___x_3551_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3549_, v___x_3550_, v_fst_3532_, v___y_3543_);
if (lean_obj_tag(v___x_3551_) == 0)
{
lean_object* v_a_3552_; lean_object* v___x_3554_; uint8_t v_isShared_3555_; uint8_t v_isSharedCheck_3560_; 
v_a_3552_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3560_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3560_ == 0)
{
v___x_3554_ = v___x_3551_;
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
else
{
lean_inc(v_a_3552_);
lean_dec(v___x_3551_);
v___x_3554_ = lean_box(0);
v_isShared_3555_ = v_isSharedCheck_3560_;
goto v_resetjp_3553_;
}
v_resetjp_3553_:
{
lean_object* v___x_3556_; lean_object* v___x_3558_; 
v___x_3556_ = l_Lean_mkAppN(v_x_3374_, v_a_3552_);
lean_dec(v_a_3552_);
if (v_isShared_3555_ == 0)
{
lean_ctor_set(v___x_3554_, 0, v___x_3556_);
v___x_3558_ = v___x_3554_;
goto v_reusejp_3557_;
}
else
{
lean_object* v_reuseFailAlloc_3559_; 
v_reuseFailAlloc_3559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3559_, 0, v___x_3556_);
v___x_3558_ = v_reuseFailAlloc_3559_;
goto v_reusejp_3557_;
}
v_reusejp_3557_:
{
return v___x_3558_;
}
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec_ref(v_x_3374_);
v_a_3561_ = lean_ctor_get(v___x_3551_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3551_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3551_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3551_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
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
else
{
lean_object* v_a_3569_; lean_object* v___x_3571_; uint8_t v_isShared_3572_; uint8_t v_isSharedCheck_3576_; 
lean_dec(v_fst_3532_);
lean_dec_ref(v_x_3374_);
v_a_3569_ = lean_ctor_get(v___x_3548_, 0);
v_isSharedCheck_3576_ = !lean_is_exclusive(v___x_3548_);
if (v_isSharedCheck_3576_ == 0)
{
v___x_3571_ = v___x_3548_;
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
else
{
lean_inc(v_a_3569_);
lean_dec(v___x_3548_);
v___x_3571_ = lean_box(0);
v_isShared_3572_ = v_isSharedCheck_3576_;
goto v_resetjp_3570_;
}
v_resetjp_3570_:
{
lean_object* v___x_3574_; 
if (v_isShared_3572_ == 0)
{
v___x_3574_ = v___x_3571_;
goto v_reusejp_3573_;
}
else
{
lean_object* v_reuseFailAlloc_3575_; 
v_reuseFailAlloc_3575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3575_, 0, v_a_3569_);
v___x_3574_ = v_reuseFailAlloc_3575_;
goto v_reusejp_3573_;
}
v_reusejp_3573_:
{
return v___x_3574_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec_ref(v_val_3525_);
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_expectedType_3368_);
v_a_3632_ = lean_ctor_get(v___x_3529_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3529_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3529_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3529_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_dec_ref(v_val_3525_);
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_expectedType_3368_);
return v___x_3526_;
}
}
else
{
lean_dec(v_a_3524_);
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
v___y_3500_ = v___y_3377_;
v___y_3501_ = v___y_3378_;
v___y_3502_ = v___y_3379_;
v___y_3503_ = v___y_3380_;
goto v___jp_3499_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v_x_3375_);
lean_dec_ref(v_x_3374_);
lean_dec_ref(v_expectedType_3368_);
lean_dec_ref(v_a_3367_);
v_a_3640_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3523_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3523_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
v___jp_3499_:
{
lean_object* v_options_3504_; uint8_t v_hasTrace_3505_; 
v_options_3504_ = lean_ctor_get(v___y_3502_, 2);
v_hasTrace_3505_ = lean_ctor_get_uint8(v_options_3504_, sizeof(void*)*1);
if (v_hasTrace_3505_ == 0)
{
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v___y_3424_ = v___y_3502_;
v_options_3425_ = v_options_3504_;
v___y_3426_ = v___y_3503_;
goto v___jp_3421_;
}
else
{
lean_object* v_inheritedTraceOptions_3506_; lean_object* v___x_3507_; uint8_t v___x_3508_; 
v_inheritedTraceOptions_3506_ = lean_ctor_get(v___y_3502_, 13);
v___x_3507_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3508_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3506_, v_options_3504_, v___x_3507_);
if (v___x_3508_ == 0)
{
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v___y_3424_ = v___y_3502_;
v_options_3425_ = v_options_3504_;
v___y_3426_ = v___y_3503_;
goto v___jp_3421_;
}
else
{
lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v___x_3512_; 
v___x_3509_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_3367_);
v___x_3510_ = l_Lean_MessageData_ofExpr(v_a_3367_);
v___x_3511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3509_);
lean_ctor_set(v___x_3511_, 1, v___x_3510_);
v___x_3512_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3498_, v___x_3511_, v___y_3500_, v___y_3501_, v___y_3502_, v___y_3503_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_dec_ref(v___x_3512_);
v___y_3422_ = v___y_3500_;
v___y_3423_ = v___y_3501_;
v___y_3424_ = v___y_3502_;
v_options_3425_ = v_options_3504_;
v___y_3426_ = v___y_3503_;
goto v___jp_3421_;
}
else
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3520_; 
lean_dec_ref(v_expectedType_3368_);
lean_dec_ref(v_a_3367_);
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3520_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3520_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3520_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_a_3513_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
}
}
}
}
}
v___jp_3382_:
{
lean_object* v___x_3387_; 
v___x_3387_ = l_Lean_enableRealizationsForConst(v___y_3384_, v___y_3385_, v___y_3386_);
if (lean_obj_tag(v___x_3387_) == 0)
{
lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
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
lean_ctor_set(v___x_3389_, 0, v___y_3383_);
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___y_3383_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
else
{
lean_object* v_a_3396_; lean_object* v___x_3398_; uint8_t v_isShared_3399_; uint8_t v_isSharedCheck_3403_; 
lean_dec_ref(v___y_3383_);
v_a_3396_ = lean_ctor_get(v___x_3387_, 0);
v_isSharedCheck_3403_ = !lean_is_exclusive(v___x_3387_);
if (v_isSharedCheck_3403_ == 0)
{
v___x_3398_ = v___x_3387_;
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
else
{
lean_inc(v_a_3396_);
lean_dec(v___x_3387_);
v___x_3398_ = lean_box(0);
v_isShared_3399_ = v_isSharedCheck_3403_;
goto v_resetjp_3397_;
}
v_resetjp_3397_:
{
lean_object* v___x_3401_; 
if (v_isShared_3399_ == 0)
{
v___x_3401_ = v___x_3398_;
goto v_reusejp_3400_;
}
else
{
lean_object* v_reuseFailAlloc_3402_; 
v_reuseFailAlloc_3402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3402_, 0, v_a_3396_);
v___x_3401_ = v_reuseFailAlloc_3402_;
goto v_reusejp_3400_;
}
v_reusejp_3400_:
{
return v___x_3401_;
}
}
}
}
v___jp_3404_:
{
if (v_compile_3371_ == 0)
{
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v___y_3408_;
goto v___jp_3382_;
}
else
{
lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3409_ = lean_unsigned_to_nat(1u);
v___x_3410_ = lean_mk_empty_array_with_capacity(v___x_3409_);
lean_inc(v___y_3406_);
v___x_3411_ = lean_array_push(v___x_3410_, v___y_3406_);
v___x_3412_ = l_Lean_compileDecls(v___x_3411_, v_logCompileErrors_3372_, v___y_3407_, v___y_3408_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_dec_ref(v___x_3412_);
v___y_3383_ = v___y_3405_;
v___y_3384_ = v___y_3406_;
v___y_3385_ = v___y_3407_;
v___y_3386_ = v___y_3408_;
goto v___jp_3382_;
}
else
{
lean_object* v_a_3413_; lean_object* v___x_3415_; uint8_t v_isShared_3416_; uint8_t v_isSharedCheck_3420_; 
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
v_isSharedCheck_3420_ = !lean_is_exclusive(v___x_3412_);
if (v_isSharedCheck_3420_ == 0)
{
v___x_3415_ = v___x_3412_;
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
else
{
lean_inc(v_a_3413_);
lean_dec(v___x_3412_);
v___x_3415_ = lean_box(0);
v_isShared_3416_ = v_isSharedCheck_3420_;
goto v_resetjp_3414_;
}
v_resetjp_3414_:
{
lean_object* v___x_3418_; 
if (v_isShared_3416_ == 0)
{
v___x_3418_ = v___x_3415_;
goto v_reusejp_3417_;
}
else
{
lean_object* v_reuseFailAlloc_3419_; 
v_reuseFailAlloc_3419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3419_, 0, v_a_3413_);
v___x_3418_ = v_reuseFailAlloc_3419_;
goto v_reusejp_3417_;
}
v_reusejp_3417_:
{
return v___x_3418_;
}
}
}
}
}
v___jp_3421_:
{
lean_object* v___x_3427_; uint8_t v___x_3428_; 
v___x_3427_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3428_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3425_, v___x_3427_);
if (v___x_3428_ == 0)
{
lean_object* v___x_3429_; 
lean_dec_ref(v_expectedType_3368_);
v___x_3429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3429_, 0, v_a_3367_);
return v___x_3429_;
}
else
{
lean_object* v___x_3430_; 
lean_inc(v___y_3426_);
lean_inc_ref(v___y_3424_);
lean_inc(v___y_3423_);
lean_inc_ref(v___y_3422_);
lean_inc_ref(v_a_3367_);
v___x_3430_ = lean_infer_type(v_a_3367_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3426_);
if (lean_obj_tag(v___x_3430_) == 0)
{
lean_object* v_a_3431_; lean_object* v___x_3432_; 
v_a_3431_ = lean_ctor_get(v___x_3430_, 0);
lean_inc(v_a_3431_);
lean_dec_ref(v___x_3430_);
lean_inc_ref(v_expectedType_3368_);
v___x_3432_ = l_Lean_Meta_isExprDefEq(v_expectedType_3368_, v_a_3431_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3426_);
if (lean_obj_tag(v___x_3432_) == 0)
{
lean_object* v_a_3433_; lean_object* v___x_3435_; uint8_t v_isShared_3436_; uint8_t v_isSharedCheck_3483_; 
v_a_3433_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3435_ = v___x_3432_;
v_isShared_3436_ = v_isSharedCheck_3483_;
goto v_resetjp_3434_;
}
else
{
lean_inc(v_a_3433_);
lean_dec(v___x_3432_);
v___x_3435_ = lean_box(0);
v_isShared_3436_ = v_isSharedCheck_3483_;
goto v_resetjp_3434_;
}
v_resetjp_3434_:
{
uint8_t v___x_3437_; 
v___x_3437_ = lean_unbox(v_a_3433_);
lean_dec(v_a_3433_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; lean_object* v___x_3439_; lean_object* v_a_3440_; lean_object* v___x_3441_; 
lean_del_object(v___x_3435_);
v___x_3438_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3439_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3438_, v___y_3426_);
v_a_3440_ = lean_ctor_get(v___x_3439_, 0);
lean_inc_n(v_a_3440_, 2);
lean_dec_ref(v___x_3439_);
v___x_3441_ = l_Lean_Meta_mkAuxDefinition(v_a_3440_, v_expectedType_3368_, v_a_3367_, v___x_3369_, v___x_3369_, v___x_3370_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3426_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; uint8_t v___x_3443_; lean_object* v___x_3444_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = 3;
lean_inc(v_a_3440_);
v___x_3444_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3440_, v___x_3443_, v___y_3423_, v___y_3426_);
lean_dec_ref(v___x_3444_);
if (v_isMeta_3373_ == 0)
{
v___y_3405_ = v_a_3442_;
v___y_3406_ = v_a_3440_;
v___y_3407_ = v___y_3424_;
v___y_3408_ = v___y_3426_;
goto v___jp_3404_;
}
else
{
lean_object* v___x_3445_; lean_object* v_env_3446_; lean_object* v_nextMacroScope_3447_; lean_object* v_ngen_3448_; lean_object* v_auxDeclNGen_3449_; lean_object* v_traceState_3450_; lean_object* v_messages_3451_; lean_object* v_infoState_3452_; lean_object* v_snapshotTasks_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3478_; 
v___x_3445_ = lean_st_ref_take(v___y_3426_);
v_env_3446_ = lean_ctor_get(v___x_3445_, 0);
v_nextMacroScope_3447_ = lean_ctor_get(v___x_3445_, 1);
v_ngen_3448_ = lean_ctor_get(v___x_3445_, 2);
v_auxDeclNGen_3449_ = lean_ctor_get(v___x_3445_, 3);
v_traceState_3450_ = lean_ctor_get(v___x_3445_, 4);
v_messages_3451_ = lean_ctor_get(v___x_3445_, 6);
v_infoState_3452_ = lean_ctor_get(v___x_3445_, 7);
v_snapshotTasks_3453_ = lean_ctor_get(v___x_3445_, 8);
v_isSharedCheck_3478_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3478_ == 0)
{
lean_object* v_unused_3479_; 
v_unused_3479_ = lean_ctor_get(v___x_3445_, 5);
lean_dec(v_unused_3479_);
v___x_3455_ = v___x_3445_;
v_isShared_3456_ = v_isSharedCheck_3478_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_snapshotTasks_3453_);
lean_inc(v_infoState_3452_);
lean_inc(v_messages_3451_);
lean_inc(v_traceState_3450_);
lean_inc(v_auxDeclNGen_3449_);
lean_inc(v_ngen_3448_);
lean_inc(v_nextMacroScope_3447_);
lean_inc(v_env_3446_);
lean_dec(v___x_3445_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3478_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
lean_inc(v_a_3440_);
v___x_3457_ = l_Lean_markMeta(v_env_3446_, v_a_3440_);
v___x_3458_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 5, v___x_3458_);
lean_ctor_set(v___x_3455_, 0, v___x_3457_);
v___x_3460_ = v___x_3455_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3477_; 
v_reuseFailAlloc_3477_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3477_, 0, v___x_3457_);
lean_ctor_set(v_reuseFailAlloc_3477_, 1, v_nextMacroScope_3447_);
lean_ctor_set(v_reuseFailAlloc_3477_, 2, v_ngen_3448_);
lean_ctor_set(v_reuseFailAlloc_3477_, 3, v_auxDeclNGen_3449_);
lean_ctor_set(v_reuseFailAlloc_3477_, 4, v_traceState_3450_);
lean_ctor_set(v_reuseFailAlloc_3477_, 5, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3477_, 6, v_messages_3451_);
lean_ctor_set(v_reuseFailAlloc_3477_, 7, v_infoState_3452_);
lean_ctor_set(v_reuseFailAlloc_3477_, 8, v_snapshotTasks_3453_);
v___x_3460_ = v_reuseFailAlloc_3477_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v_mctx_3463_; lean_object* v_zetaDeltaFVarIds_3464_; lean_object* v_postponed_3465_; lean_object* v_diag_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3475_; 
v___x_3461_ = lean_st_ref_set(v___y_3426_, v___x_3460_);
v___x_3462_ = lean_st_ref_take(v___y_3423_);
v_mctx_3463_ = lean_ctor_get(v___x_3462_, 0);
v_zetaDeltaFVarIds_3464_ = lean_ctor_get(v___x_3462_, 2);
v_postponed_3465_ = lean_ctor_get(v___x_3462_, 3);
v_diag_3466_ = lean_ctor_get(v___x_3462_, 4);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3475_ == 0)
{
lean_object* v_unused_3476_; 
v_unused_3476_ = lean_ctor_get(v___x_3462_, 1);
lean_dec(v_unused_3476_);
v___x_3468_ = v___x_3462_;
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_diag_3466_);
lean_inc(v_postponed_3465_);
lean_inc(v_zetaDeltaFVarIds_3464_);
lean_inc(v_mctx_3463_);
lean_dec(v___x_3462_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3475_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3470_; lean_object* v___x_3472_; 
v___x_3470_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3469_ == 0)
{
lean_ctor_set(v___x_3468_, 1, v___x_3470_);
v___x_3472_ = v___x_3468_;
goto v_reusejp_3471_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_mctx_3463_);
lean_ctor_set(v_reuseFailAlloc_3474_, 1, v___x_3470_);
lean_ctor_set(v_reuseFailAlloc_3474_, 2, v_zetaDeltaFVarIds_3464_);
lean_ctor_set(v_reuseFailAlloc_3474_, 3, v_postponed_3465_);
lean_ctor_set(v_reuseFailAlloc_3474_, 4, v_diag_3466_);
v___x_3472_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3471_;
}
v_reusejp_3471_:
{
lean_object* v___x_3473_; 
v___x_3473_ = lean_st_ref_set(v___y_3423_, v___x_3472_);
v___y_3405_ = v_a_3442_;
v___y_3406_ = v_a_3440_;
v___y_3407_ = v___y_3424_;
v___y_3408_ = v___y_3426_;
goto v___jp_3404_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3440_);
return v___x_3441_;
}
}
else
{
lean_object* v___x_3481_; 
lean_dec_ref(v_expectedType_3368_);
if (v_isShared_3436_ == 0)
{
lean_ctor_set(v___x_3435_, 0, v_a_3367_);
v___x_3481_ = v___x_3435_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3367_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_dec_ref(v_expectedType_3368_);
lean_dec_ref(v_a_3367_);
v_a_3484_ = lean_ctor_get(v___x_3432_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3432_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3432_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3432_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
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
else
{
lean_dec_ref(v_expectedType_3368_);
lean_dec_ref(v_a_3367_);
return v___x_3430_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(lean_object* v_a_3648_, lean_object* v_expectedType_3649_, uint8_t v___x_3650_, uint8_t v___x_3651_, uint8_t v_compile_3652_, uint8_t v_logCompileErrors_3653_, uint8_t v_isMeta_3654_, lean_object* v_x_3655_, lean_object* v_x_3656_, lean_object* v_x_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___y_3667_; lean_object* v___y_3686_; lean_object* v___y_3687_; lean_object* v___y_3688_; lean_object* v___y_3689_; lean_object* v___y_3703_; lean_object* v___y_3704_; lean_object* v___y_3705_; lean_object* v_options_3706_; lean_object* v___y_3707_; 
if (lean_obj_tag(v_x_3655_) == 5)
{
lean_object* v_fn_3773_; lean_object* v_arg_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; 
v_fn_3773_ = lean_ctor_get(v_x_3655_, 0);
lean_inc_ref(v_fn_3773_);
v_arg_3774_ = lean_ctor_get(v_x_3655_, 1);
lean_inc_ref(v_arg_3774_);
lean_dec_ref(v_x_3655_);
v___x_3775_ = lean_array_set(v_x_3656_, v_x_3657_, v_arg_3774_);
v___x_3776_ = lean_unsigned_to_nat(1u);
v___x_3777_ = lean_nat_sub(v_x_3657_, v___x_3776_);
v___x_3778_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_a_3648_, v_expectedType_3649_, v___x_3650_, v___x_3651_, v_compile_3652_, v_logCompileErrors_3653_, v_isMeta_3654_, v_fn_3773_, v___x_3775_, v___x_3777_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3778_;
}
else
{
lean_object* v_cls_3779_; lean_object* v___y_3781_; lean_object* v___y_3782_; lean_object* v___y_3783_; lean_object* v___y_3784_; lean_object* v___x_3802_; 
v_cls_3779_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_3802_ = l_Lean_Expr_constName_x3f(v_x_3655_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
v___y_3781_ = v___y_3658_;
v___y_3782_ = v___y_3659_;
v___y_3783_ = v___y_3660_;
v___y_3784_ = v___y_3661_;
goto v___jp_3780_;
}
else
{
lean_object* v_val_3803_; lean_object* v___x_3804_; 
v_val_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_val_3803_);
lean_dec_ref(v___x_3802_);
v___x_3804_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_3803_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3805_);
lean_dec_ref(v___x_3804_);
if (lean_obj_tag(v_a_3805_) == 6)
{
lean_object* v_val_3806_; lean_object* v___x_3807_; 
lean_dec_ref(v_a_3648_);
v_val_3806_ = lean_ctor_get(v_a_3805_, 0);
lean_inc_ref(v_val_3806_);
lean_dec_ref(v_a_3805_);
lean_inc(v___y_3661_);
lean_inc_ref(v___y_3660_);
lean_inc(v___y_3659_);
lean_inc_ref(v___y_3658_);
lean_inc_ref(v_x_3655_);
v___x_3807_ = lean_infer_type(v_x_3655_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; uint8_t v___x_3809_; lean_object* v___x_3810_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
lean_inc(v_a_3808_);
lean_dec_ref(v___x_3807_);
v___x_3809_ = 0;
v___x_3810_ = l_Lean_Meta_forallMetaTelescope(v_a_3808_, v___x_3809_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v_snd_3812_; lean_object* v_fst_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3912_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
lean_inc(v_a_3811_);
lean_dec_ref(v___x_3810_);
v_snd_3812_ = lean_ctor_get(v_a_3811_, 1);
v_fst_3813_ = lean_ctor_get(v_a_3811_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v_a_3811_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3815_ = v_a_3811_;
v_isShared_3816_ = v_isSharedCheck_3912_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_snd_3812_);
lean_inc(v_fst_3813_);
lean_dec(v_a_3811_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3912_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v_snd_3817_; lean_object* v___x_3819_; uint8_t v_isShared_3820_; uint8_t v_isSharedCheck_3910_; 
v_snd_3817_ = lean_ctor_get(v_snd_3812_, 1);
v_isSharedCheck_3910_ = !lean_is_exclusive(v_snd_3812_);
if (v_isSharedCheck_3910_ == 0)
{
lean_object* v_unused_3911_; 
v_unused_3911_ = lean_ctor_get(v_snd_3812_, 0);
lean_dec(v_unused_3911_);
v___x_3819_ = v_snd_3812_;
v_isShared_3820_ = v_isSharedCheck_3910_;
goto v_resetjp_3818_;
}
else
{
lean_inc(v_snd_3817_);
lean_dec(v_snd_3812_);
v___x_3819_ = lean_box(0);
v_isShared_3820_ = v_isSharedCheck_3910_;
goto v_resetjp_3818_;
}
v_resetjp_3818_:
{
lean_object* v___x_3821_; lean_object* v___y_3823_; lean_object* v___y_3824_; lean_object* v___y_3825_; lean_object* v___y_3826_; lean_object* v___x_3858_; uint8_t v___x_3859_; 
v___x_3821_ = lean_array_get_size(v_x_3656_);
v___x_3858_ = lean_array_get_size(v_fst_3813_);
v___x_3859_ = lean_nat_dec_eq(v___x_3821_, v___x_3858_);
if (v___x_3859_ == 0)
{
lean_object* v___x_3860_; lean_object* v___x_3861_; lean_object* v___x_3863_; 
lean_dec(v_snd_3817_);
lean_dec(v_fst_3813_);
lean_dec_ref(v_val_3806_);
lean_dec_ref(v_expectedType_3649_);
v___x_3860_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_3861_ = l_Lean_MessageData_ofExpr(v_x_3655_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 7);
lean_ctor_set(v___x_3819_, 1, v___x_3861_);
lean_ctor_set(v___x_3819_, 0, v___x_3860_);
v___x_3863_ = v___x_3819_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3860_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v___x_3861_);
v___x_3863_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
lean_object* v___x_3864_; lean_object* v___x_3866_; 
v___x_3864_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_3816_ == 0)
{
lean_ctor_set_tag(v___x_3815_, 7);
lean_ctor_set(v___x_3815_, 1, v___x_3864_);
lean_ctor_set(v___x_3815_, 0, v___x_3863_);
v___x_3866_ = v___x_3815_;
goto v_reusejp_3865_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3873_, 1, v___x_3864_);
v___x_3866_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3865_;
}
v_reusejp_3865_:
{
lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; 
v___x_3867_ = lean_array_to_list(v_x_3656_);
v___x_3868_ = lean_box(0);
v___x_3869_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_3867_, v___x_3868_);
v___x_3870_ = l_Lean_MessageData_ofList(v___x_3869_);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3866_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3871_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3872_;
}
}
}
else
{
lean_object* v___x_3875_; 
lean_inc_ref(v_expectedType_3649_);
v___x_3875_ = l_Lean_Meta_isExprDefEq(v_expectedType_3649_, v_snd_3817_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3875_) == 0)
{
lean_object* v_a_3876_; uint8_t v___x_3877_; 
v_a_3876_ = lean_ctor_get(v___x_3875_, 0);
lean_inc(v_a_3876_);
lean_dec_ref(v___x_3875_);
v___x_3877_ = lean_unbox(v_a_3876_);
lean_dec(v_a_3876_);
if (v___x_3877_ == 0)
{
lean_object* v_toConstantVal_3878_; lean_object* v_name_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3883_; 
lean_dec(v_fst_3813_);
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
v_toConstantVal_3878_ = lean_ctor_get(v_val_3806_, 0);
lean_inc_ref(v_toConstantVal_3878_);
lean_dec_ref(v_val_3806_);
v_name_3879_ = lean_ctor_get(v_toConstantVal_3878_, 0);
lean_inc(v_name_3879_);
lean_dec_ref(v_toConstantVal_3878_);
v___x_3880_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_3881_ = l_Lean_MessageData_ofExpr(v_expectedType_3649_);
if (v_isShared_3820_ == 0)
{
lean_ctor_set_tag(v___x_3819_, 7);
lean_ctor_set(v___x_3819_, 1, v___x_3881_);
lean_ctor_set(v___x_3819_, 0, v___x_3880_);
v___x_3883_ = v___x_3819_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v___x_3880_);
lean_ctor_set(v_reuseFailAlloc_3901_, 1, v___x_3881_);
v___x_3883_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
lean_object* v___x_3884_; lean_object* v___x_3886_; 
v___x_3884_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_3816_ == 0)
{
lean_ctor_set_tag(v___x_3815_, 7);
lean_ctor_set(v___x_3815_, 1, v___x_3884_);
lean_ctor_set(v___x_3815_, 0, v___x_3883_);
v___x_3886_ = v___x_3815_;
goto v_reusejp_3885_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3900_, 1, v___x_3884_);
v___x_3886_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3885_;
}
v_reusejp_3885_:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v_a_3892_; lean_object* v___x_3894_; uint8_t v_isShared_3895_; uint8_t v_isSharedCheck_3899_; 
v___x_3887_ = l_Lean_MessageData_ofConstName(v_name_3879_, v___x_3650_);
v___x_3888_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3886_);
lean_ctor_set(v___x_3888_, 1, v___x_3887_);
v___x_3889_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_3890_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3888_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_3890_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3899_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3899_ == 0)
{
v___x_3894_ = v___x_3891_;
v_isShared_3895_ = v_isSharedCheck_3899_;
goto v_resetjp_3893_;
}
else
{
lean_inc(v_a_3892_);
lean_dec(v___x_3891_);
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
else
{
lean_del_object(v___x_3819_);
lean_del_object(v___x_3815_);
lean_dec_ref(v_expectedType_3649_);
v___y_3823_ = v___y_3658_;
v___y_3824_ = v___y_3659_;
v___y_3825_ = v___y_3660_;
v___y_3826_ = v___y_3661_;
goto v___jp_3822_;
}
}
else
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3909_; 
lean_del_object(v___x_3819_);
lean_del_object(v___x_3815_);
lean_dec(v_fst_3813_);
lean_dec_ref(v_val_3806_);
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_expectedType_3649_);
v_a_3902_ = lean_ctor_get(v___x_3875_, 0);
v_isSharedCheck_3909_ = !lean_is_exclusive(v___x_3875_);
if (v_isSharedCheck_3909_ == 0)
{
v___x_3904_ = v___x_3875_;
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3875_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3909_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
lean_object* v___x_3907_; 
if (v_isShared_3905_ == 0)
{
v___x_3907_ = v___x_3904_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
return v___x_3907_;
}
}
}
}
v___jp_3822_:
{
lean_object* v_numParams_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; 
v_numParams_3827_ = lean_ctor_get(v_val_3806_, 3);
lean_inc(v_numParams_3827_);
lean_dec_ref(v_val_3806_);
v___x_3828_ = lean_box(0);
v___x_3829_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v___x_3821_, v_fst_3813_, v_x_3656_, v___x_3651_, v_compile_3652_, v_logCompileErrors_3653_, v_isMeta_3654_, v___x_3650_, v_numParams_3827_, v___x_3828_, v___y_3823_, v___y_3824_, v___y_3825_, v___y_3826_);
lean_dec_ref(v_x_3656_);
if (lean_obj_tag(v___x_3829_) == 0)
{
size_t v_sz_3830_; size_t v___x_3831_; lean_object* v___x_3832_; 
lean_dec_ref(v___x_3829_);
v_sz_3830_ = lean_array_size(v_fst_3813_);
v___x_3831_ = ((size_t)0ULL);
v___x_3832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_3830_, v___x_3831_, v_fst_3813_, v___y_3824_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; lean_object* v___x_3835_; uint8_t v_isShared_3836_; uint8_t v_isSharedCheck_3841_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3835_ = v___x_3832_;
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
else
{
lean_inc(v_a_3833_);
lean_dec(v___x_3832_);
v___x_3835_ = lean_box(0);
v_isShared_3836_ = v_isSharedCheck_3841_;
goto v_resetjp_3834_;
}
v_resetjp_3834_:
{
lean_object* v___x_3837_; lean_object* v___x_3839_; 
v___x_3837_ = l_Lean_mkAppN(v_x_3655_, v_a_3833_);
lean_dec(v_a_3833_);
if (v_isShared_3836_ == 0)
{
lean_ctor_set(v___x_3835_, 0, v___x_3837_);
v___x_3839_ = v___x_3835_;
goto v_reusejp_3838_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3837_);
v___x_3839_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3838_;
}
v_reusejp_3838_:
{
return v___x_3839_;
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_dec_ref(v_x_3655_);
v_a_3842_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3832_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3832_);
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
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec(v_fst_3813_);
lean_dec_ref(v_x_3655_);
v_a_3850_ = lean_ctor_get(v___x_3829_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3829_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3829_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3829_);
v___x_3852_ = lean_box(0);
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
v_resetjp_3851_:
{
lean_object* v___x_3855_; 
if (v_isShared_3853_ == 0)
{
v___x_3855_ = v___x_3852_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_a_3850_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3920_; 
lean_dec_ref(v_val_3806_);
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_expectedType_3649_);
v_a_3913_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3920_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3920_ == 0)
{
v___x_3915_ = v___x_3810_;
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_dec(v___x_3810_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3920_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3918_; 
if (v_isShared_3916_ == 0)
{
v___x_3918_ = v___x_3915_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v_a_3913_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
return v___x_3918_;
}
}
}
}
else
{
lean_dec_ref(v_val_3806_);
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_expectedType_3649_);
return v___x_3807_;
}
}
else
{
lean_dec(v_a_3805_);
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
v___y_3781_ = v___y_3658_;
v___y_3782_ = v___y_3659_;
v___y_3783_ = v___y_3660_;
v___y_3784_ = v___y_3661_;
goto v___jp_3780_;
}
}
else
{
lean_object* v_a_3921_; lean_object* v___x_3923_; uint8_t v_isShared_3924_; uint8_t v_isSharedCheck_3928_; 
lean_dec_ref(v_x_3656_);
lean_dec_ref(v_x_3655_);
lean_dec_ref(v_expectedType_3649_);
lean_dec_ref(v_a_3648_);
v_a_3921_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3923_ = v___x_3804_;
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
else
{
lean_inc(v_a_3921_);
lean_dec(v___x_3804_);
v___x_3923_ = lean_box(0);
v_isShared_3924_ = v_isSharedCheck_3928_;
goto v_resetjp_3922_;
}
v_resetjp_3922_:
{
lean_object* v___x_3926_; 
if (v_isShared_3924_ == 0)
{
v___x_3926_ = v___x_3923_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v_a_3921_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
v___jp_3780_:
{
lean_object* v_options_3785_; uint8_t v_hasTrace_3786_; 
v_options_3785_ = lean_ctor_get(v___y_3783_, 2);
v_hasTrace_3786_ = lean_ctor_get_uint8(v_options_3785_, sizeof(void*)*1);
if (v_hasTrace_3786_ == 0)
{
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v___y_3705_ = v___y_3783_;
v_options_3706_ = v_options_3785_;
v___y_3707_ = v___y_3784_;
goto v___jp_3702_;
}
else
{
lean_object* v_inheritedTraceOptions_3787_; lean_object* v___x_3788_; uint8_t v___x_3789_; 
v_inheritedTraceOptions_3787_ = lean_ctor_get(v___y_3783_, 13);
v___x_3788_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_3789_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3787_, v_options_3785_, v___x_3788_);
if (v___x_3789_ == 0)
{
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v___y_3705_ = v___y_3783_;
v_options_3706_ = v_options_3785_;
v___y_3707_ = v___y_3784_;
goto v___jp_3702_;
}
else
{
lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3790_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_3648_);
v___x_3791_ = l_Lean_MessageData_ofExpr(v_a_3648_);
v___x_3792_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3790_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_3779_, v___x_3792_, v___y_3781_, v___y_3782_, v___y_3783_, v___y_3784_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_dec_ref(v___x_3793_);
v___y_3703_ = v___y_3781_;
v___y_3704_ = v___y_3782_;
v___y_3705_ = v___y_3783_;
v_options_3706_ = v_options_3785_;
v___y_3707_ = v___y_3784_;
goto v___jp_3702_;
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_dec_ref(v_expectedType_3649_);
lean_dec_ref(v_a_3648_);
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
}
}
v___jp_3663_:
{
lean_object* v___x_3668_; 
v___x_3668_ = l_Lean_enableRealizationsForConst(v___y_3665_, v___y_3666_, v___y_3667_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v___x_3668_, 0);
lean_dec(v_unused_3676_);
v___x_3670_ = v___x_3668_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_dec(v___x_3668_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v___y_3664_);
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___y_3664_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
else
{
lean_object* v_a_3677_; lean_object* v___x_3679_; uint8_t v_isShared_3680_; uint8_t v_isSharedCheck_3684_; 
lean_dec_ref(v___y_3664_);
v_a_3677_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3679_ = v___x_3668_;
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
else
{
lean_inc(v_a_3677_);
lean_dec(v___x_3668_);
v___x_3679_ = lean_box(0);
v_isShared_3680_ = v_isSharedCheck_3684_;
goto v_resetjp_3678_;
}
v_resetjp_3678_:
{
lean_object* v___x_3682_; 
if (v_isShared_3680_ == 0)
{
v___x_3682_ = v___x_3679_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v_a_3677_);
v___x_3682_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
return v___x_3682_;
}
}
}
}
v___jp_3685_:
{
if (v_compile_3652_ == 0)
{
v___y_3664_ = v___y_3686_;
v___y_3665_ = v___y_3687_;
v___y_3666_ = v___y_3688_;
v___y_3667_ = v___y_3689_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3693_; 
v___x_3690_ = lean_unsigned_to_nat(1u);
v___x_3691_ = lean_mk_empty_array_with_capacity(v___x_3690_);
lean_inc(v___y_3687_);
v___x_3692_ = lean_array_push(v___x_3691_, v___y_3687_);
v___x_3693_ = l_Lean_compileDecls(v___x_3692_, v_logCompileErrors_3653_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3693_) == 0)
{
lean_dec_ref(v___x_3693_);
v___y_3664_ = v___y_3686_;
v___y_3665_ = v___y_3687_;
v___y_3666_ = v___y_3688_;
v___y_3667_ = v___y_3689_;
goto v___jp_3663_;
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
v_a_3694_ = lean_ctor_get(v___x_3693_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3693_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3693_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3693_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
v___jp_3702_:
{
lean_object* v___x_3708_; uint8_t v___x_3709_; 
v___x_3708_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3709_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3706_, v___x_3708_);
if (v___x_3709_ == 0)
{
lean_object* v___x_3710_; 
lean_dec_ref(v_expectedType_3649_);
v___x_3710_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3710_, 0, v_a_3648_);
return v___x_3710_;
}
else
{
lean_object* v___x_3711_; 
lean_inc(v___y_3707_);
lean_inc_ref(v___y_3705_);
lean_inc(v___y_3704_);
lean_inc_ref(v___y_3703_);
lean_inc_ref(v_a_3648_);
v___x_3711_ = lean_infer_type(v_a_3648_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3707_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
lean_inc_ref(v_expectedType_3649_);
v___x_3713_ = l_Lean_Meta_isExprDefEq(v_expectedType_3649_, v_a_3712_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3707_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3716_; uint8_t v_isShared_3717_; uint8_t v_isSharedCheck_3764_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3764_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3764_ == 0)
{
v___x_3716_ = v___x_3713_;
v_isShared_3717_ = v_isSharedCheck_3764_;
goto v_resetjp_3715_;
}
else
{
lean_inc(v_a_3714_);
lean_dec(v___x_3713_);
v___x_3716_ = lean_box(0);
v_isShared_3717_ = v_isSharedCheck_3764_;
goto v_resetjp_3715_;
}
v_resetjp_3715_:
{
uint8_t v___x_3718_; 
v___x_3718_ = lean_unbox(v_a_3714_);
lean_dec(v_a_3714_);
if (v___x_3718_ == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v_a_3721_; lean_object* v___x_3722_; 
lean_del_object(v___x_3716_);
v___x_3719_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_3720_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_3719_, v___y_3707_);
v_a_3721_ = lean_ctor_get(v___x_3720_, 0);
lean_inc_n(v_a_3721_, 2);
lean_dec_ref(v___x_3720_);
v___x_3722_ = l_Lean_Meta_mkAuxDefinition(v_a_3721_, v_expectedType_3649_, v_a_3648_, v___x_3650_, v___x_3650_, v___x_3651_, v___y_3703_, v___y_3704_, v___y_3705_, v___y_3707_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; uint8_t v___x_3724_; lean_object* v___x_3725_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = 3;
lean_inc(v_a_3721_);
v___x_3725_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_3721_, v___x_3724_, v___y_3704_, v___y_3707_);
lean_dec_ref(v___x_3725_);
if (v_isMeta_3654_ == 0)
{
v___y_3686_ = v_a_3723_;
v___y_3687_ = v_a_3721_;
v___y_3688_ = v___y_3705_;
v___y_3689_ = v___y_3707_;
goto v___jp_3685_;
}
else
{
lean_object* v___x_3726_; lean_object* v_env_3727_; lean_object* v_nextMacroScope_3728_; lean_object* v_ngen_3729_; lean_object* v_auxDeclNGen_3730_; lean_object* v_traceState_3731_; lean_object* v_messages_3732_; lean_object* v_infoState_3733_; lean_object* v_snapshotTasks_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3759_; 
v___x_3726_ = lean_st_ref_take(v___y_3707_);
v_env_3727_ = lean_ctor_get(v___x_3726_, 0);
v_nextMacroScope_3728_ = lean_ctor_get(v___x_3726_, 1);
v_ngen_3729_ = lean_ctor_get(v___x_3726_, 2);
v_auxDeclNGen_3730_ = lean_ctor_get(v___x_3726_, 3);
v_traceState_3731_ = lean_ctor_get(v___x_3726_, 4);
v_messages_3732_ = lean_ctor_get(v___x_3726_, 6);
v_infoState_3733_ = lean_ctor_get(v___x_3726_, 7);
v_snapshotTasks_3734_ = lean_ctor_get(v___x_3726_, 8);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3726_);
if (v_isSharedCheck_3759_ == 0)
{
lean_object* v_unused_3760_; 
v_unused_3760_ = lean_ctor_get(v___x_3726_, 5);
lean_dec(v_unused_3760_);
v___x_3736_ = v___x_3726_;
v_isShared_3737_ = v_isSharedCheck_3759_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_snapshotTasks_3734_);
lean_inc(v_infoState_3733_);
lean_inc(v_messages_3732_);
lean_inc(v_traceState_3731_);
lean_inc(v_auxDeclNGen_3730_);
lean_inc(v_ngen_3729_);
lean_inc(v_nextMacroScope_3728_);
lean_inc(v_env_3727_);
lean_dec(v___x_3726_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3759_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
lean_inc(v_a_3721_);
v___x_3738_ = l_Lean_markMeta(v_env_3727_, v_a_3721_);
v___x_3739_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 5, v___x_3739_);
lean_ctor_set(v___x_3736_, 0, v___x_3738_);
v___x_3741_ = v___x_3736_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v___x_3738_);
lean_ctor_set(v_reuseFailAlloc_3758_, 1, v_nextMacroScope_3728_);
lean_ctor_set(v_reuseFailAlloc_3758_, 2, v_ngen_3729_);
lean_ctor_set(v_reuseFailAlloc_3758_, 3, v_auxDeclNGen_3730_);
lean_ctor_set(v_reuseFailAlloc_3758_, 4, v_traceState_3731_);
lean_ctor_set(v_reuseFailAlloc_3758_, 5, v___x_3739_);
lean_ctor_set(v_reuseFailAlloc_3758_, 6, v_messages_3732_);
lean_ctor_set(v_reuseFailAlloc_3758_, 7, v_infoState_3733_);
lean_ctor_set(v_reuseFailAlloc_3758_, 8, v_snapshotTasks_3734_);
v___x_3741_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v_mctx_3744_; lean_object* v_zetaDeltaFVarIds_3745_; lean_object* v_postponed_3746_; lean_object* v_diag_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3756_; 
v___x_3742_ = lean_st_ref_set(v___y_3707_, v___x_3741_);
v___x_3743_ = lean_st_ref_take(v___y_3704_);
v_mctx_3744_ = lean_ctor_get(v___x_3743_, 0);
v_zetaDeltaFVarIds_3745_ = lean_ctor_get(v___x_3743_, 2);
v_postponed_3746_ = lean_ctor_get(v___x_3743_, 3);
v_diag_3747_ = lean_ctor_get(v___x_3743_, 4);
v_isSharedCheck_3756_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3756_ == 0)
{
lean_object* v_unused_3757_; 
v_unused_3757_ = lean_ctor_get(v___x_3743_, 1);
lean_dec(v_unused_3757_);
v___x_3749_ = v___x_3743_;
v_isShared_3750_ = v_isSharedCheck_3756_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_diag_3747_);
lean_inc(v_postponed_3746_);
lean_inc(v_zetaDeltaFVarIds_3745_);
lean_inc(v_mctx_3744_);
lean_dec(v___x_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3756_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; lean_object* v___x_3753_; 
v___x_3751_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 1, v___x_3751_);
v___x_3753_ = v___x_3749_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3755_; 
v_reuseFailAlloc_3755_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3755_, 0, v_mctx_3744_);
lean_ctor_set(v_reuseFailAlloc_3755_, 1, v___x_3751_);
lean_ctor_set(v_reuseFailAlloc_3755_, 2, v_zetaDeltaFVarIds_3745_);
lean_ctor_set(v_reuseFailAlloc_3755_, 3, v_postponed_3746_);
lean_ctor_set(v_reuseFailAlloc_3755_, 4, v_diag_3747_);
v___x_3753_ = v_reuseFailAlloc_3755_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
lean_object* v___x_3754_; 
v___x_3754_ = lean_st_ref_set(v___y_3704_, v___x_3753_);
v___y_3686_ = v_a_3723_;
v___y_3687_ = v_a_3721_;
v___y_3688_ = v___y_3705_;
v___y_3689_ = v___y_3707_;
goto v___jp_3685_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3721_);
return v___x_3722_;
}
}
else
{
lean_object* v___x_3762_; 
lean_dec_ref(v_expectedType_3649_);
if (v_isShared_3717_ == 0)
{
lean_ctor_set(v___x_3716_, 0, v_a_3648_);
v___x_3762_ = v___x_3716_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v_a_3648_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
return v___x_3762_;
}
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_dec_ref(v_expectedType_3649_);
lean_dec_ref(v_a_3648_);
v_a_3765_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3713_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3713_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_3649_);
lean_dec_ref(v_a_3648_);
return v___x_3711_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1(lean_object* v_expectedType_3929_, lean_object* v_inst_3930_, uint8_t v___x_3931_, uint8_t v_hasTrace_3932_, uint8_t v_compile_3933_, uint8_t v_logCompileErrors_3934_, uint8_t v_isMeta_3935_, lean_object* v_____r_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
lean_object* v___x_3942_; 
lean_inc_ref(v_expectedType_3929_);
v___x_3942_ = l_Lean_Meta_isProp(v_expectedType_3929_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3942_) == 0)
{
lean_object* v_a_3943_; lean_object* v___x_3945_; uint8_t v_isShared_3946_; uint8_t v_isSharedCheck_3964_; 
v_a_3943_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3964_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3964_ == 0)
{
v___x_3945_ = v___x_3942_;
v_isShared_3946_ = v_isSharedCheck_3964_;
goto v_resetjp_3944_;
}
else
{
lean_inc(v_a_3943_);
lean_dec(v___x_3942_);
v___x_3945_ = lean_box(0);
v_isShared_3946_ = v_isSharedCheck_3964_;
goto v_resetjp_3944_;
}
v_resetjp_3944_:
{
uint8_t v___x_3947_; 
v___x_3947_ = lean_unbox(v_a_3943_);
lean_dec(v_a_3943_);
if (v___x_3947_ == 0)
{
lean_object* v___x_3948_; 
lean_del_object(v___x_3945_);
lean_inc(v___y_3940_);
lean_inc_ref(v___y_3939_);
lean_inc(v___y_3938_);
lean_inc_ref(v___y_3937_);
v___x_3948_ = lean_whnf(v_inst_3930_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
if (lean_obj_tag(v___x_3948_) == 0)
{
lean_object* v_a_3949_; lean_object* v_dummy_3950_; lean_object* v_nargs_3951_; lean_object* v___x_3952_; lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; 
v_a_3949_ = lean_ctor_get(v___x_3948_, 0);
lean_inc_n(v_a_3949_, 2);
lean_dec_ref(v___x_3948_);
v_dummy_3950_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_3951_ = l_Lean_Expr_getAppNumArgs(v_a_3949_);
lean_inc(v_nargs_3951_);
v___x_3952_ = lean_mk_array(v_nargs_3951_, v_dummy_3950_);
v___x_3953_ = lean_unsigned_to_nat(1u);
v___x_3954_ = lean_nat_sub(v_nargs_3951_, v___x_3953_);
lean_dec(v_nargs_3951_);
v___x_3955_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_3949_, v_expectedType_3929_, v___x_3931_, v_hasTrace_3932_, v_compile_3933_, v_logCompileErrors_3934_, v_isMeta_3935_, v_a_3949_, v___x_3952_, v___x_3954_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___x_3954_);
return v___x_3955_;
}
else
{
lean_dec_ref(v_expectedType_3929_);
return v___x_3948_;
}
}
else
{
lean_object* v_options_3956_; lean_object* v___x_3957_; uint8_t v___x_3958_; 
v_options_3956_ = lean_ctor_get(v___y_3939_, 2);
v___x_3957_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_3958_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_3956_, v___x_3957_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3960_; 
lean_dec_ref(v_expectedType_3929_);
if (v_isShared_3946_ == 0)
{
lean_ctor_set(v___x_3945_, 0, v_inst_3930_);
v___x_3960_ = v___x_3945_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_inst_3930_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
else
{
lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_del_object(v___x_3945_);
v___x_3962_ = lean_box(0);
v___x_3963_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_3929_, v_inst_3930_, v_hasTrace_3932_, v___x_3962_, v_hasTrace_3932_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
return v___x_3963_;
}
}
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_dec_ref(v_inst_3930_);
lean_dec_ref(v_expectedType_3929_);
v_a_3965_ = lean_ctor_get(v___x_3942_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3942_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3942_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3942_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_wrapInstance___closed__3(void){
_start:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = ((lean_object*)(l_Lean_Meta_wrapInstance___closed__2));
v___x_3975_ = l_Lean_stringToMessageData(v___x_3974_);
return v___x_3975_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(lean_object* v_upperBound_3976_, lean_object* v_fst_3977_, lean_object* v_args_3978_, uint8_t v___x_3979_, uint8_t v_compile_3980_, uint8_t v_logCompileErrors_3981_, uint8_t v_isMeta_3982_, lean_object* v_a_3983_, lean_object* v_b_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v_a_3991_; lean_object* v___y_3996_; uint8_t v___x_4015_; 
v___x_4015_ = lean_nat_dec_lt(v_a_3983_, v_upperBound_3976_);
if (v___x_4015_ == 0)
{
lean_object* v___x_4016_; 
lean_dec(v_a_3983_);
v___x_4016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4016_, 0, v_b_3984_);
return v___x_4016_;
}
else
{
lean_object* v___x_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; 
v___x_4017_ = lean_array_fget_borrowed(v_fst_3977_, v_a_3983_);
v___x_4018_ = l_Lean_Expr_mvarId_x21(v___x_4017_);
lean_inc(v___x_4018_);
v___x_4019_ = l_Lean_MVarId_getDecl(v___x_4018_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4019_) == 0)
{
lean_object* v_a_4020_; lean_object* v_type_4021_; lean_object* v___x_4022_; 
v_a_4020_ = lean_ctor_get(v___x_4019_, 0);
lean_inc(v_a_4020_);
lean_dec_ref(v___x_4019_);
v_type_4021_ = lean_ctor_get(v_a_4020_, 2);
lean_inc_ref(v_type_4021_);
lean_dec(v_a_4020_);
v___x_4022_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4021_, v___y_3986_);
if (lean_obj_tag(v___x_4022_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4024_; 
v_a_4023_ = lean_ctor_get(v___x_4022_, 0);
lean_inc_n(v_a_4023_, 2);
lean_dec_ref(v___x_4022_);
v___x_4024_ = l_Lean_Meta_isProp(v_a_4023_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; lean_object* v_cls_4027_; lean_object* v___x_4028_; uint8_t v___x_4029_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref(v___x_4024_);
v___x_4026_ = lean_box(0);
v_cls_4027_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4028_ = lean_array_fget_borrowed(v_args_3978_, v_a_3983_);
v___x_4029_ = lean_unbox(v_a_4025_);
lean_dec(v_a_4025_);
if (v___x_4029_ == 0)
{
lean_object* v___x_4030_; 
lean_inc(v_a_4023_);
v___x_4030_ = l_Lean_Meta_isClass_x3f(v_a_4023_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4033_; uint8_t v_isShared_4034_; uint8_t v_isSharedCheck_4165_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4033_ = v___x_4030_;
v_isShared_4034_ = v_isSharedCheck_4165_;
goto v_resetjp_4032_;
}
else
{
lean_inc(v_a_4031_);
lean_dec(v___x_4030_);
v___x_4033_ = lean_box(0);
v_isShared_4034_ = v_isSharedCheck_4165_;
goto v_resetjp_4032_;
}
v_resetjp_4032_:
{
if (lean_obj_tag(v_a_4031_) == 0)
{
lean_del_object(v___x_4033_);
goto v___jp_4035_;
}
else
{
lean_dec_ref(v_a_4031_);
if (v___x_3979_ == 0)
{
lean_del_object(v___x_4033_);
goto v___jp_4035_;
}
else
{
lean_object* v_options_4125_; lean_object* v_inheritedTraceOptions_4126_; lean_object* v_a_4128_; lean_object* v___y_4131_; uint8_t v___y_4132_; lean_object* v_a_4137_; lean_object* v___y_4141_; lean_object* v___x_4145_; uint8_t v___x_4146_; 
v_options_4125_ = lean_ctor_get(v___y_3987_, 2);
v_inheritedTraceOptions_4126_ = lean_ctor_get(v___y_3987_, 13);
v___x_4145_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4146_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4125_, v___x_4145_);
if (v___x_4146_ == 0)
{
lean_object* v___x_4147_; 
lean_del_object(v___x_4033_);
lean_inc(v___x_4028_);
v___x_4147_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4028_, v_a_4023_, v_compile_3980_, v_logCompileErrors_3981_, v_isMeta_3982_, v___x_4018_, v___x_4026_, v___x_4026_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4147_;
goto v___jp_3995_;
}
else
{
lean_object* v___x_4148_; lean_object* v___x_4149_; 
v___x_4148_ = lean_box(0);
lean_inc(v_a_4023_);
v___x_4149_ = l_Lean_Meta_trySynthInstance(v_a_4023_, v___x_4148_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4150_);
lean_dec_ref(v___x_4149_);
if (lean_obj_tag(v_a_4150_) == 1)
{
lean_object* v_a_4151_; uint8_t v_hasTrace_4152_; 
v_a_4151_ = lean_ctor_get(v_a_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref(v_a_4150_);
v_hasTrace_4152_ = lean_ctor_get_uint8(v_options_4125_, sizeof(void*)*1);
if (v_hasTrace_4152_ == 0)
{
goto v___jp_4153_;
}
else
{
lean_object* v___x_4155_; uint8_t v___x_4156_; 
v___x_4155_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4156_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4126_, v_options_4125_, v___x_4155_);
if (v___x_4156_ == 0)
{
goto v___jp_4153_;
}
else
{
lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; 
v___x_4157_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_4151_);
v___x_4158_ = l_Lean_MessageData_ofExpr(v_a_4151_);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4157_);
lean_ctor_set(v___x_4159_, 1, v___x_4158_);
v___x_4160_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4027_, v___x_4159_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; lean_object* v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref(v___x_4160_);
lean_inc(v___x_4018_);
v___x_4162_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4018_, v_a_4151_, v_a_4161_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_4141_ = v___x_4162_;
goto v___jp_4140_;
}
else
{
lean_object* v_a_4163_; 
lean_dec(v_a_4151_);
v_a_4163_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4163_);
lean_dec_ref(v___x_4160_);
v_a_4137_ = v_a_4163_;
goto v___jp_4136_;
}
}
}
v___jp_4153_:
{
lean_object* v___x_4154_; 
lean_inc(v___x_4018_);
v___x_4154_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4018_, v_a_4151_, v___x_4026_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_4141_ = v___x_4154_;
goto v___jp_4140_;
}
}
else
{
lean_dec(v_a_4150_);
lean_del_object(v___x_4033_);
v_a_4128_ = v___x_4026_;
goto v___jp_4127_;
}
}
else
{
lean_object* v_a_4164_; 
v_a_4164_ = lean_ctor_get(v___x_4149_, 0);
lean_inc(v_a_4164_);
lean_dec_ref(v___x_4149_);
v_a_4137_ = v_a_4164_;
goto v___jp_4136_;
}
}
v___jp_4127_:
{
lean_object* v___x_4129_; 
lean_inc(v___x_4028_);
v___x_4129_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4028_, v_a_4023_, v_compile_3980_, v_logCompileErrors_3981_, v_isMeta_3982_, v___x_4018_, v___x_4026_, v_a_4128_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4129_;
goto v___jp_3995_;
}
v___jp_4130_:
{
if (v___y_4132_ == 0)
{
lean_dec_ref(v___y_4131_);
lean_del_object(v___x_4033_);
v_a_4128_ = v___x_4026_;
goto v___jp_4127_;
}
else
{
lean_object* v___x_4134_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
if (v_isShared_4034_ == 0)
{
lean_ctor_set_tag(v___x_4033_, 1);
lean_ctor_set(v___x_4033_, 0, v___y_4131_);
v___x_4134_ = v___x_4033_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___y_4131_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
v___jp_4136_:
{
uint8_t v___x_4138_; 
v___x_4138_ = l_Lean_Exception_isInterrupt(v_a_4137_);
if (v___x_4138_ == 0)
{
uint8_t v___x_4139_; 
lean_inc_ref(v_a_4137_);
v___x_4139_ = l_Lean_Exception_isRuntime(v_a_4137_);
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4139_;
goto v___jp_4130_;
}
else
{
v___y_4131_ = v_a_4137_;
v___y_4132_ = v___x_4138_;
goto v___jp_4130_;
}
}
v___jp_4140_:
{
if (lean_obj_tag(v___y_4141_) == 0)
{
lean_object* v_a_4142_; 
lean_del_object(v___x_4033_);
v_a_4142_ = lean_ctor_get(v___y_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref(v___y_4141_);
if (lean_obj_tag(v_a_4142_) == 0)
{
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
v_a_3991_ = v___x_4026_;
goto v___jp_3990_;
}
else
{
lean_object* v_a_4143_; 
v_a_4143_ = lean_ctor_get(v_a_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref(v_a_4142_);
v_a_4128_ = v_a_4143_;
goto v___jp_4127_;
}
}
else
{
lean_object* v_a_4144_; 
v_a_4144_ = lean_ctor_get(v___y_4141_, 0);
lean_inc(v_a_4144_);
lean_dec_ref(v___y_4141_);
v_a_4137_ = v_a_4144_;
goto v___jp_4136_;
}
}
}
}
v___jp_4035_:
{
lean_object* v_options_4036_; lean_object* v___x_4037_; uint8_t v___x_4038_; 
v_options_4036_ = lean_ctor_get(v___y_3987_, 2);
v___x_4037_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_4038_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4036_, v___x_4037_);
if (v___x_4038_ == 0)
{
lean_object* v___x_4039_; 
lean_dec(v_a_4023_);
lean_inc(v___x_4028_);
v___x_4039_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4018_, v___x_4028_, v___y_3986_);
if (lean_obj_tag(v___x_4039_) == 0)
{
lean_dec_ref(v___x_4039_);
v_a_3991_ = v___x_4026_;
goto v___jp_3990_;
}
else
{
lean_dec(v_a_3983_);
return v___x_4039_;
}
}
else
{
lean_object* v___x_4040_; 
lean_inc(v___y_3988_);
lean_inc_ref(v___y_3987_);
lean_inc(v___y_3986_);
lean_inc_ref(v___y_3985_);
lean_inc(v___x_4028_);
v___x_4040_ = lean_infer_type(v___x_4028_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4040_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4042_; 
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v___x_4040_);
lean_inc(v_a_4023_);
v___x_4042_ = l_Lean_Meta_isExprDefEq(v_a_4023_, v_a_4041_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4042_) == 0)
{
lean_object* v_a_4043_; uint8_t v___x_4044_; 
v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
lean_inc(v_a_4043_);
lean_dec_ref(v___x_4042_);
v___x_4044_ = lean_unbox(v_a_4043_);
if (v___x_4044_ == 0)
{
lean_object* v___x_4045_; lean_object* v___x_4046_; 
v___x_4045_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4046_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4045_, v___y_3988_);
if (lean_obj_tag(v___x_4046_) == 0)
{
lean_object* v_a_4047_; uint8_t v___x_4048_; uint8_t v___x_4049_; lean_object* v___x_4050_; 
v_a_4047_ = lean_ctor_get(v___x_4046_, 0);
lean_inc_n(v_a_4047_, 2);
lean_dec_ref(v___x_4046_);
v___x_4048_ = lean_unbox(v_a_4043_);
v___x_4049_ = lean_unbox(v_a_4043_);
lean_dec(v_a_4043_);
lean_inc(v___x_4028_);
v___x_4050_ = l_Lean_Meta_mkAuxDefinition(v_a_4047_, v_a_4023_, v___x_4028_, v___x_4048_, v___x_4049_, v___x_3979_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4052_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
lean_inc(v_a_4051_);
lean_dec_ref(v___x_4050_);
v___x_4052_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4018_, v_a_4051_, v___y_3986_);
if (lean_obj_tag(v___x_4052_) == 0)
{
uint8_t v___x_4053_; lean_object* v___x_4054_; 
lean_dec_ref(v___x_4052_);
v___x_4053_ = 0;
lean_inc(v_a_4047_);
v___x_4054_ = l_Lean_Meta_setInlineAttribute(v_a_4047_, v___x_4053_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_dec_ref(v___x_4054_);
if (v_isMeta_3982_ == 0)
{
lean_object* v___x_4055_; 
v___x_4055_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4047_, v___x_4026_, v_compile_3980_, v_logCompileErrors_3981_, v___x_4026_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4055_;
goto v___jp_3995_;
}
else
{
lean_object* v___x_4056_; lean_object* v_env_4057_; lean_object* v_nextMacroScope_4058_; lean_object* v_ngen_4059_; lean_object* v_auxDeclNGen_4060_; lean_object* v_traceState_4061_; lean_object* v_messages_4062_; lean_object* v_infoState_4063_; lean_object* v_snapshotTasks_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4090_; 
v___x_4056_ = lean_st_ref_take(v___y_3988_);
v_env_4057_ = lean_ctor_get(v___x_4056_, 0);
v_nextMacroScope_4058_ = lean_ctor_get(v___x_4056_, 1);
v_ngen_4059_ = lean_ctor_get(v___x_4056_, 2);
v_auxDeclNGen_4060_ = lean_ctor_get(v___x_4056_, 3);
v_traceState_4061_ = lean_ctor_get(v___x_4056_, 4);
v_messages_4062_ = lean_ctor_get(v___x_4056_, 6);
v_infoState_4063_ = lean_ctor_get(v___x_4056_, 7);
v_snapshotTasks_4064_ = lean_ctor_get(v___x_4056_, 8);
v_isSharedCheck_4090_ = !lean_is_exclusive(v___x_4056_);
if (v_isSharedCheck_4090_ == 0)
{
lean_object* v_unused_4091_; 
v_unused_4091_ = lean_ctor_get(v___x_4056_, 5);
lean_dec(v_unused_4091_);
v___x_4066_ = v___x_4056_;
v_isShared_4067_ = v_isSharedCheck_4090_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_snapshotTasks_4064_);
lean_inc(v_infoState_4063_);
lean_inc(v_messages_4062_);
lean_inc(v_traceState_4061_);
lean_inc(v_auxDeclNGen_4060_);
lean_inc(v_ngen_4059_);
lean_inc(v_nextMacroScope_4058_);
lean_inc(v_env_4057_);
lean_dec(v___x_4056_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4090_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v___x_4071_; 
lean_inc(v_a_4047_);
v___x_4068_ = l_Lean_markMeta(v_env_4057_, v_a_4047_);
v___x_4069_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4067_ == 0)
{
lean_ctor_set(v___x_4066_, 5, v___x_4069_);
lean_ctor_set(v___x_4066_, 0, v___x_4068_);
v___x_4071_ = v___x_4066_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4089_; 
v_reuseFailAlloc_4089_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4089_, 0, v___x_4068_);
lean_ctor_set(v_reuseFailAlloc_4089_, 1, v_nextMacroScope_4058_);
lean_ctor_set(v_reuseFailAlloc_4089_, 2, v_ngen_4059_);
lean_ctor_set(v_reuseFailAlloc_4089_, 3, v_auxDeclNGen_4060_);
lean_ctor_set(v_reuseFailAlloc_4089_, 4, v_traceState_4061_);
lean_ctor_set(v_reuseFailAlloc_4089_, 5, v___x_4069_);
lean_ctor_set(v_reuseFailAlloc_4089_, 6, v_messages_4062_);
lean_ctor_set(v_reuseFailAlloc_4089_, 7, v_infoState_4063_);
lean_ctor_set(v_reuseFailAlloc_4089_, 8, v_snapshotTasks_4064_);
v___x_4071_ = v_reuseFailAlloc_4089_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v_mctx_4074_; lean_object* v_zetaDeltaFVarIds_4075_; lean_object* v_postponed_4076_; lean_object* v_diag_4077_; lean_object* v___x_4079_; uint8_t v_isShared_4080_; uint8_t v_isSharedCheck_4087_; 
v___x_4072_ = lean_st_ref_set(v___y_3988_, v___x_4071_);
v___x_4073_ = lean_st_ref_take(v___y_3986_);
v_mctx_4074_ = lean_ctor_get(v___x_4073_, 0);
v_zetaDeltaFVarIds_4075_ = lean_ctor_get(v___x_4073_, 2);
v_postponed_4076_ = lean_ctor_get(v___x_4073_, 3);
v_diag_4077_ = lean_ctor_get(v___x_4073_, 4);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4073_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v___x_4073_, 1);
lean_dec(v_unused_4088_);
v___x_4079_ = v___x_4073_;
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
else
{
lean_inc(v_diag_4077_);
lean_inc(v_postponed_4076_);
lean_inc(v_zetaDeltaFVarIds_4075_);
lean_inc(v_mctx_4074_);
lean_dec(v___x_4073_);
v___x_4079_ = lean_box(0);
v_isShared_4080_ = v_isSharedCheck_4087_;
goto v_resetjp_4078_;
}
v_resetjp_4078_:
{
lean_object* v___x_4081_; lean_object* v___x_4083_; 
v___x_4081_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4080_ == 0)
{
lean_ctor_set(v___x_4079_, 1, v___x_4081_);
v___x_4083_ = v___x_4079_;
goto v_reusejp_4082_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_mctx_4074_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v___x_4081_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_zetaDeltaFVarIds_4075_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_postponed_4076_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_diag_4077_);
v___x_4083_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4082_;
}
v_reusejp_4082_:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = lean_st_ref_set(v___y_3986_, v___x_4083_);
v___x_4085_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4047_, v___x_4026_, v_compile_3980_, v_logCompileErrors_3981_, v___x_4026_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4085_;
goto v___jp_3995_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4047_);
lean_dec(v_a_3983_);
return v___x_4054_;
}
}
else
{
lean_dec(v_a_4047_);
lean_dec(v_a_3983_);
return v___x_4052_;
}
}
else
{
lean_object* v_a_4092_; lean_object* v___x_4094_; uint8_t v_isShared_4095_; uint8_t v_isSharedCheck_4099_; 
lean_dec(v_a_4047_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4092_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4094_ = v___x_4050_;
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
else
{
lean_inc(v_a_4092_);
lean_dec(v___x_4050_);
v___x_4094_ = lean_box(0);
v_isShared_4095_ = v_isSharedCheck_4099_;
goto v_resetjp_4093_;
}
v_resetjp_4093_:
{
lean_object* v___x_4097_; 
if (v_isShared_4095_ == 0)
{
v___x_4097_ = v___x_4094_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_a_4092_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
lean_dec(v_a_4043_);
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4100_ = lean_ctor_get(v___x_4046_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4046_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4046_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
else
{
lean_object* v___x_4108_; 
lean_dec(v_a_4043_);
lean_dec(v_a_4023_);
lean_inc(v___x_4028_);
v___x_4108_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4018_, v___x_4028_, v___y_3986_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_dec_ref(v___x_4108_);
v_a_3991_ = v___x_4026_;
goto v___jp_3990_;
}
else
{
lean_dec(v_a_3983_);
return v___x_4108_;
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4109_ = lean_ctor_get(v___x_4042_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4042_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4042_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4042_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4117_ = lean_ctor_get(v___x_4040_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4040_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4040_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4040_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4166_ = lean_ctor_get(v___x_4030_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4030_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4030_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4030_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
else
{
lean_object* v___x_4174_; 
lean_inc(v___y_3988_);
lean_inc_ref(v___y_3987_);
lean_inc(v___y_3986_);
lean_inc_ref(v___y_3985_);
lean_inc(v___x_4028_);
v___x_4174_ = lean_infer_type(v___x_4028_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4174_) == 0)
{
lean_object* v_a_4175_; lean_object* v___x_4176_; 
v_a_4175_ = lean_ctor_get(v___x_4174_, 0);
lean_inc_n(v_a_4175_, 2);
lean_dec_ref(v___x_4174_);
lean_inc(v_a_4023_);
v___x_4176_ = l_Lean_Meta_isExprDefEq(v_a_4023_, v_a_4175_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4176_) == 0)
{
lean_object* v_a_4177_; uint8_t v___x_4178_; 
v_a_4177_ = lean_ctor_get(v___x_4176_, 0);
lean_inc(v_a_4177_);
lean_dec_ref(v___x_4176_);
v___x_4178_ = lean_unbox(v_a_4177_);
lean_dec(v_a_4177_);
if (v___x_4178_ == 0)
{
lean_object* v_options_4179_; lean_object* v_inheritedTraceOptions_4180_; uint8_t v_hasTrace_4181_; 
v_options_4179_ = lean_ctor_get(v___y_3987_, 2);
v_inheritedTraceOptions_4180_ = lean_ctor_get(v___y_3987_, 13);
v_hasTrace_4181_ = lean_ctor_get_uint8(v_options_4179_, sizeof(void*)*1);
if (v_hasTrace_4181_ == 0)
{
lean_dec(v_a_4175_);
goto v___jp_4182_;
}
else
{
lean_object* v___x_4184_; uint8_t v___x_4185_; 
v___x_4184_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4185_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4180_, v_options_4179_, v___x_4184_);
if (v___x_4185_ == 0)
{
lean_dec(v_a_4175_);
goto v___jp_4182_;
}
else
{
lean_object* v___x_4186_; lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4186_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_3983_);
v___x_4187_ = l_Nat_reprFast(v_a_3983_);
v___x_4188_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
v___x_4189_ = l_Lean_MessageData_ofFormat(v___x_4188_);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4186_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
lean_inc(v_a_4023_);
v___x_4193_ = l_Lean_MessageData_ofExpr(v_a_4023_);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v___x_4194_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
v___x_4197_ = l_Lean_MessageData_ofExpr(v_a_4175_);
v___x_4198_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4198_, 0, v___x_4196_);
lean_ctor_set(v___x_4198_, 1, v___x_4197_);
v___x_4199_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_4200_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4200_, 0, v___x_4198_);
lean_ctor_set(v___x_4200_, 1, v___x_4199_);
lean_inc(v___x_4028_);
v___x_4201_ = l_Lean_MessageData_ofExpr(v___x_4028_);
v___x_4202_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4200_);
lean_ctor_set(v___x_4202_, 1, v___x_4201_);
v___x_4203_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4027_, v___x_4202_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref(v___x_4203_);
lean_inc(v___x_4028_);
v___x_4205_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4023_, v___x_4028_, v___x_3979_, v___x_4018_, v___x_4026_, v_a_4204_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4205_;
goto v___jp_3995_;
}
else
{
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
return v___x_4203_;
}
}
}
v___jp_4182_:
{
lean_object* v___x_4183_; 
lean_inc(v___x_4028_);
v___x_4183_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4023_, v___x_4028_, v___x_3979_, v___x_4018_, v___x_4026_, v___x_4026_, v___y_3985_, v___y_3986_, v___y_3987_, v___y_3988_);
v___y_3996_ = v___x_4183_;
goto v___jp_3995_;
}
}
else
{
lean_object* v___x_4206_; 
lean_dec(v_a_4175_);
lean_dec(v_a_4023_);
lean_inc(v___x_4028_);
v___x_4206_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4018_, v___x_4028_, v___y_3986_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_dec_ref(v___x_4206_);
v_a_3991_ = v___x_4026_;
goto v___jp_3990_;
}
else
{
lean_dec(v_a_3983_);
return v___x_4206_;
}
}
}
else
{
lean_object* v_a_4207_; lean_object* v___x_4209_; uint8_t v_isShared_4210_; uint8_t v_isSharedCheck_4214_; 
lean_dec(v_a_4175_);
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4207_ = lean_ctor_get(v___x_4176_, 0);
v_isSharedCheck_4214_ = !lean_is_exclusive(v___x_4176_);
if (v_isSharedCheck_4214_ == 0)
{
v___x_4209_ = v___x_4176_;
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
else
{
lean_inc(v_a_4207_);
lean_dec(v___x_4176_);
v___x_4209_ = lean_box(0);
v_isShared_4210_ = v_isSharedCheck_4214_;
goto v_resetjp_4208_;
}
v_resetjp_4208_:
{
lean_object* v___x_4212_; 
if (v_isShared_4210_ == 0)
{
v___x_4212_ = v___x_4209_;
goto v_reusejp_4211_;
}
else
{
lean_object* v_reuseFailAlloc_4213_; 
v_reuseFailAlloc_4213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4213_, 0, v_a_4207_);
v___x_4212_ = v_reuseFailAlloc_4213_;
goto v_reusejp_4211_;
}
v_reusejp_4211_:
{
return v___x_4212_;
}
}
}
}
else
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4222_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4215_ = lean_ctor_get(v___x_4174_, 0);
v_isSharedCheck_4222_ = !lean_is_exclusive(v___x_4174_);
if (v_isSharedCheck_4222_ == 0)
{
v___x_4217_ = v___x_4174_;
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4174_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4222_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
lean_object* v___x_4220_; 
if (v_isShared_4218_ == 0)
{
v___x_4220_ = v___x_4217_;
goto v_reusejp_4219_;
}
else
{
lean_object* v_reuseFailAlloc_4221_; 
v_reuseFailAlloc_4221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4221_, 0, v_a_4215_);
v___x_4220_ = v_reuseFailAlloc_4221_;
goto v_reusejp_4219_;
}
v_reusejp_4219_:
{
return v___x_4220_;
}
}
}
}
}
else
{
lean_object* v_a_4223_; lean_object* v___x_4225_; uint8_t v_isShared_4226_; uint8_t v_isSharedCheck_4230_; 
lean_dec(v_a_4023_);
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4223_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4230_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4230_ == 0)
{
v___x_4225_ = v___x_4024_;
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
else
{
lean_inc(v_a_4223_);
lean_dec(v___x_4024_);
v___x_4225_ = lean_box(0);
v_isShared_4226_ = v_isSharedCheck_4230_;
goto v_resetjp_4224_;
}
v_resetjp_4224_:
{
lean_object* v___x_4228_; 
if (v_isShared_4226_ == 0)
{
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
return v___x_4228_;
}
}
}
}
else
{
lean_object* v_a_4231_; lean_object* v___x_4233_; uint8_t v_isShared_4234_; uint8_t v_isSharedCheck_4238_; 
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4231_ = lean_ctor_get(v___x_4022_, 0);
v_isSharedCheck_4238_ = !lean_is_exclusive(v___x_4022_);
if (v_isSharedCheck_4238_ == 0)
{
v___x_4233_ = v___x_4022_;
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
else
{
lean_inc(v_a_4231_);
lean_dec(v___x_4022_);
v___x_4233_ = lean_box(0);
v_isShared_4234_ = v_isSharedCheck_4238_;
goto v_resetjp_4232_;
}
v_resetjp_4232_:
{
lean_object* v___x_4236_; 
if (v_isShared_4234_ == 0)
{
v___x_4236_ = v___x_4233_;
goto v_reusejp_4235_;
}
else
{
lean_object* v_reuseFailAlloc_4237_; 
v_reuseFailAlloc_4237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4237_, 0, v_a_4231_);
v___x_4236_ = v_reuseFailAlloc_4237_;
goto v_reusejp_4235_;
}
v_reusejp_4235_:
{
return v___x_4236_;
}
}
}
}
else
{
lean_object* v_a_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4246_; 
lean_dec(v___x_4018_);
lean_dec(v_a_3983_);
v_a_4239_ = lean_ctor_get(v___x_4019_, 0);
v_isSharedCheck_4246_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4246_ == 0)
{
v___x_4241_ = v___x_4019_;
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_a_4239_);
lean_dec(v___x_4019_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4246_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4244_; 
if (v_isShared_4242_ == 0)
{
v___x_4244_ = v___x_4241_;
goto v_reusejp_4243_;
}
else
{
lean_object* v_reuseFailAlloc_4245_; 
v_reuseFailAlloc_4245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4245_, 0, v_a_4239_);
v___x_4244_ = v_reuseFailAlloc_4245_;
goto v_reusejp_4243_;
}
v_reusejp_4243_:
{
return v___x_4244_;
}
}
}
}
v___jp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_unsigned_to_nat(1u);
v___x_3993_ = lean_nat_add(v_a_3983_, v___x_3992_);
lean_dec(v_a_3983_);
v_a_3983_ = v___x_3993_;
v_b_3984_ = v_a_3991_;
goto _start;
}
v___jp_3995_:
{
if (lean_obj_tag(v___y_3996_) == 0)
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4006_; 
v_a_3997_ = lean_ctor_get(v___y_3996_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___y_3996_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_3999_ = v___y_3996_;
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___y_3996_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4006_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
if (lean_obj_tag(v_a_3997_) == 0)
{
lean_object* v_a_4001_; lean_object* v___x_4003_; 
lean_dec(v_a_3983_);
v_a_4001_ = lean_ctor_get(v_a_3997_, 0);
lean_inc(v_a_4001_);
lean_dec_ref(v_a_3997_);
if (v_isShared_4000_ == 0)
{
lean_ctor_set(v___x_3999_, 0, v_a_4001_);
v___x_4003_ = v___x_3999_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4004_; 
v_reuseFailAlloc_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4004_, 0, v_a_4001_);
v___x_4003_ = v_reuseFailAlloc_4004_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
return v___x_4003_;
}
}
else
{
lean_object* v_a_4005_; 
lean_del_object(v___x_3999_);
v_a_4005_ = lean_ctor_get(v_a_3997_, 0);
lean_inc(v_a_4005_);
lean_dec_ref(v_a_3997_);
v_a_3991_ = v_a_4005_;
goto v___jp_3990_;
}
}
}
else
{
lean_object* v_a_4007_; lean_object* v___x_4009_; uint8_t v_isShared_4010_; uint8_t v_isSharedCheck_4014_; 
lean_dec(v_a_3983_);
v_a_4007_ = lean_ctor_get(v___y_3996_, 0);
v_isSharedCheck_4014_ = !lean_is_exclusive(v___y_3996_);
if (v_isSharedCheck_4014_ == 0)
{
v___x_4009_ = v___y_3996_;
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
else
{
lean_inc(v_a_4007_);
lean_dec(v___y_3996_);
v___x_4009_ = lean_box(0);
v_isShared_4010_ = v_isSharedCheck_4014_;
goto v_resetjp_4008_;
}
v_resetjp_4008_:
{
lean_object* v___x_4012_; 
if (v_isShared_4010_ == 0)
{
v___x_4012_ = v___x_4009_;
goto v_reusejp_4011_;
}
else
{
lean_object* v_reuseFailAlloc_4013_; 
v_reuseFailAlloc_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4013_, 0, v_a_4007_);
v___x_4012_ = v_reuseFailAlloc_4013_;
goto v_reusejp_4011_;
}
v_reusejp_4011_:
{
return v___x_4012_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(lean_object* v_upperBound_4247_, lean_object* v_fst_4248_, lean_object* v_args_4249_, uint8_t v___x_4250_, uint8_t v_compile_4251_, uint8_t v_logCompileErrors_4252_, uint8_t v_isMeta_4253_, lean_object* v_a_4254_, lean_object* v_b_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_a_4262_; lean_object* v___y_4267_; uint8_t v___x_4286_; 
v___x_4286_ = lean_nat_dec_lt(v_a_4254_, v_upperBound_4247_);
if (v___x_4286_ == 0)
{
lean_object* v___x_4287_; 
lean_dec(v_a_4254_);
v___x_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4287_, 0, v_b_4255_);
return v___x_4287_;
}
else
{
lean_object* v___x_4288_; lean_object* v___x_4289_; lean_object* v___x_4290_; 
v___x_4288_ = lean_array_fget_borrowed(v_fst_4248_, v_a_4254_);
v___x_4289_ = l_Lean_Expr_mvarId_x21(v___x_4288_);
lean_inc(v___x_4289_);
v___x_4290_ = l_Lean_MVarId_getDecl(v___x_4289_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4290_) == 0)
{
lean_object* v_a_4291_; lean_object* v_type_4292_; lean_object* v___x_4293_; 
v_a_4291_ = lean_ctor_get(v___x_4290_, 0);
lean_inc(v_a_4291_);
lean_dec_ref(v___x_4290_);
v_type_4292_ = lean_ctor_get(v_a_4291_, 2);
lean_inc_ref(v_type_4292_);
lean_dec(v_a_4291_);
v___x_4293_ = l_Lean_instantiateMVars___at___00Lean_Meta_abstractInstImplicitArgs_spec__2___redArg(v_type_4292_, v___y_4257_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; lean_object* v___x_4295_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc_n(v_a_4294_, 2);
lean_dec_ref(v___x_4293_);
v___x_4295_ = l_Lean_Meta_isProp(v_a_4294_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4295_) == 0)
{
lean_object* v_a_4296_; lean_object* v___x_4297_; lean_object* v_cls_4298_; lean_object* v___x_4299_; uint8_t v___x_4300_; 
v_a_4296_ = lean_ctor_get(v___x_4295_, 0);
lean_inc(v_a_4296_);
lean_dec_ref(v___x_4295_);
v___x_4297_ = lean_box(0);
v_cls_4298_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4299_ = lean_array_fget_borrowed(v_args_4249_, v_a_4254_);
v___x_4300_ = lean_unbox(v_a_4296_);
lean_dec(v_a_4296_);
if (v___x_4300_ == 0)
{
lean_object* v___x_4301_; 
lean_inc(v_a_4294_);
v___x_4301_ = l_Lean_Meta_isClass_x3f(v_a_4294_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4304_; uint8_t v_isShared_4305_; uint8_t v_isSharedCheck_4436_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4436_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4436_ == 0)
{
v___x_4304_ = v___x_4301_;
v_isShared_4305_ = v_isSharedCheck_4436_;
goto v_resetjp_4303_;
}
else
{
lean_inc(v_a_4302_);
lean_dec(v___x_4301_);
v___x_4304_ = lean_box(0);
v_isShared_4305_ = v_isSharedCheck_4436_;
goto v_resetjp_4303_;
}
v_resetjp_4303_:
{
if (lean_obj_tag(v_a_4302_) == 0)
{
lean_del_object(v___x_4304_);
goto v___jp_4306_;
}
else
{
lean_dec_ref(v_a_4302_);
if (v___x_4250_ == 0)
{
lean_del_object(v___x_4304_);
goto v___jp_4306_;
}
else
{
lean_object* v_options_4396_; lean_object* v_inheritedTraceOptions_4397_; lean_object* v_a_4399_; lean_object* v___y_4402_; uint8_t v___y_4403_; lean_object* v_a_4408_; lean_object* v___y_4412_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v_options_4396_ = lean_ctor_get(v___y_4258_, 2);
v_inheritedTraceOptions_4397_ = lean_ctor_get(v___y_4258_, 13);
v___x_4416_ = l_Lean_Meta_backward_inferInstanceAs_wrap_reuseSubInstances;
v___x_4417_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4396_, v___x_4416_);
if (v___x_4417_ == 0)
{
lean_object* v___x_4418_; 
lean_del_object(v___x_4304_);
lean_inc(v___x_4299_);
v___x_4418_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4299_, v_a_4294_, v_compile_4251_, v_logCompileErrors_4252_, v_isMeta_4253_, v___x_4289_, v___x_4297_, v___x_4297_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4418_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; 
v___x_4419_ = lean_box(0);
lean_inc(v_a_4294_);
v___x_4420_ = l_Lean_Meta_trySynthInstance(v_a_4294_, v___x_4419_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4420_) == 0)
{
lean_object* v_a_4421_; 
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4421_);
lean_dec_ref(v___x_4420_);
if (lean_obj_tag(v_a_4421_) == 1)
{
lean_object* v_a_4422_; uint8_t v_hasTrace_4423_; 
v_a_4422_ = lean_ctor_get(v_a_4421_, 0);
lean_inc(v_a_4422_);
lean_dec_ref(v_a_4421_);
v_hasTrace_4423_ = lean_ctor_get_uint8(v_options_4396_, sizeof(void*)*1);
if (v_hasTrace_4423_ == 0)
{
goto v___jp_4424_;
}
else
{
lean_object* v___x_4426_; uint8_t v___x_4427_; 
v___x_4426_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4427_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4397_, v_options_4396_, v___x_4426_);
if (v___x_4427_ == 0)
{
goto v___jp_4424_;
}
else
{
lean_object* v___x_4428_; lean_object* v___x_4429_; lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4428_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__1);
lean_inc(v_a_4422_);
v___x_4429_ = l_Lean_MessageData_ofExpr(v_a_4422_);
v___x_4430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4430_, 0, v___x_4428_);
lean_ctor_set(v___x_4430_, 1, v___x_4429_);
v___x_4431_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4298_, v___x_4430_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; lean_object* v___x_4433_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref(v___x_4431_);
lean_inc(v___x_4289_);
v___x_4433_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4289_, v_a_4422_, v_a_4432_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4412_ = v___x_4433_;
goto v___jp_4411_;
}
else
{
lean_object* v_a_4434_; 
lean_dec(v_a_4422_);
v_a_4434_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4434_);
lean_dec_ref(v___x_4431_);
v_a_4408_ = v_a_4434_;
goto v___jp_4407_;
}
}
}
v___jp_4424_:
{
lean_object* v___x_4425_; 
lean_inc(v___x_4289_);
v___x_4425_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__2(v___x_4289_, v_a_4422_, v___x_4297_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4412_ = v___x_4425_;
goto v___jp_4411_;
}
}
else
{
lean_dec(v_a_4421_);
lean_del_object(v___x_4304_);
v_a_4399_ = v___x_4297_;
goto v___jp_4398_;
}
}
else
{
lean_object* v_a_4435_; 
v_a_4435_ = lean_ctor_get(v___x_4420_, 0);
lean_inc(v_a_4435_);
lean_dec_ref(v___x_4420_);
v_a_4408_ = v_a_4435_;
goto v___jp_4407_;
}
}
v___jp_4398_:
{
lean_object* v___x_4400_; 
lean_inc(v___x_4299_);
v___x_4400_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_4299_, v_a_4294_, v_compile_4251_, v_logCompileErrors_4252_, v_isMeta_4253_, v___x_4289_, v___x_4297_, v_a_4399_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4400_;
goto v___jp_4266_;
}
v___jp_4401_:
{
if (v___y_4403_ == 0)
{
lean_dec_ref(v___y_4402_);
lean_del_object(v___x_4304_);
v_a_4399_ = v___x_4297_;
goto v___jp_4398_;
}
else
{
lean_object* v___x_4405_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
if (v_isShared_4305_ == 0)
{
lean_ctor_set_tag(v___x_4304_, 1);
lean_ctor_set(v___x_4304_, 0, v___y_4402_);
v___x_4405_ = v___x_4304_;
goto v_reusejp_4404_;
}
else
{
lean_object* v_reuseFailAlloc_4406_; 
v_reuseFailAlloc_4406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4406_, 0, v___y_4402_);
v___x_4405_ = v_reuseFailAlloc_4406_;
goto v_reusejp_4404_;
}
v_reusejp_4404_:
{
return v___x_4405_;
}
}
}
v___jp_4407_:
{
uint8_t v___x_4409_; 
v___x_4409_ = l_Lean_Exception_isInterrupt(v_a_4408_);
if (v___x_4409_ == 0)
{
uint8_t v___x_4410_; 
lean_inc_ref(v_a_4408_);
v___x_4410_ = l_Lean_Exception_isRuntime(v_a_4408_);
v___y_4402_ = v_a_4408_;
v___y_4403_ = v___x_4410_;
goto v___jp_4401_;
}
else
{
v___y_4402_ = v_a_4408_;
v___y_4403_ = v___x_4409_;
goto v___jp_4401_;
}
}
v___jp_4411_:
{
if (lean_obj_tag(v___y_4412_) == 0)
{
lean_object* v_a_4413_; 
lean_del_object(v___x_4304_);
v_a_4413_ = lean_ctor_get(v___y_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref(v___y_4412_);
if (lean_obj_tag(v_a_4413_) == 0)
{
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
v_a_4262_ = v___x_4297_;
goto v___jp_4261_;
}
else
{
lean_object* v_a_4414_; 
v_a_4414_ = lean_ctor_get(v_a_4413_, 0);
lean_inc(v_a_4414_);
lean_dec_ref(v_a_4413_);
v_a_4399_ = v_a_4414_;
goto v___jp_4398_;
}
}
else
{
lean_object* v_a_4415_; 
v_a_4415_ = lean_ctor_get(v___y_4412_, 0);
lean_inc(v_a_4415_);
lean_dec_ref(v___y_4412_);
v_a_4408_ = v_a_4415_;
goto v___jp_4407_;
}
}
}
}
v___jp_4306_:
{
lean_object* v_options_4307_; lean_object* v___x_4308_; uint8_t v___x_4309_; 
v_options_4307_ = lean_ctor_get(v___y_4258_, 2);
v___x_4308_ = l_Lean_Meta_backward_inferInstanceAs_wrap_data;
v___x_4309_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4307_, v___x_4308_);
if (v___x_4309_ == 0)
{
lean_object* v___x_4310_; 
lean_dec(v_a_4294_);
lean_inc(v___x_4299_);
v___x_4310_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4289_, v___x_4299_, v___y_4257_);
if (lean_obj_tag(v___x_4310_) == 0)
{
lean_dec_ref(v___x_4310_);
v_a_4262_ = v___x_4297_;
goto v___jp_4261_;
}
else
{
lean_dec(v_a_4254_);
return v___x_4310_;
}
}
else
{
lean_object* v___x_4311_; 
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
lean_inc(v___x_4299_);
v___x_4311_ = lean_infer_type(v___x_4299_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4313_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref(v___x_4311_);
lean_inc(v_a_4294_);
v___x_4313_ = l_Lean_Meta_isExprDefEq(v_a_4294_, v_a_4312_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; uint8_t v___x_4315_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
lean_inc(v_a_4314_);
lean_dec_ref(v___x_4313_);
v___x_4315_ = lean_unbox(v_a_4314_);
if (v___x_4315_ == 0)
{
lean_object* v___x_4316_; lean_object* v___x_4317_; 
v___x_4316_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4317_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4316_, v___y_4259_);
if (lean_obj_tag(v___x_4317_) == 0)
{
lean_object* v_a_4318_; uint8_t v___x_4319_; uint8_t v___x_4320_; lean_object* v___x_4321_; 
v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
lean_inc_n(v_a_4318_, 2);
lean_dec_ref(v___x_4317_);
v___x_4319_ = lean_unbox(v_a_4314_);
v___x_4320_ = lean_unbox(v_a_4314_);
lean_dec(v_a_4314_);
lean_inc(v___x_4299_);
v___x_4321_ = l_Lean_Meta_mkAuxDefinition(v_a_4318_, v_a_4294_, v___x_4299_, v___x_4319_, v___x_4320_, v___x_4250_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4321_) == 0)
{
lean_object* v_a_4322_; lean_object* v___x_4323_; 
v_a_4322_ = lean_ctor_get(v___x_4321_, 0);
lean_inc(v_a_4322_);
lean_dec_ref(v___x_4321_);
v___x_4323_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4289_, v_a_4322_, v___y_4257_);
if (lean_obj_tag(v___x_4323_) == 0)
{
uint8_t v___x_4324_; lean_object* v___x_4325_; 
lean_dec_ref(v___x_4323_);
v___x_4324_ = 0;
lean_inc(v_a_4318_);
v___x_4325_ = l_Lean_Meta_setInlineAttribute(v_a_4318_, v___x_4324_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4325_) == 0)
{
lean_dec_ref(v___x_4325_);
if (v_isMeta_4253_ == 0)
{
lean_object* v___x_4326_; 
v___x_4326_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4318_, v___x_4297_, v_compile_4251_, v_logCompileErrors_4252_, v___x_4297_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4326_;
goto v___jp_4266_;
}
else
{
lean_object* v___x_4327_; lean_object* v_env_4328_; lean_object* v_nextMacroScope_4329_; lean_object* v_ngen_4330_; lean_object* v_auxDeclNGen_4331_; lean_object* v_traceState_4332_; lean_object* v_messages_4333_; lean_object* v_infoState_4334_; lean_object* v_snapshotTasks_4335_; lean_object* v___x_4337_; uint8_t v_isShared_4338_; uint8_t v_isSharedCheck_4361_; 
v___x_4327_ = lean_st_ref_take(v___y_4259_);
v_env_4328_ = lean_ctor_get(v___x_4327_, 0);
v_nextMacroScope_4329_ = lean_ctor_get(v___x_4327_, 1);
v_ngen_4330_ = lean_ctor_get(v___x_4327_, 2);
v_auxDeclNGen_4331_ = lean_ctor_get(v___x_4327_, 3);
v_traceState_4332_ = lean_ctor_get(v___x_4327_, 4);
v_messages_4333_ = lean_ctor_get(v___x_4327_, 6);
v_infoState_4334_ = lean_ctor_get(v___x_4327_, 7);
v_snapshotTasks_4335_ = lean_ctor_get(v___x_4327_, 8);
v_isSharedCheck_4361_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4361_ == 0)
{
lean_object* v_unused_4362_; 
v_unused_4362_ = lean_ctor_get(v___x_4327_, 5);
lean_dec(v_unused_4362_);
v___x_4337_ = v___x_4327_;
v_isShared_4338_ = v_isSharedCheck_4361_;
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
v_isShared_4338_ = v_isSharedCheck_4361_;
goto v_resetjp_4336_;
}
v_resetjp_4336_:
{
lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4342_; 
lean_inc(v_a_4318_);
v___x_4339_ = l_Lean_markMeta(v_env_4328_, v_a_4318_);
v___x_4340_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4338_ == 0)
{
lean_ctor_set(v___x_4337_, 5, v___x_4340_);
lean_ctor_set(v___x_4337_, 0, v___x_4339_);
v___x_4342_ = v___x_4337_;
goto v_reusejp_4341_;
}
else
{
lean_object* v_reuseFailAlloc_4360_; 
v_reuseFailAlloc_4360_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4360_, 0, v___x_4339_);
lean_ctor_set(v_reuseFailAlloc_4360_, 1, v_nextMacroScope_4329_);
lean_ctor_set(v_reuseFailAlloc_4360_, 2, v_ngen_4330_);
lean_ctor_set(v_reuseFailAlloc_4360_, 3, v_auxDeclNGen_4331_);
lean_ctor_set(v_reuseFailAlloc_4360_, 4, v_traceState_4332_);
lean_ctor_set(v_reuseFailAlloc_4360_, 5, v___x_4340_);
lean_ctor_set(v_reuseFailAlloc_4360_, 6, v_messages_4333_);
lean_ctor_set(v_reuseFailAlloc_4360_, 7, v_infoState_4334_);
lean_ctor_set(v_reuseFailAlloc_4360_, 8, v_snapshotTasks_4335_);
v___x_4342_ = v_reuseFailAlloc_4360_;
goto v_reusejp_4341_;
}
v_reusejp_4341_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v_mctx_4345_; lean_object* v_zetaDeltaFVarIds_4346_; lean_object* v_postponed_4347_; lean_object* v_diag_4348_; lean_object* v___x_4350_; uint8_t v_isShared_4351_; uint8_t v_isSharedCheck_4358_; 
v___x_4343_ = lean_st_ref_set(v___y_4259_, v___x_4342_);
v___x_4344_ = lean_st_ref_take(v___y_4257_);
v_mctx_4345_ = lean_ctor_get(v___x_4344_, 0);
v_zetaDeltaFVarIds_4346_ = lean_ctor_get(v___x_4344_, 2);
v_postponed_4347_ = lean_ctor_get(v___x_4344_, 3);
v_diag_4348_ = lean_ctor_get(v___x_4344_, 4);
v_isSharedCheck_4358_ = !lean_is_exclusive(v___x_4344_);
if (v_isSharedCheck_4358_ == 0)
{
lean_object* v_unused_4359_; 
v_unused_4359_ = lean_ctor_get(v___x_4344_, 1);
lean_dec(v_unused_4359_);
v___x_4350_ = v___x_4344_;
v_isShared_4351_ = v_isSharedCheck_4358_;
goto v_resetjp_4349_;
}
else
{
lean_inc(v_diag_4348_);
lean_inc(v_postponed_4347_);
lean_inc(v_zetaDeltaFVarIds_4346_);
lean_inc(v_mctx_4345_);
lean_dec(v___x_4344_);
v___x_4350_ = lean_box(0);
v_isShared_4351_ = v_isSharedCheck_4358_;
goto v_resetjp_4349_;
}
v_resetjp_4349_:
{
lean_object* v___x_4352_; lean_object* v___x_4354_; 
v___x_4352_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4351_ == 0)
{
lean_ctor_set(v___x_4350_, 1, v___x_4352_);
v___x_4354_ = v___x_4350_;
goto v_reusejp_4353_;
}
else
{
lean_object* v_reuseFailAlloc_4357_; 
v_reuseFailAlloc_4357_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4357_, 0, v_mctx_4345_);
lean_ctor_set(v_reuseFailAlloc_4357_, 1, v___x_4352_);
lean_ctor_set(v_reuseFailAlloc_4357_, 2, v_zetaDeltaFVarIds_4346_);
lean_ctor_set(v_reuseFailAlloc_4357_, 3, v_postponed_4347_);
lean_ctor_set(v_reuseFailAlloc_4357_, 4, v_diag_4348_);
v___x_4354_ = v_reuseFailAlloc_4357_;
goto v_reusejp_4353_;
}
v_reusejp_4353_:
{
lean_object* v___x_4355_; lean_object* v___x_4356_; 
v___x_4355_ = lean_st_ref_set(v___y_4257_, v___x_4354_);
v___x_4356_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__0(v_a_4318_, v___x_4297_, v_compile_4251_, v_logCompileErrors_4252_, v___x_4297_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4356_;
goto v___jp_4266_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4318_);
lean_dec(v_a_4254_);
return v___x_4325_;
}
}
else
{
lean_dec(v_a_4318_);
lean_dec(v_a_4254_);
return v___x_4323_;
}
}
else
{
lean_object* v_a_4363_; lean_object* v___x_4365_; uint8_t v_isShared_4366_; uint8_t v_isSharedCheck_4370_; 
lean_dec(v_a_4318_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4363_ = lean_ctor_get(v___x_4321_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4321_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4365_ = v___x_4321_;
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
else
{
lean_inc(v_a_4363_);
lean_dec(v___x_4321_);
v___x_4365_ = lean_box(0);
v_isShared_4366_ = v_isSharedCheck_4370_;
goto v_resetjp_4364_;
}
v_resetjp_4364_:
{
lean_object* v___x_4368_; 
if (v_isShared_4366_ == 0)
{
v___x_4368_ = v___x_4365_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_a_4363_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
lean_dec(v_a_4314_);
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4371_ = lean_ctor_get(v___x_4317_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4317_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4317_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
else
{
lean_object* v___x_4379_; 
lean_dec(v_a_4314_);
lean_dec(v_a_4294_);
lean_inc(v___x_4299_);
v___x_4379_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4289_, v___x_4299_, v___y_4257_);
if (lean_obj_tag(v___x_4379_) == 0)
{
lean_dec_ref(v___x_4379_);
v_a_4262_ = v___x_4297_;
goto v___jp_4261_;
}
else
{
lean_dec(v_a_4254_);
return v___x_4379_;
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4380_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4313_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4313_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
else
{
lean_object* v_a_4388_; lean_object* v___x_4390_; uint8_t v_isShared_4391_; uint8_t v_isSharedCheck_4395_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4388_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4395_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4395_ == 0)
{
v___x_4390_ = v___x_4311_;
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
else
{
lean_inc(v_a_4388_);
lean_dec(v___x_4311_);
v___x_4390_ = lean_box(0);
v_isShared_4391_ = v_isSharedCheck_4395_;
goto v_resetjp_4389_;
}
v_resetjp_4389_:
{
lean_object* v___x_4393_; 
if (v_isShared_4391_ == 0)
{
v___x_4393_ = v___x_4390_;
goto v_reusejp_4392_;
}
else
{
lean_object* v_reuseFailAlloc_4394_; 
v_reuseFailAlloc_4394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4394_, 0, v_a_4388_);
v___x_4393_ = v_reuseFailAlloc_4394_;
goto v_reusejp_4392_;
}
v_reusejp_4392_:
{
return v___x_4393_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4437_; lean_object* v___x_4439_; uint8_t v_isShared_4440_; uint8_t v_isSharedCheck_4444_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4437_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4444_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4444_ == 0)
{
v___x_4439_ = v___x_4301_;
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
else
{
lean_inc(v_a_4437_);
lean_dec(v___x_4301_);
v___x_4439_ = lean_box(0);
v_isShared_4440_ = v_isSharedCheck_4444_;
goto v_resetjp_4438_;
}
v_resetjp_4438_:
{
lean_object* v___x_4442_; 
if (v_isShared_4440_ == 0)
{
v___x_4442_ = v___x_4439_;
goto v_reusejp_4441_;
}
else
{
lean_object* v_reuseFailAlloc_4443_; 
v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4437_);
v___x_4442_ = v_reuseFailAlloc_4443_;
goto v_reusejp_4441_;
}
v_reusejp_4441_:
{
return v___x_4442_;
}
}
}
}
else
{
lean_object* v___x_4445_; 
lean_inc(v___y_4259_);
lean_inc_ref(v___y_4258_);
lean_inc(v___y_4257_);
lean_inc_ref(v___y_4256_);
lean_inc(v___x_4299_);
v___x_4445_ = lean_infer_type(v___x_4299_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v_a_4446_; lean_object* v___x_4447_; 
v_a_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc_n(v_a_4446_, 2);
lean_dec_ref(v___x_4445_);
lean_inc(v_a_4294_);
v___x_4447_ = l_Lean_Meta_isExprDefEq(v_a_4294_, v_a_4446_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; uint8_t v___x_4449_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref(v___x_4447_);
v___x_4449_ = lean_unbox(v_a_4448_);
lean_dec(v_a_4448_);
if (v___x_4449_ == 0)
{
lean_object* v_options_4450_; lean_object* v_inheritedTraceOptions_4451_; uint8_t v_hasTrace_4452_; 
v_options_4450_ = lean_ctor_get(v___y_4258_, 2);
v_inheritedTraceOptions_4451_ = lean_ctor_get(v___y_4258_, 13);
v_hasTrace_4452_ = lean_ctor_get_uint8(v_options_4450_, sizeof(void*)*1);
if (v_hasTrace_4452_ == 0)
{
lean_dec(v_a_4446_);
goto v___jp_4453_;
}
else
{
lean_object* v___x_4455_; uint8_t v___x_4456_; 
v___x_4455_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4456_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4451_, v_options_4450_, v___x_4455_);
if (v___x_4456_ == 0)
{
lean_dec(v_a_4446_);
goto v___jp_4453_;
}
else
{
lean_object* v___x_4457_; lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; lean_object* v___x_4470_; lean_object* v___x_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4457_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__3);
lean_inc(v_a_4254_);
v___x_4458_ = l_Nat_reprFast(v_a_4254_);
v___x_4459_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_4459_, 0, v___x_4458_);
v___x_4460_ = l_Lean_MessageData_ofFormat(v___x_4459_);
v___x_4461_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4461_, 0, v___x_4457_);
lean_ctor_set(v___x_4461_, 1, v___x_4460_);
v___x_4462_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__5);
v___x_4463_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4463_, 0, v___x_4461_);
lean_ctor_set(v___x_4463_, 1, v___x_4462_);
lean_inc(v_a_4294_);
v___x_4464_ = l_Lean_MessageData_ofExpr(v_a_4294_);
v___x_4465_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4465_, 0, v___x_4463_);
lean_ctor_set(v___x_4465_, 1, v___x_4464_);
v___x_4466_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__7);
v___x_4467_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4467_, 0, v___x_4465_);
lean_ctor_set(v___x_4467_, 1, v___x_4466_);
v___x_4468_ = l_Lean_MessageData_ofExpr(v_a_4446_);
v___x_4469_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4469_, 0, v___x_4467_);
lean_ctor_set(v___x_4469_, 1, v___x_4468_);
v___x_4470_ = lean_obj_once(&l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9, &l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9_once, _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___closed__9);
v___x_4471_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4471_, 0, v___x_4469_);
lean_ctor_set(v___x_4471_, 1, v___x_4470_);
lean_inc(v___x_4299_);
v___x_4472_ = l_Lean_MessageData_ofExpr(v___x_4299_);
v___x_4473_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4473_, 0, v___x_4471_);
lean_ctor_set(v___x_4473_, 1, v___x_4472_);
v___x_4474_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4298_, v___x_4473_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_object* v_a_4475_; lean_object* v___x_4476_; 
v_a_4475_ = lean_ctor_get(v___x_4474_, 0);
lean_inc(v_a_4475_);
lean_dec_ref(v___x_4474_);
lean_inc(v___x_4299_);
v___x_4476_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4294_, v___x_4299_, v___x_4250_, v___x_4289_, v___x_4297_, v_a_4475_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4476_;
goto v___jp_4266_;
}
else
{
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
return v___x_4474_;
}
}
}
v___jp_4453_:
{
lean_object* v___x_4454_; 
lean_inc(v___x_4299_);
v___x_4454_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__3(v_a_4294_, v___x_4299_, v___x_4250_, v___x_4289_, v___x_4297_, v___x_4297_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
v___y_4267_ = v___x_4454_;
goto v___jp_4266_;
}
}
else
{
lean_object* v___x_4477_; 
lean_dec(v_a_4446_);
lean_dec(v_a_4294_);
lean_inc(v___x_4299_);
v___x_4477_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_4289_, v___x_4299_, v___y_4257_);
if (lean_obj_tag(v___x_4477_) == 0)
{
lean_dec_ref(v___x_4477_);
v_a_4262_ = v___x_4297_;
goto v___jp_4261_;
}
else
{
lean_dec(v_a_4254_);
return v___x_4477_;
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec(v_a_4446_);
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4478_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4447_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4447_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
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
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4486_ = lean_ctor_get(v___x_4445_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4445_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4445_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4445_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
else
{
lean_object* v_a_4494_; lean_object* v___x_4496_; uint8_t v_isShared_4497_; uint8_t v_isSharedCheck_4501_; 
lean_dec(v_a_4294_);
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4494_ = lean_ctor_get(v___x_4295_, 0);
v_isSharedCheck_4501_ = !lean_is_exclusive(v___x_4295_);
if (v_isSharedCheck_4501_ == 0)
{
v___x_4496_ = v___x_4295_;
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
else
{
lean_inc(v_a_4494_);
lean_dec(v___x_4295_);
v___x_4496_ = lean_box(0);
v_isShared_4497_ = v_isSharedCheck_4501_;
goto v_resetjp_4495_;
}
v_resetjp_4495_:
{
lean_object* v___x_4499_; 
if (v_isShared_4497_ == 0)
{
v___x_4499_ = v___x_4496_;
goto v_reusejp_4498_;
}
else
{
lean_object* v_reuseFailAlloc_4500_; 
v_reuseFailAlloc_4500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4500_, 0, v_a_4494_);
v___x_4499_ = v_reuseFailAlloc_4500_;
goto v_reusejp_4498_;
}
v_reusejp_4498_:
{
return v___x_4499_;
}
}
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4502_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4293_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4293_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
else
{
lean_object* v_a_4510_; lean_object* v___x_4512_; uint8_t v_isShared_4513_; uint8_t v_isSharedCheck_4517_; 
lean_dec(v___x_4289_);
lean_dec(v_a_4254_);
v_a_4510_ = lean_ctor_get(v___x_4290_, 0);
v_isSharedCheck_4517_ = !lean_is_exclusive(v___x_4290_);
if (v_isSharedCheck_4517_ == 0)
{
v___x_4512_ = v___x_4290_;
v_isShared_4513_ = v_isSharedCheck_4517_;
goto v_resetjp_4511_;
}
else
{
lean_inc(v_a_4510_);
lean_dec(v___x_4290_);
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
v___jp_4261_:
{
lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; 
v___x_4263_ = lean_unsigned_to_nat(1u);
v___x_4264_ = lean_nat_add(v_a_4254_, v___x_4263_);
lean_dec(v_a_4254_);
v___x_4265_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_4247_, v_fst_4248_, v_args_4249_, v___x_4250_, v_compile_4251_, v_logCompileErrors_4252_, v_isMeta_4253_, v___x_4264_, v_a_4262_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4265_;
}
v___jp_4266_:
{
if (lean_obj_tag(v___y_4267_) == 0)
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4277_; 
v_a_4268_ = lean_ctor_get(v___y_4267_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___y_4267_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4270_ = v___y_4267_;
v_isShared_4271_ = v_isSharedCheck_4277_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___y_4267_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4277_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
if (lean_obj_tag(v_a_4268_) == 0)
{
lean_object* v_a_4272_; lean_object* v___x_4274_; 
lean_dec(v_a_4254_);
v_a_4272_ = lean_ctor_get(v_a_4268_, 0);
lean_inc(v_a_4272_);
lean_dec_ref(v_a_4268_);
if (v_isShared_4271_ == 0)
{
lean_ctor_set(v___x_4270_, 0, v_a_4272_);
v___x_4274_ = v___x_4270_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4272_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
else
{
lean_object* v_a_4276_; 
lean_del_object(v___x_4270_);
v_a_4276_ = lean_ctor_get(v_a_4268_, 0);
lean_inc(v_a_4276_);
lean_dec_ref(v_a_4268_);
v_a_4262_ = v_a_4276_;
goto v___jp_4261_;
}
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec(v_a_4254_);
v_a_4278_ = lean_ctor_get(v___y_4267_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___y_4267_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___y_4267_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___y_4267_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(lean_object* v_a_4518_, lean_object* v_expectedType_4519_, uint8_t v___x_4520_, uint8_t v_compile_4521_, uint8_t v_logCompileErrors_4522_, uint8_t v_isMeta_4523_, lean_object* v_x_4524_, lean_object* v_x_4525_, lean_object* v_x_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; lean_object* v___y_4558_; lean_object* v___y_4572_; lean_object* v___y_4573_; lean_object* v___y_4574_; lean_object* v_options_4575_; lean_object* v___y_4576_; 
if (lean_obj_tag(v_x_4524_) == 5)
{
lean_object* v_fn_4644_; lean_object* v_arg_4645_; lean_object* v___x_4646_; lean_object* v___x_4647_; lean_object* v___x_4648_; 
v_fn_4644_ = lean_ctor_get(v_x_4524_, 0);
lean_inc_ref(v_fn_4644_);
v_arg_4645_ = lean_ctor_get(v_x_4524_, 1);
lean_inc_ref(v_arg_4645_);
lean_dec_ref(v_x_4524_);
v___x_4646_ = lean_array_set(v_x_4525_, v_x_4526_, v_arg_4645_);
v___x_4647_ = lean_unsigned_to_nat(1u);
v___x_4648_ = lean_nat_sub(v_x_4526_, v___x_4647_);
lean_dec(v_x_4526_);
v_x_4524_ = v_fn_4644_;
v_x_4525_ = v___x_4646_;
v_x_4526_ = v___x_4648_;
goto _start;
}
else
{
lean_object* v_cls_4650_; lean_object* v___y_4652_; lean_object* v___y_4653_; lean_object* v___y_4654_; lean_object* v___y_4655_; lean_object* v___x_4673_; 
lean_dec(v_x_4526_);
v_cls_4650_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4673_ = l_Lean_Expr_constName_x3f(v_x_4524_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
v___y_4652_ = v___y_4527_;
v___y_4653_ = v___y_4528_;
v___y_4654_ = v___y_4529_;
v___y_4655_ = v___y_4530_;
goto v___jp_4651_;
}
else
{
lean_object* v_val_4674_; lean_object* v___x_4675_; 
v_val_4674_ = lean_ctor_get(v___x_4673_, 0);
lean_inc(v_val_4674_);
lean_dec_ref(v___x_4673_);
v___x_4675_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4674_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4675_) == 0)
{
lean_object* v_a_4676_; 
v_a_4676_ = lean_ctor_get(v___x_4675_, 0);
lean_inc(v_a_4676_);
lean_dec_ref(v___x_4675_);
if (lean_obj_tag(v_a_4676_) == 6)
{
lean_object* v_val_4677_; lean_object* v___x_4678_; 
lean_dec_ref(v_a_4518_);
v_val_4677_ = lean_ctor_get(v_a_4676_, 0);
lean_inc_ref(v_val_4677_);
lean_dec_ref(v_a_4676_);
lean_inc(v___y_4530_);
lean_inc_ref(v___y_4529_);
lean_inc(v___y_4528_);
lean_inc_ref(v___y_4527_);
lean_inc_ref(v_x_4524_);
v___x_4678_ = lean_infer_type(v_x_4524_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4678_) == 0)
{
lean_object* v_a_4679_; uint8_t v___x_4680_; lean_object* v___x_4681_; 
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
lean_inc(v_a_4679_);
lean_dec_ref(v___x_4678_);
v___x_4680_ = 0;
v___x_4681_ = l_Lean_Meta_forallMetaTelescope(v_a_4679_, v___x_4680_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v_snd_4683_; lean_object* v_fst_4684_; lean_object* v___x_4686_; uint8_t v_isShared_4687_; uint8_t v_isSharedCheck_4784_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref(v___x_4681_);
v_snd_4683_ = lean_ctor_get(v_a_4682_, 1);
v_fst_4684_ = lean_ctor_get(v_a_4682_, 0);
v_isSharedCheck_4784_ = !lean_is_exclusive(v_a_4682_);
if (v_isSharedCheck_4784_ == 0)
{
v___x_4686_ = v_a_4682_;
v_isShared_4687_ = v_isSharedCheck_4784_;
goto v_resetjp_4685_;
}
else
{
lean_inc(v_snd_4683_);
lean_inc(v_fst_4684_);
lean_dec(v_a_4682_);
v___x_4686_ = lean_box(0);
v_isShared_4687_ = v_isSharedCheck_4784_;
goto v_resetjp_4685_;
}
v_resetjp_4685_:
{
lean_object* v_snd_4688_; lean_object* v___x_4690_; uint8_t v_isShared_4691_; uint8_t v_isSharedCheck_4782_; 
v_snd_4688_ = lean_ctor_get(v_snd_4683_, 1);
v_isSharedCheck_4782_ = !lean_is_exclusive(v_snd_4683_);
if (v_isSharedCheck_4782_ == 0)
{
lean_object* v_unused_4783_; 
v_unused_4783_ = lean_ctor_get(v_snd_4683_, 0);
lean_dec(v_unused_4783_);
v___x_4690_ = v_snd_4683_;
v_isShared_4691_ = v_isSharedCheck_4782_;
goto v_resetjp_4689_;
}
else
{
lean_inc(v_snd_4688_);
lean_dec(v_snd_4683_);
v___x_4690_ = lean_box(0);
v_isShared_4691_ = v_isSharedCheck_4782_;
goto v_resetjp_4689_;
}
v_resetjp_4689_:
{
lean_object* v___x_4692_; lean_object* v___y_4694_; lean_object* v___y_4695_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___x_4729_; uint8_t v___x_4730_; 
v___x_4692_ = lean_array_get_size(v_x_4525_);
v___x_4729_ = lean_array_get_size(v_fst_4684_);
v___x_4730_ = lean_nat_dec_eq(v___x_4692_, v___x_4729_);
if (v___x_4730_ == 0)
{
lean_object* v___x_4731_; lean_object* v___x_4732_; lean_object* v___x_4734_; 
lean_dec(v_snd_4688_);
lean_dec(v_fst_4684_);
lean_dec_ref(v_val_4677_);
lean_dec_ref(v_expectedType_4519_);
v___x_4731_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_4732_ = l_Lean_MessageData_ofExpr(v_x_4524_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 7);
lean_ctor_set(v___x_4690_, 1, v___x_4732_);
lean_ctor_set(v___x_4690_, 0, v___x_4731_);
v___x_4734_ = v___x_4690_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4745_; 
v_reuseFailAlloc_4745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4745_, 0, v___x_4731_);
lean_ctor_set(v_reuseFailAlloc_4745_, 1, v___x_4732_);
v___x_4734_ = v_reuseFailAlloc_4745_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
lean_object* v___x_4735_; lean_object* v___x_4737_; 
v___x_4735_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 7);
lean_ctor_set(v___x_4686_, 1, v___x_4735_);
lean_ctor_set(v___x_4686_, 0, v___x_4734_);
v___x_4737_ = v___x_4686_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4744_; 
v_reuseFailAlloc_4744_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4744_, 0, v___x_4734_);
lean_ctor_set(v_reuseFailAlloc_4744_, 1, v___x_4735_);
v___x_4737_ = v_reuseFailAlloc_4744_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
lean_object* v___x_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; lean_object* v___x_4742_; lean_object* v___x_4743_; 
v___x_4738_ = lean_array_to_list(v_x_4525_);
v___x_4739_ = lean_box(0);
v___x_4740_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_4738_, v___x_4739_);
v___x_4741_ = l_Lean_MessageData_ofList(v___x_4740_);
v___x_4742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4742_, 0, v___x_4737_);
lean_ctor_set(v___x_4742_, 1, v___x_4741_);
v___x_4743_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4742_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
return v___x_4743_;
}
}
}
else
{
lean_object* v___x_4746_; 
lean_inc_ref(v_expectedType_4519_);
v___x_4746_ = l_Lean_Meta_isExprDefEq(v_expectedType_4519_, v_snd_4688_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v_a_4747_; uint8_t v___x_4748_; 
v_a_4747_ = lean_ctor_get(v___x_4746_, 0);
lean_inc(v_a_4747_);
lean_dec_ref(v___x_4746_);
v___x_4748_ = lean_unbox(v_a_4747_);
if (v___x_4748_ == 0)
{
lean_object* v_toConstantVal_4749_; lean_object* v_name_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; lean_object* v___x_4754_; 
lean_dec(v_fst_4684_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
v_toConstantVal_4749_ = lean_ctor_get(v_val_4677_, 0);
lean_inc_ref(v_toConstantVal_4749_);
lean_dec_ref(v_val_4677_);
v_name_4750_ = lean_ctor_get(v_toConstantVal_4749_, 0);
lean_inc(v_name_4750_);
lean_dec_ref(v_toConstantVal_4749_);
v___x_4751_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_4752_ = l_Lean_MessageData_ofExpr(v_expectedType_4519_);
if (v_isShared_4691_ == 0)
{
lean_ctor_set_tag(v___x_4690_, 7);
lean_ctor_set(v___x_4690_, 1, v___x_4752_);
lean_ctor_set(v___x_4690_, 0, v___x_4751_);
v___x_4754_ = v___x_4690_;
goto v_reusejp_4753_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v___x_4751_);
lean_ctor_set(v_reuseFailAlloc_4773_, 1, v___x_4752_);
v___x_4754_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4753_;
}
v_reusejp_4753_:
{
lean_object* v___x_4755_; lean_object* v___x_4757_; 
v___x_4755_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_4687_ == 0)
{
lean_ctor_set_tag(v___x_4686_, 7);
lean_ctor_set(v___x_4686_, 1, v___x_4755_);
lean_ctor_set(v___x_4686_, 0, v___x_4754_);
v___x_4757_ = v___x_4686_;
goto v_reusejp_4756_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v___x_4754_);
lean_ctor_set(v_reuseFailAlloc_4772_, 1, v___x_4755_);
v___x_4757_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4756_;
}
v_reusejp_4756_:
{
uint8_t v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v___x_4762_; lean_object* v___x_4763_; lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
v___x_4758_ = lean_unbox(v_a_4747_);
lean_dec(v_a_4747_);
v___x_4759_ = l_Lean_MessageData_ofConstName(v_name_4750_, v___x_4758_);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4757_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_4762_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4762_, 0, v___x_4760_);
lean_ctor_set(v___x_4762_, 1, v___x_4761_);
v___x_4763_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_4762_, v___y_4527_, v___y_4528_, v___y_4529_, v___y_4530_);
v_a_4764_ = lean_ctor_get(v___x_4763_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4763_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4763_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4763_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
else
{
lean_dec(v_a_4747_);
lean_del_object(v___x_4690_);
lean_del_object(v___x_4686_);
lean_dec_ref(v_expectedType_4519_);
v___y_4694_ = v___y_4527_;
v___y_4695_ = v___y_4528_;
v___y_4696_ = v___y_4529_;
v___y_4697_ = v___y_4530_;
goto v___jp_4693_;
}
}
else
{
lean_object* v_a_4774_; lean_object* v___x_4776_; uint8_t v_isShared_4777_; uint8_t v_isSharedCheck_4781_; 
lean_del_object(v___x_4690_);
lean_del_object(v___x_4686_);
lean_dec(v_fst_4684_);
lean_dec_ref(v_val_4677_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_expectedType_4519_);
v_a_4774_ = lean_ctor_get(v___x_4746_, 0);
v_isSharedCheck_4781_ = !lean_is_exclusive(v___x_4746_);
if (v_isSharedCheck_4781_ == 0)
{
v___x_4776_ = v___x_4746_;
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
else
{
lean_inc(v_a_4774_);
lean_dec(v___x_4746_);
v___x_4776_ = lean_box(0);
v_isShared_4777_ = v_isSharedCheck_4781_;
goto v_resetjp_4775_;
}
v_resetjp_4775_:
{
lean_object* v___x_4779_; 
if (v_isShared_4777_ == 0)
{
v___x_4779_ = v___x_4776_;
goto v_reusejp_4778_;
}
else
{
lean_object* v_reuseFailAlloc_4780_; 
v_reuseFailAlloc_4780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4780_, 0, v_a_4774_);
v___x_4779_ = v_reuseFailAlloc_4780_;
goto v_reusejp_4778_;
}
v_reusejp_4778_:
{
return v___x_4779_;
}
}
}
}
v___jp_4693_:
{
lean_object* v_numParams_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; 
v_numParams_4698_ = lean_ctor_get(v_val_4677_, 3);
lean_inc(v_numParams_4698_);
lean_dec_ref(v_val_4677_);
v___x_4699_ = lean_box(0);
v___x_4700_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4692_, v_fst_4684_, v_x_4525_, v___x_4520_, v_compile_4521_, v_logCompileErrors_4522_, v_isMeta_4523_, v_numParams_4698_, v___x_4699_, v___y_4694_, v___y_4695_, v___y_4696_, v___y_4697_);
lean_dec_ref(v_x_4525_);
if (lean_obj_tag(v___x_4700_) == 0)
{
size_t v_sz_4701_; size_t v___x_4702_; lean_object* v___x_4703_; 
lean_dec_ref(v___x_4700_);
v_sz_4701_ = lean_array_size(v_fst_4684_);
v___x_4702_ = ((size_t)0ULL);
v___x_4703_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4701_, v___x_4702_, v_fst_4684_, v___y_4695_);
if (lean_obj_tag(v___x_4703_) == 0)
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4712_; 
v_a_4704_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4706_ = v___x_4703_;
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4703_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4712_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4708_; lean_object* v___x_4710_; 
v___x_4708_ = l_Lean_mkAppN(v_x_4524_, v_a_4704_);
lean_dec(v_a_4704_);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 0, v___x_4708_);
v___x_4710_ = v___x_4706_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v___x_4708_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
else
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4720_; 
lean_dec_ref(v_x_4524_);
v_a_4713_ = lean_ctor_get(v___x_4703_, 0);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4703_);
if (v_isSharedCheck_4720_ == 0)
{
v___x_4715_ = v___x_4703_;
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4703_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4720_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
lean_object* v___x_4718_; 
if (v_isShared_4716_ == 0)
{
v___x_4718_ = v___x_4715_;
goto v_reusejp_4717_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_a_4713_);
v___x_4718_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4717_;
}
v_reusejp_4717_:
{
return v___x_4718_;
}
}
}
}
else
{
lean_object* v_a_4721_; lean_object* v___x_4723_; uint8_t v_isShared_4724_; uint8_t v_isSharedCheck_4728_; 
lean_dec(v_fst_4684_);
lean_dec_ref(v_x_4524_);
v_a_4721_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4728_ == 0)
{
v___x_4723_ = v___x_4700_;
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
else
{
lean_inc(v_a_4721_);
lean_dec(v___x_4700_);
v___x_4723_ = lean_box(0);
v_isShared_4724_ = v_isSharedCheck_4728_;
goto v_resetjp_4722_;
}
v_resetjp_4722_:
{
lean_object* v___x_4726_; 
if (v_isShared_4724_ == 0)
{
v___x_4726_ = v___x_4723_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v_a_4721_);
v___x_4726_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
return v___x_4726_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_4785_; lean_object* v___x_4787_; uint8_t v_isShared_4788_; uint8_t v_isSharedCheck_4792_; 
lean_dec_ref(v_val_4677_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_expectedType_4519_);
v_a_4785_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4792_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4792_ == 0)
{
v___x_4787_ = v___x_4681_;
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
else
{
lean_inc(v_a_4785_);
lean_dec(v___x_4681_);
v___x_4787_ = lean_box(0);
v_isShared_4788_ = v_isSharedCheck_4792_;
goto v_resetjp_4786_;
}
v_resetjp_4786_:
{
lean_object* v___x_4790_; 
if (v_isShared_4788_ == 0)
{
v___x_4790_ = v___x_4787_;
goto v_reusejp_4789_;
}
else
{
lean_object* v_reuseFailAlloc_4791_; 
v_reuseFailAlloc_4791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4791_, 0, v_a_4785_);
v___x_4790_ = v_reuseFailAlloc_4791_;
goto v_reusejp_4789_;
}
v_reusejp_4789_:
{
return v___x_4790_;
}
}
}
}
else
{
lean_dec_ref(v_val_4677_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_expectedType_4519_);
return v___x_4678_;
}
}
else
{
lean_dec(v_a_4676_);
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
v___y_4652_ = v___y_4527_;
v___y_4653_ = v___y_4528_;
v___y_4654_ = v___y_4529_;
v___y_4655_ = v___y_4530_;
goto v___jp_4651_;
}
}
else
{
lean_object* v_a_4793_; lean_object* v___x_4795_; uint8_t v_isShared_4796_; uint8_t v_isSharedCheck_4800_; 
lean_dec_ref(v_x_4525_);
lean_dec_ref(v_x_4524_);
lean_dec_ref(v_expectedType_4519_);
lean_dec_ref(v_a_4518_);
v_a_4793_ = lean_ctor_get(v___x_4675_, 0);
v_isSharedCheck_4800_ = !lean_is_exclusive(v___x_4675_);
if (v_isSharedCheck_4800_ == 0)
{
v___x_4795_ = v___x_4675_;
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
else
{
lean_inc(v_a_4793_);
lean_dec(v___x_4675_);
v___x_4795_ = lean_box(0);
v_isShared_4796_ = v_isSharedCheck_4800_;
goto v_resetjp_4794_;
}
v_resetjp_4794_:
{
lean_object* v___x_4798_; 
if (v_isShared_4796_ == 0)
{
v___x_4798_ = v___x_4795_;
goto v_reusejp_4797_;
}
else
{
lean_object* v_reuseFailAlloc_4799_; 
v_reuseFailAlloc_4799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4799_, 0, v_a_4793_);
v___x_4798_ = v_reuseFailAlloc_4799_;
goto v_reusejp_4797_;
}
v_reusejp_4797_:
{
return v___x_4798_;
}
}
}
}
v___jp_4651_:
{
lean_object* v_options_4656_; uint8_t v_hasTrace_4657_; 
v_options_4656_ = lean_ctor_get(v___y_4654_, 2);
v_hasTrace_4657_ = lean_ctor_get_uint8(v_options_4656_, sizeof(void*)*1);
if (v_hasTrace_4657_ == 0)
{
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v___y_4574_ = v___y_4654_;
v_options_4575_ = v_options_4656_;
v___y_4576_ = v___y_4655_;
goto v___jp_4571_;
}
else
{
lean_object* v_inheritedTraceOptions_4658_; lean_object* v___x_4659_; uint8_t v___x_4660_; 
v_inheritedTraceOptions_4658_ = lean_ctor_get(v___y_4654_, 13);
v___x_4659_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4660_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4658_, v_options_4656_, v___x_4659_);
if (v___x_4660_ == 0)
{
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v___y_4574_ = v___y_4654_;
v_options_4575_ = v_options_4656_;
v___y_4576_ = v___y_4655_;
goto v___jp_4571_;
}
else
{
lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; 
v___x_4661_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_4518_);
v___x_4662_ = l_Lean_MessageData_ofExpr(v_a_4518_);
v___x_4663_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4663_, 0, v___x_4661_);
lean_ctor_set(v___x_4663_, 1, v___x_4662_);
v___x_4664_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4650_, v___x_4663_, v___y_4652_, v___y_4653_, v___y_4654_, v___y_4655_);
if (lean_obj_tag(v___x_4664_) == 0)
{
lean_dec_ref(v___x_4664_);
v___y_4572_ = v___y_4652_;
v___y_4573_ = v___y_4653_;
v___y_4574_ = v___y_4654_;
v_options_4575_ = v_options_4656_;
v___y_4576_ = v___y_4655_;
goto v___jp_4571_;
}
else
{
lean_object* v_a_4665_; lean_object* v___x_4667_; uint8_t v_isShared_4668_; uint8_t v_isSharedCheck_4672_; 
lean_dec_ref(v_expectedType_4519_);
lean_dec_ref(v_a_4518_);
v_a_4665_ = lean_ctor_get(v___x_4664_, 0);
v_isSharedCheck_4672_ = !lean_is_exclusive(v___x_4664_);
if (v_isSharedCheck_4672_ == 0)
{
v___x_4667_ = v___x_4664_;
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
else
{
lean_inc(v_a_4665_);
lean_dec(v___x_4664_);
v___x_4667_ = lean_box(0);
v_isShared_4668_ = v_isSharedCheck_4672_;
goto v_resetjp_4666_;
}
v_resetjp_4666_:
{
lean_object* v___x_4670_; 
if (v_isShared_4668_ == 0)
{
v___x_4670_ = v___x_4667_;
goto v_reusejp_4669_;
}
else
{
lean_object* v_reuseFailAlloc_4671_; 
v_reuseFailAlloc_4671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4671_, 0, v_a_4665_);
v___x_4670_ = v_reuseFailAlloc_4671_;
goto v_reusejp_4669_;
}
v_reusejp_4669_:
{
return v___x_4670_;
}
}
}
}
}
}
}
v___jp_4532_:
{
lean_object* v___x_4537_; 
v___x_4537_ = l_Lean_enableRealizationsForConst(v___y_4534_, v___y_4535_, v___y_4536_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4544_ == 0)
{
lean_object* v_unused_4545_; 
v_unused_4545_ = lean_ctor_get(v___x_4537_, 0);
lean_dec(v_unused_4545_);
v___x_4539_ = v___x_4537_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_dec(v___x_4537_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
lean_ctor_set(v___x_4539_, 0, v___y_4533_);
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v___y_4533_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v___y_4533_);
v_a_4546_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4537_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4537_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
v___jp_4554_:
{
if (v_compile_4521_ == 0)
{
v___y_4533_ = v___y_4555_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
v___y_4536_ = v___y_4558_;
goto v___jp_4532_;
}
else
{
lean_object* v___x_4559_; lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v___x_4562_; 
v___x_4559_ = lean_unsigned_to_nat(1u);
v___x_4560_ = lean_mk_empty_array_with_capacity(v___x_4559_);
lean_inc(v___y_4556_);
v___x_4561_ = lean_array_push(v___x_4560_, v___y_4556_);
v___x_4562_ = l_Lean_compileDecls(v___x_4561_, v_logCompileErrors_4522_, v___y_4557_, v___y_4558_);
if (lean_obj_tag(v___x_4562_) == 0)
{
lean_dec_ref(v___x_4562_);
v___y_4533_ = v___y_4555_;
v___y_4534_ = v___y_4556_;
v___y_4535_ = v___y_4557_;
v___y_4536_ = v___y_4558_;
goto v___jp_4532_;
}
else
{
lean_object* v_a_4563_; lean_object* v___x_4565_; uint8_t v_isShared_4566_; uint8_t v_isSharedCheck_4570_; 
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
v_a_4563_ = lean_ctor_get(v___x_4562_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4562_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4565_ = v___x_4562_;
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
else
{
lean_inc(v_a_4563_);
lean_dec(v___x_4562_);
v___x_4565_ = lean_box(0);
v_isShared_4566_ = v_isSharedCheck_4570_;
goto v_resetjp_4564_;
}
v_resetjp_4564_:
{
lean_object* v___x_4568_; 
if (v_isShared_4566_ == 0)
{
v___x_4568_ = v___x_4565_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_a_4563_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
}
v___jp_4571_:
{
lean_object* v___x_4577_; uint8_t v___x_4578_; 
v___x_4577_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4578_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4575_, v___x_4577_);
if (v___x_4578_ == 0)
{
lean_object* v___x_4579_; 
lean_dec_ref(v_expectedType_4519_);
v___x_4579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4579_, 0, v_a_4518_);
return v___x_4579_;
}
else
{
lean_object* v___x_4580_; 
lean_inc(v___y_4576_);
lean_inc_ref(v___y_4574_);
lean_inc(v___y_4573_);
lean_inc_ref(v___y_4572_);
lean_inc_ref(v_a_4518_);
v___x_4580_ = lean_infer_type(v_a_4518_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4576_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v_a_4581_; lean_object* v___x_4582_; 
v_a_4581_ = lean_ctor_get(v___x_4580_, 0);
lean_inc(v_a_4581_);
lean_dec_ref(v___x_4580_);
lean_inc_ref(v_expectedType_4519_);
v___x_4582_ = l_Lean_Meta_isExprDefEq(v_expectedType_4519_, v_a_4581_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4576_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4585_; uint8_t v_isShared_4586_; uint8_t v_isSharedCheck_4635_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4635_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4635_ == 0)
{
v___x_4585_ = v___x_4582_;
v_isShared_4586_ = v_isSharedCheck_4635_;
goto v_resetjp_4584_;
}
else
{
lean_inc(v_a_4583_);
lean_dec(v___x_4582_);
v___x_4585_ = lean_box(0);
v_isShared_4586_ = v_isSharedCheck_4635_;
goto v_resetjp_4584_;
}
v_resetjp_4584_:
{
uint8_t v___x_4587_; 
v___x_4587_ = lean_unbox(v_a_4583_);
if (v___x_4587_ == 0)
{
lean_object* v___x_4588_; lean_object* v___x_4589_; lean_object* v_a_4590_; uint8_t v___x_4591_; uint8_t v___x_4592_; lean_object* v___x_4593_; 
lean_del_object(v___x_4585_);
v___x_4588_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4589_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4588_, v___y_4576_);
v_a_4590_ = lean_ctor_get(v___x_4589_, 0);
lean_inc_n(v_a_4590_, 2);
lean_dec_ref(v___x_4589_);
v___x_4591_ = lean_unbox(v_a_4583_);
v___x_4592_ = lean_unbox(v_a_4583_);
lean_dec(v_a_4583_);
v___x_4593_ = l_Lean_Meta_mkAuxDefinition(v_a_4590_, v_expectedType_4519_, v_a_4518_, v___x_4591_, v___x_4592_, v___x_4520_, v___y_4572_, v___y_4573_, v___y_4574_, v___y_4576_);
if (lean_obj_tag(v___x_4593_) == 0)
{
lean_object* v_a_4594_; uint8_t v___x_4595_; lean_object* v___x_4596_; 
v_a_4594_ = lean_ctor_get(v___x_4593_, 0);
lean_inc(v_a_4594_);
lean_dec_ref(v___x_4593_);
v___x_4595_ = 3;
lean_inc(v_a_4590_);
v___x_4596_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4590_, v___x_4595_, v___y_4573_, v___y_4576_);
lean_dec_ref(v___x_4596_);
if (v_isMeta_4523_ == 0)
{
v___y_4555_ = v_a_4594_;
v___y_4556_ = v_a_4590_;
v___y_4557_ = v___y_4574_;
v___y_4558_ = v___y_4576_;
goto v___jp_4554_;
}
else
{
lean_object* v___x_4597_; lean_object* v_env_4598_; lean_object* v_nextMacroScope_4599_; lean_object* v_ngen_4600_; lean_object* v_auxDeclNGen_4601_; lean_object* v_traceState_4602_; lean_object* v_messages_4603_; lean_object* v_infoState_4604_; lean_object* v_snapshotTasks_4605_; lean_object* v___x_4607_; uint8_t v_isShared_4608_; uint8_t v_isSharedCheck_4630_; 
v___x_4597_ = lean_st_ref_take(v___y_4576_);
v_env_4598_ = lean_ctor_get(v___x_4597_, 0);
v_nextMacroScope_4599_ = lean_ctor_get(v___x_4597_, 1);
v_ngen_4600_ = lean_ctor_get(v___x_4597_, 2);
v_auxDeclNGen_4601_ = lean_ctor_get(v___x_4597_, 3);
v_traceState_4602_ = lean_ctor_get(v___x_4597_, 4);
v_messages_4603_ = lean_ctor_get(v___x_4597_, 6);
v_infoState_4604_ = lean_ctor_get(v___x_4597_, 7);
v_snapshotTasks_4605_ = lean_ctor_get(v___x_4597_, 8);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4630_ == 0)
{
lean_object* v_unused_4631_; 
v_unused_4631_ = lean_ctor_get(v___x_4597_, 5);
lean_dec(v_unused_4631_);
v___x_4607_ = v___x_4597_;
v_isShared_4608_ = v_isSharedCheck_4630_;
goto v_resetjp_4606_;
}
else
{
lean_inc(v_snapshotTasks_4605_);
lean_inc(v_infoState_4604_);
lean_inc(v_messages_4603_);
lean_inc(v_traceState_4602_);
lean_inc(v_auxDeclNGen_4601_);
lean_inc(v_ngen_4600_);
lean_inc(v_nextMacroScope_4599_);
lean_inc(v_env_4598_);
lean_dec(v___x_4597_);
v___x_4607_ = lean_box(0);
v_isShared_4608_ = v_isSharedCheck_4630_;
goto v_resetjp_4606_;
}
v_resetjp_4606_:
{
lean_object* v___x_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_inc(v_a_4590_);
v___x_4609_ = l_Lean_markMeta(v_env_4598_, v_a_4590_);
v___x_4610_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4608_ == 0)
{
lean_ctor_set(v___x_4607_, 5, v___x_4610_);
lean_ctor_set(v___x_4607_, 0, v___x_4609_);
v___x_4612_ = v___x_4607_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4629_, 1, v_nextMacroScope_4599_);
lean_ctor_set(v_reuseFailAlloc_4629_, 2, v_ngen_4600_);
lean_ctor_set(v_reuseFailAlloc_4629_, 3, v_auxDeclNGen_4601_);
lean_ctor_set(v_reuseFailAlloc_4629_, 4, v_traceState_4602_);
lean_ctor_set(v_reuseFailAlloc_4629_, 5, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4629_, 6, v_messages_4603_);
lean_ctor_set(v_reuseFailAlloc_4629_, 7, v_infoState_4604_);
lean_ctor_set(v_reuseFailAlloc_4629_, 8, v_snapshotTasks_4605_);
v___x_4612_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
lean_object* v___x_4613_; lean_object* v___x_4614_; lean_object* v_mctx_4615_; lean_object* v_zetaDeltaFVarIds_4616_; lean_object* v_postponed_4617_; lean_object* v_diag_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4627_; 
v___x_4613_ = lean_st_ref_set(v___y_4576_, v___x_4612_);
v___x_4614_ = lean_st_ref_take(v___y_4573_);
v_mctx_4615_ = lean_ctor_get(v___x_4614_, 0);
v_zetaDeltaFVarIds_4616_ = lean_ctor_get(v___x_4614_, 2);
v_postponed_4617_ = lean_ctor_get(v___x_4614_, 3);
v_diag_4618_ = lean_ctor_get(v___x_4614_, 4);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; 
v_unused_4628_ = lean_ctor_get(v___x_4614_, 1);
lean_dec(v_unused_4628_);
v___x_4620_ = v___x_4614_;
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_diag_4618_);
lean_inc(v_postponed_4617_);
lean_inc(v_zetaDeltaFVarIds_4616_);
lean_inc(v_mctx_4615_);
lean_dec(v___x_4614_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4627_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4622_; lean_object* v___x_4624_; 
v___x_4622_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4621_ == 0)
{
lean_ctor_set(v___x_4620_, 1, v___x_4622_);
v___x_4624_ = v___x_4620_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_mctx_4615_);
lean_ctor_set(v_reuseFailAlloc_4626_, 1, v___x_4622_);
lean_ctor_set(v_reuseFailAlloc_4626_, 2, v_zetaDeltaFVarIds_4616_);
lean_ctor_set(v_reuseFailAlloc_4626_, 3, v_postponed_4617_);
lean_ctor_set(v_reuseFailAlloc_4626_, 4, v_diag_4618_);
v___x_4624_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
lean_object* v___x_4625_; 
v___x_4625_ = lean_st_ref_set(v___y_4573_, v___x_4624_);
v___y_4555_ = v_a_4594_;
v___y_4556_ = v_a_4590_;
v___y_4557_ = v___y_4574_;
v___y_4558_ = v___y_4576_;
goto v___jp_4554_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4590_);
return v___x_4593_;
}
}
else
{
lean_object* v___x_4633_; 
lean_dec(v_a_4583_);
lean_dec_ref(v_expectedType_4519_);
if (v_isShared_4586_ == 0)
{
lean_ctor_set(v___x_4585_, 0, v_a_4518_);
v___x_4633_ = v___x_4585_;
goto v_reusejp_4632_;
}
else
{
lean_object* v_reuseFailAlloc_4634_; 
v_reuseFailAlloc_4634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4634_, 0, v_a_4518_);
v___x_4633_ = v_reuseFailAlloc_4634_;
goto v_reusejp_4632_;
}
v_reusejp_4632_:
{
return v___x_4633_;
}
}
}
}
else
{
lean_object* v_a_4636_; lean_object* v___x_4638_; uint8_t v_isShared_4639_; uint8_t v_isSharedCheck_4643_; 
lean_dec_ref(v_expectedType_4519_);
lean_dec_ref(v_a_4518_);
v_a_4636_ = lean_ctor_get(v___x_4582_, 0);
v_isSharedCheck_4643_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4643_ == 0)
{
v___x_4638_ = v___x_4582_;
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
else
{
lean_inc(v_a_4636_);
lean_dec(v___x_4582_);
v___x_4638_ = lean_box(0);
v_isShared_4639_ = v_isSharedCheck_4643_;
goto v_resetjp_4637_;
}
v_resetjp_4637_:
{
lean_object* v___x_4641_; 
if (v_isShared_4639_ == 0)
{
v___x_4641_ = v___x_4638_;
goto v_reusejp_4640_;
}
else
{
lean_object* v_reuseFailAlloc_4642_; 
v_reuseFailAlloc_4642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4636_);
v___x_4641_ = v_reuseFailAlloc_4642_;
goto v_reusejp_4640_;
}
v_reusejp_4640_:
{
return v___x_4641_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4519_);
lean_dec_ref(v_a_4518_);
return v___x_4580_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(lean_object* v_a_4801_, lean_object* v_expectedType_4802_, uint8_t v___x_4803_, uint8_t v_compile_4804_, uint8_t v_logCompileErrors_4805_, uint8_t v_isMeta_4806_, lean_object* v_x_4807_, lean_object* v_x_4808_, lean_object* v_x_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v___y_4816_; lean_object* v___y_4817_; lean_object* v___y_4818_; lean_object* v___y_4819_; lean_object* v___y_4838_; lean_object* v___y_4839_; lean_object* v___y_4840_; lean_object* v___y_4841_; lean_object* v___y_4855_; lean_object* v___y_4856_; lean_object* v___y_4857_; lean_object* v_options_4858_; lean_object* v___y_4859_; 
if (lean_obj_tag(v_x_4807_) == 5)
{
lean_object* v_fn_4927_; lean_object* v_arg_4928_; lean_object* v___x_4929_; lean_object* v___x_4930_; lean_object* v___x_4931_; lean_object* v___x_4932_; 
v_fn_4927_ = lean_ctor_get(v_x_4807_, 0);
lean_inc_ref(v_fn_4927_);
v_arg_4928_ = lean_ctor_get(v_x_4807_, 1);
lean_inc_ref(v_arg_4928_);
lean_dec_ref(v_x_4807_);
v___x_4929_ = lean_array_set(v_x_4808_, v_x_4809_, v_arg_4928_);
v___x_4930_ = lean_unsigned_to_nat(1u);
v___x_4931_ = lean_nat_sub(v_x_4809_, v___x_4930_);
v___x_4932_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(v_a_4801_, v_expectedType_4802_, v___x_4803_, v_compile_4804_, v_logCompileErrors_4805_, v_isMeta_4806_, v_fn_4927_, v___x_4929_, v___x_4931_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_4932_;
}
else
{
lean_object* v_cls_4933_; lean_object* v___y_4935_; lean_object* v___y_4936_; lean_object* v___y_4937_; lean_object* v___y_4938_; lean_object* v___x_4956_; 
v_cls_4933_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_4956_ = l_Lean_Expr_constName_x3f(v_x_4807_);
if (lean_obj_tag(v___x_4956_) == 0)
{
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
v___y_4935_ = v___y_4810_;
v___y_4936_ = v___y_4811_;
v___y_4937_ = v___y_4812_;
v___y_4938_ = v___y_4813_;
goto v___jp_4934_;
}
else
{
lean_object* v_val_4957_; lean_object* v___x_4958_; 
v_val_4957_ = lean_ctor_get(v___x_4956_, 0);
lean_inc(v_val_4957_);
lean_dec_ref(v___x_4956_);
v___x_4958_ = l_Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4(v_val_4957_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4958_) == 0)
{
lean_object* v_a_4959_; 
v_a_4959_ = lean_ctor_get(v___x_4958_, 0);
lean_inc(v_a_4959_);
lean_dec_ref(v___x_4958_);
if (lean_obj_tag(v_a_4959_) == 6)
{
lean_object* v_val_4960_; lean_object* v___x_4961_; 
lean_dec_ref(v_a_4801_);
v_val_4960_ = lean_ctor_get(v_a_4959_, 0);
lean_inc_ref(v_val_4960_);
lean_dec_ref(v_a_4959_);
lean_inc(v___y_4813_);
lean_inc_ref(v___y_4812_);
lean_inc(v___y_4811_);
lean_inc_ref(v___y_4810_);
lean_inc_ref(v_x_4807_);
v___x_4961_ = lean_infer_type(v_x_4807_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4961_) == 0)
{
lean_object* v_a_4962_; uint8_t v___x_4963_; lean_object* v___x_4964_; 
v_a_4962_ = lean_ctor_get(v___x_4961_, 0);
lean_inc(v_a_4962_);
lean_dec_ref(v___x_4961_);
v___x_4963_ = 0;
v___x_4964_ = l_Lean_Meta_forallMetaTelescope(v_a_4962_, v___x_4963_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_4964_) == 0)
{
lean_object* v_a_4965_; lean_object* v_snd_4966_; lean_object* v_fst_4967_; lean_object* v___x_4969_; uint8_t v_isShared_4970_; uint8_t v_isSharedCheck_5067_; 
v_a_4965_ = lean_ctor_get(v___x_4964_, 0);
lean_inc(v_a_4965_);
lean_dec_ref(v___x_4964_);
v_snd_4966_ = lean_ctor_get(v_a_4965_, 1);
v_fst_4967_ = lean_ctor_get(v_a_4965_, 0);
v_isSharedCheck_5067_ = !lean_is_exclusive(v_a_4965_);
if (v_isSharedCheck_5067_ == 0)
{
v___x_4969_ = v_a_4965_;
v_isShared_4970_ = v_isSharedCheck_5067_;
goto v_resetjp_4968_;
}
else
{
lean_inc(v_snd_4966_);
lean_inc(v_fst_4967_);
lean_dec(v_a_4965_);
v___x_4969_ = lean_box(0);
v_isShared_4970_ = v_isSharedCheck_5067_;
goto v_resetjp_4968_;
}
v_resetjp_4968_:
{
lean_object* v_snd_4971_; lean_object* v___x_4973_; uint8_t v_isShared_4974_; uint8_t v_isSharedCheck_5065_; 
v_snd_4971_ = lean_ctor_get(v_snd_4966_, 1);
v_isSharedCheck_5065_ = !lean_is_exclusive(v_snd_4966_);
if (v_isSharedCheck_5065_ == 0)
{
lean_object* v_unused_5066_; 
v_unused_5066_ = lean_ctor_get(v_snd_4966_, 0);
lean_dec(v_unused_5066_);
v___x_4973_ = v_snd_4966_;
v_isShared_4974_ = v_isSharedCheck_5065_;
goto v_resetjp_4972_;
}
else
{
lean_inc(v_snd_4971_);
lean_dec(v_snd_4966_);
v___x_4973_ = lean_box(0);
v_isShared_4974_ = v_isSharedCheck_5065_;
goto v_resetjp_4972_;
}
v_resetjp_4972_:
{
lean_object* v___x_4975_; lean_object* v___y_4977_; lean_object* v___y_4978_; lean_object* v___y_4979_; lean_object* v___y_4980_; lean_object* v___x_5012_; uint8_t v___x_5013_; 
v___x_4975_ = lean_array_get_size(v_x_4808_);
v___x_5012_ = lean_array_get_size(v_fst_4967_);
v___x_5013_ = lean_nat_dec_eq(v___x_4975_, v___x_5012_);
if (v___x_5013_ == 0)
{
lean_object* v___x_5014_; lean_object* v___x_5015_; lean_object* v___x_5017_; 
lean_dec(v_snd_4971_);
lean_dec(v_fst_4967_);
lean_dec_ref(v_val_4960_);
lean_dec_ref(v_expectedType_4802_);
v___x_5014_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__8);
v___x_5015_ = l_Lean_MessageData_ofExpr(v_x_4807_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set_tag(v___x_4973_, 7);
lean_ctor_set(v___x_4973_, 1, v___x_5015_);
lean_ctor_set(v___x_4973_, 0, v___x_5014_);
v___x_5017_ = v___x_4973_;
goto v_reusejp_5016_;
}
else
{
lean_object* v_reuseFailAlloc_5028_; 
v_reuseFailAlloc_5028_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5028_, 0, v___x_5014_);
lean_ctor_set(v_reuseFailAlloc_5028_, 1, v___x_5015_);
v___x_5017_ = v_reuseFailAlloc_5028_;
goto v_reusejp_5016_;
}
v_reusejp_5016_:
{
lean_object* v___x_5018_; lean_object* v___x_5020_; 
v___x_5018_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__10);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 7);
lean_ctor_set(v___x_4969_, 1, v___x_5018_);
lean_ctor_set(v___x_4969_, 0, v___x_5017_);
v___x_5020_ = v___x_4969_;
goto v_reusejp_5019_;
}
else
{
lean_object* v_reuseFailAlloc_5027_; 
v_reuseFailAlloc_5027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5027_, 0, v___x_5017_);
lean_ctor_set(v_reuseFailAlloc_5027_, 1, v___x_5018_);
v___x_5020_ = v_reuseFailAlloc_5027_;
goto v_reusejp_5019_;
}
v_reusejp_5019_:
{
lean_object* v___x_5021_; lean_object* v___x_5022_; lean_object* v___x_5023_; lean_object* v___x_5024_; lean_object* v___x_5025_; lean_object* v___x_5026_; 
v___x_5021_ = lean_array_to_list(v_x_4808_);
v___x_5022_ = lean_box(0);
v___x_5023_ = l_List_mapTR_loop___at___00Lean_Meta_wrapInstance_spec__8(v___x_5021_, v___x_5022_);
v___x_5024_ = l_Lean_MessageData_ofList(v___x_5023_);
v___x_5025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5025_, 0, v___x_5020_);
lean_ctor_set(v___x_5025_, 1, v___x_5024_);
v___x_5026_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5025_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
return v___x_5026_;
}
}
}
else
{
lean_object* v___x_5029_; 
lean_inc_ref(v_expectedType_4802_);
v___x_5029_ = l_Lean_Meta_isExprDefEq(v_expectedType_4802_, v_snd_4971_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
if (lean_obj_tag(v___x_5029_) == 0)
{
lean_object* v_a_5030_; uint8_t v___x_5031_; 
v_a_5030_ = lean_ctor_get(v___x_5029_, 0);
lean_inc(v_a_5030_);
lean_dec_ref(v___x_5029_);
v___x_5031_ = lean_unbox(v_a_5030_);
if (v___x_5031_ == 0)
{
lean_object* v_toConstantVal_5032_; lean_object* v_name_5033_; lean_object* v___x_5034_; lean_object* v___x_5035_; lean_object* v___x_5037_; 
lean_dec(v_fst_4967_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
v_toConstantVal_5032_ = lean_ctor_get(v_val_4960_, 0);
lean_inc_ref(v_toConstantVal_5032_);
lean_dec_ref(v_val_4960_);
v_name_5033_ = lean_ctor_get(v_toConstantVal_5032_, 0);
lean_inc(v_name_5033_);
lean_dec_ref(v_toConstantVal_5032_);
v___x_5034_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__12);
v___x_5035_ = l_Lean_MessageData_ofExpr(v_expectedType_4802_);
if (v_isShared_4974_ == 0)
{
lean_ctor_set_tag(v___x_4973_, 7);
lean_ctor_set(v___x_4973_, 1, v___x_5035_);
lean_ctor_set(v___x_4973_, 0, v___x_5034_);
v___x_5037_ = v___x_4973_;
goto v_reusejp_5036_;
}
else
{
lean_object* v_reuseFailAlloc_5056_; 
v_reuseFailAlloc_5056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5056_, 0, v___x_5034_);
lean_ctor_set(v_reuseFailAlloc_5056_, 1, v___x_5035_);
v___x_5037_ = v_reuseFailAlloc_5056_;
goto v_reusejp_5036_;
}
v_reusejp_5036_:
{
lean_object* v___x_5038_; lean_object* v___x_5040_; 
v___x_5038_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__14);
if (v_isShared_4970_ == 0)
{
lean_ctor_set_tag(v___x_4969_, 7);
lean_ctor_set(v___x_4969_, 1, v___x_5038_);
lean_ctor_set(v___x_4969_, 0, v___x_5037_);
v___x_5040_ = v___x_4969_;
goto v_reusejp_5039_;
}
else
{
lean_object* v_reuseFailAlloc_5055_; 
v_reuseFailAlloc_5055_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5055_, 0, v___x_5037_);
lean_ctor_set(v_reuseFailAlloc_5055_, 1, v___x_5038_);
v___x_5040_ = v_reuseFailAlloc_5055_;
goto v_reusejp_5039_;
}
v_reusejp_5039_:
{
uint8_t v___x_5041_; lean_object* v___x_5042_; lean_object* v___x_5043_; lean_object* v___x_5044_; lean_object* v___x_5045_; lean_object* v___x_5046_; lean_object* v_a_5047_; lean_object* v___x_5049_; uint8_t v_isShared_5050_; uint8_t v_isSharedCheck_5054_; 
v___x_5041_ = lean_unbox(v_a_5030_);
lean_dec(v_a_5030_);
v___x_5042_ = l_Lean_MessageData_ofConstName(v_name_5033_, v___x_5041_);
v___x_5043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5043_, 0, v___x_5040_);
lean_ctor_set(v___x_5043_, 1, v___x_5042_);
v___x_5044_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg___closed__3);
v___x_5045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5045_, 0, v___x_5043_);
lean_ctor_set(v___x_5045_, 1, v___x_5044_);
v___x_5046_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v___x_5045_, v___y_4810_, v___y_4811_, v___y_4812_, v___y_4813_);
v_a_5047_ = lean_ctor_get(v___x_5046_, 0);
v_isSharedCheck_5054_ = !lean_is_exclusive(v___x_5046_);
if (v_isSharedCheck_5054_ == 0)
{
v___x_5049_ = v___x_5046_;
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
else
{
lean_inc(v_a_5047_);
lean_dec(v___x_5046_);
v___x_5049_ = lean_box(0);
v_isShared_5050_ = v_isSharedCheck_5054_;
goto v_resetjp_5048_;
}
v_resetjp_5048_:
{
lean_object* v___x_5052_; 
if (v_isShared_5050_ == 0)
{
v___x_5052_ = v___x_5049_;
goto v_reusejp_5051_;
}
else
{
lean_object* v_reuseFailAlloc_5053_; 
v_reuseFailAlloc_5053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5053_, 0, v_a_5047_);
v___x_5052_ = v_reuseFailAlloc_5053_;
goto v_reusejp_5051_;
}
v_reusejp_5051_:
{
return v___x_5052_;
}
}
}
}
}
else
{
lean_dec(v_a_5030_);
lean_del_object(v___x_4973_);
lean_del_object(v___x_4969_);
lean_dec_ref(v_expectedType_4802_);
v___y_4977_ = v___y_4810_;
v___y_4978_ = v___y_4811_;
v___y_4979_ = v___y_4812_;
v___y_4980_ = v___y_4813_;
goto v___jp_4976_;
}
}
else
{
lean_object* v_a_5057_; lean_object* v___x_5059_; uint8_t v_isShared_5060_; uint8_t v_isSharedCheck_5064_; 
lean_del_object(v___x_4973_);
lean_del_object(v___x_4969_);
lean_dec(v_fst_4967_);
lean_dec_ref(v_val_4960_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_expectedType_4802_);
v_a_5057_ = lean_ctor_get(v___x_5029_, 0);
v_isSharedCheck_5064_ = !lean_is_exclusive(v___x_5029_);
if (v_isSharedCheck_5064_ == 0)
{
v___x_5059_ = v___x_5029_;
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
else
{
lean_inc(v_a_5057_);
lean_dec(v___x_5029_);
v___x_5059_ = lean_box(0);
v_isShared_5060_ = v_isSharedCheck_5064_;
goto v_resetjp_5058_;
}
v_resetjp_5058_:
{
lean_object* v___x_5062_; 
if (v_isShared_5060_ == 0)
{
v___x_5062_ = v___x_5059_;
goto v_reusejp_5061_;
}
else
{
lean_object* v_reuseFailAlloc_5063_; 
v_reuseFailAlloc_5063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5063_, 0, v_a_5057_);
v___x_5062_ = v_reuseFailAlloc_5063_;
goto v_reusejp_5061_;
}
v_reusejp_5061_:
{
return v___x_5062_;
}
}
}
}
v___jp_4976_:
{
lean_object* v_numParams_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v_numParams_4981_ = lean_ctor_get(v_val_4960_, 3);
lean_inc(v_numParams_4981_);
lean_dec_ref(v_val_4960_);
v___x_4982_ = lean_box(0);
v___x_4983_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v___x_4975_, v_fst_4967_, v_x_4808_, v___x_4803_, v_compile_4804_, v_logCompileErrors_4805_, v_isMeta_4806_, v_numParams_4981_, v___x_4982_, v___y_4977_, v___y_4978_, v___y_4979_, v___y_4980_);
lean_dec_ref(v_x_4808_);
if (lean_obj_tag(v___x_4983_) == 0)
{
size_t v_sz_4984_; size_t v___x_4985_; lean_object* v___x_4986_; 
lean_dec_ref(v___x_4983_);
v_sz_4984_ = lean_array_size(v_fst_4967_);
v___x_4985_ = ((size_t)0ULL);
v___x_4986_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_4984_, v___x_4985_, v_fst_4967_, v___y_4978_);
if (lean_obj_tag(v___x_4986_) == 0)
{
lean_object* v_a_4987_; lean_object* v___x_4989_; uint8_t v_isShared_4990_; uint8_t v_isSharedCheck_4995_; 
v_a_4987_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_4995_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_4995_ == 0)
{
v___x_4989_ = v___x_4986_;
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
else
{
lean_inc(v_a_4987_);
lean_dec(v___x_4986_);
v___x_4989_ = lean_box(0);
v_isShared_4990_ = v_isSharedCheck_4995_;
goto v_resetjp_4988_;
}
v_resetjp_4988_:
{
lean_object* v___x_4991_; lean_object* v___x_4993_; 
v___x_4991_ = l_Lean_mkAppN(v_x_4807_, v_a_4987_);
lean_dec(v_a_4987_);
if (v_isShared_4990_ == 0)
{
lean_ctor_set(v___x_4989_, 0, v___x_4991_);
v___x_4993_ = v___x_4989_;
goto v_reusejp_4992_;
}
else
{
lean_object* v_reuseFailAlloc_4994_; 
v_reuseFailAlloc_4994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4994_, 0, v___x_4991_);
v___x_4993_ = v_reuseFailAlloc_4994_;
goto v_reusejp_4992_;
}
v_reusejp_4992_:
{
return v___x_4993_;
}
}
}
else
{
lean_object* v_a_4996_; lean_object* v___x_4998_; uint8_t v_isShared_4999_; uint8_t v_isSharedCheck_5003_; 
lean_dec_ref(v_x_4807_);
v_a_4996_ = lean_ctor_get(v___x_4986_, 0);
v_isSharedCheck_5003_ = !lean_is_exclusive(v___x_4986_);
if (v_isSharedCheck_5003_ == 0)
{
v___x_4998_ = v___x_4986_;
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
else
{
lean_inc(v_a_4996_);
lean_dec(v___x_4986_);
v___x_4998_ = lean_box(0);
v_isShared_4999_ = v_isSharedCheck_5003_;
goto v_resetjp_4997_;
}
v_resetjp_4997_:
{
lean_object* v___x_5001_; 
if (v_isShared_4999_ == 0)
{
v___x_5001_ = v___x_4998_;
goto v_reusejp_5000_;
}
else
{
lean_object* v_reuseFailAlloc_5002_; 
v_reuseFailAlloc_5002_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5002_, 0, v_a_4996_);
v___x_5001_ = v_reuseFailAlloc_5002_;
goto v_reusejp_5000_;
}
v_reusejp_5000_:
{
return v___x_5001_;
}
}
}
}
else
{
lean_object* v_a_5004_; lean_object* v___x_5006_; uint8_t v_isShared_5007_; uint8_t v_isSharedCheck_5011_; 
lean_dec(v_fst_4967_);
lean_dec_ref(v_x_4807_);
v_a_5004_ = lean_ctor_get(v___x_4983_, 0);
v_isSharedCheck_5011_ = !lean_is_exclusive(v___x_4983_);
if (v_isSharedCheck_5011_ == 0)
{
v___x_5006_ = v___x_4983_;
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
else
{
lean_inc(v_a_5004_);
lean_dec(v___x_4983_);
v___x_5006_ = lean_box(0);
v_isShared_5007_ = v_isSharedCheck_5011_;
goto v_resetjp_5005_;
}
v_resetjp_5005_:
{
lean_object* v___x_5009_; 
if (v_isShared_5007_ == 0)
{
v___x_5009_ = v___x_5006_;
goto v_reusejp_5008_;
}
else
{
lean_object* v_reuseFailAlloc_5010_; 
v_reuseFailAlloc_5010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5010_, 0, v_a_5004_);
v___x_5009_ = v_reuseFailAlloc_5010_;
goto v_reusejp_5008_;
}
v_reusejp_5008_:
{
return v___x_5009_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_5068_; lean_object* v___x_5070_; uint8_t v_isShared_5071_; uint8_t v_isSharedCheck_5075_; 
lean_dec_ref(v_val_4960_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_expectedType_4802_);
v_a_5068_ = lean_ctor_get(v___x_4964_, 0);
v_isSharedCheck_5075_ = !lean_is_exclusive(v___x_4964_);
if (v_isSharedCheck_5075_ == 0)
{
v___x_5070_ = v___x_4964_;
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
else
{
lean_inc(v_a_5068_);
lean_dec(v___x_4964_);
v___x_5070_ = lean_box(0);
v_isShared_5071_ = v_isSharedCheck_5075_;
goto v_resetjp_5069_;
}
v_resetjp_5069_:
{
lean_object* v___x_5073_; 
if (v_isShared_5071_ == 0)
{
v___x_5073_ = v___x_5070_;
goto v_reusejp_5072_;
}
else
{
lean_object* v_reuseFailAlloc_5074_; 
v_reuseFailAlloc_5074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5074_, 0, v_a_5068_);
v___x_5073_ = v_reuseFailAlloc_5074_;
goto v_reusejp_5072_;
}
v_reusejp_5072_:
{
return v___x_5073_;
}
}
}
}
else
{
lean_dec_ref(v_val_4960_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_expectedType_4802_);
return v___x_4961_;
}
}
else
{
lean_dec(v_a_4959_);
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
v___y_4935_ = v___y_4810_;
v___y_4936_ = v___y_4811_;
v___y_4937_ = v___y_4812_;
v___y_4938_ = v___y_4813_;
goto v___jp_4934_;
}
}
else
{
lean_object* v_a_5076_; lean_object* v___x_5078_; uint8_t v_isShared_5079_; uint8_t v_isSharedCheck_5083_; 
lean_dec_ref(v_x_4808_);
lean_dec_ref(v_x_4807_);
lean_dec_ref(v_expectedType_4802_);
lean_dec_ref(v_a_4801_);
v_a_5076_ = lean_ctor_get(v___x_4958_, 0);
v_isSharedCheck_5083_ = !lean_is_exclusive(v___x_4958_);
if (v_isSharedCheck_5083_ == 0)
{
v___x_5078_ = v___x_4958_;
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
else
{
lean_inc(v_a_5076_);
lean_dec(v___x_4958_);
v___x_5078_ = lean_box(0);
v_isShared_5079_ = v_isSharedCheck_5083_;
goto v_resetjp_5077_;
}
v_resetjp_5077_:
{
lean_object* v___x_5081_; 
if (v_isShared_5079_ == 0)
{
v___x_5081_ = v___x_5078_;
goto v_reusejp_5080_;
}
else
{
lean_object* v_reuseFailAlloc_5082_; 
v_reuseFailAlloc_5082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5082_, 0, v_a_5076_);
v___x_5081_ = v_reuseFailAlloc_5082_;
goto v_reusejp_5080_;
}
v_reusejp_5080_:
{
return v___x_5081_;
}
}
}
}
v___jp_4934_:
{
lean_object* v_options_4939_; uint8_t v_hasTrace_4940_; 
v_options_4939_ = lean_ctor_get(v___y_4937_, 2);
v_hasTrace_4940_ = lean_ctor_get_uint8(v_options_4939_, sizeof(void*)*1);
if (v_hasTrace_4940_ == 0)
{
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v___y_4857_ = v___y_4937_;
v_options_4858_ = v_options_4939_;
v___y_4859_ = v___y_4938_;
goto v___jp_4854_;
}
else
{
lean_object* v_inheritedTraceOptions_4941_; lean_object* v___x_4942_; uint8_t v___x_4943_; 
v_inheritedTraceOptions_4941_ = lean_ctor_get(v___y_4937_, 13);
v___x_4942_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_4943_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_4941_, v_options_4939_, v___x_4942_);
if (v___x_4943_ == 0)
{
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v___y_4857_ = v___y_4937_;
v_options_4858_ = v_options_4939_;
v___y_4859_ = v___y_4938_;
goto v___jp_4854_;
}
else
{
lean_object* v___x_4944_; lean_object* v___x_4945_; lean_object* v___x_4946_; lean_object* v___x_4947_; 
v___x_4944_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__6);
lean_inc_ref(v_a_4801_);
v___x_4945_ = l_Lean_MessageData_ofExpr(v_a_4801_);
v___x_4946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4946_, 0, v___x_4944_);
lean_ctor_set(v___x_4946_, 1, v___x_4945_);
v___x_4947_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_4933_, v___x_4946_, v___y_4935_, v___y_4936_, v___y_4937_, v___y_4938_);
if (lean_obj_tag(v___x_4947_) == 0)
{
lean_dec_ref(v___x_4947_);
v___y_4855_ = v___y_4935_;
v___y_4856_ = v___y_4936_;
v___y_4857_ = v___y_4937_;
v_options_4858_ = v_options_4939_;
v___y_4859_ = v___y_4938_;
goto v___jp_4854_;
}
else
{
lean_object* v_a_4948_; lean_object* v___x_4950_; uint8_t v_isShared_4951_; uint8_t v_isSharedCheck_4955_; 
lean_dec_ref(v_expectedType_4802_);
lean_dec_ref(v_a_4801_);
v_a_4948_ = lean_ctor_get(v___x_4947_, 0);
v_isSharedCheck_4955_ = !lean_is_exclusive(v___x_4947_);
if (v_isSharedCheck_4955_ == 0)
{
v___x_4950_ = v___x_4947_;
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
else
{
lean_inc(v_a_4948_);
lean_dec(v___x_4947_);
v___x_4950_ = lean_box(0);
v_isShared_4951_ = v_isSharedCheck_4955_;
goto v_resetjp_4949_;
}
v_resetjp_4949_:
{
lean_object* v___x_4953_; 
if (v_isShared_4951_ == 0)
{
v___x_4953_ = v___x_4950_;
goto v_reusejp_4952_;
}
else
{
lean_object* v_reuseFailAlloc_4954_; 
v_reuseFailAlloc_4954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4954_, 0, v_a_4948_);
v___x_4953_ = v_reuseFailAlloc_4954_;
goto v_reusejp_4952_;
}
v_reusejp_4952_:
{
return v___x_4953_;
}
}
}
}
}
}
}
v___jp_4815_:
{
lean_object* v___x_4820_; 
v___x_4820_ = l_Lean_enableRealizationsForConst(v___y_4817_, v___y_4818_, v___y_4819_);
if (lean_obj_tag(v___x_4820_) == 0)
{
lean_object* v___x_4822_; uint8_t v_isShared_4823_; uint8_t v_isSharedCheck_4827_; 
v_isSharedCheck_4827_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4827_ == 0)
{
lean_object* v_unused_4828_; 
v_unused_4828_ = lean_ctor_get(v___x_4820_, 0);
lean_dec(v_unused_4828_);
v___x_4822_ = v___x_4820_;
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
else
{
lean_dec(v___x_4820_);
v___x_4822_ = lean_box(0);
v_isShared_4823_ = v_isSharedCheck_4827_;
goto v_resetjp_4821_;
}
v_resetjp_4821_:
{
lean_object* v___x_4825_; 
if (v_isShared_4823_ == 0)
{
lean_ctor_set(v___x_4822_, 0, v___y_4816_);
v___x_4825_ = v___x_4822_;
goto v_reusejp_4824_;
}
else
{
lean_object* v_reuseFailAlloc_4826_; 
v_reuseFailAlloc_4826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4826_, 0, v___y_4816_);
v___x_4825_ = v_reuseFailAlloc_4826_;
goto v_reusejp_4824_;
}
v_reusejp_4824_:
{
return v___x_4825_;
}
}
}
else
{
lean_object* v_a_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4836_; 
lean_dec_ref(v___y_4816_);
v_a_4829_ = lean_ctor_get(v___x_4820_, 0);
v_isSharedCheck_4836_ = !lean_is_exclusive(v___x_4820_);
if (v_isSharedCheck_4836_ == 0)
{
v___x_4831_ = v___x_4820_;
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_a_4829_);
lean_dec(v___x_4820_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4836_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___x_4834_; 
if (v_isShared_4832_ == 0)
{
v___x_4834_ = v___x_4831_;
goto v_reusejp_4833_;
}
else
{
lean_object* v_reuseFailAlloc_4835_; 
v_reuseFailAlloc_4835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4835_, 0, v_a_4829_);
v___x_4834_ = v_reuseFailAlloc_4835_;
goto v_reusejp_4833_;
}
v_reusejp_4833_:
{
return v___x_4834_;
}
}
}
}
v___jp_4837_:
{
if (v_compile_4804_ == 0)
{
v___y_4816_ = v___y_4838_;
v___y_4817_ = v___y_4839_;
v___y_4818_ = v___y_4840_;
v___y_4819_ = v___y_4841_;
goto v___jp_4815_;
}
else
{
lean_object* v___x_4842_; lean_object* v___x_4843_; lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4842_ = lean_unsigned_to_nat(1u);
v___x_4843_ = lean_mk_empty_array_with_capacity(v___x_4842_);
lean_inc(v___y_4839_);
v___x_4844_ = lean_array_push(v___x_4843_, v___y_4839_);
v___x_4845_ = l_Lean_compileDecls(v___x_4844_, v_logCompileErrors_4805_, v___y_4840_, v___y_4841_);
if (lean_obj_tag(v___x_4845_) == 0)
{
lean_dec_ref(v___x_4845_);
v___y_4816_ = v___y_4838_;
v___y_4817_ = v___y_4839_;
v___y_4818_ = v___y_4840_;
v___y_4819_ = v___y_4841_;
goto v___jp_4815_;
}
else
{
lean_object* v_a_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4853_; 
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
v_a_4846_ = lean_ctor_get(v___x_4845_, 0);
v_isSharedCheck_4853_ = !lean_is_exclusive(v___x_4845_);
if (v_isSharedCheck_4853_ == 0)
{
v___x_4848_ = v___x_4845_;
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_a_4846_);
lean_dec(v___x_4845_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4853_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___x_4851_; 
if (v_isShared_4849_ == 0)
{
v___x_4851_ = v___x_4848_;
goto v_reusejp_4850_;
}
else
{
lean_object* v_reuseFailAlloc_4852_; 
v_reuseFailAlloc_4852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4852_, 0, v_a_4846_);
v___x_4851_ = v_reuseFailAlloc_4852_;
goto v_reusejp_4850_;
}
v_reusejp_4850_:
{
return v___x_4851_;
}
}
}
}
}
v___jp_4854_:
{
lean_object* v___x_4860_; uint8_t v___x_4861_; 
v___x_4860_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_4861_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_4858_, v___x_4860_);
if (v___x_4861_ == 0)
{
lean_object* v___x_4862_; 
lean_dec_ref(v_expectedType_4802_);
v___x_4862_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4862_, 0, v_a_4801_);
return v___x_4862_;
}
else
{
lean_object* v___x_4863_; 
lean_inc(v___y_4859_);
lean_inc_ref(v___y_4857_);
lean_inc(v___y_4856_);
lean_inc_ref(v___y_4855_);
lean_inc_ref(v_a_4801_);
v___x_4863_ = lean_infer_type(v_a_4801_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4859_);
if (lean_obj_tag(v___x_4863_) == 0)
{
lean_object* v_a_4864_; lean_object* v___x_4865_; 
v_a_4864_ = lean_ctor_get(v___x_4863_, 0);
lean_inc(v_a_4864_);
lean_dec_ref(v___x_4863_);
lean_inc_ref(v_expectedType_4802_);
v___x_4865_ = l_Lean_Meta_isExprDefEq(v_expectedType_4802_, v_a_4864_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4859_);
if (lean_obj_tag(v___x_4865_) == 0)
{
lean_object* v_a_4866_; lean_object* v___x_4868_; uint8_t v_isShared_4869_; uint8_t v_isSharedCheck_4918_; 
v_a_4866_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4868_ = v___x_4865_;
v_isShared_4869_ = v_isSharedCheck_4918_;
goto v_resetjp_4867_;
}
else
{
lean_inc(v_a_4866_);
lean_dec(v___x_4865_);
v___x_4868_ = lean_box(0);
v_isShared_4869_ = v_isSharedCheck_4918_;
goto v_resetjp_4867_;
}
v_resetjp_4867_:
{
uint8_t v___x_4870_; 
v___x_4870_ = lean_unbox(v_a_4866_);
if (v___x_4870_ == 0)
{
lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v_a_4873_; uint8_t v___x_4874_; uint8_t v___x_4875_; lean_object* v___x_4876_; 
lean_del_object(v___x_4868_);
v___x_4871_ = ((lean_object*)(l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__1));
v___x_4872_ = l_Lean_mkAuxDeclName___at___00Lean_Meta_wrapInstance_spec__1___redArg(v___x_4871_, v___y_4859_);
v_a_4873_ = lean_ctor_get(v___x_4872_, 0);
lean_inc_n(v_a_4873_, 2);
lean_dec_ref(v___x_4872_);
v___x_4874_ = lean_unbox(v_a_4866_);
v___x_4875_ = lean_unbox(v_a_4866_);
lean_dec(v_a_4866_);
v___x_4876_ = l_Lean_Meta_mkAuxDefinition(v_a_4873_, v_expectedType_4802_, v_a_4801_, v___x_4874_, v___x_4875_, v___x_4803_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4859_);
if (lean_obj_tag(v___x_4876_) == 0)
{
lean_object* v_a_4877_; uint8_t v___x_4878_; lean_object* v___x_4879_; 
v_a_4877_ = lean_ctor_get(v___x_4876_, 0);
lean_inc(v_a_4877_);
lean_dec_ref(v___x_4876_);
v___x_4878_ = 3;
lean_inc(v_a_4873_);
v___x_4879_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg(v_a_4873_, v___x_4878_, v___y_4856_, v___y_4859_);
lean_dec_ref(v___x_4879_);
if (v_isMeta_4806_ == 0)
{
v___y_4838_ = v_a_4877_;
v___y_4839_ = v_a_4873_;
v___y_4840_ = v___y_4857_;
v___y_4841_ = v___y_4859_;
goto v___jp_4837_;
}
else
{
lean_object* v___x_4880_; lean_object* v_env_4881_; lean_object* v_nextMacroScope_4882_; lean_object* v_ngen_4883_; lean_object* v_auxDeclNGen_4884_; lean_object* v_traceState_4885_; lean_object* v_messages_4886_; lean_object* v_infoState_4887_; lean_object* v_snapshotTasks_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4913_; 
v___x_4880_ = lean_st_ref_take(v___y_4859_);
v_env_4881_ = lean_ctor_get(v___x_4880_, 0);
v_nextMacroScope_4882_ = lean_ctor_get(v___x_4880_, 1);
v_ngen_4883_ = lean_ctor_get(v___x_4880_, 2);
v_auxDeclNGen_4884_ = lean_ctor_get(v___x_4880_, 3);
v_traceState_4885_ = lean_ctor_get(v___x_4880_, 4);
v_messages_4886_ = lean_ctor_get(v___x_4880_, 6);
v_infoState_4887_ = lean_ctor_get(v___x_4880_, 7);
v_snapshotTasks_4888_ = lean_ctor_get(v___x_4880_, 8);
v_isSharedCheck_4913_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4913_ == 0)
{
lean_object* v_unused_4914_; 
v_unused_4914_ = lean_ctor_get(v___x_4880_, 5);
lean_dec(v_unused_4914_);
v___x_4890_ = v___x_4880_;
v_isShared_4891_ = v_isSharedCheck_4913_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_snapshotTasks_4888_);
lean_inc(v_infoState_4887_);
lean_inc(v_messages_4886_);
lean_inc(v_traceState_4885_);
lean_inc(v_auxDeclNGen_4884_);
lean_inc(v_ngen_4883_);
lean_inc(v_nextMacroScope_4882_);
lean_inc(v_env_4881_);
lean_dec(v___x_4880_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4913_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4895_; 
lean_inc(v_a_4873_);
v___x_4892_ = l_Lean_markMeta(v_env_4881_, v_a_4873_);
v___x_4893_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__2);
if (v_isShared_4891_ == 0)
{
lean_ctor_set(v___x_4890_, 5, v___x_4893_);
lean_ctor_set(v___x_4890_, 0, v___x_4892_);
v___x_4895_ = v___x_4890_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4912_; 
v_reuseFailAlloc_4912_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4912_, 0, v___x_4892_);
lean_ctor_set(v_reuseFailAlloc_4912_, 1, v_nextMacroScope_4882_);
lean_ctor_set(v_reuseFailAlloc_4912_, 2, v_ngen_4883_);
lean_ctor_set(v_reuseFailAlloc_4912_, 3, v_auxDeclNGen_4884_);
lean_ctor_set(v_reuseFailAlloc_4912_, 4, v_traceState_4885_);
lean_ctor_set(v_reuseFailAlloc_4912_, 5, v___x_4893_);
lean_ctor_set(v_reuseFailAlloc_4912_, 6, v_messages_4886_);
lean_ctor_set(v_reuseFailAlloc_4912_, 7, v_infoState_4887_);
lean_ctor_set(v_reuseFailAlloc_4912_, 8, v_snapshotTasks_4888_);
v___x_4895_ = v_reuseFailAlloc_4912_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
lean_object* v___x_4896_; lean_object* v___x_4897_; lean_object* v_mctx_4898_; lean_object* v_zetaDeltaFVarIds_4899_; lean_object* v_postponed_4900_; lean_object* v_diag_4901_; lean_object* v___x_4903_; uint8_t v_isShared_4904_; uint8_t v_isSharedCheck_4910_; 
v___x_4896_ = lean_st_ref_set(v___y_4859_, v___x_4895_);
v___x_4897_ = lean_st_ref_take(v___y_4856_);
v_mctx_4898_ = lean_ctor_get(v___x_4897_, 0);
v_zetaDeltaFVarIds_4899_ = lean_ctor_get(v___x_4897_, 2);
v_postponed_4900_ = lean_ctor_get(v___x_4897_, 3);
v_diag_4901_ = lean_ctor_get(v___x_4897_, 4);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4897_);
if (v_isSharedCheck_4910_ == 0)
{
lean_object* v_unused_4911_; 
v_unused_4911_ = lean_ctor_get(v___x_4897_, 1);
lean_dec(v_unused_4911_);
v___x_4903_ = v___x_4897_;
v_isShared_4904_ = v_isSharedCheck_4910_;
goto v_resetjp_4902_;
}
else
{
lean_inc(v_diag_4901_);
lean_inc(v_postponed_4900_);
lean_inc(v_zetaDeltaFVarIds_4899_);
lean_inc(v_mctx_4898_);
lean_dec(v___x_4897_);
v___x_4903_ = lean_box(0);
v_isShared_4904_ = v_isSharedCheck_4910_;
goto v_resetjp_4902_;
}
v_resetjp_4902_:
{
lean_object* v___x_4905_; lean_object* v___x_4907_; 
v___x_4905_ = lean_obj_once(&l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3, &l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3_once, _init_l_Lean_setReducibilityStatus___at___00Lean_Meta_wrapInstance_spec__2___redArg___closed__3);
if (v_isShared_4904_ == 0)
{
lean_ctor_set(v___x_4903_, 1, v___x_4905_);
v___x_4907_ = v___x_4903_;
goto v_reusejp_4906_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_mctx_4898_);
lean_ctor_set(v_reuseFailAlloc_4909_, 1, v___x_4905_);
lean_ctor_set(v_reuseFailAlloc_4909_, 2, v_zetaDeltaFVarIds_4899_);
lean_ctor_set(v_reuseFailAlloc_4909_, 3, v_postponed_4900_);
lean_ctor_set(v_reuseFailAlloc_4909_, 4, v_diag_4901_);
v___x_4907_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4906_;
}
v_reusejp_4906_:
{
lean_object* v___x_4908_; 
v___x_4908_ = lean_st_ref_set(v___y_4856_, v___x_4907_);
v___y_4838_ = v_a_4877_;
v___y_4839_ = v_a_4873_;
v___y_4840_ = v___y_4857_;
v___y_4841_ = v___y_4859_;
goto v___jp_4837_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4873_);
return v___x_4876_;
}
}
else
{
lean_object* v___x_4916_; 
lean_dec(v_a_4866_);
lean_dec_ref(v_expectedType_4802_);
if (v_isShared_4869_ == 0)
{
lean_ctor_set(v___x_4868_, 0, v_a_4801_);
v___x_4916_ = v___x_4868_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4801_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_dec_ref(v_expectedType_4802_);
lean_dec_ref(v_a_4801_);
v_a_4919_ = lean_ctor_get(v___x_4865_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4865_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4865_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4865_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
else
{
lean_dec_ref(v_expectedType_4802_);
lean_dec_ref(v_a_4801_);
return v___x_4863_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2(lean_object* v_expectedType_5084_, lean_object* v_inst_5085_, uint8_t v___x_5086_, uint8_t v_compile_5087_, uint8_t v_logCompileErrors_5088_, uint8_t v_isMeta_5089_, lean_object* v_____r_5090_, lean_object* v___y_5091_, lean_object* v___y_5092_, lean_object* v___y_5093_, lean_object* v___y_5094_){
_start:
{
lean_object* v___x_5096_; 
lean_inc_ref(v_expectedType_5084_);
v___x_5096_ = l_Lean_Meta_isProp(v_expectedType_5084_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
if (lean_obj_tag(v___x_5096_) == 0)
{
lean_object* v_a_5097_; lean_object* v___x_5099_; uint8_t v_isShared_5100_; uint8_t v_isSharedCheck_5118_; 
v_a_5097_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5118_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5118_ == 0)
{
v___x_5099_ = v___x_5096_;
v_isShared_5100_ = v_isSharedCheck_5118_;
goto v_resetjp_5098_;
}
else
{
lean_inc(v_a_5097_);
lean_dec(v___x_5096_);
v___x_5099_ = lean_box(0);
v_isShared_5100_ = v_isSharedCheck_5118_;
goto v_resetjp_5098_;
}
v_resetjp_5098_:
{
uint8_t v___x_5101_; 
v___x_5101_ = lean_unbox(v_a_5097_);
lean_dec(v_a_5097_);
if (v___x_5101_ == 0)
{
lean_object* v___x_5102_; 
lean_del_object(v___x_5099_);
lean_inc(v___y_5094_);
lean_inc_ref(v___y_5093_);
lean_inc(v___y_5092_);
lean_inc_ref(v___y_5091_);
v___x_5102_ = lean_whnf(v_inst_5085_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
if (lean_obj_tag(v___x_5102_) == 0)
{
lean_object* v_a_5103_; lean_object* v_dummy_5104_; lean_object* v_nargs_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v_a_5103_ = lean_ctor_get(v___x_5102_, 0);
lean_inc_n(v_a_5103_, 2);
lean_dec_ref(v___x_5102_);
v_dummy_5104_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5105_ = l_Lean_Expr_getAppNumArgs(v_a_5103_);
lean_inc(v_nargs_5105_);
v___x_5106_ = lean_mk_array(v_nargs_5105_, v_dummy_5104_);
v___x_5107_ = lean_unsigned_to_nat(1u);
v___x_5108_ = lean_nat_sub(v_nargs_5105_, v___x_5107_);
lean_dec(v_nargs_5105_);
v___x_5109_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_a_5103_, v_expectedType_5084_, v___x_5086_, v_compile_5087_, v_logCompileErrors_5088_, v_isMeta_5089_, v_a_5103_, v___x_5106_, v___x_5108_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
lean_dec(v___x_5108_);
return v___x_5109_;
}
else
{
lean_dec_ref(v_expectedType_5084_);
return v___x_5102_;
}
}
else
{
lean_object* v_options_5110_; lean_object* v___x_5111_; uint8_t v___x_5112_; 
v_options_5110_ = lean_ctor_get(v___y_5093_, 2);
v___x_5111_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5112_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5110_, v___x_5111_);
if (v___x_5112_ == 0)
{
lean_object* v___x_5114_; 
lean_dec_ref(v_expectedType_5084_);
if (v_isShared_5100_ == 0)
{
lean_ctor_set(v___x_5099_, 0, v_inst_5085_);
v___x_5114_ = v___x_5099_;
goto v_reusejp_5113_;
}
else
{
lean_object* v_reuseFailAlloc_5115_; 
v_reuseFailAlloc_5115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5115_, 0, v_inst_5085_);
v___x_5114_ = v_reuseFailAlloc_5115_;
goto v_reusejp_5113_;
}
v_reusejp_5113_:
{
return v___x_5114_;
}
}
else
{
lean_object* v___x_5116_; lean_object* v___x_5117_; 
lean_del_object(v___x_5099_);
v___x_5116_ = lean_box(0);
v___x_5117_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5084_, v_inst_5085_, v___x_5086_, v___x_5116_, v___x_5086_, v___y_5091_, v___y_5092_, v___y_5093_, v___y_5094_);
return v___x_5117_;
}
}
}
}
else
{
lean_object* v_a_5119_; lean_object* v___x_5121_; uint8_t v_isShared_5122_; uint8_t v_isSharedCheck_5126_; 
lean_dec_ref(v_inst_5085_);
lean_dec_ref(v_expectedType_5084_);
v_a_5119_ = lean_ctor_get(v___x_5096_, 0);
v_isSharedCheck_5126_ = !lean_is_exclusive(v___x_5096_);
if (v_isSharedCheck_5126_ == 0)
{
v___x_5121_ = v___x_5096_;
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
else
{
lean_inc(v_a_5119_);
lean_dec(v___x_5096_);
v___x_5121_ = lean_box(0);
v_isShared_5122_ = v_isSharedCheck_5126_;
goto v_resetjp_5120_;
}
v_resetjp_5120_:
{
lean_object* v___x_5124_; 
if (v_isShared_5122_ == 0)
{
v___x_5124_ = v___x_5121_;
goto v_reusejp_5123_;
}
else
{
lean_object* v_reuseFailAlloc_5125_; 
v_reuseFailAlloc_5125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5125_, 0, v_a_5119_);
v___x_5124_ = v_reuseFailAlloc_5125_;
goto v_reusejp_5123_;
}
v_reusejp_5123_:
{
return v___x_5124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance(lean_object* v_inst_5127_, lean_object* v_expectedType_5128_, uint8_t v_compile_5129_, uint8_t v_logCompileErrors_5130_, uint8_t v_isMeta_5131_, lean_object* v_a_5132_, lean_object* v_a_5133_, lean_object* v_a_5134_, lean_object* v_a_5135_){
_start:
{
lean_object* v___x_5137_; lean_object* v_options_5138_; uint8_t v_foApprox_5139_; uint8_t v_ctxApprox_5140_; uint8_t v_quasiPatternApprox_5141_; uint8_t v_constApprox_5142_; uint8_t v_isDefEqStuckEx_5143_; uint8_t v_unificationHints_5144_; uint8_t v_proofIrrelevance_5145_; uint8_t v_assignSyntheticOpaque_5146_; uint8_t v_offsetCnstrs_5147_; uint8_t v_etaStruct_5148_; uint8_t v_univApprox_5149_; uint8_t v_iota_5150_; uint8_t v_beta_5151_; uint8_t v_proj_5152_; uint8_t v_zeta_5153_; uint8_t v_zetaDelta_5154_; uint8_t v_zetaUnused_5155_; uint8_t v_zetaHave_5156_; lean_object* v___x_5158_; uint8_t v_isShared_5159_; uint8_t v_isSharedCheck_5404_; 
v___x_5137_ = l_Lean_Meta_Context_config(v_a_5132_);
v_options_5138_ = lean_ctor_get(v_a_5134_, 2);
v_foApprox_5139_ = lean_ctor_get_uint8(v___x_5137_, 0);
v_ctxApprox_5140_ = lean_ctor_get_uint8(v___x_5137_, 1);
v_quasiPatternApprox_5141_ = lean_ctor_get_uint8(v___x_5137_, 2);
v_constApprox_5142_ = lean_ctor_get_uint8(v___x_5137_, 3);
v_isDefEqStuckEx_5143_ = lean_ctor_get_uint8(v___x_5137_, 4);
v_unificationHints_5144_ = lean_ctor_get_uint8(v___x_5137_, 5);
v_proofIrrelevance_5145_ = lean_ctor_get_uint8(v___x_5137_, 6);
v_assignSyntheticOpaque_5146_ = lean_ctor_get_uint8(v___x_5137_, 7);
v_offsetCnstrs_5147_ = lean_ctor_get_uint8(v___x_5137_, 8);
v_etaStruct_5148_ = lean_ctor_get_uint8(v___x_5137_, 10);
v_univApprox_5149_ = lean_ctor_get_uint8(v___x_5137_, 11);
v_iota_5150_ = lean_ctor_get_uint8(v___x_5137_, 12);
v_beta_5151_ = lean_ctor_get_uint8(v___x_5137_, 13);
v_proj_5152_ = lean_ctor_get_uint8(v___x_5137_, 14);
v_zeta_5153_ = lean_ctor_get_uint8(v___x_5137_, 15);
v_zetaDelta_5154_ = lean_ctor_get_uint8(v___x_5137_, 16);
v_zetaUnused_5155_ = lean_ctor_get_uint8(v___x_5137_, 17);
v_zetaHave_5156_ = lean_ctor_get_uint8(v___x_5137_, 18);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5137_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5158_ = v___x_5137_;
v_isShared_5159_ = v_isSharedCheck_5404_;
goto v_resetjp_5157_;
}
else
{
lean_dec(v___x_5137_);
v___x_5158_ = lean_box(0);
v_isShared_5159_ = v_isSharedCheck_5404_;
goto v_resetjp_5157_;
}
v_resetjp_5157_:
{
uint8_t v_trackZetaDelta_5160_; lean_object* v_zetaDeltaSet_5161_; lean_object* v_lctx_5162_; lean_object* v_localInstances_5163_; lean_object* v_defEqCtx_x3f_5164_; lean_object* v_synthPendingDepth_5165_; lean_object* v_canUnfold_x3f_5166_; uint8_t v_univApprox_5167_; uint8_t v_inTypeClassResolution_5168_; uint8_t v_cacheInferType_5169_; lean_object* v_inheritedTraceOptions_5170_; uint8_t v_hasTrace_5171_; uint8_t v___x_5172_; lean_object* v_config_5174_; 
v_trackZetaDelta_5160_ = lean_ctor_get_uint8(v_a_5132_, sizeof(void*)*7);
v_zetaDeltaSet_5161_ = lean_ctor_get(v_a_5132_, 1);
v_lctx_5162_ = lean_ctor_get(v_a_5132_, 2);
v_localInstances_5163_ = lean_ctor_get(v_a_5132_, 3);
v_defEqCtx_x3f_5164_ = lean_ctor_get(v_a_5132_, 4);
v_synthPendingDepth_5165_ = lean_ctor_get(v_a_5132_, 5);
v_canUnfold_x3f_5166_ = lean_ctor_get(v_a_5132_, 6);
v_univApprox_5167_ = lean_ctor_get_uint8(v_a_5132_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_5168_ = lean_ctor_get_uint8(v_a_5132_, sizeof(void*)*7 + 2);
v_cacheInferType_5169_ = lean_ctor_get_uint8(v_a_5132_, sizeof(void*)*7 + 3);
v_inheritedTraceOptions_5170_ = lean_ctor_get(v_a_5134_, 13);
v_hasTrace_5171_ = lean_ctor_get_uint8(v_options_5138_, sizeof(void*)*1);
v___x_5172_ = 3;
if (v_isShared_5159_ == 0)
{
v_config_5174_ = v___x_5158_;
goto v_reusejp_5173_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 0, v_foApprox_5139_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 1, v_ctxApprox_5140_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 2, v_quasiPatternApprox_5141_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 3, v_constApprox_5142_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 4, v_isDefEqStuckEx_5143_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 5, v_unificationHints_5144_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 6, v_proofIrrelevance_5145_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 7, v_assignSyntheticOpaque_5146_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 8, v_offsetCnstrs_5147_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 10, v_etaStruct_5148_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 11, v_univApprox_5149_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 12, v_iota_5150_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 13, v_beta_5151_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 14, v_proj_5152_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 15, v_zeta_5153_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 16, v_zetaDelta_5154_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 17, v_zetaUnused_5155_);
lean_ctor_set_uint8(v_reuseFailAlloc_5403_, 18, v_zetaHave_5156_);
v_config_5174_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5173_;
}
v_reusejp_5173_:
{
uint64_t v___x_5175_; uint64_t v___x_5176_; uint64_t v___x_5177_; uint64_t v___x_5178_; uint64_t v___x_5179_; uint64_t v_key_5180_; lean_object* v___x_5181_; lean_object* v___x_5182_; 
lean_ctor_set_uint8(v_config_5174_, 9, v___x_5172_);
v___x_5175_ = l_Lean_Meta_Context_configKey(v_a_5132_);
v___x_5176_ = 2ULL;
v___x_5177_ = lean_uint64_shift_right(v___x_5175_, v___x_5176_);
v___x_5178_ = lean_uint64_shift_left(v___x_5177_, v___x_5176_);
v___x_5179_ = lean_uint64_once(&l_Lean_Meta_wrapInstance___closed__0, &l_Lean_Meta_wrapInstance___closed__0_once, _init_l_Lean_Meta_wrapInstance___closed__0);
v_key_5180_ = lean_uint64_lor(v___x_5178_, v___x_5179_);
v___x_5181_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5181_, 0, v_config_5174_);
lean_ctor_set_uint64(v___x_5181_, sizeof(void*)*1, v_key_5180_);
lean_inc(v_canUnfold_x3f_5166_);
lean_inc(v_synthPendingDepth_5165_);
lean_inc(v_defEqCtx_x3f_5164_);
lean_inc_ref(v_localInstances_5163_);
lean_inc_ref(v_lctx_5162_);
lean_inc(v_zetaDeltaSet_5161_);
v___x_5182_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5182_, 0, v___x_5181_);
lean_ctor_set(v___x_5182_, 1, v_zetaDeltaSet_5161_);
lean_ctor_set(v___x_5182_, 2, v_lctx_5162_);
lean_ctor_set(v___x_5182_, 3, v_localInstances_5163_);
lean_ctor_set(v___x_5182_, 4, v_defEqCtx_x3f_5164_);
lean_ctor_set(v___x_5182_, 5, v_synthPendingDepth_5165_);
lean_ctor_set(v___x_5182_, 6, v_canUnfold_x3f_5166_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*7, v_trackZetaDelta_5160_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*7 + 1, v_univApprox_5167_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*7 + 2, v_inTypeClassResolution_5168_);
lean_ctor_set_uint8(v___x_5182_, sizeof(void*)*7 + 3, v_cacheInferType_5169_);
if (v_hasTrace_5171_ == 0)
{
lean_object* v___x_5183_; 
lean_inc_ref(v_expectedType_5128_);
v___x_5183_ = l_Lean_Meta_isClass_x3f(v_expectedType_5128_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5183_) == 0)
{
lean_object* v_a_5184_; lean_object* v___x_5186_; uint8_t v_isShared_5187_; uint8_t v_isSharedCheck_5221_; 
v_a_5184_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5221_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5221_ == 0)
{
v___x_5186_ = v___x_5183_;
v_isShared_5187_ = v_isSharedCheck_5221_;
goto v_resetjp_5185_;
}
else
{
lean_inc(v_a_5184_);
lean_dec(v___x_5183_);
v___x_5186_ = lean_box(0);
v_isShared_5187_ = v_isSharedCheck_5221_;
goto v_resetjp_5185_;
}
v_resetjp_5185_:
{
if (lean_obj_tag(v_a_5184_) == 1)
{
lean_object* v___x_5188_; 
lean_dec_ref(v_a_5184_);
lean_del_object(v___x_5186_);
lean_inc_ref(v_expectedType_5128_);
v___x_5188_ = l_Lean_Meta_isProp(v_expectedType_5128_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5188_) == 0)
{
lean_object* v_a_5189_; lean_object* v___x_5191_; uint8_t v_isShared_5192_; uint8_t v_isSharedCheck_5209_; 
v_a_5189_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5209_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5209_ == 0)
{
v___x_5191_ = v___x_5188_;
v_isShared_5192_ = v_isSharedCheck_5209_;
goto v_resetjp_5190_;
}
else
{
lean_inc(v_a_5189_);
lean_dec(v___x_5188_);
v___x_5191_ = lean_box(0);
v_isShared_5192_ = v_isSharedCheck_5209_;
goto v_resetjp_5190_;
}
v_resetjp_5190_:
{
uint8_t v___x_5193_; 
v___x_5193_ = lean_unbox(v_a_5189_);
lean_dec(v_a_5189_);
if (v___x_5193_ == 0)
{
lean_object* v___x_5194_; 
lean_del_object(v___x_5191_);
lean_inc(v_a_5135_);
lean_inc_ref(v_a_5134_);
lean_inc(v_a_5133_);
lean_inc_ref(v___x_5182_);
v___x_5194_ = lean_whnf(v_inst_5127_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5194_) == 0)
{
lean_object* v_a_5195_; lean_object* v_dummy_5196_; lean_object* v_nargs_5197_; lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; lean_object* v___x_5201_; 
v_a_5195_ = lean_ctor_get(v___x_5194_, 0);
lean_inc_n(v_a_5195_, 2);
lean_dec_ref(v___x_5194_);
v_dummy_5196_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5197_ = l_Lean_Expr_getAppNumArgs(v_a_5195_);
lean_inc(v_nargs_5197_);
v___x_5198_ = lean_mk_array(v_nargs_5197_, v_dummy_5196_);
v___x_5199_ = lean_unsigned_to_nat(1u);
v___x_5200_ = lean_nat_sub(v_nargs_5197_, v___x_5199_);
lean_dec(v_nargs_5197_);
v___x_5201_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_a_5195_, v_expectedType_5128_, v_hasTrace_5171_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v_a_5195_, v___x_5198_, v___x_5200_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
lean_dec_ref(v___x_5182_);
lean_dec(v___x_5200_);
return v___x_5201_;
}
else
{
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
return v___x_5194_;
}
}
else
{
lean_object* v___x_5202_; uint8_t v___x_5203_; 
v___x_5202_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5203_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5138_, v___x_5202_);
if (v___x_5203_ == 0)
{
lean_object* v___x_5205_; 
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
if (v_isShared_5192_ == 0)
{
lean_ctor_set(v___x_5191_, 0, v_inst_5127_);
v___x_5205_ = v___x_5191_;
goto v_reusejp_5204_;
}
else
{
lean_object* v_reuseFailAlloc_5206_; 
v_reuseFailAlloc_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5206_, 0, v_inst_5127_);
v___x_5205_ = v_reuseFailAlloc_5206_;
goto v_reusejp_5204_;
}
v_reusejp_5204_:
{
return v___x_5205_;
}
}
else
{
lean_object* v___x_5207_; lean_object* v___x_5208_; 
lean_del_object(v___x_5191_);
v___x_5207_ = lean_box(0);
v___x_5208_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5128_, v_inst_5127_, v___x_5203_, v___x_5207_, v___x_5203_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
lean_dec_ref(v___x_5182_);
return v___x_5208_;
}
}
}
}
else
{
lean_object* v_a_5210_; lean_object* v___x_5212_; uint8_t v_isShared_5213_; uint8_t v_isSharedCheck_5217_; 
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5210_ = lean_ctor_get(v___x_5188_, 0);
v_isSharedCheck_5217_ = !lean_is_exclusive(v___x_5188_);
if (v_isSharedCheck_5217_ == 0)
{
v___x_5212_ = v___x_5188_;
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
else
{
lean_inc(v_a_5210_);
lean_dec(v___x_5188_);
v___x_5212_ = lean_box(0);
v_isShared_5213_ = v_isSharedCheck_5217_;
goto v_resetjp_5211_;
}
v_resetjp_5211_:
{
lean_object* v___x_5215_; 
if (v_isShared_5213_ == 0)
{
v___x_5215_ = v___x_5212_;
goto v_reusejp_5214_;
}
else
{
lean_object* v_reuseFailAlloc_5216_; 
v_reuseFailAlloc_5216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5216_, 0, v_a_5210_);
v___x_5215_ = v_reuseFailAlloc_5216_;
goto v_reusejp_5214_;
}
v_reusejp_5214_:
{
return v___x_5215_;
}
}
}
}
else
{
lean_object* v___x_5219_; 
lean_dec(v_a_5184_);
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
if (v_isShared_5187_ == 0)
{
lean_ctor_set(v___x_5186_, 0, v_inst_5127_);
v___x_5219_ = v___x_5186_;
goto v_reusejp_5218_;
}
else
{
lean_object* v_reuseFailAlloc_5220_; 
v_reuseFailAlloc_5220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5220_, 0, v_inst_5127_);
v___x_5219_ = v_reuseFailAlloc_5220_;
goto v_reusejp_5218_;
}
v_reusejp_5218_:
{
return v___x_5219_;
}
}
}
}
else
{
lean_object* v_a_5222_; lean_object* v___x_5224_; uint8_t v_isShared_5225_; uint8_t v_isSharedCheck_5229_; 
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5222_ = lean_ctor_get(v___x_5183_, 0);
v_isSharedCheck_5229_ = !lean_is_exclusive(v___x_5183_);
if (v_isSharedCheck_5229_ == 0)
{
v___x_5224_ = v___x_5183_;
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
else
{
lean_inc(v_a_5222_);
lean_dec(v___x_5183_);
v___x_5224_ = lean_box(0);
v_isShared_5225_ = v_isSharedCheck_5229_;
goto v_resetjp_5223_;
}
v_resetjp_5223_:
{
lean_object* v___x_5227_; 
if (v_isShared_5225_ == 0)
{
v___x_5227_ = v___x_5224_;
goto v_reusejp_5226_;
}
else
{
lean_object* v_reuseFailAlloc_5228_; 
v_reuseFailAlloc_5228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5228_, 0, v_a_5222_);
v___x_5227_ = v_reuseFailAlloc_5228_;
goto v_reusejp_5226_;
}
v_reusejp_5226_:
{
return v___x_5227_;
}
}
}
}
else
{
lean_object* v___f_5230_; lean_object* v_cls_5231_; lean_object* v___x_5232_; lean_object* v___x_5233_; uint8_t v___x_5234_; lean_object* v___y_5236_; lean_object* v___y_5237_; lean_object* v_a_5238_; lean_object* v___y_5248_; lean_object* v___y_5249_; lean_object* v_a_5250_; lean_object* v___y_5253_; lean_object* v___y_5254_; lean_object* v_a_5255_; lean_object* v___y_5258_; lean_object* v___y_5259_; lean_object* v___y_5260_; lean_object* v___y_5264_; lean_object* v___y_5265_; lean_object* v_a_5266_; lean_object* v___y_5279_; lean_object* v___y_5280_; lean_object* v_a_5281_; lean_object* v___y_5284_; lean_object* v___y_5285_; lean_object* v_a_5286_; lean_object* v___y_5289_; lean_object* v___y_5290_; lean_object* v___y_5291_; 
lean_inc_ref(v_expectedType_5128_);
v___f_5230_ = lean_alloc_closure((void*)(l_Lean_Meta_wrapInstance___lam__0___boxed), 7, 1);
lean_closure_set(v___f_5230_, 0, v_expectedType_5128_);
v_cls_5231_ = ((lean_object*)(l___private_Lean_Meta_WrapInstance_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_WrapInstance_3246864463____hygCtx___hyg_2_));
v___x_5232_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3___closed__1));
v___x_5233_ = lean_obj_once(&l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4, &l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4_once, _init_l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___closed__4);
v___x_5234_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_5170_, v_options_5138_, v___x_5233_);
if (v___x_5234_ == 0)
{
lean_object* v___x_5335_; uint8_t v___x_5336_; lean_object* v___y_5338_; lean_object* v___y_5339_; lean_object* v___y_5340_; lean_object* v___y_5341_; 
v___x_5335_ = l_Lean_trace_profiler;
v___x_5336_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5138_, v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5373_; 
lean_dec_ref(v___f_5230_);
lean_inc_ref(v_expectedType_5128_);
v___x_5373_ = l_Lean_Meta_isClass_x3f(v_expectedType_5128_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5373_) == 0)
{
lean_object* v_a_5374_; lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5394_; 
v_a_5374_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5394_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5394_ == 0)
{
v___x_5376_ = v___x_5373_;
v_isShared_5377_ = v_isSharedCheck_5394_;
goto v_resetjp_5375_;
}
else
{
lean_inc(v_a_5374_);
lean_dec(v___x_5373_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5394_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
if (lean_obj_tag(v_a_5374_) == 1)
{
lean_del_object(v___x_5376_);
if (v___x_5234_ == 0)
{
lean_dec_ref(v_a_5374_);
v___y_5338_ = v___x_5182_;
v___y_5339_ = v_a_5133_;
v___y_5340_ = v_a_5134_;
v___y_5341_ = v_a_5135_;
goto v___jp_5337_;
}
else
{
lean_object* v_val_5378_; lean_object* v___x_5379_; lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
v_val_5378_ = lean_ctor_get(v_a_5374_, 0);
lean_inc(v_val_5378_);
lean_dec_ref(v_a_5374_);
v___x_5379_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5380_ = l_Lean_MessageData_ofName(v_val_5378_);
v___x_5381_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5381_, 0, v___x_5379_);
lean_ctor_set(v___x_5381_, 1, v___x_5380_);
v___x_5382_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5231_, v___x_5381_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5382_) == 0)
{
lean_dec_ref(v___x_5382_);
v___y_5338_ = v___x_5182_;
v___y_5339_ = v_a_5133_;
v___y_5340_ = v_a_5134_;
v___y_5341_ = v_a_5135_;
goto v___jp_5337_;
}
else
{
lean_object* v_a_5383_; lean_object* v___x_5385_; uint8_t v_isShared_5386_; uint8_t v_isSharedCheck_5390_; 
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5383_ = lean_ctor_get(v___x_5382_, 0);
v_isSharedCheck_5390_ = !lean_is_exclusive(v___x_5382_);
if (v_isSharedCheck_5390_ == 0)
{
v___x_5385_ = v___x_5382_;
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
else
{
lean_inc(v_a_5383_);
lean_dec(v___x_5382_);
v___x_5385_ = lean_box(0);
v_isShared_5386_ = v_isSharedCheck_5390_;
goto v_resetjp_5384_;
}
v_resetjp_5384_:
{
lean_object* v___x_5388_; 
if (v_isShared_5386_ == 0)
{
v___x_5388_ = v___x_5385_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v_a_5383_);
v___x_5388_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
return v___x_5388_;
}
}
}
}
}
else
{
lean_object* v___x_5392_; 
lean_dec(v_a_5374_);
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 0, v_inst_5127_);
v___x_5392_ = v___x_5376_;
goto v_reusejp_5391_;
}
else
{
lean_object* v_reuseFailAlloc_5393_; 
v_reuseFailAlloc_5393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5393_, 0, v_inst_5127_);
v___x_5392_ = v_reuseFailAlloc_5393_;
goto v_reusejp_5391_;
}
v_reusejp_5391_:
{
return v___x_5392_;
}
}
}
}
else
{
lean_object* v_a_5395_; lean_object* v___x_5397_; uint8_t v_isShared_5398_; uint8_t v_isSharedCheck_5402_; 
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5395_ = lean_ctor_get(v___x_5373_, 0);
v_isSharedCheck_5402_ = !lean_is_exclusive(v___x_5373_);
if (v_isSharedCheck_5402_ == 0)
{
v___x_5397_ = v___x_5373_;
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
else
{
lean_inc(v_a_5395_);
lean_dec(v___x_5373_);
v___x_5397_ = lean_box(0);
v_isShared_5398_ = v_isSharedCheck_5402_;
goto v_resetjp_5396_;
}
v_resetjp_5396_:
{
lean_object* v___x_5400_; 
if (v_isShared_5398_ == 0)
{
v___x_5400_ = v___x_5397_;
goto v_reusejp_5399_;
}
else
{
lean_object* v_reuseFailAlloc_5401_; 
v_reuseFailAlloc_5401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5401_, 0, v_a_5395_);
v___x_5400_ = v_reuseFailAlloc_5401_;
goto v_reusejp_5399_;
}
v_reusejp_5399_:
{
return v___x_5400_;
}
}
}
}
else
{
goto v___jp_5294_;
}
v___jp_5337_:
{
lean_object* v___x_5342_; 
lean_inc_ref(v_expectedType_5128_);
v___x_5342_ = l_Lean_Meta_isProp(v_expectedType_5128_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5342_) == 0)
{
lean_object* v_a_5343_; lean_object* v___x_5345_; uint8_t v_isShared_5346_; uint8_t v_isSharedCheck_5364_; 
v_a_5343_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5364_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5364_ == 0)
{
v___x_5345_ = v___x_5342_;
v_isShared_5346_ = v_isSharedCheck_5364_;
goto v_resetjp_5344_;
}
else
{
lean_inc(v_a_5343_);
lean_dec(v___x_5342_);
v___x_5345_ = lean_box(0);
v_isShared_5346_ = v_isSharedCheck_5364_;
goto v_resetjp_5344_;
}
v_resetjp_5344_:
{
uint8_t v___x_5347_; 
v___x_5347_ = lean_unbox(v_a_5343_);
lean_dec(v_a_5343_);
if (v___x_5347_ == 0)
{
lean_object* v___x_5348_; 
lean_del_object(v___x_5345_);
lean_inc(v___y_5341_);
lean_inc_ref(v___y_5340_);
lean_inc(v___y_5339_);
lean_inc_ref(v___y_5338_);
v___x_5348_ = lean_whnf(v_inst_5127_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
if (lean_obj_tag(v___x_5348_) == 0)
{
lean_object* v_a_5349_; lean_object* v_dummy_5350_; lean_object* v_nargs_5351_; lean_object* v___x_5352_; lean_object* v___x_5353_; lean_object* v___x_5354_; lean_object* v___x_5355_; 
v_a_5349_ = lean_ctor_get(v___x_5348_, 0);
lean_inc_n(v_a_5349_, 2);
lean_dec_ref(v___x_5348_);
v_dummy_5350_ = lean_obj_once(&l_Lean_Meta_abstractInstImplicitArgs___closed__0, &l_Lean_Meta_abstractInstImplicitArgs___closed__0_once, _init_l_Lean_Meta_abstractInstImplicitArgs___closed__0);
v_nargs_5351_ = l_Lean_Expr_getAppNumArgs(v_a_5349_);
lean_inc(v_nargs_5351_);
v___x_5352_ = lean_mk_array(v_nargs_5351_, v_dummy_5350_);
v___x_5353_ = lean_unsigned_to_nat(1u);
v___x_5354_ = lean_nat_sub(v_nargs_5351_, v___x_5353_);
lean_dec(v_nargs_5351_);
v___x_5355_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_5349_, v_expectedType_5128_, v___x_5336_, v_hasTrace_5171_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v_a_5349_, v___x_5352_, v___x_5354_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec_ref(v___y_5338_);
lean_dec(v___x_5354_);
return v___x_5355_;
}
else
{
lean_dec_ref(v___y_5338_);
lean_dec_ref(v_expectedType_5128_);
return v___x_5348_;
}
}
else
{
lean_object* v_options_5356_; lean_object* v___x_5357_; uint8_t v___x_5358_; 
v_options_5356_ = lean_ctor_get(v___y_5340_, 2);
v___x_5357_ = l_Lean_Meta_backward_inferInstanceAs_wrap_instances;
v___x_5358_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5356_, v___x_5357_);
if (v___x_5358_ == 0)
{
lean_object* v___x_5360_; 
lean_dec_ref(v___y_5338_);
lean_dec_ref(v_expectedType_5128_);
if (v_isShared_5346_ == 0)
{
lean_ctor_set(v___x_5345_, 0, v_inst_5127_);
v___x_5360_ = v___x_5345_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v_inst_5127_);
v___x_5360_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
return v___x_5360_;
}
}
else
{
lean_object* v___x_5362_; lean_object* v___x_5363_; 
lean_del_object(v___x_5345_);
v___x_5362_ = lean_box(0);
v___x_5363_ = l_Lean_Meta_mkAuxTheorem(v_expectedType_5128_, v_inst_5127_, v_hasTrace_5171_, v___x_5362_, v_hasTrace_5171_, v___y_5338_, v___y_5339_, v___y_5340_, v___y_5341_);
lean_dec_ref(v___y_5338_);
return v___x_5363_;
}
}
}
}
else
{
lean_object* v_a_5365_; lean_object* v___x_5367_; uint8_t v_isShared_5368_; uint8_t v_isSharedCheck_5372_; 
lean_dec_ref(v___y_5338_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5365_ = lean_ctor_get(v___x_5342_, 0);
v_isSharedCheck_5372_ = !lean_is_exclusive(v___x_5342_);
if (v_isSharedCheck_5372_ == 0)
{
v___x_5367_ = v___x_5342_;
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
else
{
lean_inc(v_a_5365_);
lean_dec(v___x_5342_);
v___x_5367_ = lean_box(0);
v_isShared_5368_ = v_isSharedCheck_5372_;
goto v_resetjp_5366_;
}
v_resetjp_5366_:
{
lean_object* v___x_5370_; 
if (v_isShared_5368_ == 0)
{
v___x_5370_ = v___x_5367_;
goto v_reusejp_5369_;
}
else
{
lean_object* v_reuseFailAlloc_5371_; 
v_reuseFailAlloc_5371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5371_, 0, v_a_5365_);
v___x_5370_ = v_reuseFailAlloc_5371_;
goto v_reusejp_5369_;
}
v_reusejp_5369_:
{
return v___x_5370_;
}
}
}
}
}
else
{
goto v___jp_5294_;
}
v___jp_5235_:
{
lean_object* v___x_5239_; double v___x_5240_; double v___x_5241_; lean_object* v___x_5242_; lean_object* v___x_5243_; lean_object* v___x_5244_; lean_object* v___x_5245_; lean_object* v___x_5246_; 
v___x_5239_ = lean_io_get_num_heartbeats();
v___x_5240_ = lean_float_of_nat(v___y_5236_);
v___x_5241_ = lean_float_of_nat(v___x_5239_);
v___x_5242_ = lean_box_float(v___x_5240_);
v___x_5243_ = lean_box_float(v___x_5241_);
v___x_5244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5244_, 0, v___x_5242_);
lean_ctor_set(v___x_5244_, 1, v___x_5243_);
v___x_5245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5245_, 0, v_a_5238_);
lean_ctor_set(v___x_5245_, 1, v___x_5244_);
v___x_5246_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_5231_, v_hasTrace_5171_, v___x_5232_, v_options_5138_, v___x_5234_, v___y_5237_, v___f_5230_, v___x_5245_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
lean_dec_ref(v___x_5182_);
return v___x_5246_;
}
v___jp_5247_:
{
lean_object* v___x_5251_; 
v___x_5251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5251_, 0, v_a_5250_);
v___y_5236_ = v___y_5248_;
v___y_5237_ = v___y_5249_;
v_a_5238_ = v___x_5251_;
goto v___jp_5235_;
}
v___jp_5252_:
{
lean_object* v___x_5256_; 
v___x_5256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5256_, 0, v_a_5255_);
v___y_5236_ = v___y_5253_;
v___y_5237_ = v___y_5254_;
v_a_5238_ = v___x_5256_;
goto v___jp_5235_;
}
v___jp_5257_:
{
if (lean_obj_tag(v___y_5260_) == 0)
{
lean_object* v_a_5261_; 
v_a_5261_ = lean_ctor_get(v___y_5260_, 0);
lean_inc(v_a_5261_);
lean_dec_ref(v___y_5260_);
v___y_5248_ = v___y_5258_;
v___y_5249_ = v___y_5259_;
v_a_5250_ = v_a_5261_;
goto v___jp_5247_;
}
else
{
lean_object* v_a_5262_; 
v_a_5262_ = lean_ctor_get(v___y_5260_, 0);
lean_inc(v_a_5262_);
lean_dec_ref(v___y_5260_);
v___y_5253_ = v___y_5258_;
v___y_5254_ = v___y_5259_;
v_a_5255_ = v_a_5262_;
goto v___jp_5252_;
}
}
v___jp_5263_:
{
lean_object* v___x_5267_; double v___x_5268_; double v___x_5269_; double v___x_5270_; double v___x_5271_; double v___x_5272_; lean_object* v___x_5273_; lean_object* v___x_5274_; lean_object* v___x_5275_; lean_object* v___x_5276_; lean_object* v___x_5277_; 
v___x_5267_ = lean_io_mono_nanos_now();
v___x_5268_ = lean_float_of_nat(v___y_5264_);
v___x_5269_ = lean_float_once(&l_Lean_Meta_wrapInstance___closed__1, &l_Lean_Meta_wrapInstance___closed__1_once, _init_l_Lean_Meta_wrapInstance___closed__1);
v___x_5270_ = lean_float_div(v___x_5268_, v___x_5269_);
v___x_5271_ = lean_float_of_nat(v___x_5267_);
v___x_5272_ = lean_float_div(v___x_5271_, v___x_5269_);
v___x_5273_ = lean_box_float(v___x_5270_);
v___x_5274_ = lean_box_float(v___x_5272_);
v___x_5275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5273_);
lean_ctor_set(v___x_5275_, 1, v___x_5274_);
v___x_5276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5276_, 0, v_a_5266_);
lean_ctor_set(v___x_5276_, 1, v___x_5275_);
v___x_5277_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15(v_cls_5231_, v_hasTrace_5171_, v___x_5232_, v_options_5138_, v___x_5234_, v___y_5265_, v___f_5230_, v___x_5276_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
lean_dec_ref(v___x_5182_);
return v___x_5277_;
}
v___jp_5278_:
{
lean_object* v___x_5282_; 
v___x_5282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5282_, 0, v_a_5281_);
v___y_5264_ = v___y_5279_;
v___y_5265_ = v___y_5280_;
v_a_5266_ = v___x_5282_;
goto v___jp_5263_;
}
v___jp_5283_:
{
lean_object* v___x_5287_; 
v___x_5287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5287_, 0, v_a_5286_);
v___y_5264_ = v___y_5284_;
v___y_5265_ = v___y_5285_;
v_a_5266_ = v___x_5287_;
goto v___jp_5263_;
}
v___jp_5288_:
{
if (lean_obj_tag(v___y_5291_) == 0)
{
lean_object* v_a_5292_; 
v_a_5292_ = lean_ctor_get(v___y_5291_, 0);
lean_inc(v_a_5292_);
lean_dec_ref(v___y_5291_);
v___y_5279_ = v___y_5289_;
v___y_5280_ = v___y_5290_;
v_a_5281_ = v_a_5292_;
goto v___jp_5278_;
}
else
{
lean_object* v_a_5293_; 
v_a_5293_ = lean_ctor_get(v___y_5291_, 0);
lean_inc(v_a_5293_);
lean_dec_ref(v___y_5291_);
v___y_5284_ = v___y_5289_;
v___y_5285_ = v___y_5290_;
v_a_5286_ = v_a_5293_;
goto v___jp_5283_;
}
}
v___jp_5294_:
{
lean_object* v___x_5295_; 
v___x_5295_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_wrapInstance_spec__10___redArg(v_a_5135_);
if (lean_obj_tag(v___x_5295_) == 0)
{
lean_object* v_a_5296_; lean_object* v___x_5297_; uint8_t v___x_5298_; 
v_a_5296_ = lean_ctor_get(v___x_5295_, 0);
lean_inc(v_a_5296_);
lean_dec_ref(v___x_5295_);
v___x_5297_ = l_Lean_trace_profiler_useHeartbeats;
v___x_5298_ = l_Lean_Option_get___at___00Lean_Meta_wrapInstance_spec__0(v_options_5138_, v___x_5297_);
if (v___x_5298_ == 0)
{
lean_object* v___x_5299_; lean_object* v___x_5300_; 
v___x_5299_ = lean_io_mono_nanos_now();
lean_inc_ref(v_expectedType_5128_);
v___x_5300_ = l_Lean_Meta_isClass_x3f(v_expectedType_5128_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5300_) == 0)
{
lean_object* v_a_5301_; 
v_a_5301_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5301_);
lean_dec_ref(v___x_5300_);
if (lean_obj_tag(v_a_5301_) == 1)
{
if (v___x_5234_ == 0)
{
lean_object* v___x_5302_; lean_object* v___x_5303_; 
lean_dec_ref(v_a_5301_);
v___x_5302_ = lean_box(0);
v___x_5303_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5128_, v_inst_5127_, v___x_5298_, v_hasTrace_5171_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v___x_5302_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
v___y_5289_ = v___x_5299_;
v___y_5290_ = v_a_5296_;
v___y_5291_ = v___x_5303_;
goto v___jp_5288_;
}
else
{
lean_object* v_val_5304_; lean_object* v___x_5305_; lean_object* v___x_5306_; lean_object* v___x_5307_; lean_object* v___x_5308_; 
v_val_5304_ = lean_ctor_get(v_a_5301_, 0);
lean_inc(v_val_5304_);
lean_dec_ref(v_a_5301_);
v___x_5305_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5306_ = l_Lean_MessageData_ofName(v_val_5304_);
v___x_5307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5307_, 0, v___x_5305_);
lean_ctor_set(v___x_5307_, 1, v___x_5306_);
v___x_5308_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5231_, v___x_5307_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5308_) == 0)
{
lean_object* v_a_5309_; lean_object* v___x_5310_; 
v_a_5309_ = lean_ctor_get(v___x_5308_, 0);
lean_inc(v_a_5309_);
lean_dec_ref(v___x_5308_);
v___x_5310_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5128_, v_inst_5127_, v___x_5298_, v_hasTrace_5171_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v_a_5309_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
v___y_5289_ = v___x_5299_;
v___y_5290_ = v_a_5296_;
v___y_5291_ = v___x_5310_;
goto v___jp_5288_;
}
else
{
lean_object* v_a_5311_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5311_ = lean_ctor_get(v___x_5308_, 0);
lean_inc(v_a_5311_);
lean_dec_ref(v___x_5308_);
v___y_5284_ = v___x_5299_;
v___y_5285_ = v_a_5296_;
v_a_5286_ = v_a_5311_;
goto v___jp_5283_;
}
}
}
else
{
lean_dec(v_a_5301_);
lean_dec_ref(v_expectedType_5128_);
v___y_5279_ = v___x_5299_;
v___y_5280_ = v_a_5296_;
v_a_5281_ = v_inst_5127_;
goto v___jp_5278_;
}
}
else
{
lean_object* v_a_5312_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5312_ = lean_ctor_get(v___x_5300_, 0);
lean_inc(v_a_5312_);
lean_dec_ref(v___x_5300_);
v___y_5284_ = v___x_5299_;
v___y_5285_ = v_a_5296_;
v_a_5286_ = v_a_5312_;
goto v___jp_5283_;
}
}
else
{
lean_object* v___x_5313_; lean_object* v___x_5314_; 
v___x_5313_ = lean_io_get_num_heartbeats();
lean_inc_ref(v_expectedType_5128_);
v___x_5314_ = l_Lean_Meta_isClass_x3f(v_expectedType_5128_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5314_) == 0)
{
lean_object* v_a_5315_; 
v_a_5315_ = lean_ctor_get(v___x_5314_, 0);
lean_inc(v_a_5315_);
lean_dec_ref(v___x_5314_);
if (lean_obj_tag(v_a_5315_) == 1)
{
if (v___x_5234_ == 0)
{
lean_object* v___x_5316_; lean_object* v___x_5317_; 
lean_dec_ref(v_a_5315_);
v___x_5316_ = lean_box(0);
v___x_5317_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5128_, v_inst_5127_, v___x_5298_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v___x_5316_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
v___y_5258_ = v___x_5313_;
v___y_5259_ = v_a_5296_;
v___y_5260_ = v___x_5317_;
goto v___jp_5257_;
}
else
{
lean_object* v_val_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5322_; 
v_val_5318_ = lean_ctor_get(v_a_5315_, 0);
lean_inc(v_val_5318_);
lean_dec_ref(v_a_5315_);
v___x_5319_ = lean_obj_once(&l_Lean_Meta_wrapInstance___closed__3, &l_Lean_Meta_wrapInstance___closed__3_once, _init_l_Lean_Meta_wrapInstance___closed__3);
v___x_5320_ = l_Lean_MessageData_ofName(v_val_5318_);
v___x_5321_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5319_);
lean_ctor_set(v___x_5321_, 1, v___x_5320_);
v___x_5322_ = l_Lean_addTrace___at___00Lean_Meta_wrapInstance_spec__3(v_cls_5231_, v___x_5321_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
if (lean_obj_tag(v___x_5322_) == 0)
{
lean_object* v_a_5323_; lean_object* v___x_5324_; 
v_a_5323_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5323_);
lean_dec_ref(v___x_5322_);
v___x_5324_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5128_, v_inst_5127_, v___x_5298_, v_compile_5129_, v_logCompileErrors_5130_, v_isMeta_5131_, v_a_5323_, v___x_5182_, v_a_5133_, v_a_5134_, v_a_5135_);
v___y_5258_ = v___x_5313_;
v___y_5259_ = v_a_5296_;
v___y_5260_ = v___x_5324_;
goto v___jp_5257_;
}
else
{
lean_object* v_a_5325_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5325_ = lean_ctor_get(v___x_5322_, 0);
lean_inc(v_a_5325_);
lean_dec_ref(v___x_5322_);
v___y_5253_ = v___x_5313_;
v___y_5254_ = v_a_5296_;
v_a_5255_ = v_a_5325_;
goto v___jp_5252_;
}
}
}
else
{
lean_dec(v_a_5315_);
lean_dec_ref(v_expectedType_5128_);
v___y_5248_ = v___x_5313_;
v___y_5249_ = v_a_5296_;
v_a_5250_ = v_inst_5127_;
goto v___jp_5247_;
}
}
else
{
lean_object* v_a_5326_; 
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5326_ = lean_ctor_get(v___x_5314_, 0);
lean_inc(v_a_5326_);
lean_dec_ref(v___x_5314_);
v___y_5253_ = v___x_5313_;
v___y_5254_ = v_a_5296_;
v_a_5255_ = v_a_5326_;
goto v___jp_5252_;
}
}
}
else
{
lean_object* v_a_5327_; lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5334_; 
lean_dec_ref(v___f_5230_);
lean_dec_ref(v___x_5182_);
lean_dec_ref(v_expectedType_5128_);
lean_dec_ref(v_inst_5127_);
v_a_5327_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5329_ = v___x_5295_;
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
else
{
lean_inc(v_a_5327_);
lean_dec(v___x_5295_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5334_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v___x_5332_; 
if (v_isShared_5330_ == 0)
{
v___x_5332_ = v___x_5329_;
goto v_reusejp_5331_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_a_5327_);
v___x_5332_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5331_;
}
v_reusejp_5331_:
{
return v___x_5332_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(lean_object* v___x_5405_, lean_object* v_a_5406_, uint8_t v_compile_5407_, uint8_t v_logCompileErrors_5408_, uint8_t v_isMeta_5409_, lean_object* v___x_5410_, lean_object* v___x_5411_, lean_object* v_____r_5412_, lean_object* v___y_5413_, lean_object* v___y_5414_, lean_object* v___y_5415_, lean_object* v___y_5416_){
_start:
{
lean_object* v___x_5418_; 
v___x_5418_ = l_Lean_Meta_wrapInstance(v___x_5405_, v_a_5406_, v_compile_5407_, v_logCompileErrors_5408_, v_isMeta_5409_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
if (lean_obj_tag(v___x_5418_) == 0)
{
lean_object* v_a_5419_; lean_object* v___x_5420_; 
v_a_5419_ = lean_ctor_get(v___x_5418_, 0);
lean_inc(v_a_5419_);
lean_dec_ref(v___x_5418_);
v___x_5420_ = l_Lean_MVarId_assign___at___00Lean_Meta_abstractInstImplicitArgs_spec__0___redArg(v___x_5410_, v_a_5419_, v___y_5414_);
if (lean_obj_tag(v___x_5420_) == 0)
{
lean_object* v___x_5422_; uint8_t v_isShared_5423_; uint8_t v_isSharedCheck_5428_; 
v_isSharedCheck_5428_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5428_ == 0)
{
lean_object* v_unused_5429_; 
v_unused_5429_ = lean_ctor_get(v___x_5420_, 0);
lean_dec(v_unused_5429_);
v___x_5422_ = v___x_5420_;
v_isShared_5423_ = v_isSharedCheck_5428_;
goto v_resetjp_5421_;
}
else
{
lean_dec(v___x_5420_);
v___x_5422_ = lean_box(0);
v_isShared_5423_ = v_isSharedCheck_5428_;
goto v_resetjp_5421_;
}
v_resetjp_5421_:
{
lean_object* v___x_5424_; lean_object* v___x_5426_; 
v___x_5424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5424_, 0, v___x_5411_);
if (v_isShared_5423_ == 0)
{
lean_ctor_set(v___x_5422_, 0, v___x_5424_);
v___x_5426_ = v___x_5422_;
goto v_reusejp_5425_;
}
else
{
lean_object* v_reuseFailAlloc_5427_; 
v_reuseFailAlloc_5427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5427_, 0, v___x_5424_);
v___x_5426_ = v_reuseFailAlloc_5427_;
goto v_reusejp_5425_;
}
v_reusejp_5425_:
{
return v___x_5426_;
}
}
}
else
{
lean_object* v_a_5430_; lean_object* v___x_5432_; uint8_t v_isShared_5433_; uint8_t v_isSharedCheck_5437_; 
v_a_5430_ = lean_ctor_get(v___x_5420_, 0);
v_isSharedCheck_5437_ = !lean_is_exclusive(v___x_5420_);
if (v_isSharedCheck_5437_ == 0)
{
v___x_5432_ = v___x_5420_;
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
else
{
lean_inc(v_a_5430_);
lean_dec(v___x_5420_);
v___x_5432_ = lean_box(0);
v_isShared_5433_ = v_isSharedCheck_5437_;
goto v_resetjp_5431_;
}
v_resetjp_5431_:
{
lean_object* v___x_5435_; 
if (v_isShared_5433_ == 0)
{
v___x_5435_ = v___x_5432_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v_a_5430_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
else
{
lean_object* v_a_5438_; lean_object* v___x_5440_; uint8_t v_isShared_5441_; uint8_t v_isSharedCheck_5445_; 
lean_dec(v___x_5410_);
v_a_5438_ = lean_ctor_get(v___x_5418_, 0);
v_isSharedCheck_5445_ = !lean_is_exclusive(v___x_5418_);
if (v_isSharedCheck_5445_ == 0)
{
v___x_5440_ = v___x_5418_;
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
else
{
lean_inc(v_a_5438_);
lean_dec(v___x_5418_);
v___x_5440_ = lean_box(0);
v_isShared_5441_ = v_isSharedCheck_5445_;
goto v_resetjp_5439_;
}
v_resetjp_5439_:
{
lean_object* v___x_5443_; 
if (v_isShared_5441_ == 0)
{
v___x_5443_ = v___x_5440_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v_a_5438_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1___boxed(lean_object* v___x_5446_, lean_object* v_a_5447_, lean_object* v_compile_5448_, lean_object* v_logCompileErrors_5449_, lean_object* v_isMeta_5450_, lean_object* v___x_5451_, lean_object* v___x_5452_, lean_object* v_____r_5453_, lean_object* v___y_5454_, lean_object* v___y_5455_, lean_object* v___y_5456_, lean_object* v___y_5457_, lean_object* v___y_5458_){
_start:
{
uint8_t v_compile_boxed_5459_; uint8_t v_logCompileErrors_boxed_5460_; uint8_t v_isMeta_boxed_5461_; lean_object* v_res_5462_; 
v_compile_boxed_5459_ = lean_unbox(v_compile_5448_);
v_logCompileErrors_boxed_5460_ = lean_unbox(v_logCompileErrors_5449_);
v_isMeta_boxed_5461_ = lean_unbox(v_isMeta_5450_);
v_res_5462_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___lam__1(v___x_5446_, v_a_5447_, v_compile_boxed_5459_, v_logCompileErrors_boxed_5460_, v_isMeta_boxed_5461_, v___x_5451_, v___x_5452_, v_____r_5453_, v___y_5454_, v___y_5455_, v___y_5456_, v___y_5457_);
lean_dec(v___y_5457_);
lean_dec_ref(v___y_5456_);
lean_dec(v___y_5455_);
lean_dec_ref(v___y_5454_);
return v_res_5462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__1___boxed(lean_object* v_expectedType_5463_, lean_object* v_inst_5464_, lean_object* v___x_5465_, lean_object* v_hasTrace_5466_, lean_object* v_compile_5467_, lean_object* v_logCompileErrors_5468_, lean_object* v_isMeta_5469_, lean_object* v_____r_5470_, lean_object* v___y_5471_, lean_object* v___y_5472_, lean_object* v___y_5473_, lean_object* v___y_5474_, lean_object* v___y_5475_){
_start:
{
uint8_t v___x_122036__boxed_5476_; uint8_t v_hasTrace_boxed_5477_; uint8_t v_compile_boxed_5478_; uint8_t v_logCompileErrors_boxed_5479_; uint8_t v_isMeta_boxed_5480_; lean_object* v_res_5481_; 
v___x_122036__boxed_5476_ = lean_unbox(v___x_5465_);
v_hasTrace_boxed_5477_ = lean_unbox(v_hasTrace_5466_);
v_compile_boxed_5478_ = lean_unbox(v_compile_5467_);
v_logCompileErrors_boxed_5479_ = lean_unbox(v_logCompileErrors_5468_);
v_isMeta_boxed_5480_ = lean_unbox(v_isMeta_5469_);
v_res_5481_ = l_Lean_Meta_wrapInstance___lam__1(v_expectedType_5463_, v_inst_5464_, v___x_122036__boxed_5476_, v_hasTrace_boxed_5477_, v_compile_boxed_5478_, v_logCompileErrors_boxed_5479_, v_isMeta_boxed_5480_, v_____r_5470_, v___y_5471_, v___y_5472_, v___y_5473_, v___y_5474_);
lean_dec(v___y_5474_);
lean_dec_ref(v___y_5473_);
lean_dec(v___y_5472_);
lean_dec_ref(v___y_5471_);
return v_res_5481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___lam__2___boxed(lean_object* v_expectedType_5482_, lean_object* v_inst_5483_, lean_object* v___x_5484_, lean_object* v_compile_5485_, lean_object* v_logCompileErrors_5486_, lean_object* v_isMeta_5487_, lean_object* v_____r_5488_, lean_object* v___y_5489_, lean_object* v___y_5490_, lean_object* v___y_5491_, lean_object* v___y_5492_, lean_object* v___y_5493_){
_start:
{
uint8_t v___x_122060__boxed_5494_; uint8_t v_compile_boxed_5495_; uint8_t v_logCompileErrors_boxed_5496_; uint8_t v_isMeta_boxed_5497_; lean_object* v_res_5498_; 
v___x_122060__boxed_5494_ = lean_unbox(v___x_5484_);
v_compile_boxed_5495_ = lean_unbox(v_compile_5485_);
v_logCompileErrors_boxed_5496_ = lean_unbox(v_logCompileErrors_5486_);
v_isMeta_boxed_5497_ = lean_unbox(v_isMeta_5487_);
v_res_5498_ = l_Lean_Meta_wrapInstance___lam__2(v_expectedType_5482_, v_inst_5483_, v___x_122060__boxed_5494_, v_compile_boxed_5495_, v_logCompileErrors_boxed_5496_, v_isMeta_boxed_5497_, v_____r_5488_, v___y_5489_, v___y_5490_, v___y_5491_, v___y_5492_);
lean_dec(v___y_5492_);
lean_dec_ref(v___y_5491_);
lean_dec(v___y_5490_);
lean_dec_ref(v___y_5489_);
return v_res_5498_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17___boxed(lean_object* v_a_5499_, lean_object* v_expectedType_5500_, lean_object* v___x_5501_, lean_object* v___x_5502_, lean_object* v_compile_5503_, lean_object* v_logCompileErrors_5504_, lean_object* v_isMeta_5505_, lean_object* v_x_5506_, lean_object* v_x_5507_, lean_object* v_x_5508_, lean_object* v___y_5509_, lean_object* v___y_5510_, lean_object* v___y_5511_, lean_object* v___y_5512_, lean_object* v___y_5513_){
_start:
{
uint8_t v___x_122109__boxed_5514_; uint8_t v___x_122110__boxed_5515_; uint8_t v_compile_boxed_5516_; uint8_t v_logCompileErrors_boxed_5517_; uint8_t v_isMeta_boxed_5518_; lean_object* v_res_5519_; 
v___x_122109__boxed_5514_ = lean_unbox(v___x_5501_);
v___x_122110__boxed_5515_ = lean_unbox(v___x_5502_);
v_compile_boxed_5516_ = lean_unbox(v_compile_5503_);
v_logCompileErrors_boxed_5517_ = lean_unbox(v_logCompileErrors_5504_);
v_isMeta_boxed_5518_ = lean_unbox(v_isMeta_5505_);
v_res_5519_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12_spec__17(v_a_5499_, v_expectedType_5500_, v___x_122109__boxed_5514_, v___x_122110__boxed_5515_, v_compile_boxed_5516_, v_logCompileErrors_boxed_5517_, v_isMeta_boxed_5518_, v_x_5506_, v_x_5507_, v_x_5508_, v___y_5509_, v___y_5510_, v___y_5511_, v___y_5512_);
lean_dec(v___y_5512_);
lean_dec_ref(v___y_5511_);
lean_dec(v___y_5510_);
lean_dec_ref(v___y_5509_);
return v_res_5519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21___boxed(lean_object* v_a_5520_, lean_object* v_expectedType_5521_, lean_object* v___x_5522_, lean_object* v_compile_5523_, lean_object* v_logCompileErrors_5524_, lean_object* v_isMeta_5525_, lean_object* v_x_5526_, lean_object* v_x_5527_, lean_object* v_x_5528_, lean_object* v___y_5529_, lean_object* v___y_5530_, lean_object* v___y_5531_, lean_object* v___y_5532_, lean_object* v___y_5533_){
_start:
{
uint8_t v___x_122265__boxed_5534_; uint8_t v_compile_boxed_5535_; uint8_t v_logCompileErrors_boxed_5536_; uint8_t v_isMeta_boxed_5537_; lean_object* v_res_5538_; 
v___x_122265__boxed_5534_ = lean_unbox(v___x_5522_);
v_compile_boxed_5535_ = lean_unbox(v_compile_5523_);
v_logCompileErrors_boxed_5536_ = lean_unbox(v_logCompileErrors_5524_);
v_isMeta_boxed_5537_ = lean_unbox(v_isMeta_5525_);
v_res_5538_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14_spec__21(v_a_5520_, v_expectedType_5521_, v___x_122265__boxed_5534_, v_compile_boxed_5535_, v_logCompileErrors_boxed_5536_, v_isMeta_boxed_5537_, v_x_5526_, v_x_5527_, v_x_5528_, v___y_5529_, v___y_5530_, v___y_5531_, v___y_5532_);
lean_dec(v___y_5532_);
lean_dec_ref(v___y_5531_);
lean_dec(v___y_5530_);
lean_dec_ref(v___y_5529_);
return v_res_5538_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12___boxed(lean_object* v_a_5539_, lean_object* v_expectedType_5540_, lean_object* v___x_5541_, lean_object* v___x_5542_, lean_object* v_compile_5543_, lean_object* v_logCompileErrors_5544_, lean_object* v_isMeta_5545_, lean_object* v_x_5546_, lean_object* v_x_5547_, lean_object* v_x_5548_, lean_object* v___y_5549_, lean_object* v___y_5550_, lean_object* v___y_5551_, lean_object* v___y_5552_, lean_object* v___y_5553_){
_start:
{
uint8_t v___x_122433__boxed_5554_; uint8_t v___x_122434__boxed_5555_; uint8_t v_compile_boxed_5556_; uint8_t v_logCompileErrors_boxed_5557_; uint8_t v_isMeta_boxed_5558_; lean_object* v_res_5559_; 
v___x_122433__boxed_5554_ = lean_unbox(v___x_5541_);
v___x_122434__boxed_5555_ = lean_unbox(v___x_5542_);
v_compile_boxed_5556_ = lean_unbox(v_compile_5543_);
v_logCompileErrors_boxed_5557_ = lean_unbox(v_logCompileErrors_5544_);
v_isMeta_boxed_5558_ = lean_unbox(v_isMeta_5545_);
v_res_5559_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__12(v_a_5539_, v_expectedType_5540_, v___x_122433__boxed_5554_, v___x_122434__boxed_5555_, v_compile_boxed_5556_, v_logCompileErrors_boxed_5557_, v_isMeta_boxed_5558_, v_x_5546_, v_x_5547_, v_x_5548_, v___y_5549_, v___y_5550_, v___y_5551_, v___y_5552_);
lean_dec(v___y_5552_);
lean_dec_ref(v___y_5551_);
lean_dec(v___y_5550_);
lean_dec_ref(v___y_5549_);
lean_dec(v_x_5548_);
return v_res_5559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14___boxed(lean_object* v_a_5560_, lean_object* v_expectedType_5561_, lean_object* v___x_5562_, lean_object* v_compile_5563_, lean_object* v_logCompileErrors_5564_, lean_object* v_isMeta_5565_, lean_object* v_x_5566_, lean_object* v_x_5567_, lean_object* v_x_5568_, lean_object* v___y_5569_, lean_object* v___y_5570_, lean_object* v___y_5571_, lean_object* v___y_5572_, lean_object* v___y_5573_){
_start:
{
uint8_t v___x_122602__boxed_5574_; uint8_t v_compile_boxed_5575_; uint8_t v_logCompileErrors_boxed_5576_; uint8_t v_isMeta_boxed_5577_; lean_object* v_res_5578_; 
v___x_122602__boxed_5574_ = lean_unbox(v___x_5562_);
v_compile_boxed_5575_ = lean_unbox(v_compile_5563_);
v_logCompileErrors_boxed_5576_ = lean_unbox(v_logCompileErrors_5564_);
v_isMeta_boxed_5577_ = lean_unbox(v_isMeta_5565_);
v_res_5578_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__14(v_a_5560_, v_expectedType_5561_, v___x_122602__boxed_5574_, v_compile_boxed_5575_, v_logCompileErrors_boxed_5576_, v_isMeta_boxed_5577_, v_x_5566_, v_x_5567_, v_x_5568_, v___y_5569_, v___y_5570_, v___y_5571_, v___y_5572_);
lean_dec(v___y_5572_);
lean_dec_ref(v___y_5571_);
lean_dec(v___y_5570_);
lean_dec_ref(v___y_5569_);
lean_dec(v_x_5568_);
return v_res_5578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12___boxed(lean_object* v_a_5579_, lean_object* v_expectedType_5580_, lean_object* v___x_5581_, lean_object* v_compile_5582_, lean_object* v_logCompileErrors_5583_, lean_object* v_isMeta_5584_, lean_object* v_x_5585_, lean_object* v_x_5586_, lean_object* v_x_5587_, lean_object* v___y_5588_, lean_object* v___y_5589_, lean_object* v___y_5590_, lean_object* v___y_5591_, lean_object* v___y_5592_){
_start:
{
uint8_t v___x_122770__boxed_5593_; uint8_t v_compile_boxed_5594_; uint8_t v_logCompileErrors_boxed_5595_; uint8_t v_isMeta_boxed_5596_; lean_object* v_res_5597_; 
v___x_122770__boxed_5593_ = lean_unbox(v___x_5581_);
v_compile_boxed_5594_ = lean_unbox(v_compile_5582_);
v_logCompileErrors_boxed_5595_ = lean_unbox(v_logCompileErrors_5583_);
v_isMeta_boxed_5596_ = lean_unbox(v_isMeta_5584_);
v_res_5597_ = l_Lean_Expr_withAppAux___at___00Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9_spec__12(v_a_5579_, v_expectedType_5580_, v___x_122770__boxed_5593_, v_compile_boxed_5594_, v_logCompileErrors_boxed_5595_, v_isMeta_boxed_5596_, v_x_5585_, v_x_5586_, v_x_5587_, v___y_5588_, v___y_5589_, v___y_5590_, v___y_5591_);
lean_dec(v___y_5591_);
lean_dec_ref(v___y_5590_);
lean_dec(v___y_5589_);
lean_dec_ref(v___y_5588_);
return v_res_5597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9___boxed(lean_object* v_a_5598_, lean_object* v_expectedType_5599_, lean_object* v___x_5600_, lean_object* v_compile_5601_, lean_object* v_logCompileErrors_5602_, lean_object* v_isMeta_5603_, lean_object* v_x_5604_, lean_object* v_x_5605_, lean_object* v_x_5606_, lean_object* v___y_5607_, lean_object* v___y_5608_, lean_object* v___y_5609_, lean_object* v___y_5610_, lean_object* v___y_5611_){
_start:
{
uint8_t v___x_122939__boxed_5612_; uint8_t v_compile_boxed_5613_; uint8_t v_logCompileErrors_boxed_5614_; uint8_t v_isMeta_boxed_5615_; lean_object* v_res_5616_; 
v___x_122939__boxed_5612_ = lean_unbox(v___x_5600_);
v_compile_boxed_5613_ = lean_unbox(v_compile_5601_);
v_logCompileErrors_boxed_5614_ = lean_unbox(v_logCompileErrors_5602_);
v_isMeta_boxed_5615_ = lean_unbox(v_isMeta_5603_);
v_res_5616_ = l_Lean_Expr_withAppAux___at___00Lean_Meta_wrapInstance_spec__9(v_a_5598_, v_expectedType_5599_, v___x_122939__boxed_5612_, v_compile_boxed_5613_, v_logCompileErrors_boxed_5614_, v_isMeta_boxed_5615_, v_x_5604_, v_x_5605_, v_x_5606_, v___y_5607_, v___y_5608_, v___y_5609_, v___y_5610_);
lean_dec(v___y_5610_);
lean_dec_ref(v___y_5609_);
lean_dec(v___y_5608_);
lean_dec_ref(v___y_5607_);
lean_dec(v_x_5606_);
return v_res_5616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_wrapInstance___boxed(lean_object* v_inst_5617_, lean_object* v_expectedType_5618_, lean_object* v_compile_5619_, lean_object* v_logCompileErrors_5620_, lean_object* v_isMeta_5621_, lean_object* v_a_5622_, lean_object* v_a_5623_, lean_object* v_a_5624_, lean_object* v_a_5625_, lean_object* v_a_5626_){
_start:
{
uint8_t v_compile_boxed_5627_; uint8_t v_logCompileErrors_boxed_5628_; uint8_t v_isMeta_boxed_5629_; lean_object* v_res_5630_; 
v_compile_boxed_5627_ = lean_unbox(v_compile_5619_);
v_logCompileErrors_boxed_5628_ = lean_unbox(v_logCompileErrors_5620_);
v_isMeta_boxed_5629_ = lean_unbox(v_isMeta_5621_);
v_res_5630_ = l_Lean_Meta_wrapInstance(v_inst_5617_, v_expectedType_5618_, v_compile_boxed_5627_, v_logCompileErrors_boxed_5628_, v_isMeta_boxed_5629_, v_a_5622_, v_a_5623_, v_a_5624_, v_a_5625_);
lean_dec(v_a_5625_);
lean_dec_ref(v_a_5624_);
lean_dec(v_a_5623_);
lean_dec_ref(v_a_5622_);
return v_res_5630_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg___boxed(lean_object* v_upperBound_5631_, lean_object* v_fst_5632_, lean_object* v_args_5633_, lean_object* v_compile_5634_, lean_object* v_logCompileErrors_5635_, lean_object* v_isMeta_5636_, lean_object* v___x_5637_, lean_object* v_a_5638_, lean_object* v_b_5639_, lean_object* v___y_5640_, lean_object* v___y_5641_, lean_object* v___y_5642_, lean_object* v___y_5643_, lean_object* v___y_5644_){
_start:
{
uint8_t v_compile_boxed_5645_; uint8_t v_logCompileErrors_boxed_5646_; uint8_t v_isMeta_boxed_5647_; uint8_t v___x_123294__boxed_5648_; lean_object* v_res_5649_; 
v_compile_boxed_5645_ = lean_unbox(v_compile_5634_);
v_logCompileErrors_boxed_5646_ = lean_unbox(v_logCompileErrors_5635_);
v_isMeta_boxed_5647_ = lean_unbox(v_isMeta_5636_);
v___x_123294__boxed_5648_ = lean_unbox(v___x_5637_);
v_res_5649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_5631_, v_fst_5632_, v_args_5633_, v_compile_boxed_5645_, v_logCompileErrors_boxed_5646_, v_isMeta_boxed_5647_, v___x_123294__boxed_5648_, v_a_5638_, v_b_5639_, v___y_5640_, v___y_5641_, v___y_5642_, v___y_5643_);
lean_dec(v___y_5643_);
lean_dec_ref(v___y_5642_);
lean_dec(v___y_5641_);
lean_dec_ref(v___y_5640_);
lean_dec_ref(v_args_5633_);
lean_dec_ref(v_fst_5632_);
lean_dec(v_upperBound_5631_);
return v_res_5649_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg___boxed(lean_object* v_upperBound_5650_, lean_object* v_fst_5651_, lean_object* v_args_5652_, lean_object* v_compile_5653_, lean_object* v_logCompileErrors_5654_, lean_object* v_isMeta_5655_, lean_object* v___x_5656_, lean_object* v_a_5657_, lean_object* v_b_5658_, lean_object* v___y_5659_, lean_object* v___y_5660_, lean_object* v___y_5661_, lean_object* v___y_5662_, lean_object* v___y_5663_){
_start:
{
uint8_t v_compile_boxed_5664_; uint8_t v_logCompileErrors_boxed_5665_; uint8_t v_isMeta_boxed_5666_; uint8_t v___x_123449__boxed_5667_; lean_object* v_res_5668_; 
v_compile_boxed_5664_ = lean_unbox(v_compile_5653_);
v_logCompileErrors_boxed_5665_ = lean_unbox(v_logCompileErrors_5654_);
v_isMeta_boxed_5666_ = lean_unbox(v_isMeta_5655_);
v___x_123449__boxed_5667_ = lean_unbox(v___x_5656_);
v_res_5668_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_5650_, v_fst_5651_, v_args_5652_, v_compile_boxed_5664_, v_logCompileErrors_boxed_5665_, v_isMeta_boxed_5666_, v___x_123449__boxed_5667_, v_a_5657_, v_b_5658_, v___y_5659_, v___y_5660_, v___y_5661_, v___y_5662_);
lean_dec(v___y_5662_);
lean_dec_ref(v___y_5661_);
lean_dec(v___y_5660_);
lean_dec_ref(v___y_5659_);
lean_dec_ref(v_args_5652_);
lean_dec_ref(v_fst_5651_);
lean_dec(v_upperBound_5650_);
return v_res_5668_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg___boxed(lean_object* v_upperBound_5669_, lean_object* v_fst_5670_, lean_object* v_args_5671_, lean_object* v___x_5672_, lean_object* v_compile_5673_, lean_object* v_logCompileErrors_5674_, lean_object* v_isMeta_5675_, lean_object* v_a_5676_, lean_object* v_b_5677_, lean_object* v___y_5678_, lean_object* v___y_5679_, lean_object* v___y_5680_, lean_object* v___y_5681_, lean_object* v___y_5682_){
_start:
{
uint8_t v___x_123618__boxed_5683_; uint8_t v_compile_boxed_5684_; uint8_t v_logCompileErrors_boxed_5685_; uint8_t v_isMeta_boxed_5686_; lean_object* v_res_5687_; 
v___x_123618__boxed_5683_ = lean_unbox(v___x_5672_);
v_compile_boxed_5684_ = lean_unbox(v_compile_5673_);
v_logCompileErrors_boxed_5685_ = lean_unbox(v_logCompileErrors_5674_);
v_isMeta_boxed_5686_ = lean_unbox(v_isMeta_5675_);
v_res_5687_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_5669_, v_fst_5670_, v_args_5671_, v___x_123618__boxed_5683_, v_compile_boxed_5684_, v_logCompileErrors_boxed_5685_, v_isMeta_boxed_5686_, v_a_5676_, v_b_5677_, v___y_5678_, v___y_5679_, v___y_5680_, v___y_5681_);
lean_dec(v___y_5681_);
lean_dec_ref(v___y_5680_);
lean_dec(v___y_5679_);
lean_dec_ref(v___y_5678_);
lean_dec_ref(v_args_5671_);
lean_dec_ref(v_fst_5670_);
lean_dec(v_upperBound_5669_);
return v_res_5687_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg___boxed(lean_object* v_upperBound_5688_, lean_object* v_fst_5689_, lean_object* v_args_5690_, lean_object* v___x_5691_, lean_object* v_compile_5692_, lean_object* v_logCompileErrors_5693_, lean_object* v_isMeta_5694_, lean_object* v_a_5695_, lean_object* v_b_5696_, lean_object* v___y_5697_, lean_object* v___y_5698_, lean_object* v___y_5699_, lean_object* v___y_5700_, lean_object* v___y_5701_){
_start:
{
uint8_t v___x_123788__boxed_5702_; uint8_t v_compile_boxed_5703_; uint8_t v_logCompileErrors_boxed_5704_; uint8_t v_isMeta_boxed_5705_; lean_object* v_res_5706_; 
v___x_123788__boxed_5702_ = lean_unbox(v___x_5691_);
v_compile_boxed_5703_ = lean_unbox(v_compile_5692_);
v_logCompileErrors_boxed_5704_ = lean_unbox(v_logCompileErrors_5693_);
v_isMeta_boxed_5705_ = lean_unbox(v_isMeta_5694_);
v_res_5706_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_5688_, v_fst_5689_, v_args_5690_, v___x_123788__boxed_5702_, v_compile_boxed_5703_, v_logCompileErrors_boxed_5704_, v_isMeta_boxed_5705_, v_a_5695_, v_b_5696_, v___y_5697_, v___y_5698_, v___y_5699_, v___y_5700_);
lean_dec(v___y_5700_);
lean_dec_ref(v___y_5699_);
lean_dec(v___y_5698_);
lean_dec_ref(v___y_5697_);
lean_dec_ref(v_args_5690_);
lean_dec_ref(v_fst_5689_);
lean_dec(v_upperBound_5688_);
return v_res_5706_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg___boxed(lean_object* v_upperBound_5707_, lean_object* v_fst_5708_, lean_object* v_args_5709_, lean_object* v___x_5710_, lean_object* v_compile_5711_, lean_object* v_logCompileErrors_5712_, lean_object* v_isMeta_5713_, lean_object* v___x_5714_, lean_object* v_a_5715_, lean_object* v_b_5716_, lean_object* v___y_5717_, lean_object* v___y_5718_, lean_object* v___y_5719_, lean_object* v___y_5720_, lean_object* v___y_5721_){
_start:
{
uint8_t v___x_123958__boxed_5722_; uint8_t v_compile_boxed_5723_; uint8_t v_logCompileErrors_boxed_5724_; uint8_t v_isMeta_boxed_5725_; uint8_t v___x_123959__boxed_5726_; lean_object* v_res_5727_; 
v___x_123958__boxed_5722_ = lean_unbox(v___x_5710_);
v_compile_boxed_5723_ = lean_unbox(v_compile_5711_);
v_logCompileErrors_boxed_5724_ = lean_unbox(v_logCompileErrors_5712_);
v_isMeta_boxed_5725_ = lean_unbox(v_isMeta_5713_);
v___x_123959__boxed_5726_ = lean_unbox(v___x_5714_);
v_res_5727_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_5707_, v_fst_5708_, v_args_5709_, v___x_123958__boxed_5722_, v_compile_boxed_5723_, v_logCompileErrors_boxed_5724_, v_isMeta_boxed_5725_, v___x_123959__boxed_5726_, v_a_5715_, v_b_5716_, v___y_5717_, v___y_5718_, v___y_5719_, v___y_5720_);
lean_dec(v___y_5720_);
lean_dec_ref(v___y_5719_);
lean_dec(v___y_5718_);
lean_dec_ref(v___y_5717_);
lean_dec_ref(v_args_5709_);
lean_dec_ref(v_fst_5708_);
lean_dec(v_upperBound_5707_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg___boxed(lean_object* v_upperBound_5728_, lean_object* v_fst_5729_, lean_object* v_args_5730_, lean_object* v___x_5731_, lean_object* v_compile_5732_, lean_object* v_logCompileErrors_5733_, lean_object* v_isMeta_5734_, lean_object* v___x_5735_, lean_object* v_a_5736_, lean_object* v_b_5737_, lean_object* v___y_5738_, lean_object* v___y_5739_, lean_object* v___y_5740_, lean_object* v___y_5741_, lean_object* v___y_5742_){
_start:
{
uint8_t v___x_124132__boxed_5743_; uint8_t v_compile_boxed_5744_; uint8_t v_logCompileErrors_boxed_5745_; uint8_t v_isMeta_boxed_5746_; uint8_t v___x_124133__boxed_5747_; lean_object* v_res_5748_; 
v___x_124132__boxed_5743_ = lean_unbox(v___x_5731_);
v_compile_boxed_5744_ = lean_unbox(v_compile_5732_);
v_logCompileErrors_boxed_5745_ = lean_unbox(v_logCompileErrors_5733_);
v_isMeta_boxed_5746_ = lean_unbox(v_isMeta_5734_);
v___x_124133__boxed_5747_ = lean_unbox(v___x_5735_);
v_res_5748_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_5728_, v_fst_5729_, v_args_5730_, v___x_124132__boxed_5743_, v_compile_boxed_5744_, v_logCompileErrors_boxed_5745_, v_isMeta_boxed_5746_, v___x_124133__boxed_5747_, v_a_5736_, v_b_5737_, v___y_5738_, v___y_5739_, v___y_5740_, v___y_5741_);
lean_dec(v___y_5741_);
lean_dec_ref(v___y_5740_);
lean_dec(v___y_5739_);
lean_dec_ref(v___y_5738_);
lean_dec_ref(v_args_5730_);
lean_dec_ref(v_fst_5729_);
lean_dec(v_upperBound_5728_);
return v_res_5748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(size_t v_sz_5749_, size_t v_i_5750_, lean_object* v_bs_5751_, lean_object* v___y_5752_, lean_object* v___y_5753_, lean_object* v___y_5754_, lean_object* v___y_5755_){
_start:
{
lean_object* v___x_5757_; 
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___redArg(v_sz_5749_, v_i_5750_, v_bs_5751_, v___y_5753_);
return v___x_5757_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5___boxed(lean_object* v_sz_5758_, lean_object* v_i_5759_, lean_object* v_bs_5760_, lean_object* v___y_5761_, lean_object* v___y_5762_, lean_object* v___y_5763_, lean_object* v___y_5764_, lean_object* v___y_5765_){
_start:
{
size_t v_sz_boxed_5766_; size_t v_i_boxed_5767_; lean_object* v_res_5768_; 
v_sz_boxed_5766_ = lean_unbox_usize(v_sz_5758_);
lean_dec(v_sz_5758_);
v_i_boxed_5767_ = lean_unbox_usize(v_i_5759_);
lean_dec(v_i_5759_);
v_res_5768_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_wrapInstance_spec__5(v_sz_boxed_5766_, v_i_boxed_5767_, v_bs_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_);
lean_dec(v___y_5764_);
lean_dec_ref(v___y_5763_);
lean_dec(v___y_5762_);
lean_dec_ref(v___y_5761_);
return v_res_5768_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(lean_object* v_upperBound_5769_, lean_object* v_fst_5770_, lean_object* v_args_5771_, uint8_t v_compile_5772_, uint8_t v_logCompileErrors_5773_, uint8_t v_isMeta_5774_, uint8_t v___x_5775_, lean_object* v_inst_5776_, lean_object* v_R_5777_, lean_object* v_a_5778_, lean_object* v_b_5779_, lean_object* v_c_5780_, lean_object* v___y_5781_, lean_object* v___y_5782_, lean_object* v___y_5783_, lean_object* v___y_5784_){
_start:
{
lean_object* v___x_5786_; 
v___x_5786_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___redArg(v_upperBound_5769_, v_fst_5770_, v_args_5771_, v_compile_5772_, v_logCompileErrors_5773_, v_isMeta_5774_, v___x_5775_, v_a_5778_, v_b_5779_, v___y_5781_, v___y_5782_, v___y_5783_, v___y_5784_);
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_5787_ = _args[0];
lean_object* v_fst_5788_ = _args[1];
lean_object* v_args_5789_ = _args[2];
lean_object* v_compile_5790_ = _args[3];
lean_object* v_logCompileErrors_5791_ = _args[4];
lean_object* v_isMeta_5792_ = _args[5];
lean_object* v___x_5793_ = _args[6];
lean_object* v_inst_5794_ = _args[7];
lean_object* v_R_5795_ = _args[8];
lean_object* v_a_5796_ = _args[9];
lean_object* v_b_5797_ = _args[10];
lean_object* v_c_5798_ = _args[11];
lean_object* v___y_5799_ = _args[12];
lean_object* v___y_5800_ = _args[13];
lean_object* v___y_5801_ = _args[14];
lean_object* v___y_5802_ = _args[15];
lean_object* v___y_5803_ = _args[16];
_start:
{
uint8_t v_compile_boxed_5804_; uint8_t v_logCompileErrors_boxed_5805_; uint8_t v_isMeta_boxed_5806_; uint8_t v___x_129214__boxed_5807_; lean_object* v_res_5808_; 
v_compile_boxed_5804_ = lean_unbox(v_compile_5790_);
v_logCompileErrors_boxed_5805_ = lean_unbox(v_logCompileErrors_5791_);
v_isMeta_boxed_5806_ = lean_unbox(v_isMeta_5792_);
v___x_129214__boxed_5807_ = lean_unbox(v___x_5793_);
v_res_5808_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6(v_upperBound_5787_, v_fst_5788_, v_args_5789_, v_compile_boxed_5804_, v_logCompileErrors_boxed_5805_, v_isMeta_boxed_5806_, v___x_129214__boxed_5807_, v_inst_5794_, v_R_5795_, v_a_5796_, v_b_5797_, v_c_5798_, v___y_5799_, v___y_5800_, v___y_5801_, v___y_5802_);
lean_dec(v___y_5802_);
lean_dec_ref(v___y_5801_);
lean_dec(v___y_5800_);
lean_dec_ref(v___y_5799_);
lean_dec_ref(v_args_5789_);
lean_dec_ref(v_fst_5788_);
lean_dec(v_upperBound_5787_);
return v_res_5808_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7(lean_object* v_00_u03b1_5809_, lean_object* v_msg_5810_, lean_object* v___y_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_, lean_object* v___y_5814_){
_start:
{
lean_object* v___x_5816_; 
v___x_5816_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___redArg(v_msg_5810_, v___y_5811_, v___y_5812_, v___y_5813_, v___y_5814_);
return v___x_5816_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7___boxed(lean_object* v_00_u03b1_5817_, lean_object* v_msg_5818_, lean_object* v___y_5819_, lean_object* v___y_5820_, lean_object* v___y_5821_, lean_object* v___y_5822_, lean_object* v___y_5823_){
_start:
{
lean_object* v_res_5824_; 
v_res_5824_ = l_Lean_throwError___at___00Lean_Meta_wrapInstance_spec__7(v_00_u03b1_5817_, v_msg_5818_, v___y_5819_, v___y_5820_, v___y_5821_, v___y_5822_);
lean_dec(v___y_5822_);
lean_dec_ref(v___y_5821_);
lean_dec(v___y_5820_);
lean_dec_ref(v___y_5819_);
return v_res_5824_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(lean_object* v_upperBound_5825_, lean_object* v_fst_5826_, lean_object* v_args_5827_, uint8_t v___x_5828_, uint8_t v_compile_5829_, uint8_t v_logCompileErrors_5830_, uint8_t v_isMeta_5831_, uint8_t v___x_5832_, lean_object* v_inst_5833_, lean_object* v_R_5834_, lean_object* v_a_5835_, lean_object* v_b_5836_, lean_object* v_c_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_, lean_object* v___y_5841_){
_start:
{
lean_object* v___x_5843_; 
v___x_5843_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___redArg(v_upperBound_5825_, v_fst_5826_, v_args_5827_, v___x_5828_, v_compile_5829_, v_logCompileErrors_5830_, v_isMeta_5831_, v___x_5832_, v_a_5835_, v_b_5836_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_);
return v___x_5843_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11___boxed(lean_object** _args){
lean_object* v_upperBound_5844_ = _args[0];
lean_object* v_fst_5845_ = _args[1];
lean_object* v_args_5846_ = _args[2];
lean_object* v___x_5847_ = _args[3];
lean_object* v_compile_5848_ = _args[4];
lean_object* v_logCompileErrors_5849_ = _args[5];
lean_object* v_isMeta_5850_ = _args[6];
lean_object* v___x_5851_ = _args[7];
lean_object* v_inst_5852_ = _args[8];
lean_object* v_R_5853_ = _args[9];
lean_object* v_a_5854_ = _args[10];
lean_object* v_b_5855_ = _args[11];
lean_object* v_c_5856_ = _args[12];
lean_object* v___y_5857_ = _args[13];
lean_object* v___y_5858_ = _args[14];
lean_object* v___y_5859_ = _args[15];
lean_object* v___y_5860_ = _args[16];
lean_object* v___y_5861_ = _args[17];
_start:
{
uint8_t v___x_129260__boxed_5862_; uint8_t v_compile_boxed_5863_; uint8_t v_logCompileErrors_boxed_5864_; uint8_t v_isMeta_boxed_5865_; uint8_t v___x_129261__boxed_5866_; lean_object* v_res_5867_; 
v___x_129260__boxed_5862_ = lean_unbox(v___x_5847_);
v_compile_boxed_5863_ = lean_unbox(v_compile_5848_);
v_logCompileErrors_boxed_5864_ = lean_unbox(v_logCompileErrors_5849_);
v_isMeta_boxed_5865_ = lean_unbox(v_isMeta_5850_);
v___x_129261__boxed_5866_ = lean_unbox(v___x_5851_);
v_res_5867_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11(v_upperBound_5844_, v_fst_5845_, v_args_5846_, v___x_129260__boxed_5862_, v_compile_boxed_5863_, v_logCompileErrors_boxed_5864_, v_isMeta_boxed_5865_, v___x_129261__boxed_5866_, v_inst_5852_, v_R_5853_, v_a_5854_, v_b_5855_, v_c_5856_, v___y_5857_, v___y_5858_, v___y_5859_, v___y_5860_);
lean_dec(v___y_5860_);
lean_dec_ref(v___y_5859_);
lean_dec(v___y_5858_);
lean_dec_ref(v___y_5857_);
lean_dec_ref(v_args_5846_);
lean_dec_ref(v_fst_5845_);
lean_dec(v_upperBound_5844_);
return v_res_5867_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(lean_object* v_upperBound_5868_, lean_object* v_fst_5869_, lean_object* v_args_5870_, uint8_t v___x_5871_, uint8_t v_compile_5872_, uint8_t v_logCompileErrors_5873_, uint8_t v_isMeta_5874_, lean_object* v_inst_5875_, lean_object* v_R_5876_, lean_object* v_a_5877_, lean_object* v_b_5878_, lean_object* v_c_5879_, lean_object* v___y_5880_, lean_object* v___y_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_){
_start:
{
lean_object* v___x_5885_; 
v___x_5885_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___redArg(v_upperBound_5868_, v_fst_5869_, v_args_5870_, v___x_5871_, v_compile_5872_, v_logCompileErrors_5873_, v_isMeta_5874_, v_a_5877_, v_b_5878_, v___y_5880_, v___y_5881_, v___y_5882_, v___y_5883_);
return v___x_5885_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13___boxed(lean_object** _args){
lean_object* v_upperBound_5886_ = _args[0];
lean_object* v_fst_5887_ = _args[1];
lean_object* v_args_5888_ = _args[2];
lean_object* v___x_5889_ = _args[3];
lean_object* v_compile_5890_ = _args[4];
lean_object* v_logCompileErrors_5891_ = _args[5];
lean_object* v_isMeta_5892_ = _args[6];
lean_object* v_inst_5893_ = _args[7];
lean_object* v_R_5894_ = _args[8];
lean_object* v_a_5895_ = _args[9];
lean_object* v_b_5896_ = _args[10];
lean_object* v_c_5897_ = _args[11];
lean_object* v___y_5898_ = _args[12];
lean_object* v___y_5899_ = _args[13];
lean_object* v___y_5900_ = _args[14];
lean_object* v___y_5901_ = _args[15];
lean_object* v___y_5902_ = _args[16];
_start:
{
uint8_t v___x_129292__boxed_5903_; uint8_t v_compile_boxed_5904_; uint8_t v_logCompileErrors_boxed_5905_; uint8_t v_isMeta_boxed_5906_; lean_object* v_res_5907_; 
v___x_129292__boxed_5903_ = lean_unbox(v___x_5889_);
v_compile_boxed_5904_ = lean_unbox(v_compile_5890_);
v_logCompileErrors_boxed_5905_ = lean_unbox(v_logCompileErrors_5891_);
v_isMeta_boxed_5906_ = lean_unbox(v_isMeta_5892_);
v_res_5907_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13(v_upperBound_5886_, v_fst_5887_, v_args_5888_, v___x_129292__boxed_5903_, v_compile_boxed_5904_, v_logCompileErrors_boxed_5905_, v_isMeta_boxed_5906_, v_inst_5893_, v_R_5894_, v_a_5895_, v_b_5896_, v_c_5897_, v___y_5898_, v___y_5899_, v___y_5900_, v___y_5901_);
lean_dec(v___y_5901_);
lean_dec_ref(v___y_5900_);
lean_dec(v___y_5899_);
lean_dec_ref(v___y_5898_);
lean_dec_ref(v_args_5888_);
lean_dec_ref(v_fst_5887_);
lean_dec(v_upperBound_5886_);
return v_res_5907_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25(lean_object* v_00_u03b1_5908_, lean_object* v_x_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_, lean_object* v___y_5912_, lean_object* v___y_5913_){
_start:
{
lean_object* v___x_5915_; 
v___x_5915_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___redArg(v_x_5909_);
return v___x_5915_;
}
}
LEAN_EXPORT lean_object* l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25___boxed(lean_object* v_00_u03b1_5916_, lean_object* v_x_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_wrapInstance_spec__15_spec__25(v_00_u03b1_5916_, v_x_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5(lean_object* v_00_u03b1_5924_, lean_object* v_constName_5925_, lean_object* v___y_5926_, lean_object* v___y_5927_, lean_object* v___y_5928_, lean_object* v___y_5929_){
_start:
{
lean_object* v___x_5931_; 
v___x_5931_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___redArg(v_constName_5925_, v___y_5926_, v___y_5927_, v___y_5928_, v___y_5929_);
return v___x_5931_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5___boxed(lean_object* v_00_u03b1_5932_, lean_object* v_constName_5933_, lean_object* v___y_5934_, lean_object* v___y_5935_, lean_object* v___y_5936_, lean_object* v___y_5937_, lean_object* v___y_5938_){
_start:
{
lean_object* v_res_5939_; 
v_res_5939_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5(v_00_u03b1_5932_, v_constName_5933_, v___y_5934_, v___y_5935_, v___y_5936_, v___y_5937_);
lean_dec(v___y_5937_);
lean_dec_ref(v___y_5936_);
lean_dec(v___y_5935_);
lean_dec_ref(v___y_5934_);
return v_res_5939_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8(lean_object* v_upperBound_5940_, lean_object* v_fst_5941_, lean_object* v_args_5942_, uint8_t v_compile_5943_, uint8_t v_logCompileErrors_5944_, uint8_t v_isMeta_5945_, uint8_t v___x_5946_, lean_object* v_inst_5947_, lean_object* v_R_5948_, lean_object* v_a_5949_, lean_object* v_b_5950_, lean_object* v_c_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_, lean_object* v___y_5954_, lean_object* v___y_5955_){
_start:
{
lean_object* v___x_5957_; 
v___x_5957_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___redArg(v_upperBound_5940_, v_fst_5941_, v_args_5942_, v_compile_5943_, v_logCompileErrors_5944_, v_isMeta_5945_, v___x_5946_, v_a_5949_, v_b_5950_, v___y_5952_, v___y_5953_, v___y_5954_, v___y_5955_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8___boxed(lean_object** _args){
lean_object* v_upperBound_5958_ = _args[0];
lean_object* v_fst_5959_ = _args[1];
lean_object* v_args_5960_ = _args[2];
lean_object* v_compile_5961_ = _args[3];
lean_object* v_logCompileErrors_5962_ = _args[4];
lean_object* v_isMeta_5963_ = _args[5];
lean_object* v___x_5964_ = _args[6];
lean_object* v_inst_5965_ = _args[7];
lean_object* v_R_5966_ = _args[8];
lean_object* v_a_5967_ = _args[9];
lean_object* v_b_5968_ = _args[10];
lean_object* v_c_5969_ = _args[11];
lean_object* v___y_5970_ = _args[12];
lean_object* v___y_5971_ = _args[13];
lean_object* v___y_5972_ = _args[14];
lean_object* v___y_5973_ = _args[15];
lean_object* v___y_5974_ = _args[16];
_start:
{
uint8_t v_compile_boxed_5975_; uint8_t v_logCompileErrors_boxed_5976_; uint8_t v_isMeta_boxed_5977_; uint8_t v___x_129358__boxed_5978_; lean_object* v_res_5979_; 
v_compile_boxed_5975_ = lean_unbox(v_compile_5961_);
v_logCompileErrors_boxed_5976_ = lean_unbox(v_logCompileErrors_5962_);
v_isMeta_boxed_5977_ = lean_unbox(v_isMeta_5963_);
v___x_129358__boxed_5978_ = lean_unbox(v___x_5964_);
v_res_5979_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__6_spec__8(v_upperBound_5958_, v_fst_5959_, v_args_5960_, v_compile_boxed_5975_, v_logCompileErrors_boxed_5976_, v_isMeta_boxed_5977_, v___x_129358__boxed_5978_, v_inst_5965_, v_R_5966_, v_a_5967_, v_b_5968_, v_c_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_);
lean_dec(v___y_5973_);
lean_dec_ref(v___y_5972_);
lean_dec(v___y_5971_);
lean_dec_ref(v___y_5970_);
lean_dec_ref(v_args_5960_);
lean_dec_ref(v_fst_5959_);
lean_dec(v_upperBound_5958_);
return v_res_5979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15(lean_object* v_upperBound_5980_, lean_object* v_fst_5981_, lean_object* v_args_5982_, uint8_t v___x_5983_, uint8_t v_compile_5984_, uint8_t v_logCompileErrors_5985_, uint8_t v_isMeta_5986_, uint8_t v___x_5987_, lean_object* v_inst_5988_, lean_object* v_R_5989_, lean_object* v_a_5990_, lean_object* v_b_5991_, lean_object* v_c_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_){
_start:
{
lean_object* v___x_5998_; 
v___x_5998_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___redArg(v_upperBound_5980_, v_fst_5981_, v_args_5982_, v___x_5983_, v_compile_5984_, v_logCompileErrors_5985_, v_isMeta_5986_, v___x_5987_, v_a_5990_, v_b_5991_, v___y_5993_, v___y_5994_, v___y_5995_, v___y_5996_);
return v___x_5998_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15___boxed(lean_object** _args){
lean_object* v_upperBound_5999_ = _args[0];
lean_object* v_fst_6000_ = _args[1];
lean_object* v_args_6001_ = _args[2];
lean_object* v___x_6002_ = _args[3];
lean_object* v_compile_6003_ = _args[4];
lean_object* v_logCompileErrors_6004_ = _args[5];
lean_object* v_isMeta_6005_ = _args[6];
lean_object* v___x_6006_ = _args[7];
lean_object* v_inst_6007_ = _args[8];
lean_object* v_R_6008_ = _args[9];
lean_object* v_a_6009_ = _args[10];
lean_object* v_b_6010_ = _args[11];
lean_object* v_c_6011_ = _args[12];
lean_object* v___y_6012_ = _args[13];
lean_object* v___y_6013_ = _args[14];
lean_object* v___y_6014_ = _args[15];
lean_object* v___y_6015_ = _args[16];
lean_object* v___y_6016_ = _args[17];
_start:
{
uint8_t v___x_129387__boxed_6017_; uint8_t v_compile_boxed_6018_; uint8_t v_logCompileErrors_boxed_6019_; uint8_t v_isMeta_boxed_6020_; uint8_t v___x_129388__boxed_6021_; lean_object* v_res_6022_; 
v___x_129387__boxed_6017_ = lean_unbox(v___x_6002_);
v_compile_boxed_6018_ = lean_unbox(v_compile_6003_);
v_logCompileErrors_boxed_6019_ = lean_unbox(v_logCompileErrors_6004_);
v_isMeta_boxed_6020_ = lean_unbox(v_isMeta_6005_);
v___x_129388__boxed_6021_ = lean_unbox(v___x_6006_);
v_res_6022_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__11_spec__15(v_upperBound_5999_, v_fst_6000_, v_args_6001_, v___x_129387__boxed_6017_, v_compile_boxed_6018_, v_logCompileErrors_boxed_6019_, v_isMeta_boxed_6020_, v___x_129388__boxed_6021_, v_inst_6007_, v_R_6008_, v_a_6009_, v_b_6010_, v_c_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_);
lean_dec(v___y_6015_);
lean_dec_ref(v___y_6014_);
lean_dec(v___y_6013_);
lean_dec_ref(v___y_6012_);
lean_dec_ref(v_args_6001_);
lean_dec_ref(v_fst_6000_);
lean_dec(v_upperBound_5999_);
return v_res_6022_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19(lean_object* v_upperBound_6023_, lean_object* v_fst_6024_, lean_object* v_args_6025_, uint8_t v___x_6026_, uint8_t v_compile_6027_, uint8_t v_logCompileErrors_6028_, uint8_t v_isMeta_6029_, lean_object* v_inst_6030_, lean_object* v_R_6031_, lean_object* v_a_6032_, lean_object* v_b_6033_, lean_object* v_c_6034_, lean_object* v___y_6035_, lean_object* v___y_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_){
_start:
{
lean_object* v___x_6040_; 
v___x_6040_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___redArg(v_upperBound_6023_, v_fst_6024_, v_args_6025_, v___x_6026_, v_compile_6027_, v_logCompileErrors_6028_, v_isMeta_6029_, v_a_6032_, v_b_6033_, v___y_6035_, v___y_6036_, v___y_6037_, v___y_6038_);
return v___x_6040_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19___boxed(lean_object** _args){
lean_object* v_upperBound_6041_ = _args[0];
lean_object* v_fst_6042_ = _args[1];
lean_object* v_args_6043_ = _args[2];
lean_object* v___x_6044_ = _args[3];
lean_object* v_compile_6045_ = _args[4];
lean_object* v_logCompileErrors_6046_ = _args[5];
lean_object* v_isMeta_6047_ = _args[6];
lean_object* v_inst_6048_ = _args[7];
lean_object* v_R_6049_ = _args[8];
lean_object* v_a_6050_ = _args[9];
lean_object* v_b_6051_ = _args[10];
lean_object* v_c_6052_ = _args[11];
lean_object* v___y_6053_ = _args[12];
lean_object* v___y_6054_ = _args[13];
lean_object* v___y_6055_ = _args[14];
lean_object* v___y_6056_ = _args[15];
lean_object* v___y_6057_ = _args[16];
_start:
{
uint8_t v___x_129419__boxed_6058_; uint8_t v_compile_boxed_6059_; uint8_t v_logCompileErrors_boxed_6060_; uint8_t v_isMeta_boxed_6061_; lean_object* v_res_6062_; 
v___x_129419__boxed_6058_ = lean_unbox(v___x_6044_);
v_compile_boxed_6059_ = lean_unbox(v_compile_6045_);
v_logCompileErrors_boxed_6060_ = lean_unbox(v_logCompileErrors_6046_);
v_isMeta_boxed_6061_ = lean_unbox(v_isMeta_6047_);
v_res_6062_ = l_WellFounded_opaqueFix_u2083___at___00WellFounded_opaqueFix_u2083___at___00Lean_Meta_wrapInstance_spec__13_spec__19(v_upperBound_6041_, v_fst_6042_, v_args_6043_, v___x_129419__boxed_6058_, v_compile_boxed_6059_, v_logCompileErrors_boxed_6060_, v_isMeta_boxed_6061_, v_inst_6048_, v_R_6049_, v_a_6050_, v_b_6051_, v_c_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
lean_dec(v___y_6056_);
lean_dec_ref(v___y_6055_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec_ref(v_args_6043_);
lean_dec_ref(v_fst_6042_);
lean_dec(v_upperBound_6041_);
return v_res_6062_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7(lean_object* v_00_u03b1_6063_, lean_object* v_ref_6064_, lean_object* v_constName_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_, lean_object* v___y_6068_, lean_object* v___y_6069_){
_start:
{
lean_object* v___x_6071_; 
v___x_6071_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___redArg(v_ref_6064_, v_constName_6065_, v___y_6066_, v___y_6067_, v___y_6068_, v___y_6069_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7___boxed(lean_object* v_00_u03b1_6072_, lean_object* v_ref_6073_, lean_object* v_constName_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7(v_00_u03b1_6072_, v_ref_6073_, v_constName_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
lean_dec(v_ref_6073_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21(lean_object* v_00_u03b1_6081_, lean_object* v_ref_6082_, lean_object* v_msg_6083_, lean_object* v_declHint_6084_, lean_object* v___y_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_, lean_object* v___y_6088_){
_start:
{
lean_object* v___x_6090_; 
v___x_6090_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___redArg(v_ref_6082_, v_msg_6083_, v_declHint_6084_, v___y_6085_, v___y_6086_, v___y_6087_, v___y_6088_);
return v___x_6090_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21___boxed(lean_object* v_00_u03b1_6091_, lean_object* v_ref_6092_, lean_object* v_msg_6093_, lean_object* v_declHint_6094_, lean_object* v___y_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_){
_start:
{
lean_object* v_res_6100_; 
v_res_6100_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21(v_00_u03b1_6091_, v_ref_6092_, v_msg_6093_, v_declHint_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v___y_6096_);
lean_dec_ref(v___y_6095_);
lean_dec(v_ref_6092_);
return v_res_6100_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31(lean_object* v_msg_6101_, lean_object* v_declHint_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_){
_start:
{
lean_object* v___x_6108_; 
v___x_6108_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___redArg(v_msg_6101_, v_declHint_6102_, v___y_6106_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31___boxed(lean_object* v_msg_6109_, lean_object* v_declHint_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_, lean_object* v___y_6115_){
_start:
{
lean_object* v_res_6116_; 
v_res_6116_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__29_spec__31(v_msg_6109_, v_declHint_6110_, v___y_6111_, v___y_6112_, v___y_6113_, v___y_6114_);
lean_dec(v___y_6114_);
lean_dec_ref(v___y_6113_);
lean_dec(v___y_6112_);
lean_dec_ref(v___y_6111_);
return v_res_6116_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30(lean_object* v_00_u03b1_6117_, lean_object* v_ref_6118_, lean_object* v_msg_6119_, lean_object* v___y_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v___x_6125_; 
v___x_6125_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___redArg(v_ref_6118_, v_msg_6119_, v___y_6120_, v___y_6121_, v___y_6122_, v___y_6123_);
return v___x_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30___boxed(lean_object* v_00_u03b1_6126_, lean_object* v_ref_6127_, lean_object* v_msg_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_){
_start:
{
lean_object* v_res_6134_; 
v_res_6134_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_wrapInstance_spec__4_spec__5_spec__7_spec__21_spec__30(v_00_u03b1_6126_, v_ref_6127_, v_msg_6128_, v___y_6129_, v___y_6130_, v___y_6131_, v___y_6132_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
lean_dec(v_ref_6127_);
return v_res_6134_;
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
